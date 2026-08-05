(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*       Lucas Pluvinage, OCaml Labs intern, ENS Paris student            *)
(*                                                                        *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open Misc
open Cmm
open Reg
open Mach

(* Instruction selection *)

let word_addressed = false

(*
  Integer register map:
    a0       return address
    a1       stack pointer
    a2 - a7  general purpose (preserved on call)
    a8 - a14 general purpose (not preserved)
    a15      scratch register

  Floating point registers (single precision)
    f0       trap pointer (preserved)
    f1       allocation pointer (preserved)
    f2       domain state pointer (preserved)
    f8       temp float for neg/abs
*)

(* Registers available for register allocation.
Floating point registers are useless in a floating point computing purpose
as they are single precision (whereas OCaml uses double precision floats.) *)
(* Maybe we could use them as another class of general purpose registers.*)
(* Moving from general purpose to fp has a latency of 2 instructions cycles *)
let int_reg_name =
  [|"a2"; "a3"; "a4"; "a5"; "a6"; "a7";
    "a8"; "a9"; "a10"; "a11"; "a12"; "a13"; "a14"|]

let num_register_classes = 1

let register_class r =
  match r.typ with
  | Val | Int | Addr -> 0
  | Float -> 0

let num_available_registers = [| 13 |]

let first_available_register = [| 0 |]

let register_name r = assert (r < 13);int_reg_name.(r)

let rotate_registers = true

(* Representation of hard registers by pseudo-registers *)
let hard_int_reg =
  let v = Array.make 13 Reg.dummy in
  for i = 0 to 12 do v.(i) <- Reg.at_location Int (Reg i) done; v

let all_phys_regs = hard_int_reg

let phys_reg n = hard_int_reg.(n)

let stack_slot slot ty =
  Reg.at_location ty (Stack slot)

(******************** OCaml compilation scheme on ESP32. **********************

Xtensa LX6 processor has 64 registers, but only 16 are visible by standard
instructions. The "window" of visible registers can be rotated by function
calls and returns, thus acting as a physical stack with overlaps to be able to
pass parameters and return values.

There are mechanisms for automatic spilling when the stack overflows
(happening generally after a depth of eight C calls) which put the registers in
pre-defined spaces on the stack. This increases efficiency by reducing register
spilling, as long as the program doesn't swing much in call depth.

C code is compiled using this ABI, but I choose to start with a regular calling
convention for OCaml, as it seems that windowed calling conventions are not
supported (`loc_results` doesn't take into account the fact that the caller's
result register is different from the callee's result register.).

As a consequence:
C is called using windowed calls (CALL4 = rotate window by 4 registers).
OCaml to OCaml calls are made using CALL0. (no register window rotation).
The weirdnesses in the runtime are mainly to ensure compatibility between the
two ABIs.
*)

let loc_int last_reg make_stack reg ofs =
  if !reg <= last_reg then begin
    let l = phys_reg !reg in
    incr reg; l
  end else begin
    let l = stack_slot (make_stack !ofs) Int in
    ofs := !ofs + 4; l
  end

let loc_int_pair last_reg make_stack reg ofs =
  (* 64-bit quantities occupy either a consecutive pair of registers whose
     lowest numbered one is even, or an 8-byte aligned pair of stack
     slots. *)
  reg := Misc.align !reg 2;
  if !reg + 1 <= last_reg then begin
    let reg_lower = phys_reg !reg
    and reg_upper = phys_reg (!reg + 1) in
    reg := !reg + 2;
    [| reg_lower; reg_upper |]
  end else begin
    ofs := Misc.align !ofs 8;
    let stack_lower = stack_slot (make_stack !ofs) Int
    and stack_upper = stack_slot (make_stack (!ofs + 4)) Int in
    ofs := !ofs + 8;
    [| stack_lower; stack_upper |]
  end

let calling_conventions
    first_reg last_reg make_stack arg =
  let loc = Array.make (Array.length arg) Reg.dummy in
  let current_reg = ref first_reg in
  let stack_ofs = ref 0 in
  for i = 0 to Array.length arg - 1 do
    match arg.(i) with
    | Val | Int | Addr ->
        loc.(i) <- loc_int last_reg make_stack current_reg stack_ofs
    | Float ->
        (* Selection.regs_for expands Float into a pair of integer
           registers, the FPU being single-precision only, so no Float
           component reaches here. *)
        fatal_error "Proc.calling_conventions: unexpected Float component"
  done;
  (loc, Misc.align !stack_ofs 16)

let incoming ofs = Incoming ofs
let outgoing ofs = Outgoing ofs
let not_supported _ofs = fatal_error "Proc.loc_results: cannot call"

let max_arguments_for_tailcalls = 6

(*
 * Calling conventions CALL0 ABI
 * a0 Return Address
 * a1 sp (preserved)
 * a2 – a7 Function Arguments
 *)
let loc_arguments arg =
  calling_conventions 0 5 outgoing arg

let loc_parameters arg =
  let (loc, _ofs) =
    calling_conventions 0 5 incoming arg
  in
  loc

let loc_results res =
  let (loc, _ofs) =
    calling_conventions 0 3 not_supported res
  in
  loc

(*
 * Calling conventions CALL4 ABI
 * a4 Return Address
 * a5 Callee's stack pointer (set by ENTRY)
 * a6 – a11 Function Arguments
 * Return in a6 – a9
 * a2 and a3 are saved.
 *)
let loc_external_results res =
  let (loc, _ofs) =
    calling_conventions 4 7 not_supported res
  in
  loc

let external_calling_conventions
    first_reg last_reg make_stack ty_args =
  let loc = Array.make (List.length ty_args) [| Reg.dummy |] in
  let current_reg = ref first_reg in
  let stack_ofs = ref 0 in
  List.iteri
    (fun i ty_arg ->
      match ty_arg with
      | XInt | XInt32 ->
          loc.(i) <- [| loc_int last_reg make_stack current_reg stack_ofs |]
      | XInt64 | XFloat ->
          loc.(i) <- loc_int_pair last_reg make_stack current_reg stack_ofs)
    ty_args;
  (loc, Misc.align !stack_ofs 16)

let loc_external_arguments ty_args =
  external_calling_conventions 4 9 outgoing ty_args

(* a2 *)
let loc_exn_bucket = phys_reg 0

let regs_are_volatile _rs = false

let call4_destroyed =
  Array.of_list(List.map phys_reg
    [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12])

let destroyed_at_oper = function
  | Iop(Icall_ind | Icall_imm _)
  | Iop(Iextcall { alloc = true; _}) -> all_phys_regs
  | Iop(Iextcall { alloc = false; _}) -> call4_destroyed
  | Iop(Ialloc { bytes = (8 | 12 | 16); _ }) ->
    (* a11-a15 are destroyed by the caml_alloc{1,2,3} helpers. *)
    Array.of_list(List.map phys_reg [9; 10; 11; 12])
  | Iop(Ialloc _) ->
    (* caml_allocN additionally takes its size argument in a2. *)
    Array.of_list(List.map phys_reg [0; 9; 10; 11; 12])
  | _ -> [||]

let destroyed_at_raise = all_phys_regs

let destroyed_at_reloadretaddr = [| |]

(* Maximal register pressure *)
let safe_register_pressure = function
  | Iextcall _ -> 0
  | Icall_ind | Icall_imm _ -> 0
  | Ialloc _ -> 0
  | _ -> 13

let max_register_pressure arg = [| safe_register_pressure arg |]

(* Layout of the stack *)

(* New requirements. *)

let frame_required fd =
  fd.fun_contains_calls
    || fd.fun_num_stack_slots.(0) > 0

let prologue_required fd =
  frame_required fd


let dwarf_register_numbers ~reg_class:_ = [|
  2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15
|]

let stack_ptr_dwarf_register_number = 1

(* Calling the assembler *)

let assemble_file infile outfile =
  Ccomp.command (Config.asm ^ " -o " ^
                 Filename.quote outfile ^ " " ^ Filename.quote infile)

let init () = ()
