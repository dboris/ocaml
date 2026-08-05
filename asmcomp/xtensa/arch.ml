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

open Format

let command_line_options = []

type specific_operation = unit

type addressing_mode = Iindexed of int

(* Whether the backend emits immutable static data into a separate
   read-only section.  When it does, [Cmm_helpers.data_segment_table]
   registers that section as a second static data segment per unit, so
   that both halves are still classified [In_static_data]. *)
let rodata_section = true

let big_endian = false

let size_addr = 4
let size_int = size_addr
let size_float = 8

let allow_unaligned_access = false
let division_crashes_on_overflow = false 

let identity_addressing = Iindexed 0
let offset_addressing (Iindexed n) delta = 
    Iindexed(n + delta)
let num_args_addressing = function 
    | Iindexed _ -> 1


let print_addressing printreg addr ppf arg =
    match addr with 
    | Iindexed n -> printreg ppf arg.(0);
    if n <> 0 then fprintf ppf ", %i" n

let print_specific_operation _printreg _op _ppf _arg = ()

(* Specific operations that are pure *)

let operation_is_pure _ = true

(* Specific operations that can raise *)

let operation_can_raise _ = false

