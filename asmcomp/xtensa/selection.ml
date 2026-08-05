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

open Arch
open Cmm
open Mach

let is_offset chunk n = match chunk with 
  | Byte_unsigned | Byte_signed -> n >= 0 && n <= 255
  | Sixteen_unsigned | Sixteen_signed -> n >= 0 && n <= 510 && n mod 2 == 0
  | _ -> n >= 0 && n <= 1020 && n mod 4 == 0


class selector = object (self)

inherit Selectgen.selector_generic as super 

method! regs_for tyv =
  Reg.createv (begin
                 (* Expand floats into pairs of integer registers *)
                 let rec expand = function
                   [] -> []
                 | Float :: tyl -> Int :: Int :: expand tyl
                 | ty :: tyl -> ty :: expand tyl in
                 Array.of_list (expand (Array.to_list tyv))
               end
               )

(* Xtensa has no andi/ori/xori/subi, and the generic Iintop_imm path in
   emit.mlp just suffixes the mnemonic with "i", so no integer operation
   may take an immediate operand.  Overrides the default, which would
   admit shift immediates. *)
method! is_immediate _op _n = false

method is_immediate_test _op _n = false

method private iextcall func ty_res ty_args =
  Iextcall { func; ty_res; ty_args; alloc = false; }

method! select_operation op args dbg =
  match (op, args) with 
    | (Cmuli, args) -> (Iintop Imul, args)
    | (Cmulhi, args) -> (Iintop Imulh, args)
    | (Cdivi, args) -> (Iintop Idiv, args)
    | (Cmodi, args) -> (Iintop Imod, args)
    | _ -> self#select_operation_softfp op args dbg

(* As the FP co-processor is single precision, there's no use for OCaml and 
 we must fall back to soft floating point. *)
method select_operation_softfp op args dbg = 
  match (op, args) with 
    | (Caddf, args) ->
        (self#iextcall "__adddf3" typ_float [XFloat;XFloat], args)
    | (Cmulf, args) ->
        (self#iextcall "__muldf3" typ_float [XFloat;XFloat], args)
    | (Cdivf, args) ->
        (self#iextcall "__divdf3" typ_float [XFloat;XFloat], args)
    | (Csubf, args) ->
        (self#iextcall "__subdf3" typ_float [XFloat;XFloat], args)
    | (Cfloatofint, args) ->
        (self#iextcall "__floatsidf" typ_float [XInt], args)
    | (Cintoffloat, args) ->
        (self#iextcall "__fixdfsi" typ_int [XFloat], args)
    | (Ccmpf comp, args) ->
        let fn, comp = match comp with 
          | CFeq -> "__eqdf2", Ceq
          | CFneq -> "__nedf2", Cne
          | CFlt -> "__ltdf2", Clt
          | CFle -> "__ledf2", Cle
          | CFgt -> "__gtdf2", Cgt
          | CFge -> "__gedf2", Cge
          | CFnlt -> "__ltdf2", Cge
          | CFnle -> "__ledf2", Cgt
          | CFngt -> "__gtdf2", Cle
          | CFnge -> "__gedf2", Clt
        in
        (Iintop_imm(Icomp(Isigned comp), 0),
        [Cop(Cextcall(fn, typ_int, [XFloat;XFloat], false), args, dbg)])
    | (Cload (Single, mut), args) ->
      (self#iextcall "__extendsfdf2" typ_float [XInt],
        [Cop(Cload (Word_int, mut), args, dbg)])
    | (Cstore (Single, init), [arg1; arg2]) ->
      let arg2' =
        Cop(Cextcall("__truncdfsf2", typ_int, [XFloat], false),
            [arg2], dbg) in
      self#select_operation (Cstore (Word_int, init)) [arg1; arg2'] dbg
    | _ -> super#select_operation op args dbg

method! select_condition = function 
  (* Turn fp comparisons into runtime ABI calls *)
  | Cop(Ccmpf _ as op, args, dbg) ->
      begin match self#select_operation_softfp op args dbg with
        | (Iintop_imm(Icomp(Isigned cmp), 0), [arg]) -> 
            (Iinttest_imm(Isigned cmp, 0), arg)
        | _ -> assert false
      end
  | expr ->
      super#select_condition expr

method select_addressing chunk = function 
  | Cop((Cadda | Caddv), [arg; Cconst_int (n, _)], _)
    when is_offset chunk n -> 
      (Iindexed n, arg)
  | Cop((Cadda | Caddv as op), [arg1; Cop(Caddi, [arg2; Cconst_int (n, _)], _)], dbg)
    when is_offset chunk n ->
      (Iindexed n, Cop(op, [arg1; arg2], dbg))
  | arg -> 
      (Iindexed 0, arg)

end 

let fundecl ~future_funcnames f =
  (new selector)#emit_fundecl ~future_funcnames f 