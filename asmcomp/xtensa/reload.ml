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


class reload = object 

inherit Reloadgen.reload_generic as _super 

end

let fundecl f num_stack_slots =
  (new reload)#fundecl f num_stack_slots
