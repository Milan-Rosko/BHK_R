
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val the_Fermat_Barrier : __ **)

let the_Fermat_Barrier =
  __
