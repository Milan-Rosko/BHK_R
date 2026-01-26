(* P1_S__Fermat_Interface.v *)

Require Import BHK_R.C000.P0__BHK.
Module N := BHK_R.C000.P0__BHK.BHK.

Module Fermat_Interface.

  (*
    The Semantic Triple: (a, b, c)
  *)
  Definition Triple : Type := (N.nat * N.nat * N.nat)%type.

  (*
    The Relation: a^n + b^n = c^n
    We define the signature here; implementation of pow is in R.
  *)
  
  Parameter Fermat_Relation_Sig : N.nat -> Triple -> Prop.

End Fermat_Interface.
