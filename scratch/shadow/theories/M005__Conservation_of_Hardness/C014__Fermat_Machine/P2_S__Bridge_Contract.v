(* P2_S__Bridge_Contract.v *)

From C014 Require Import P1_T__Arithmetic_Surface.
From C012 Require Import P1_S__Structure.

Module Bridge_Contract.
  Module Str := C012.P1_S__Structure.C012_Structure_S.
  Import C014_Arithmetic_T.

  (* 
    The Bridge Contract: A Fermat Witness implies Diophantine Solvability
  *)
  
  Parameter Fermat_Triple_Implies_Solvable :
    forall (t : Triple) (n : N.nat),
      Fermat_Relation n t ->
      Str.Solvable (Str.decode_equation n).

  (*
    Domain constraint
  *)

  Parameter Index_Condition : forall n : N.nat, gt n P1_R__Peano_Arithmetic.two.

End Bridge_Contract.
