(* P1_T__Arithmetic_Surface.v *)

From Fermat_Machine.C014 Require Export P1_S__Fermat_Interface P1_R__Peano_Arithmetic.
Import Fermat_Interface.

Module C014_Arithmetic_T.

  (*
    Re-export Nucleus
  *)
  Module N := P1_R__Peano_Arithmetic.N.

  (*
    Re-export Triple for downstream modules
  *)

  Definition Triple : Type := Fermat_Interface.Triple.

  (*
    Concrete Relation Definition
  *)

  Definition Fermat_Relation (n : N.nat) (t : Triple) : Prop :=
    let '(a, b, c) := t in
      (P1_R__Peano_Arithmetic.leb (P1_R__Peano_Arithmetic.three) n = true) /\ (* n > 2 *)
      (a <> N.O) /\ (b <> N.O) /\ (c <> N.O) /\
      (N.add (P1_R__Peano_Arithmetic.pow a n)
             (P1_R__Peano_Arithmetic.pow b n) = P1_R__Peano_Arithmetic.pow c n).

  (*
    Basic Notations
  *)
  
  Declare Scope bhk_scope.
  Delimit Scope bhk_scope with bhk.
  Bind Scope bhk_scope with N.nat.

  Definition lt (n m : N.nat) : Prop := P1_R__Peano_Arithmetic.leb (N.S n) m = true.
  Definition gt (n m : N.nat) : Prop := lt m n.
  Notation "a > b" := (gt a b) (at level 70) : bhk_scope.

End C014_Arithmetic_T.
