(* P3_S__Machine_Definition.v *)

From Fermat_Machine.C014 Require Import P1_T__Arithmetic_Surface.
From Quintic_Hardness.C011 Require Import P1_S__Diophantine_Basis.

Module Machine_Definition.
  Import C014_Arithmetic_T.
  Module Rad := Quintic_Hardness.C011.P1_S__Diophantine_Basis.C011_Diophantine_S.

  (** A Radical (Primitive Recursive) Machine M *)
  Definition Radical (M : N.nat -> Triple) : Prop :=
    Rad.Solvable_By_Radicals (fun n => let '(a, _, _) := M n in a) /\
    Rad.Solvable_By_Radicals (fun n => let '(_, b, _) := M n in b) /\
    Rad.Solvable_By_Radicals (fun n => let '(_, _, c) := M n in c).

  (** The Fermat Machine: A Radical generator of witnesses for n > 2 *)
  Definition Fermat_Machine (M : N.nat -> Triple) : Prop :=
    Radical M /\
    (forall n, gt n P1_R__Peano_Arithmetic.two -> Fermat_Relation n (M n)).

End Machine_Definition.
