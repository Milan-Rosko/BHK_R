(* P1_R__PCC.v — realization: concrete code + proof terms over the BHK core. *)
Require Import P0_S__bhk.
Import BHK.

Set Implicit Arguments.
Unset Strict Implicit.

Module PCC_R.

  (*************************************************************************)
  (*                                                                       *)
  (* Realization: explicit code + explicit proof terms                     *)
  (*                                                                       *)
  (* This file depends only on the Phase-0 BHK core (P0_S__bhk).           *)
  (* Computation is by kernel conversion plus explicit recursion/ind.      *)
  (*                                                                       *)
  (*************************************************************************)

  (* The code we want to carry *)
  Definition add_to_O : nat -> nat := fun n => add n O.

  (* The certificate: not definitional in general, requires induction *)
  Theorem add_O_r : forall n : nat, add n O = n.
  Proof.
    intro n.
    induction n as [| n' IH].
    - simpl. exact (eq_refl _).
    - simpl. rewrite IH. exact (eq_refl _).
  Qed.

End PCC_R.

Export PCC_R.
