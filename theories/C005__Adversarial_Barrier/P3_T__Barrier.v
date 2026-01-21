(* P3_T__Barrier.v *)
(* theories/C005__Adversarial_Barrier/P3_T__Barrier.v                   *)
(***********************************************************************)

From Coq Require Import Init.Logic.
From Adversarial_Barrier.C005 Require Export P1_S__Barrier_Definition.
From Adversarial_Barrier.C005 Require Import P2_R__Barrier_Proof.

Set Implicit Arguments.
Unset Strict Implicit.

Module C005_Barrier_T.
  Module Def := C005_Barrier_Def_S.

  Definition SEPARATOR := Def.SEPARATOR.
  Definition Disjointness := Def.Semantic_Disjointness.

  Theorem Adversarial_Barrier :
    forall (S : Def.SEPARATOR)
           (Is_Disjoint : Def.Semantic_Disjointness)
           (Soundness : forall phi, Def.P.ATP_Prov phi -> Def.Truth phi),
      (exists (d : Def.N.nat) (D : Def.P.ATP_Form),
        (Def.Truth D <-> Def.Truth (Def.Flip_Logic S d)) /\
        (Def.Truth (Def.A d) <-> Def.Truth D) /\
        (Def.Truth (Def.B d) <-> Def.Truth D))
      -> False.
  Proof.
    intros S Is_Disjoint Soundness Hdiag.
    eapply C005_Barrier_Proof_R.Barrier_Law; eauto.
  Qed.

End C005_Barrier_T.

Export C005_Barrier_T.
