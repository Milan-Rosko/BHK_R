(* P2_R__Barrier_Proof.v *)

From Coq Require Import Init.Logic.
From C002 Require Import P5_T__Proof_Theory.
From C005 Require Import P1_S__Barrier_Definition.

Set Implicit Arguments.
Unset Strict Implicit.

Module C005_Barrier_Proof_F (Ctx : C005_Barrier_Ctx).

  Module Def := C005_Barrier_Def_F(Ctx).
  Module P := C002.P5_T__Proof_Theory.ATP.

  Section The_Trap.

  Variable S : Def.SEPARATOR.

  (* 
    Disjointness: Program is consistent (A and B cannot both be true).
  *)

  Hypothesis Is_Disjoint : Def.Semantic_Disjointness.

  (*
    Soundness: The system respects the Program (Prov -> Truth).
  *)

  Hypothesis Soundness : forall phi, P.ATP_Prov phi -> Def.Truth phi.

  (*
    Diagonal existence and truth tracking.
  *)

  Hypothesis Adversarial_Diagonal :
    exists (d : Def.N.nat) (D : P.ATP_Form),
      (Def.Truth D <-> Def.Truth (Def.Flip_Logic S d)) /\
      (Def.Truth (Def.A d) <-> Def.Truth D) /\
      (Def.Truth (Def.B d) <-> Def.Truth D).

  Theorem Barrier_Law : False.
  Proof.
    destruct Adversarial_Diagonal as [d [D [H_FixedPoint [H_TrackA H_TrackB]]]].

    destruct (S.(Def.sigma) d) eqn:Heq_dec.

    - (*
        Decision = true: certified A, flip gives B.
      *)

      pose proof (S.(Def.cert) d) as H_Prov_Outcome.
      rewrite Heq_dec in H_Prov_Outcome.
      pose proof (Soundness (phi := Def.A d) H_Prov_Outcome) as HTruthA.

      pose proof (proj1 H_TrackA HTruthA) as HTruthD.
      unfold Def.Flip_Logic in H_FixedPoint; rewrite Heq_dec in H_FixedPoint.
      pose proof (proj1 H_FixedPoint HTruthD) as HTruthB.

      exact (Is_Disjoint (n := d) HTruthA HTruthB).

    - (*
        Decision = false: certified B, flip gives A.
      *)

      pose proof (S.(Def.cert) d) as H_Prov_Outcome.
      rewrite Heq_dec in H_Prov_Outcome.
      pose proof (Soundness (phi := Def.B d) H_Prov_Outcome) as HTruthB.

      pose proof (proj1 H_TrackB HTruthB) as HTruthD.
      unfold Def.Flip_Logic in H_FixedPoint; rewrite Heq_dec in H_FixedPoint.
      pose proof (proj1 H_FixedPoint HTruthD) as HTruthA.

      exact (Is_Disjoint (n := d) HTruthA HTruthB).
  Qed.

  End The_Trap.

End C005_Barrier_Proof_F.

Module C005_Barrier_Proof_R.

  Module Def := C005_Barrier_Def_S.
  Module P := C002.P5_T__Proof_Theory.ATP.

  Section The_Trap.

  Variable S : Def.SEPARATOR.

  (*
    Disjointness: Program is consistent (A and B cannot both be true).
  *)

  Hypothesis Is_Disjoint : Def.Semantic_Disjointness.

  (*
    Soundness: The system respects the Program (Prov -> Truth).
  *)

  Hypothesis Soundness : forall phi, P.ATP_Prov phi -> Def.Truth phi.

  (* 
    Diagonal existence and truth tracking.
  *)

  Hypothesis Adversarial_Diagonal :
    exists (d : Def.N.nat) (D : P.ATP_Form),
      (Def.Truth D <-> Def.Truth (Def.Flip_Logic S d)) /\
      (Def.Truth (Def.A d) <-> Def.Truth D) /\
      (Def.Truth (Def.B d) <-> Def.Truth D).

  Theorem Barrier_Law : False.
  Proof.
    destruct Adversarial_Diagonal as [d [D [H_FixedPoint [H_TrackA H_TrackB]]]].

    destruct (S.(Def.sigma) d) eqn:Heq_dec.

    - (*
        Decision = true: certified A, flip gives B.
      *)

      pose proof (S.(Def.cert) d) as H_Prov_Outcome.
      rewrite Heq_dec in H_Prov_Outcome.
      pose proof (Soundness (phi := Def.A d) H_Prov_Outcome) as HTruthA.

      pose proof (proj1 H_TrackA HTruthA) as HTruthD.
      unfold Def.Flip_Logic in H_FixedPoint; rewrite Heq_dec in H_FixedPoint.
      pose proof (proj1 H_FixedPoint HTruthD) as HTruthB.

      exact (Is_Disjoint (n := d) HTruthA HTruthB).

    - (*
        Decision = false: certified B, flip gives A.
      *)

      pose proof (S.(Def.cert) d) as H_Prov_Outcome.
      rewrite Heq_dec in H_Prov_Outcome.
      pose proof (Soundness (phi := Def.B d) H_Prov_Outcome) as HTruthB.

      pose proof (proj1 H_TrackB HTruthB) as HTruthD.
      unfold Def.Flip_Logic in H_FixedPoint; rewrite Heq_dec in H_FixedPoint.
      pose proof (proj1 H_FixedPoint HTruthD) as HTruthA.

      exact (Is_Disjoint (n := d) HTruthA HTruthB).
  Qed.

  End The_Trap.

End C005_Barrier_Proof_R.

Export C005_Barrier_Proof_R.
