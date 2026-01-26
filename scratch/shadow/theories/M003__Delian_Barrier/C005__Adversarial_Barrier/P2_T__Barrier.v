(* P2_T__Barrier.v *)

(*************************************************************************)
(*                                                                       *)
(*  C005 / Phase 2 (T): The Adversarial Barrier Theorem (Public Surface) *)
(*                                                                       *)
(*  What This File Provides                                              *)
(*                                                                       *)
(*    The public-facing Adversarial Barrier theorem:                     *)
(*                                                                       *)
(*      ∀S : SEPARATOR. Diagonal_Witness(S) → ⊥                          *)
(*                                                                       *)
(*    A packaged impossibility result for certified separators.          *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.
From Adversarial_Barrier.C005 Require Export P1_S__Barrier_Definition.
From Adversarial_Barrier.C005 Require Import P2_R__Barrier_Proof.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  Module: C005_Barrier_T_F (Functor for Parametric Export)             *)
(*                                                                       *)
(*  Provides the barrier theorem parametrized by barrier context Ctx.    *)
(*                                                                       *)
(*  Purpose:                                                             *)
(*                                                                       *)
(*    Enables modular composition with varying semantic interpretations  *)
(*    of A, B, and Truth.                                                *)
(*                                                                       *)
(*************************************************************************)

Module C005_Barrier_T_F (Ctx : C005_Barrier_Ctx).
  Module Proof := C005_Barrier_Proof_F(Ctx).
  Module Def := Proof.Def.

  (*
    Type Exports for Public Interface

    SEPARATOR    — Certified decision device (parametric)
    Disjointness — Semantic disjointness predicate
  *)

  Definition SEPARATOR := Def.SEPARATOR.
  Definition Disjointness := Def.Semantic_Disjointness.

  (***********************************************************************)
  (*                                                                     *)
  (*  Theorem: Adversarial_Barrier (Functor Version)                     *)
  (*                                                                     *)
  (*  The main impossibility theorem for certified separators.           *)
  (*                                                                     *)
  (*    No certified separator can exist when fed to a diagonal device   *)
  (*    that creates self-referential sentences via flip logic.          *)
  (*                                                                     *)
  (*    The diagonal witness D collapses A(d) and B(d) together,         *)
  (*    violating semantic disjointness.                                 *)
  (*                                                                     *)
  (***********************************************************************)

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

    (*
      Direct application of Barrier_Law from realization layer (P2_R).
    *)

    exact (@Proof.Barrier_Law S Is_Disjoint Soundness Hdiag).
  Qed.

End C005_Barrier_T_F.

(***********************************************************************)
(*                                                                     *)
(*  Recommended Usage:                                                 *)
(*                                                                     *)
(*   Users want to import this module rather than the functor.         *)
(*                                                                     *)
(***********************************************************************)

Module C005_Barrier_T.
  Module Def := C005_Barrier_Def_S.

  (*
    Type Exports for Public Interface

    SEPARATOR    — Certified decision device record
    Disjointness — Semantic disjointness predicate
  *)
  
  Definition SEPARATOR := Def.SEPARATOR.
  Definition Disjointness := Def.Semantic_Disjointness.

  (***********************************************************************)
  (*                                                                     *)
  (*  Theorem: Adversarial_Barrier (Canonical Export)                    *)
  (*                                                                     *)
  (*  This is the recommended entry point for downstream use.            *)
  (*                                                                     *)
  (*  Statement (Informal):                                              *)
  (*                                                                     *)
  (*    “No certified separator can exist.”                              *)
  (*                                                                     *)
  (*  Statement (Formal):                                                *)
  (*                                                                     *)
  (*    ∀S : SEPARATOR.                                                  *)
  (*      Disjoint(A, B) ∧ Sound(Prov) ∧ Diagonal(S) → ⊥                 *)
  (*                                                                     *)
  (*    There exists (d, D) such that:                                   *)
  (*                                                                     *)
  (*      Truth(D) ↔ Truth(Flip(S, d))                                   *)
  (*      Truth(A(d)) ↔ Truth(D)                                         *)
  (*      Truth(B(d)) ↔ Truth(D)                                         *)
  (*                                                                     *)
  (*    This forces Truth(A(d)) ↔ Truth(B(d)), violating disjointness.   *)
  (*                                                                     *)
  (***********************************************************************)

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

    (*
      Apply Barrier_Law from realization layer (P2_R).
      Uses eapply/eauto for clean proof interface.
    *)

    eapply C005_Barrier_Proof_R.Barrier_Law; eauto.
  Qed.

End C005_Barrier_T.

Export C005_Barrier_T.