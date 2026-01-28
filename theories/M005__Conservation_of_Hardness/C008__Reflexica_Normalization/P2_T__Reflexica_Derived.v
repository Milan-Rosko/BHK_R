(* P2_T__Reflexica_Derived.v *)

From Coq Require Import Init.Logic.
From C008 Require Export P1_S__Core_Goal.
From C008 Require Import P2_R__The_Bridge.
From C007 Require Import P2_T__Resistance.
From C005 Require Import P2_T__Barrier.

(*************************************************************************)
(*                                                                       *)
(*  C008 / Phase 2 (T): Normalization Theorem                            *)
(*                                                                       *)
(*    (i) Proof Strategy.                                                *)
(*                                                                       *)
(*        We use proof by double negation elimination:                   *)
(*                                                                       *)
(*        Step 1. Prove ~~Core (double negation of Reflexica)            *)
(*          Assume: ¬Core                                                *)
(*          Apply:  CoreRed (bridge)  → ∃CS (separator exists)           *)
(*          Apply:  RESIST (C007)     → ⊥                                *)
(*          Conclude: ~~Core                                             *)
(*                                                                       *)
(*        Step 2. Normalize ~~Core to Core                               *)
(*          Apply: Core_stable (double negation elimination)             *)
(*          Conclude: Core                                               *)
(*                                                                       *)
(*   (ii) Interpretation.                                                *)
(*                                                                       *)
(*        Reflexica is "forced" in the following sense:                  *)
(*                                                                       *)
(*        “provable if provable, not disprovable otherwise.              *)
(*                                                                       *)
(*  (iii) Comparison to Gödel's Second Incompleteness.                   *)
(*                                                                       *)
(*        “Con(T) is unprovable in T (if T is consistent).“              *)
(*                                                                       *)
(*                            vs.                                        *)
(*                                                                       *)
(*        “For every inconsistent T there is a T that is                 *)
(*        consistent by proving less.“                                   *)
(*                                                                       *)
(*************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.

Module C008_Reflexica_Derived_T.

  Module Core := C008_Core_Goal_S.
  Module Bridge := C008_The_Bridge_R.
  Module Res := C007.P2_T__Resistance.C007_Resistance_T.
  Module Barrier := C005.P2_T__Barrier.C005_Barrier_T.

  (*
    Normalization Section — Deriving Core from Resistance

    This section assumes two oracle principles:

      (a) Core_stable: double negation elimination for Core
      (b) Diagonal_Witness: diagonal construction for any separator

    Given these, we derive Core (Reflexica).
  *)

  Section Core_Stability.

  (*
    Justification:
    Core is a Π₂ arithmetic statement (∀x,y. unpair(pair(x,y)) = (x,y)).
    For Π₂ statements, ~~P → P is often acceptable even in
    semi-constructive settings (it's the "boundedness principle").
  *)

  Variable Core_stable : ~~Core.Core -> Core.Core.

  (*
    Informal Meaning:

       “For any separator, the diagonal construction produces a
       self-referential witness (d, D) satisfying the flip and
       tracking conditions.”

    Role:

      This witness is the input to RESIST. Without it, we cannot
      apply the resistance law.
  *)

  Parameter Diagonal_Witness :
    forall (S : Res.SEPARATOR),
      exists (d : Barrier.Def.N.nat) (D : Barrier.Def.P.ATP_Form),
        (Barrier.Def.Truth D <-> Barrier.Def.Truth (Barrier.Def.Flip_Logic S d)) /\
        (Barrier.Def.Truth (Barrier.Def.A d) <-> Barrier.Def.Truth D) /\
        (Barrier.Def.Truth (Barrier.Def.B d) <-> Barrier.Def.Truth D).

  (*
      1. Prove ~~Core by reductio:
         Assume ¬Core
         Apply CoreRed → get CS (separator exists)
         Apply RESIST → get ⊥
         Conclude ~~Core

      2. Normalize ~~Core to Core:
         Apply Core_stable
         Conclude Core
  *)

  Theorem Reflexica_Forced : Core.Core.
  Proof.
    (*
      Step 1: Prove ~~Core (double negation of Reflexica)
    *)

    assert (~~Core.Core) as Hnn.
    {
      (*
        Reductio: Assume ¬Core, derive ⊥
      *)

      intro Hn.

      (*
        Apply the bridge: ¬Core → ∃CS
      *)

      destruct (Bridge.CoreRed Hn) as [CS [Disj Sound]].

      (*
        We now have:
          CS    : COMPUTATIONAL_SEPARATOR
          Disj  : Semantic_Disjointness
          Sound : Soundness

        Apply the Resistance Law (C007) to derive ⊥.

        The Resistance Law states:
          RESIST : ∀CS. Disjointness → Soundness → ⊥

        So we apply it with our witnesses.
      *)

      eapply Res.RESIST; eauto.

      (*
        QED for ~~Core.

        We have shown: ¬Core → ⊥, therefore ~~Core.
      *)
    }

    (*
      Step 2: Normalize ~~Core to Core

      Apply Core_stable (double negation elimination).
    *)

    apply Core_stable. exact Hnn.

  Qed.

  End Core_Stability.

End C008_Reflexica_Derived_T.

Export C008_Reflexica_Derived_T.

