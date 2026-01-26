(* P1_S__Context.v *)

From Coq Require Import Init.Logic.
From ATP.C002 Require Import P5_T__Proof_Theory.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C004 / Phase 1 (S): Mirror Context & Negation Definition             *)
(*                                                                       *)
(*  What This File Provides                                              *)
(*                                                                       *)
(*    (i)   The local logical context for the "Mirror Lemma."            *)
(*          We re-export the Additive Theory of Provability (C002)       *)
(*          under a minimal, stable vocabulary.                          *)
(*                                                                       *)
(*    (ii)  The canonical definition of object-language negation (¬).    *)
(*          Since the C002 object language is an implicational fragment  *)
(*          with ⊥, negation is derived, not primitive:                  *)
(*                                                                       *)
(*           ¬φ  ≜  φ → ⊥                                                *)
(*                                                                       *)
(*  Role in the Mirror Lemma                                             *)
(*                                                                       *)
(*      Meta-level non-refutability  ←→  Object-level "As-If" bounding   *)
(*                                                                       *)
(*    This requires a precise definition of "refutation" inside the      *)
(*    object logic. We fix:                                              *)
(*                                                                       *)
(*      Refute(φ) ≜ Prov(¬φ) ≜ Prov(φ → ⊥)                               *)
(*                                                                       *)
(*  The Recursive Mirror Lemma                                           *)
(*                                                                       *)
(*    (i)   Final frontier: The theorem itself becomes its own fixed     *)
(*          point (Quinean self-reference).                              *)
(*                                                                       *)
(*    (ii)  Yet it still obeys the laws of logic (consistency is         *)
(*          preserved through stratification).                           *)
(*                                                                       *)
(*  Design Discipline                                                    *)
(*                                                                       *)
(*    (i)   Alias Stability: Local names (Form, Prov, Imp) decouple      *)
(*          the Core (P2) and Recursive (P3) layers from the specific    *)
(*          import path of C002.                                         *)
(*                                                                       *)
(*    (ii)  Negation as Implication: Defining NotF explicitly prevents   *)
(*          ambiguity between intuitionistic negation and potential      *)
(*          classical extensions in downstream use.                      *)
(*                                                                       *)
(*************************************************************************)

Module C_004_Context.

  Module Prelude := ATP.C002.P5_T__Proof_Theory.Prelude.
  Module ATP     := ATP.C002.P5_T__Proof_Theory.ATP.

  Definition nat  : Type := Prelude.nat.
  Definition Form : Type := ATP.ATP_Form.

  Definition Imp  : Form -> Form -> Form := ATP.ATP_Imp.
  Definition Bot  : Form := ATP.ATP_Bot.
  Definition Prov : Form -> Prop := ATP.ATP_Prov.

  (*
    Object-Language Negation

    Since the object logic is an implicational fragment with ⊥,
    negation is derived:

      ¬φ  ≜  φ → ⊥

    This is the standard intuitionistic treatment of negation.
  *)

  Definition NotF (phi : Form) : Form := Imp phi Bot.

End C_004_Context.

Export C_004_Context.
