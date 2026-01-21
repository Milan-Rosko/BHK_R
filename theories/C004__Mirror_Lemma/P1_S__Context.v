(* P1_S__Context.v *)

(*************************************************************************)
(*                                                                       *)
(*  C_004 / Phase 1 (S): Mirror Context & Negation Definition            *)
(*                                                                       *)
(*  What this file provides.                                             *)
(*                                                                       *)
(*    (i) The local logical context for the Mirror Lemma.                *)
(*        It re-exports the Additive Theory of Provability (C002)        *)
(*        under a minimal, stable vocabulary.                            *)
(*                                                                       *)
(*   (ii) The canonical definition of Object-Language Negation (NotF).   *)
(*         Since the C002 object language is an implicational fragment   *)
(*         with Bottom, negation is derived, not primitive.              *)
(*                                                                       *)
(*         Role in the Mirror Lemma.                                     *)
(*                                                                       *)
(*    (i) The Mirror Schema relates meta-level non-refutability to       *)
(*        object-level bounding ("As-If").                               *)
(*                                                                       *)
(*   (ii) This requires a precise definition of "refutation" inside      *)
(*        the object logic. We fix this here as:                         *)
(*                                                                       *)
(*         NotF(phi) := phi -> Bot                                       *)
(*                                                                       *)
(*         Design Discipline.                                            *)
(*                                                                       *)
(*    (i) Alias Stability: Local names (Form, Prov, Imp) ensure that     *)
(*        the Core (P2) and Recursive (P3) layers are decoupled from     *)
(*        the specific path of the C002 implementation.                  *)
(*                                                                       *)
(*   (ii) Negation as Implication: By defining NotF explicitly here,     *)
(*        we prevent ambiguity between intuitionistic negation and       *)
(*        potential classical extensions in downstream use.              *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.
From ATP.C002 Require Import P5_T__Proof_Theory.

Set Implicit Arguments.
Unset Strict Implicit.

Module C_004_Context.

  Module Prelude := ATP.C002.P5_T__Proof_Theory.Prelude.
  Module ATP     := ATP.C002.P5_T__Proof_Theory.ATP.

  Definition nat  : Type := Prelude.nat.
  Definition Form : Type := ATP.ATP_Form.

  Definition Imp  : Form -> Form -> Form := ATP.ATP_Imp.
  Definition Bot  : Form := ATP.ATP_Bot.
  Definition Prov : Form -> Prop := ATP.ATP_Prov.

  (* Object-language negation: phi -> Bot *)
  Definition NotF (phi : Form) : Form := Imp phi Bot.

End C_004_Context.

Export C_004_Context.
