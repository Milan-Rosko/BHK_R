(* P2_T__Public_Surface.v *)

From Coq Require Import Init.Logic.

From C000 Require Export P0__BHK.
From C000 Require Export P0__Reflexica.

From C001 Require Export P5_T__Carryless_Pairing.
From C002 Require Export P5_T__Proof_Theory.
From C003 Require Export P2_T__Diagonal.
From C004 Require Export P3_T__Weakforcing.
From C005 Require Export P2_T__Barrier.
From C006 Require Export P1_S__Context.
From C006 Require Export P2_T__Audit_Barrier.
From C007 Require Export P2_T__Resistance.
From C008 Require Export P2_T__Reflexica_Derived.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C008 / Phase 5 (T): Public Stable Surface                            *)
(*                                                                       *)
(*  The Complete ProofCase Stack — Public API                            *)
(*                                                                       *)
(*  What This File Provides                                              *)
(*                                                                       *)
(*    Layer 1: Arithmetic Foundation (M001)                              *)
(*      C000 — BHK_R nucleus (nat, O, S)                                 *)
(*      C001 — Carryless pairing device                                  *)
(*      C002 — Additive Hilbert system (proof theory)                    *)
(*                                                                       *)
(*    Layer 2: Diagonal Construction (M002)                              *)
(*      C003 — Carryless diagonal lemma                                  *)
(*      C004 — Mirror lemma (weak forcing, As-If)                        *)
(*                                                                       *)
(*    Layer 3: Impossibility Barriers (M003)                             *)
(*      C005 — Adversarial barrier (no certified separators)             *)
(*      C006 — Audit barrier (no self-auditing systems)                  *)
(*      C007 — Resistance law (computational separators impossible)      *)
(*      C008 — Reflexica normalization (forced truth)                    *)
(*                                                                       *)
(*  Design Discipline                                                    *)
(*                                                                       *)
(*    This file intentionally excludes certificate axioms (Reflexica     *)
(*    from C001/P6_A). It provides only the stable, provable theorems.   *)
(*                                                                       *)
(*    Certificate axioms are imported explicitly when needed, not        *)
(*    bundled into the public surface.                                   *)
(*                                                                       *)
(*  Usage                                                                *)
(*                                                                       *)
(*    Import this file to access the complete ProofCase stack:           *)
(*                                                                       *)
(*      From C008 Require Import                 *)
(*        P2_T__Public_Surface.                                          *)
(*                                                                       *)
(*    Then use module-qualified names:                                   *)
(*                                                                       *)
(*      C008_Public_T.Diagonal.diag                                      *)
(*      C008_Public_T.Barrier.Adversarial_Barrier                        *)
(*      C008_Public_T.Resistance.RESIST                                  *)
(*                                                                       *)
(*************************************************************************)

Module C008_Public_T.

  (*************************************************************************)
  (*                                                                       *)
  (*  Layer 1. Arithmetic Foundation (M001)                                *)
  (*                                                                       *)
  (*************************************************************************)

  (*
    Prelude — BHK_R Nucleus (C000)

    The minimal arithmetic core:
      nat, O, S (naturals with zero and successor)

    This is the foundational type theory for all constructions.
  *)

  Module Prelude := C000.P0__BHK.BHK.

  (*
    Pairing — Carryless Pairing Device (C001)

    Effective pairing device:
      pair   : nat → nat → nat
      unpair : nat → nat × nat

    Computationally effective but axiom-free (no Reflexica certificate).
  *)

  Module Pairing := C001.P5_T__Carryless_Pairing.

  (*
    ProofTheory — Additive Hilbert System (C002)

    Proof theory interface:
      ATP_Form : Type (formulas)
      ATP_Prov : Form → Prop (provability predicate)

    Provides the formal logic for barrier constructions.
  *)

  Module ProofTheory := C002.P5_T__Proof_Theory.

  (*************************************************************************)
  (*                                                                       *)
  (*  Layer 2. Diagonal Construction (M002)                                *)
  (*                                                                       *)
  (*************************************************************************)

  (*
    Diagonal — Carryless Diagonal Lemma (C003)

    Diagonal construction device:
      diag : Template → Form
      diag_spec_code : ⌈diag(t)⌉ = ⟦Eₜ⟧(selfpack(⌈δₜ⌉))

    Phase-safe diagonal construction (axiom-free, total).
  *)

  Module Diagonal := C003.P2_T__Diagonal.

  (*
    Mirror — Weak Forcing & As-If (C004)

    Mirror lemma and weak forcing interface:
      AsIF(φ) — "As-If" predicate (forced state)
      Mirror_fixed_witness : ¬Prov(¬φ) → AsIF(φ)

    Bridges meta-level non-refutability to object-level As-If.
  *)

  Module Mirror := C004.P3_T__Weakforcing.

  (*************************************************************************)
  (*                                                                       *)
  (*  Layer 3. Impossibility Barriers (M003)                               *)
  (*                                                                       *)
  (*************************************************************************)

  (*
    Barrier — Adversarial Barrier (C005)

    Main impossibility theorem:
      Adversarial_Barrier : SEPARATOR → ⊥

    No certified separator can exist when fed to diagonal device.
  *)

  Module Barrier := C005.P2_T__Barrier.

  (*
    Audit_Context, Audit_Barrier — Audit Barrier (C006)

    Self-auditing impossibility:
      Audit_Barrier : DECIDER_T → ¬AuditInt

    A system cannot both decide completely and self-audit.
  *)

  Module Audit_Context := C006.P1_S__Context.
  Module Audit_Barrier := C006.P2_T__Audit_Barrier.

  (*
    Resistance — Resistance Law (C007)

    Computational separator impossibility:
      RESIST : COMPUTATIONAL_SEPARATOR → ⊥

    "Computational separators resist their own construction."
  *)

  Module Resistance := C007.P2_T__Resistance.

  (*
    Reflexica_Derived — Reflexica Normalization (C008)

    Derived truth of Reflexica via resistance:
      The carryless pairing inversion law is "forced to be true"
      by the impossibility of computational separators.
  *)

  Module Reflexica_Derived := C008.P2_T__Reflexica_Derived.

End C008_Public_T.

Export C008_Public_T.
