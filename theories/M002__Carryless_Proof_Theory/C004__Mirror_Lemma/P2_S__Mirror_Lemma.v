(* P2_S__Mirror_Lemma.v *)

From Coq Require Import Init.Logic.
From ATP.C004__Mirror_Lemma Require Import P1_S__Context.
From ATP.C004__Mirror_Lemma Require Import P2_R__Mirror_Core.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C004 / Phase 2 (S): Mirror Lemma Façade                              *)
(*                                                                       *)
(*  What This File Provides                                              *)
(*                                                                       *)
(*    (i) Semantic Façade for the Mirror Core.                           *)
(*        Aggregates the Context (P1) and the Realization (P2_R)         *)
(*        into a single module structure.                                *)
(*                                                                       *)
(*    (i) Usage Policy.                                                  *)
(*        This layer hides the internal R-file organization.             *)
(*        Consumers of the fixed-witness theorem should import this      *)
(*        file (or the T-layer), not the P2_R realization directly.      *)
(*                                                                       *)
(*  The Mirror Lemma (Fixed-Witness Pattern)                             *)
(*                                                                       *)
(*    For any formula φ, there exists a fixed point ψ such that:         *)
(*                                                                       *)
(*      Prov(ψ ↔ φ(⌜ψ⌝))                                                 *)
(*                                                                       *)
(*    This is the semantic foundation for the Recursive Mirror Lemma.    *)
(*                                                                       *)
(*************************************************************************)

Module C_004_Mirror_S.
  Include C_004_Context.

  (*
    The Core Lemma — Fixed-Witness Pattern

    Imported from the realization layer (P2_R__Mirror_Core).
  *)

  Include C_004_Mirror_Core_R.
End C_004_Mirror_S.

Export C_004_Mirror_S.
