(* P2_S__Mirror_Lemma.v *)

(*************************************************************************)
(*                                                                       *)
(*  C_004 / Phase 2 (S): Mirror Lemma Façade                             *)
(*                                                                       *)
(*  What this file provides.                                             *)
(*                                                                       *)
(*    (i) The Semantic Façade for the Mirror Core.                       *)
(*        It aggregates the Context (P1) and the Realization (P2_R)      *)
(*        into a single module structure.                                *)
(*                                                                       *)
(*   (ii) Usage Policy.                                                  *)
(*        This layer hides the internal "R" file organization.           *)
(*        Consumers of the fixed-witness theorem should import this      *)
(*        file (or the T-layer P5), not the P2_R realization directly.   *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.
From ATP.C004__Mirror_Lemma Require Import P1_S__Context.
From ATP.C004__Mirror_Lemma Require Import P2_R__Mirror_Core.

Set Implicit Arguments.
Unset Strict Implicit.

Module C_004_Mirror_S.
  Include C_004_Context.
  (* The Core Lemma: Fixed-Witness Pattern *)
  Include C_004_Mirror_Core_R.
End C_004_Mirror_S.

Export C_004_Mirror_S.
