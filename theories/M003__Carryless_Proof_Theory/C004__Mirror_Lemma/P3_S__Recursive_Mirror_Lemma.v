(* P3_S__Recursive_Mirror_Lemma.v *)

(*************************************************************************)
(*                                                                       *)
(*  C004 / Phase 3 (S): Recursive Mirror Façade                          *)
(*                                                                       *)
(*  What This File Provides                                              *)
(*                                                                       *)
(*   (i)    Semantic Façade for the Recursive Extension.                 *)
(*          Exposes the machinery required to apply the Mirror Lemma     *)
(*          to self-referential sentences (via the Diagonal Device).     *)
(*                                                                       *)
(*   (ii)   Why separate?                                                *)
(*                                                                       *)
(*          Core (P2):       Static formulas φ                           *)
(*          Recursive (P3):  Dynamic fixed points ψ ≜ diag(φ)            *)
(*                                                                       *)
(*          This separation ensures that the core "As-If" logic is not   *)
(*          entangled with the complexity of diagonal construction.      *)
(*                                                                       *)
(*  The Recursive Mirror Schema combines the Mirror Lemma with the       *)
(*  Diagonal Device, given template φ(□), construct ψ ≜ diag(φ):         *)
(*                                                                       *)
(*                           Prov(ψ ↔ φ(⌜ψ⌝)).                           *)
(*                                                                       *)
(*   This is the semantic foundation for “Gödel's First Incompleteness   *)
(*   Theorem” and “Löb's Theorem.”                                          *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.
From C004 Require Import P1_S__Context.
From C004 Require Import P2_R__Mirror_Transport.

Set Implicit Arguments.
Unset Strict Implicit.

Module C_004_Recursive_Mirror_S.
  Include C_004_Context.

  (*
    The Recursive Extension,
    Mirror + Diagonal
    Imported from the realization layer (P2_R__Mirror_Transport).
  *)

  Include C_004_Recursive_Mirror_R.
End C_004_Recursive_Mirror_S.

Export C_004_Recursive_Mirror_S.
