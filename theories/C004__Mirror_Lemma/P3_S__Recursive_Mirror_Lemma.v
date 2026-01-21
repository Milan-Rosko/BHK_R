(* P3_S__Recursive_Mirror_Lemma.v *)

(*************************************************************************)
(*                                                                       *)
(*  C_004 / Phase 3 (S): Recursive Mirror Façade                         *)
(*                                                                       *)
(*  What this file provides.                                             *)
(*                                                                       *)
(*    (i) The Semantic Façade for the Recursive Extension.               *)
(*        It exposes the machinery required to apply the Mirror Lemma    *)
(*        to self-referential sentences (via the Diagonal).              *)
(*                                                                       *)
(*   (ii) Why is this separate?                                          *)
(*        The Core (P2) deals with static formulas.                      *)
(*        The Recursive layer (P3) deals with dynamic fixed points.      *)
(*        This separation ensures that the core logic of "AsIF" is       *)
(*        not entangled with the complexity of the Diagonal Device.      *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.
From ATP.C004__Mirror_Lemma Require Import P1_S__Context.
From ATP.C004__Mirror_Lemma Require Import P2_R__Mirror_Transport.

Set Implicit Arguments.
Unset Strict Implicit.

Module C_004_Recursive_Mirror_S.
  Include C_004_Context.
  (* The Recursive Extension *)
  Include C_004_Recursive_Mirror_R.
End C_004_Recursive_Mirror_S.

Export C_004_Recursive_Mirror_S.
