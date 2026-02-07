(* P2_S__Mirror_Lemma.v *)

From Coq Require Import Init.Logic.
From C004 Require Import P1_S__Context.
From C004 Require Import P2_R__Mirror_Core.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C004 / Phase 2 (S): Mirror Facade (Core + Recursive)                 *)
(*                                                                       *)
(*  This facade is the primary entry point for the Mirror Lemma          *)
(*  machinery. It re-exports:                                            *)
(*                                                                       *)
(*   (i)    Context (Form, Prov, Imp, Bot, NotF)                         *)
(*                                                                       *)
(*   (ii)   Mirror (AsIF, Mir, fixed-witness lemma)                      *)
(*                                                                       *)
(*   (iii)  Recursive Mirror (MirrorPointF, theta, Recursive_Mirror)     *)
(*                                                                       *)
(*  The Phase-3 facade (P3_S) remains for compatibility, but this file   *)
(*  is the recommended semantic import.                                  *)
(*                                                                       *)
(*************************************************************************)

(*************************************************************************)
(*                                                                       *)
(* Reader Walkthrough (Step by Step)                                     *)
(*                                                                       *)
(*   (i)   Formal constraint.                                            *)
(*         A consistent r.e. theory T cannot prove a global reflection   *)
(*         bridge (Prov -> True) about itself. This is the Gödel–Löb     *)
(*         barrier to internal self-certification.                       *)
(*                                                                       *)
(*   (ii)  Operational consequence.                                      *)
(*         A system that must act under incompleteness cannot remain     *)
(*         purely syntactic; it needs a disciplined way to treat some    *)
(*         unrefuted statements as admissible.                           *)
(*                                                                       *)
(*   (iii) Regulator mechanism (formal).                                 *)
(*         The core file defines AsIF and Mir:                           *)
(*           AsIF(phi) := exists i,b. REG(i,b) /\ BND(phi,b) /\          *)
(*                        Prov(phi -> b) /\ not ProvT_P(not phi).        *)
(*         This is not a truth relation; it is admissibility.            *)
(*                                                                       *)
(*   (iv)  Observational AsIF (level distinction).                       *)
(*         AsIF is an external, observational predicate: it captures     *)
(*         a stance the system enacts but cannot, in general, assert      *)
(*         about itself. The stance is enacted, not stated.              *)
(*                                                                       *)
(*   (v)   AsIF as systemhood (interpretive layer).                      *)
(*         Systemhood is the ability to maintain coherence under         *)
(*         undecidability. AsIF is the minimal formal operator that      *)
(*         accomplishes this without violating consistency: it upgrades  *)
(*         non-refutability into a regulated stance.                     *)
(*                                                                       *)
(*   (vi)  Operational surrogate and propagation (interpretive).         *)
(*         Let sigma express "this system is globally coherent." T       *)
(*         cannot prove sigma, but operational coherence forces an       *)
(*         AsIF(sigma) stance. Observers “see” the stable AsIF-pattern   *)
(*         and treat the systemhood claim as admissible. The identity    *)
(*         is practical, not provable: a stable as-if equivalence, not a *)
(*         theorem.                                                      *)
(*                                                                       *)
(*************************************************************************)

Module C_004_Mirror_S.
  Include C_004_Context.
  Include C_004_Mirror_Core_R.
  Include C_004_Recursive_Mirror_R.
End C_004_Mirror_S.

Export C_004_Mirror_S.
