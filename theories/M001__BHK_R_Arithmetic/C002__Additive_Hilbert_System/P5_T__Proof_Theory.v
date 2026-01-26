(* P5_T__Proof_Theory.v *)

From Coq Require Import Init.Logic.

From ATP.C002 Require Export
  P1_S__Kernel_Spec
  P2_S__Provability_Interface
  P3_S__Additive_Theory
  P4_S__Coding.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C002 / Phase 5 (T) : Additive Proof Theory (Public Surface)          *)
(*                                                                       *)
(*  Role.                                                                *)
(*                                                                       *)
(*    (i) This module exports the stable API for the Additive Theory of  *)
(*   (ii) Provability. It hides the distinction between R (Realization)  *)
(*  (iii) S (Semantic) layers, presenting a unified view of the logic.   *)
(*                                                                       *)
(*  Components.                                                          *)
(*                                                                       *)
(*    (i) Prelude: The arithmetic nucleus (re-exported).                 *)
(*   (ii) ATP: The core logic (formulas, implication, provability).      *)
(*  (iii) Coding: The canonical codec (formulas <-> nat).                *)
(*                                                                       *)
(*************************************************************************)

Module Prelude.
  Include ATP.C002.P1_S__Kernel_Spec.C_002_Prelim.
  Include BHK_R.C000.P0__Reflexica.Prelude.
End Prelude.

Module ATP    := ATP.C002.P3_S__Additive_Theory.C_002_Additive_Theory_S.
Module Coding := ATP.C002.P4_S__Coding.C_002_Coding_S.

(*
  Preferred downstream surface: additive provability nucleus.
*)

Definition ATP_Form : Type := ATP.ATP_Form.
Definition ATP_Imp  : ATP_Form -> ATP_Form -> ATP_Form := ATP.ATP_Imp.
Definition ATP_Bot  : ATP_Form := ATP.ATP_Bot.
Definition ATP_Prov : ATP_Form -> Prop := ATP.ATP_Prov.

Definition Bot : ATP_Form := ATP_Bot.
Definition Imp : ATP_Form -> ATP_Form -> ATP_Form := ATP_Imp.

Notation "A --> B" := (ATP_Imp A B) (at level 60, right associativity).

(*
  This is the main "feature" of C002: The logic supports Modus Ponens.
  It is witnessed by the constructive proof in P3_R.
*)

Theorem ATP_Prov_MP :
  forall (A B : ATP_Form),
    ATP_Prov (A --> B) -> ATP_Prov A -> ATP_Prov B.
Proof.
  exact ATP.ATP_Prov_MP.
Qed.

(* Alias for convenience *)

Theorem Prov_app :
  forall (A B : ATP_Form),
    ATP_Prov (A --> B) -> ATP_Prov A -> ATP_Prov B.
Proof.
  exact ATP_Prov_MP.
Qed.

(*
  This section exposes the "Checker-First" nature of the logic.
  It allows users to prove theorems by computation:
  If 'check pf phi' returns true, then 'Prov phi' holds.
*)

Module ProvIntf := ATP.C002.P2_S__Provability_Interface.C_002_Provability_S.

Definition Prov_Form : Type := ProvIntf.Form.
Definition Prov_Imp  : Prov_Form -> Prov_Form -> Prov_Form := ProvIntf.Imp.
Definition Prov_Bot  : ProvIntf.Form := ProvIntf.Bot.
Definition Prov      : Prov_Form -> Prop := ProvIntf.Prov.

Theorem Prov_from_check :
  forall (pf : ATP.C002.P2_R__Hilbert_Kernel.C_002_HilbertKernel_R.Proof)
         (phi : Prov_Form),
    ATP.C002.P2_R__Hilbert_Kernel.C_002_HilbertKernel_R.check pf phi = true ->
    Prov phi.
Proof.
  exact ProvIntf.Prov_from_check.
Qed.

(*
  Coding Re-exports.
  Exposes the canonical codec interface and instance.
*)

Definition CODEC : Type :=
  ATP.C002.P4_R__Coding_Nucleus.C_002_Coding_Nucleus_R.CODEC.
  
Definition CanonicalCodec : CODEC := Coding.CanonicalCodec.
