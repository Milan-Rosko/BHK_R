(* P1_S__Context.v *)

From Coq Require Import Init.Logic.
From C002 Require Import P5_T__Proof_Theory.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C004 / Phase 1 (S): Mirror Context                                   *)
(*                                                                       *)
(*  This file fixes the object-language vocabulary used by the Mirror    *)
(*  Lemma and its recursive extension. It re-exports the additive        *)
(*  proof theory (C002) under stable local names and defines             *)
(*  object-language negation as implication to bottom.                   *)
(*                                                                       *)
(*                       NotF(phi) := Imp phi Bot                        *)
(*                                                                       *)
(*************************************************************************)

Module C_004_Context.

  (* Stable aliases to the underlying proof theory components. *)
  (* This avoids long paths and keeps later refactors localized. *)
  Module Prelude := C002.P5_T__Proof_Theory.Prelude.
  Module ATP     := C002.P5_T__Proof_Theory.ATP.

  (* Object-language types and connectives used throughout C004. *)
  Definition nat  : Type := Prelude.nat.
  Definition Form : Type := ATP.ATP_Form.

  Definition Imp  : Form -> Form -> Form := ATP.ATP_Imp.
  Definition Bot  : Form := ATP.ATP_Bot.
  Definition Prov : Form -> Prop := ATP.ATP_Prov.

  (*
    Object-language negation (syntactic):

        [ NotF(phi) := Imp phi Bot ]
   
    This is a “formula former”, not a meta-level negation.
  *)
 
  Definition NotF (phi : Form) : Form := Imp phi Bot.

End C_004_Context.

Export C_004_Context.
