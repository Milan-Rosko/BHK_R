(* P3_S__Additive_Theory.v *)

From Coq Require Import Init.Logic.

From C002 Require Import P1_S__Kernel_Spec.            (* The Interface Spec *)
From C002 Require Import P2_S__Provability_Interface.  (* The 'Prov' binding *)
From C002 Require Import P3_R__Additive_Laws.          (* The MP Proof (Realization) *)

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C002 / Phase 3 (S) : Additive Theory Packaging                       *)
(*                                                                       *)
(*  Role.                                                                *)
(*                                                                       *)
(*  This module builds the final "Container" for the proof system.       *)
(*                                                                       *)
(*  It takes the raw components,                                         *)
(*                                                                       *)
(*    (i) The Kernel Spec (P1_S)                                         *)
(*                                                                       *)
(*   (ii) The Provability Predicate (P2_S)                               *)
(*                                                                       *)
(*  (iii) The Modus Ponens Realization (P3_R)                            *)
(*                                                                       *)
(*   and packages them into a single ”Additive Provability” record.      *)
(*                                                                       *)
(*   Analogy. A “CSS Class“, or this “box”                               *)
(*                                                                       *)
(*************************************************************************)

Module C_002_Additive_Theory_S.

  Import C_002_Prelim.
  Import C_002_Provability_S.
  Import C_002_Additive_Laws_R. (* Contains the constructive proof of MP *)

  (*************************************************************************)
  (*                                                                       *)
  (*  The Additive Theory Container                                        *)
  (*                                                                       *)
  (*  Here we instantiate the 'AdditiveProvability' record defined in P1.  *)
  (*  We are filling the "div" with concrete content.                      *)
  (*                                                                       *)
  (*************************************************************************)

  Definition C_002_ATP : AdditiveProvability :=
    {|
      Form_ATP := Form;
      C_002_Prelim.Imp := Imp;
      C_002_Prelim.Bot := Bot;

      (*
        The Content: The Provability Predicate
      *)
      
      C_002_Prelim.Prov := Prov;

      (*
        We use the constructive proof 'Prov_MP' from P3_R
      *)

      C_002_Prelim.Prov_MP := Prov_MP
    |}.

  (*
    We alias the fields of the container so downstream users can use
    'ATP_Imp', 'ATP_Prov', etc., without digging into the record.
  *)

  Definition ATP_Form : Type := C_002_ATP.(C_002_Prelim.Form_ATP).
  Definition ATP_Imp  : ATP_Form -> ATP_Form -> ATP_Form := C_002_ATP.(C_002_Prelim.Imp).
  Definition ATP_Bot  : ATP_Form := C_002_ATP.(C_002_Prelim.Bot).
  Definition ATP_Prov : ATP_Form -> Prop := C_002_ATP.(C_002_Prelim.Prov).

  (*
    Our main theory of provability:
    The logic works as expected.
  *)

  Theorem ATP_Prov_MP :
    forall (A B : ATP_Form),
      ATP_Prov (ATP_Imp A B) -> ATP_Prov A -> ATP_Prov B.
  Proof.
    exact (C_002_ATP.(C_002_Prelim.Prov_MP)).
  Qed.

End C_002_Additive_Theory_S.

Export C_002_Additive_Theory_S.
