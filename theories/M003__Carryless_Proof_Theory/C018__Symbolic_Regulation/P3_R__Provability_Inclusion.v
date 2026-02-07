(* P3_R__Provability_Inclusion.v *)

(*************************************************************************)
(*                                                                       *)
(*  C018 / Phase 3 (R): Provability Inclusion (Core)                     *)
(*                                                                       *)
(*  Defines the structural inclusion predicate as a record.              *)
(*  This is the core shape; certificates live in the A-layer.            *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.
From C004 Require Import P1_S__Context.
From C018 Require Import P1_R__Core.

Set Implicit Arguments.
Unset Strict Implicit.

Module C_018_Provability_Inclusion_R.

  Import C_004_Context.
  Module SR := C_018_Symbolic_Regulation_R.

  (*************************************************************************)
  (*                                                                       *)
  (*  Provability Inclusion Record                                         *)
  (*                                                                       *)
  (*************************************************************************)

  (*
    A provability inclusion gives a translation [ Embed ] together with
    two bridge conditions:
      (i)  If the model proves [ phi ], then [ T ] proves [ Embed phi ].
      (ii) If the model is consistent, then [ T ] is consistent.
  *)

  Record ProvabilityInclusion (R : SR.SymbolicRegulator) : Type := {
    Embed : Form -> Form;

    Include_Prov : forall phi : Form,
      R.(SR.SR_ModelProv) phi -> Prov (Embed phi);

    Include_Con :
      (~ R.(SR.SR_ModelProv) Bot) -> (~ Prov Bot)
  }.

  (*************************************************************************)
  (*                                                                       *)
  (*  Consistency Shorthands                                               *)
  (*                                                                       *)
  (*************************************************************************)

  Definition ModelConsistent (R : SR.SymbolicRegulator) : Prop :=
    ~ R.(SR.SR_ModelProv) Bot.

  Definition BaseConsistent : Prop :=
    ~ Prov Bot.

  Lemma Inclusion_preserves_consistency :
    forall (R : SR.SymbolicRegulator) (PI : ProvabilityInclusion R),
      ModelConsistent R -> BaseConsistent.
  Proof.
    intros R PI Hc.
    unfold ModelConsistent, BaseConsistent in *.
    exact (Include_Con PI Hc).
  Qed.

End C_018_Provability_Inclusion_R.

Export C_018_Provability_Inclusion_R.
