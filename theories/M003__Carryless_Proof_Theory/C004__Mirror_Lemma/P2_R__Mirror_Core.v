(* P2_R__Mirror_Core.v *)

(*************************************************************************)
(*                                                                       *)
(*  C004 / Phase 2 (R): Mirror Core + Recursive Extension                *)
(*                                                                       *)
(*  This file concentrates the formal content for the Mirror Lemma:      *)
(*                                                                       *)
(*   (i)    Mirror core                                                  *)
(*                                                                       *)
(*          (a) “Regulator” Parameters: REG, BND, ProvT_P                *)
(*          (b) AsIF predicate and Mirror schema                         *)
(*          (c) Fixed-witness lemma                                      *)
(*                                                                       *)
(*   (ii)   Diagonal interface                                           *)
(*                                                                       *)
(*          (a) Transformer, DiagDevice                                  *)
(*                                                                       *)
(*   (iii)  Recursive mirror point                                       *)
(*                                                                       *)
(*          (a) MirrorPointF, theta, Recursive_Mirror_Lemma              *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.
From C004 Require Import P1_S__Context.

Set Implicit Arguments.
Unset Strict Implicit.

Module C_004_Mirror_Core_R.

  Import C_004_Context.

  (*************************************************************************)
  (*                                                                       *)
  (*  parameters, AsIF, Mir                                                *)
  (*                                                                       *)
  (*************************************************************************)

  Record MirrorParams : Type := {
    REG      : nat -> Form -> Prop;
    BND      : Form -> Form -> Prop;
    ProvT_P  : Form -> Prop
  }.

  (*
    AsIF(φ) := ∃ i, b.
    BND(φ, b) ∧ REG(i, b) ∧ Prov(φ → b) ∧ ¬ProvT_P(¬φ)
  *)

  Definition AsIF (MP : MirrorParams) (phi : Form) : Prop :=
    exists i : nat,
    exists b : Form,
      MP.(BND) phi b /\
      MP.(REG) i b /\
      Prov (Imp phi b) /\
      ~ MP.(ProvT_P) (NotF phi).

  (*
    AsIF_simple(φ) := ¬ProvT_P(¬φ)
    Used when regulator context is “suppressed”.
  *)

  Definition AsIF_simple (MP : MirrorParams) (phi : Form) : Prop :=
    ~ MP.(ProvT_P) (NotF phi).

  (*
    Mir(φ) := ¬ProvT_P(¬φ) → AsIF(φ)
  *)
  
  Definition Mir (MP : MirrorParams) (phi : Form) : Prop :=
    ~ MP.(ProvT_P) (NotF phi) -> AsIF MP phi.

  (*************************************************************************)
  (*                                                                       *)
  (*  Fixed-witness Lemma                                                  *)
  (*                                                                       *)
  (*************************************************************************)

  Section FixedWitness.
    Context (MP : MirrorParams).

    Variable i0 : nat.
    Variable b0 : Form.

    Hypothesis REG0 : MP.(REG) i0 b0.
    Hypothesis BND0 : forall phi : Form, MP.(BND) phi b0.
    Hypothesis PRV0 : forall phi : Form, Prov (Imp phi b0).

    Theorem Mirror_fixed_witness :
      forall phi : Form,
        ~ MP.(ProvT_P) (NotF phi) -> AsIF MP phi.
    Proof.
      intros phi Hnr.
      exists i0. exists b0.
      repeat split.
      - apply BND0.
      - exact REG0.
      - apply PRV0.
      - exact Hnr.
    Qed.

    Theorem Mir_schema_fixed_witness :
      forall phi : Form, Mir MP phi.
    Proof.
      intro phi; unfold Mir.
      intro Hnr; apply Mirror_fixed_witness; exact Hnr.
    Qed.

  End FixedWitness.

  (*************************************************************************)
  (*                                                                       *)
  (*  Diagonal Interface                                                   *)
  (*                                                                       *)
  (*************************************************************************)

  Record Transformer : Type := {
    trF   : Form -> Form;
    trRep : Prop
  }.

  Definition applyT (G : Transformer) : Form -> Form := trF G.

  Record DiagDevice : Type := {
    diag : Transformer -> Form;
    diag_fwd :
      forall (G : Transformer),
        Prov (Imp (diag G) (applyT G (diag G)));
    diag_bwd :
      forall (G : Transformer),
        Prov (Imp (applyT G (diag G)) (diag G))
  }.

End C_004_Mirror_Core_R.

Export C_004_Mirror_Core_R.

(*************************************************************************)
(*                                                                       *)
(*  Recursive Mirror Point (diagonalization)                             *)
(*                                                                       *)
(*************************************************************************)

Module C_004_Recursive_Mirror_R.

  Import C_004_Context.
  Module Core := C_004_Mirror_Core_R.
  Import Core.

  Record ProvFormer : Type := {
    ProvT_F : Form -> Form
  }.

  Section RecursiveMirrorPoint.

    Context (MP : MirrorParams).
    Context (PF : ProvFormer).
    Context (D  : DiagDevice).

    (*
      MirrorPointF(phi) := (notF ProvT_F(notF phi)) -> phi
    *)

    Definition MirrorPointF (phi : Form) : Form :=
      Imp (NotF (PF.(ProvT_F) (NotF phi))) phi.

    Variable MirrorPointF_rep : Prop.

    Definition MirrorPointT : Transformer :=
      {| trF := MirrorPointF; trRep := MirrorPointF_rep |}.

    Definition theta : Form := D.(diag) MirrorPointT.

    Theorem Recursive_Mirror_Lemma :
      Prov (Imp theta (MirrorPointF theta)) /\ Prov (Imp (MirrorPointF theta) theta).
    Proof.
      split.
      - exact (D.(diag_fwd) MirrorPointT).
      - exact (D.(diag_bwd) MirrorPointT).
    Qed.

  End RecursiveMirrorPoint.

End C_004_Recursive_Mirror_R.

Export C_004_Recursive_Mirror_R.
