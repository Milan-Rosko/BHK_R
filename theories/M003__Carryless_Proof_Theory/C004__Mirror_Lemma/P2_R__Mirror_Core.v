(* P2_R__Mirror_Core.v *)

(*************************************************************************)
(*                                                                       *)
(*  C004 / Phase 2 (R): Mirror Core + Recursive Extension                *)
(*                                                                       *)
(*  This file concentrates the formal content for the Mirror Lemma:      *)
(*                                                                       *)
(*   (i)    Mirror core, parameters and schema:                          *)
(*                                                                       *)
(*          (a) [ MirrorParams ] collects a regulator context. It is     *)
(*              purely parametric: no properties are assumed beyond what *)
(*              later lemmas explicitly require.                         *)
(*          (b) AsIF [ MP ] [ phi ] is a meta‑level predicate of         *)
(*              regulated adoption. It holds iff there exist witnesses   *)
(*              [ i, b ] that satisfy the defining conditions.           *)
(*          (c) AsIF_simple drops the regulator data and keeps only the  *)
(*              non‑refutability condition.                              *)
(*          (d) Mir [ MP ] [ phi ] is the “Mirror Lemma” schema: if      *)
(*              [ phi ] is not refuted by [ T ], then [ AsIF MP phi ]    *)
(*              holds.                                                   *)
(*          (e) Fixed‑witness lemma: if one pair [ (i0, b0) ] works for  *)
(*              all [ phi ], then [ Mir ] holds for all [ phi ].         *)
(*                                                                       *)
(*   (ii)   Diagonal interface                                           *)
(*                                                                       *)
(*          (a) Transformer packages a syntactic map [ trF ] together    *)
(*              with a representation predicate [ trRep ].               *)
(*          (b) DiagDevice provides a diagonal sentence [ diag G ], plus *)
(*              proofs of [ diag G -> trF G (diag G) ] and the converse. *)
(*                                                                       *)
(*   (iii)  Recursive mirror point                                       *)
(*                                                                       *)
(*          (a) [ MirrorPointF, theta, Recursive_Mirror_Lemma ]          *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.
From C004 Require Import P1_S__Context.

Set Implicit Arguments.
Unset Strict Implicit.

Module C_004_Mirror_Core_R.

  Import C_004_Context.

  (*
    A “Symbolic Regulator” [ Sλ ] is a conservative enrichment of [ T ].
    It adds a first‑order interface for statements like
    “instruction [ i ] licenses commitment [ x ]”, without claiming global
    soundness. We establish [ MirrorParams ] as the regulator context used by
    the core. It packages the minimal primitives needed for the Mirror Lemma.
    Intuition. [ REG ] and [ BND ] describe admissible support, while
    [ ProvT_P ] is the chosen internal provability predicate for [ T ].
  *)

  Record MirrorParams : Type := {
    REG      : nat -> Form -> Prop;
    BND      : Form -> Form -> Prop;
    ProvT_P  : Form -> Prop
  }.

  (*
    AsIF(φ) := ∃ i, b.
    BND(φ, b) ∧ REG(i, b) ∧ Prov(φ → b) ∧ ¬ProvT_P(¬φ)

    It holds iff there exist [ i, b ] such that:

      (i)    [ BND phi b ]           [ b ] is an admissible bound for [ phi ]
      (ii)   [ REG i b ]             [ i ] certifies/derives [ b ]
      (iii)  [ Prov (phi -> b) ]     internal proof of [ phi -> b ]
      (iv)   [ ~ProvT_P (NotF phi) ] [ T ] does not refute [ phi ]

    Remark. This is not a truth relation. It is a licensed stance that
    depends on explicit regulator support plus non‑refutability.
  *)

  (*************************************************************************)
  (*                                                                       *)
  (*  Mirror Lemma                                                         *)
  (*                                                                       *)
  (*************************************************************************)

  
  Definition AsIF (MP : MirrorParams) (phi : Form) : Prop :=
    exists i : nat,
    exists b : Form,
      MP.(BND) phi b /\
      MP.(REG) i b /\
      Prov (Imp phi b) /\
      ~ MP.(ProvT_P) (NotF phi).

  (*
    AsIF_simple(φ) := ¬ProvT_P(¬φ)
    This is the non‑refutability fragment of AsIF.
    It is used when regulator witnesses are intentionally suppressed.
  *)

  Definition AsIF_simple (MP : MirrorParams) (phi : Form) : Prop :=
    ~ MP.(ProvT_P) (NotF phi).

  (*
    Mir(φ) := ¬ProvT_P(¬φ) → AsIF(φ)
    This is the core conditional that the Mirror Lemma establishes.
  *)

  Definition Mir (MP : MirrorParams) (phi : Form) : Prop :=
    ~ MP.(ProvT_P) (NotF phi) -> AsIF MP phi.

  Section FixedWitness.
    Context (MP : MirrorParams).

    Variable i0 : nat.
    Variable b0 : Form.

    Hypothesis REG0 : MP.(REG) i0 b0.
    Hypothesis BND0 : forall phi : Form, MP.(BND) phi b0.
    Hypothesis PRV0 : forall phi : Form, Prov (Imp phi b0).

    (*
      Then: non‑refutation implies AsIF, uniformly in [ phi ].
      The witnesses [ (i0, b0) ] are fixed and reused for all [ phi ].
    *)

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

    (*
      A direct corollary: the Mirror schema holds for all [ phi ].
    *)

    Theorem Mir_schema_fixed_witness :
      forall phi : Form, Mir MP phi.
    Proof.
      intro phi; unfold Mir.
      intro Hnr; apply Mirror_fixed_witness; exact Hnr.
    Qed.

  End FixedWitness.

  (*
    Transformer: a syntactic map [ trF ] plus a representation predicate.
    The field [ trRep ] can track representability when that matters.
  *)

  Record Transformer : Type := {
    trF   : Form -> Form;
    trRep : Prop
  }.

  (*
    applyT is a convenience name for the underlying transformer.
  *)

  Definition applyT (G : Transformer) : Form -> Form := trF G.

  (*
    DiagDevice provides a diagonal sentence with provable equivalence.
    The forward/backward clauses are the internalized fixed‑point laws.
  *)

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
(*  “Recursive” Mirror Lemma                                             *)
(*                                                                       *)
(*************************************************************************)

Module C_004_Recursive_Mirror_R.

  Import C_004_Context.
  Module Core := C_004_Mirror_Core_R.
  Import Core.

  (*
    ProvFormer packages a unary "provability former" at the formula level.
    It can encode an internal provability predicate or another modal operator.
  *)

  Record ProvFormer : Type := {
    ProvT_F : Form -> Form
  }.

  Section RecursiveMirrorPoint.

    Context (MP : MirrorParams).
    Context (PF : ProvFormer).
    Context (D  : DiagDevice).

    (*
      MirrorPointF(phi) := (notF ProvT_F(notF phi)) -> phi
      Intuition: "if [ phi ] is not refutable by the provability‑former,
      then [ phi ] holds." This is the mirror‑point transform used for
      diagonalization.
    *)

    (*
      MirrorPointF as a formula transformer.
    *)

    Definition MirrorPointF (phi : Form) : Form :=
      Imp (NotF (PF.(ProvT_F) (NotF phi))) phi.

    (*
      Optional representation predicate for MirrorPointF.
    *)

    Variable MirrorPointF_rep : Prop.

    (*
      Package MirrorPointF as a Transformer to feed to the diagonal device.
    *)

    Definition MirrorPointT : Transformer :=
      {| trF := MirrorPointF; trRep := MirrorPointF_rep |}.

    (*
      The diagonal sentence for the mirror‑point transformer.
    *)

    Definition theta : Form := D.(diag) MirrorPointT.

    (*
      The diagonal device yields provable equivalence in both directions.
    *)

    Theorem Recursive_Mirror_Lemma :
      Prov (Imp theta (MirrorPointF theta)) /\ Prov (Imp (MirrorPointF theta) theta).
    Proof.
      split.
      - exact (D.(diag_fwd) MirrorPointT).
      - exact (D.(diag_bwd) MirrorPointT).
    Qed.

    (*
      Analogy. No matter how primitive or small an observer is, a mirror still
      hides a part of them from their own view. The observer always blocks some
      of the reflected image. In an infinite mirror setup, the hidden fraction
      does not disappear; it repeats and accumulates across reflections.
    *)

  End RecursiveMirrorPoint.

End C_004_Recursive_Mirror_R.

Export C_004_Recursive_Mirror_R.
