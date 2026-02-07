(* P1_R__Core.v *)

(*************************************************************************)
(*                                                                       *)
(*  C018 / Phase 1 (R): Symbolic Regulation Core                         *)
(*                                                                       *)
(*  This file defines the core record for a symbolic regulator and       *)
(*  provides a bridge into the Mirror Lemma parameters.                  *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.
From C004 Require Import P1_S__Context.
From C004 Require Import P2_R__Mirror_Core.

Set Implicit Arguments.
Unset Strict Implicit.

Module C_018_Symbolic_Regulation_R.

  Import C_004_Context.
  Module Mirror := C_004_Mirror_Core_R.

  (*************************************************************************)
  (*                                                                       *)
  (*  Symbolic Regulator Core                                              *)
  (*                                                                       *)
  (*************************************************************************)

  (*
    A symbolic regulator packages the primitives needed for regulated
    adoption. It is intentionally minimal. No properties are assumed
    beyond what later lemmas require.
    
    The field [ SR_ModelProv ] is left abstract so that different
    model interfaces can be instantiated later.
  *)

  Record SymbolicRegulator : Type := {
    SR_REG       : nat -> Form -> Prop;
    SR_BND       : Form -> Form -> Prop;
    SR_ProvT_P   : Form -> Prop;
    SR_ModelProv : Form -> Prop
  }.

  (*
    Bridge: every symbolic regulator induces [ MirrorParams ].
    This lets us reuse the Mirror Lemma machinery without re-deriving it.
  *)

  Definition SR_to_MirrorParams (SR : SymbolicRegulator) : Mirror.MirrorParams :=
    {| Mirror.REG     := SR.(SR_REG)
     ; Mirror.BND     := SR.(SR_BND)
     ; Mirror.ProvT_P := SR.(SR_ProvT_P)
    |}.

  (*************************************************************************)
  (*                                                                       *)
  (*  AsIF / Mir (delegated to C004)                                       *)
  (*                                                                       *)
  (*************************************************************************)

  (*
    AsIF, AsIF_simple, and Mir are defined by delegation to C004.
    This keeps the core small and stable.
  *)

  Definition AsIF (SR : SymbolicRegulator) (phi : Form) : Prop :=
    Mirror.AsIF (SR_to_MirrorParams SR) phi.

  Definition AsIF_simple (SR : SymbolicRegulator) (phi : Form) : Prop :=
    Mirror.AsIF_simple (SR_to_MirrorParams SR) phi.

  Definition Mir (SR : SymbolicRegulator) (phi : Form) : Prop :=
    Mirror.Mir (SR_to_MirrorParams SR) phi.

  (*
    Readable alias for non-refutability.
  *)

  Definition NonRefutable (SR : SymbolicRegulator) (phi : Form) : Prop :=
    AsIF_simple SR phi.

  (*************************************************************************)
  (*                                                                       *)
  (*  Basic Lemma                                                          *)
  (*                                                                       *)
  (*************************************************************************)

  (*
    AsIF implies its non-refutability fragment.
  *)

  Lemma AsIF_implies_AsIF_simple :
    forall (SR : SymbolicRegulator) (phi : Form),
      AsIF SR phi -> AsIF_simple SR phi.
  Proof.
    intros SR phi H.
    unfold AsIF, AsIF_simple in *.
    unfold Mirror.AsIF in H.
    unfold Mirror.AsIF_simple.
    destruct H as [i [b [_ [_ [_ Hnr]]]]].
    exact Hnr.
  Qed.

  Lemma AsIF_implies_NonRefutable :
    forall (SR : SymbolicRegulator) (phi : Form),
      AsIF SR phi -> NonRefutable SR phi.
  Proof.
    intros SR phi H; exact (@AsIF_implies_AsIF_simple SR phi H).
  Qed.

End C_018_Symbolic_Regulation_R.

Export C_018_Symbolic_Regulation_R.
