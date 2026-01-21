(* P5_T__Weakforcing.v *)

(*************************************************************************)
(*                                                                       *)
(*  C_004 / Phase 5 (T): Weak Forcing (Public Surface)                   *)
(*                                                                       *)
(*  What is "Weak Forcing"?                                              *)
(*                                                                       *)
(*  Standard “Cohen” Forcing extends the universe to make a              *)
(*  statement True.                                                      *)
(*                                                                       *)
(*  Weak Forcing (C004) locates a bounded state within the               *)
(*  EXISTING universe where the statement behaves "As-If" it were true.  *)
(*  (It never left the universe, it could just errs)                     *)
(*                                                                       *)
(*  We do not add axioms. We discover that incompleteness “forces”       *)
(*  the existence of bounded witnesses.                                  *)
(*                                                                       *)
(*  It is a result within the First Order Logic (FOL), that is,          *)
(*  the logical kernel (ATP) defined in C002 is strictly the “additive   *)
(*  fragment” of Propositional Logic.                                    *)
(*                                                                       *)
(*  Downstream API.                                                      *)
(*                                                                       *)
(*    (i) MirrorParams: The interface for regulators/separators.         *)
(*                                                                       *)
(*   (ii) AsIF: The predicate identifying "forced" statements.           *)
(*                                                                       *)
(*  (iii) Mirror_fixed_witness: The main engine.                         *)
(*        (Non-refutability + Regulator -> AsIF).                        *)
(*                                                                       *)
(*   (iv) Recursive_Mirror_Lemma: The extension for the Diagonal.        *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.

(* Guard: do not import any A/TA module here. *)

From ATP.C004__Mirror_Lemma Require Export
  P1_S__Context
  P2_S__Mirror_Lemma
  P3_S__Recursive_Mirror_Lemma.

Set Implicit Arguments.
Unset Strict Implicit.

(* Conceptual Namespaces *)
Module Prelude := ATP.C004__Mirror_Lemma.P1_S__Context.C_004_Context.
Module Mirror  := ATP.C004__Mirror_Lemma.P2_S__Mirror_Lemma.C_004_Mirror_S.
Module RecMirror := ATP.C004__Mirror_Lemma.P3_S__Recursive_Mirror_Lemma.C_004_Recursive_Mirror_S.

(* Type Re-exports *)
Definition nat  : Type := Prelude.nat.
Definition Form : Type := Prelude.Form.
Definition Imp  : Form -> Form -> Form := Prelude.Imp.
Definition Bot  : Form := Prelude.Bot.
Definition Prov : Form -> Prop := Prelude.Prov.
Definition NotF (phi : Form) : Form := Prelude.NotF phi.

(* Mirror Core API *)
Definition MirrorParams : Type := Mirror.MirrorParams.
Definition AsIF        : MirrorParams -> Form -> Prop := Mirror.AsIF.
Definition AsIF_simple : MirrorParams -> Form -> Prop := Mirror.AsIF_simple.
Definition Mir         : MirrorParams -> Form -> Prop := Mirror.Mir.

(* Fixed-witness Lemma *)
Definition Mirror_fixed_witness
  (MP : MirrorParams) (i0 : nat) (b0 : Form)
  (REG0 : MP.(Mirror.REG) i0 b0)
  (BND0 : forall phi : Form, MP.(Mirror.BND) phi b0)
  (PRV0 : forall phi : Form, Prov (Imp phi b0))
  : forall phi : Form, ~ MP.(Mirror.ProvT_P) (NotF phi) -> AsIF MP phi
  := Mirror.Mirror_fixed_witness (MP := MP) (i0 := i0) (b0 := b0) REG0 BND0 PRV0.

(* Restricted Diagonal Interface *)
Definition Transformer : Type := Mirror.Transformer.
Definition DiagDevice  : Type := Mirror.DiagDevice.
Definition trF   (G : Transformer) : Form -> Form := Mirror.trF G.

(* Recursive Mirror Extensions *)
Definition ProvFormer : Type := RecMirror.ProvFormer.

Definition MirrorPointF
  (_MP : MirrorParams) (PF : ProvFormer) (_D : DiagDevice) (phi : Form) : Form :=
  RecMirror.MirrorPointF PF phi.

Definition theta
  (_MP : MirrorParams) (PF : ProvFormer) (D : DiagDevice) (rep : Prop) : Form :=
  RecMirror.theta PF D rep.

Theorem Recursive_Mirror_Lemma
  (MP : MirrorParams) (PF : ProvFormer) (D : DiagDevice) (rep : Prop) :
  Prov (Imp (theta MP PF D rep) (MirrorPointF MP PF D (theta MP PF D rep)))
  /\
  Prov (Imp (MirrorPointF MP PF D (theta MP PF D rep)) (theta MP PF D rep)).
Proof.
  exact (RecMirror.Recursive_Mirror_Lemma PF D rep).
Qed.

