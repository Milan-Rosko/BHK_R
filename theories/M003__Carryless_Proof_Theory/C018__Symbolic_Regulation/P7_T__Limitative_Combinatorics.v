(* P7_T__Limitative_Combinatorics.v *)

(*************************************************************************)
(*                                                                       *)
(*  C018 / Phase 7 (T): Limitative Combinatorics                         *)
(*                                                                       *)
(*  Finite-pattern principles and constraint interfaces for              *)
(*  regulator classification.                                            *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.
From Coq Require Import Lists.List.
From C018 Require Import P1_R__Core.
From C018 Require Import P3_R__Provability_Inclusion.
From C004 Require Import P1_S__Context.

Set Implicit Arguments.
Unset Strict Implicit.

Module C_018_Limitative_Combinatorics_T.

  Module SR := C_018_Symbolic_Regulation_R.
  Module PI := C_018_Provability_Inclusion_R.
  Import ListNotations.
  Import SR.
  Import C_004_Context.

  (*************************************************************************)
  (*                                                                       *)
  (*  Principle Signatures                                                 *)
  (*                                                                       *)
  (*************************************************************************)

  (*
    A principle is a predicate on symbolic regulators.
  *)

  Definition Principle : Type := SR.SymbolicRegulator -> Prop.

  (*
    The finite pattern of principles P1..P10 is packaged as a record.
    This avoids any axioms and keeps the structure explicit.
  *)

  Record PrinciplePack : Type := {
    P1  : Principle; (* Externalization *)
    P2  : Principle; (* Presumption *)
    P3  : Principle; (* Dismissal *)
    P4  : Principle; (* Trust / Complacency *)
    P5  : Principle; (* Unity / Iterated Reflection *)
    P6  : Principle; (* Self‑Blindness *)
    P7  : Principle; (* Mirror Witness *)
    P8  : Principle; (* Epistemic Conservativity *)
    P9  : Principle; (* AsIF Normalization *)
    P10 : Principle  (* Omega Ascent *)
  }.

  (*************************************************************************)
  (*                                                                       *)
  (*  Named Principles (Definitions)                                       *)
  (*                                                                       *)
  (*************************************************************************)

  (*
    These definitions are intentionally conservative. They are concrete
    predicates (not axioms) and can be strengthened later.
  *)

  (*
    Externalization (current formalization).
    There exists some [ phi ] that is adopted under [ AsIF ].
    This is a weak, AsIF-level proxy for the modal export of undecidable
    content into a surrogate token.
  *)

  Definition Externalization_def : Principle :=
    fun R => exists phi : Form, AsIF R phi.

  (*
    Presumption (current formalization).
    There exists [ phi ] that is non-refutable, while the model does not
    certify its negation. This captures "treated as settled" without a
    boxed proof, in a weak AsIF sense.
  *)

  Definition Presumption_def : Principle :=
    fun R => exists phi : Form, NonRefutable R phi /\ ~ SR_ModelProv R (NotF phi).

  (*
    Dismissal (current formalization).
    The model certifies [ not phi ] while [ AsIF phi ] still holds.
    This encodes a forced blind spot under the regulator.
  *)

  Definition Dismissal_def : Principle :=
    fun R => exists phi : Form, SR_ModelProv R (NotF phi) /\ AsIF R phi.

  (*
    Trust / Complacency (current formalization).
    There exists [ phi ] that is both model-provable and AsIF-adopted.
    This is the weak proxy for forced trust under imperfect audit.
  *)

  Definition Trust_def : Principle :=
    fun R => exists phi : Form, SR_ModelProv R phi /\ AsIF R phi.

  (*
    Unity / Iterated Reflection (current formalization).
    Any AsIF-adopted statement is model-provable.
    This expresses a collapse direction only; the converse is not assumed.
  *)

  Definition Unity_def : Principle :=
    fun R => forall phi : Form, AsIF R phi -> SR_ModelProv R phi.

  (*
    Self-Blindness (current formalization).
    There exists [ phi ] that the model proves, but the regulator does not
    adopt via AsIF. This encodes "can see, cannot internalize."
  *)

  Definition SelfBlindness_def : Principle :=
    fun R => exists phi : Form, SR_ModelProv R phi /\ ~ AsIF R phi.

  (*
    Mirror Witness (current formalization).
    There exists [ phi ] adopted by AsIF that the model does not prove.
    This is a weak analogue of a witness to unboxed truth.
  *)

  Definition MirrorWitness_def : Principle :=
    fun R => exists phi : Form, AsIF R phi /\ ~ SR_ModelProv R phi.

  (*
    Epistemic Conservativity (current formalization).
    Model-provable statements are AsIF-adopted.
    This is a one-way shadow of conservativity.
  *)

  Definition ConservativityShadow_def : Principle :=
    fun R => forall phi : Form, SR_ModelProv R phi -> AsIF R phi.

  (*
    AsIF Normalization (current formalization).
    There exists [ phi ] such that AsIF holds for [ phi ] but not for
    its negation. This encodes a minimal normalization asymmetry.
  *)

  Definition NormalizationShadow_def : Principle :=
    fun R => exists phi : Form, AsIF R phi /\ ~ AsIF R (NotF phi).

  (*
    Omega Ascent (current formalization).
    There exists [ phi ] such that AsIF holds for [ phi ] and for its
    double negation. This is a weak surrogate for limit ascent.
  *)

  Definition OmegaAscent_def : Principle :=
    fun R => exists phi : Form, AsIF R phi /\ AsIF R (NotF (NotF phi)).

  (*
    A default pack that provides concrete inhabitants.
  *)

  Definition DefaultPrinciples : PrinciplePack := {|
    P1  := Externalization_def;
    P2  := Presumption_def;
    P3  := Dismissal_def;
    P4  := Trust_def;
    P5  := Unity_def;
    P6  := SelfBlindness_def;
    P7  := MirrorWitness_def;
    P8  := ConservativityShadow_def;
    P9  := NormalizationShadow_def;
    P10 := OmegaAscent_def
  |}.

  (*
    A regulator realizes a principle when the predicate holds.
  *)

  Definition Realizes (R : SR.SymbolicRegulator) (P : Principle) : Prop :=
    P R.

  (*************************************************************************)
  (*                                                                       *)
  (*  Named Aliases                                                        *)
  (*                                                                       *)
  (*************************************************************************)

  (*
    Convenience aliases that pin the narrative names to P1..P10.
    These are definitions, not additional assumptions.
  *)

  Definition Externalization (PP : PrinciplePack) : Principle := P1 PP.
  Definition Presumption (PP : PrinciplePack) : Principle := P2 PP.
  Definition Dismissal (PP : PrinciplePack) : Principle := P3 PP.
  Definition Trust (PP : PrinciplePack) : Principle := P4 PP.
  Definition Unity (PP : PrinciplePack) : Principle := P5 PP.
  Definition SelfBlindness (PP : PrinciplePack) : Principle := P6 PP.
  Definition MirrorWitness (PP : PrinciplePack) : Principle := P7 PP.
  Definition ConservativityShadow (PP : PrinciplePack) : Principle := P8 PP.
  Definition NormalizationShadow (PP : PrinciplePack) : Principle := P9 PP.
  Definition OmegaAscent (PP : PrinciplePack) : Principle := P10 PP.

  (*************************************************************************)
  (*                                                                       *)
  (*  Finite Pattern Interface                                             *)
  (*                                                                       *)
  (*************************************************************************)

  (*
    A pattern is a finite list of principles.
    A regulator realizes a pattern when it realizes each member.
  *)

  Definition Pattern : Type := list Principle.

  Definition RealizesPattern (R : SR.SymbolicRegulator) (Ps : Pattern) : Prop :=
    Forall (fun P => P R) Ps.

  (*
    Basic lemmas for reasoning about patterns.
  *)

  Lemma RealizesPattern_nil :
    forall R : SR.SymbolicRegulator, RealizesPattern R [].
  Proof.
    intro R; constructor.
  Qed.

  Lemma RealizesPattern_cons :
    forall (R : SR.SymbolicRegulator) (P : Principle) (Ps : Pattern),
      RealizesPattern R (P :: Ps) <-> (P R /\ RealizesPattern R Ps).
  Proof.
    intros R P Ps; split.
    - intro H; inversion H; subst; split; assumption.
    - intros [HP Hrest]; constructor; assumption.
  Qed.

  Lemma RealizesPattern_head :
    forall (R : SR.SymbolicRegulator) (P : Principle) (Ps : Pattern),
      RealizesPattern R (P :: Ps) -> P R.
  Proof.
    intros R P Ps H.
    destruct (proj1 (RealizesPattern_cons R P Ps) H) as [HP _].
    exact HP.
  Qed.

  Lemma RealizesPattern_tail :
    forall (R : SR.SymbolicRegulator) (P : Principle) (Ps : Pattern),
      RealizesPattern R (P :: Ps) -> RealizesPattern R Ps.
  Proof.
    intros R P Ps H.
    destruct (proj1 (RealizesPattern_cons R P Ps) H) as [_ Hrest].
    exact Hrest.
  Qed.

  Lemma RealizesPattern_singleton :
    forall (R : SR.SymbolicRegulator) (P : Principle),
      RealizesPattern R [P] <-> P R.
  Proof.
    intros R P; split.
    - intro H.
      destruct (proj1 (RealizesPattern_cons R P []) H) as [HP _].
      exact HP.
    - intro HP.
      apply (proj2 (RealizesPattern_cons R P [])).
      split.
      + exact HP.
      + apply RealizesPattern_nil.
  Qed.

  Lemma RealizesPattern_app :
    forall (R : SR.SymbolicRegulator) (Ps Qs : Pattern),
      RealizesPattern R (Ps ++ Qs) <-> (RealizesPattern R Ps /\ RealizesPattern R Qs).
  Proof.
    intros R Ps Qs; unfold RealizesPattern.
    rewrite Forall_app; tauto.
  Qed.

  (*
    The full signature pattern (P1..P10) as a single list.
  *)

  Definition FullPattern (PP : PrinciplePack) : Pattern :=
    [ Externalization PP
    ; Presumption PP
    ; Dismissal PP
    ; Trust PP
    ; Unity PP
    ; SelfBlindness PP
    ; MirrorWitness PP
    ; ConservativityShadow PP
    ; NormalizationShadow PP
    ; OmegaAscent PP
    ].

  (*
    A convenience lemma: full pattern realization is just list realization.
    It is phrased as a named alias for clarity in downstream proofs.
  *)

  Definition RealizesFullPattern
    (PP : PrinciplePack) (R : SR.SymbolicRegulator) : Prop :=
    RealizesPattern R (FullPattern PP).

  (*************************************************************************)
  (*                                                                       *)
  (*  Constraint Interface                                                 *)
  (*                                                                       *)
  (*************************************************************************)

  Record ConstraintInterface : Type := {
    CI_Constraint : Type;
    CI_Extract : SR.SymbolicRegulator -> list CI_Constraint;
    CI_Satisfies : list CI_Constraint -> Prop
  }.

  Definition Membership (CI : ConstraintInterface) (R : SR.SymbolicRegulator) : Prop :=
    CI.(CI_Satisfies) (CI.(CI_Extract) R).

End C_018_Limitative_Combinatorics_T.

Export C_018_Limitative_Combinatorics_T.
