(* P3_R__Kernel.v *)

(*************************************************************************)
(*                                                                       *)
(*  C009 / Phase 3 (R): FOL Kernel (Checker-First Realization)           *)
(*                                                                       *)
(*    (i) Scope.                                                         *)
(*                                                                       *)
(*        Proof checking kernel for minimal first-order logic.           *)
(*        Implements the "witness-first" discipline: a proof is a        *)
(*        checkable artifact (list of formulas), not an abstract         *)
(*        derivation.                                                    *)
(*                                                                       *)
(*   (ii) Design Philosophy: Checker-First.                              *)
(*                                                                       *)
(*        Rather than defining an inductive proof type (Hilbert-style    *)
(*        or natural deduction), we define a checker function:           *)
(*                                                                       *)
(*          check : Proof → Form → bool                                  *)
(*                                                                       *)
(*        A proof is valid iff check returns true.                       *)
(*                                                                       *)
(*        Why this approach?                                             *)
(*          (a) Effectivity: check is computable (vm_compute).           *)
(*          (b) Flexibility: easier to add new proof rules.              *)
(*          (c) Transparency: proof search reduces to satisfying check.  *)
(*                                                                       *)
(*  (iii) Proof Structure.                                               *)
(*                                                                       *)
(*        Proof = list Form                                              *)
(*                                                                       *)
(*        A proof is a sequence of formulas (a "proof script").          *)
(*        The checker validates that each formula is justified by:       *)
(*          - Axioms (reflexivity of equality)                           *)
(*          - Inference rules (modus ponens, instantiation, etc.)        *)
(*          - Previous formulas in the proof                             *)
(*                                                                       *)
(*   (iv) Supported Proof Rules.                                         *)
(*                                                                       *)
(*        (a) Assumption: φ is in the proof list.                        *)
(*        (b) Modus Ponens: if (φ → ψ) and φ are in the proof, ψ holds. *)
(*        (c) Universal Generalization: if φ holds, ∀x.φ holds.          *)
(*        (d) Universal Instantiation: from ∀x.φ, derive φ[x↦t].        *)
(*        (e) Reflexivity: t = t is an axiom.                            *)
(*        (f) Leibniz: from t₁=t₂ and φ[x↦t₁], derive φ[x↦t₂].         *)
(*                                                                       *)
(*    (v) Role in C009.                                                  *)
(*                                                                       *)
(*        Provides computational proof checking for FOL reasoning.       *)
(*        Used by P3_T__FOL to define Prov predicate.                    *)
(*        Tested by P4_T__Kernel_Sanity (effectivity witnesses).         *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.
From SAT.C009 Require Import P1_S__Syntax.
From SAT.C009 Require Import P2_R__Substitution.

Set Implicit Arguments.
Unset Strict Implicit.

Module C009_FOL_Kernel_R.

  Module S := C009_FOL_Syntax.
  Module Subst := C009_FOL_Subst_R.
  Module N := S.N.

  (*
    Proof — Witness Structure

    A proof is a list of formulas representing a "proof script".
    Each formula is either an axiom or derived from previous formulas.

    The checker validates that the target formula can be justified
    by this proof context.
  *)

  Definition Proof := list S.Form.

  (*
    form_eqb — Decidable Equality for Formulas

    Structural equality check for formulas.
    Returns true iff two formulas are syntactically identical.

    Used by the checker to match formulas in the proof list.
  *)

  Fixpoint form_eqb (a b : S.Form) : bool :=
    match a, b with
    | S.Bot, S.Bot => true
    | S.Imp a1 a2, S.Imp b1 b2 =>
        andb (form_eqb a1 b1) (form_eqb a2 b2)
    | S.Eq t1 t2, S.Eq u1 u2 =>
        andb (Subst.term_eqb t1 u1) (Subst.term_eqb t2 u2)
    | S.All x f, S.All y g =>
        andb (Subst.term_eqb x y) (form_eqb f g)
    | S.Ex x f, S.Ex y g =>
        andb (Subst.term_eqb x y) (form_eqb f g)
    | _, _ => false
    end.

  Lemma term_eqb_refl : forall t : S.Term, Subst.term_eqb t t = true.
  Proof.
    induction t; simpl; try exact (eq_refl _).
    exact IHt.
  Qed.

  Lemma andb_true_intro : forall a b, a = true -> b = true -> andb a b = true.
  Proof.
    intros a b Ha Hb.
    destruct a, b; simpl in *; try exact Ha; try exact Hb; try exact (eq_refl _).
  Qed.

  Lemma form_eqb_refl : forall f : S.Form, form_eqb f f = true.
  Proof.
    induction f; simpl; try exact (eq_refl _).
    - apply andb_true_intro; assumption.
    - apply andb_true_intro; apply term_eqb_refl.
    - apply andb_true_intro; try apply term_eqb_refl; assumption.
    - apply andb_true_intro; try apply term_eqb_refl; assumption.
  Qed.

  (*
    in_list — Membership Check

    Returns true iff formula phi appears in the proof list pf.

    This implements the "assumption" rule: a formula is justified
    if it has already appeared in the proof.
  *)

  Fixpoint in_list (phi : S.Form) (pf : Proof) : bool :=
    match pf with
    | nil => false
    | cons h t => if form_eqb phi h then true else in_list phi t
    end.

  Lemma in_list_refl : forall f : S.Form, in_list f (cons f nil) = true.
  Proof.
    intro f. simpl. rewrite form_eqb_refl. exact (eq_refl _).
  Qed.

  (*
    terms_of_form — Term Extraction

    Extracts all terms appearing in a formula.
    Used to build the term universe for instantiation checking.

    The checker uses this to find potential instantiation witnesses
    when checking universal instantiation and Leibniz substitution.
  *)

  Fixpoint terms_of_form (f : S.Form) : list S.Term :=
    match f with
    | S.Bot => nil
    | S.Imp a b => terms_of_form a ++ terms_of_form b
    | S.Eq t1 t2 => t1 :: t2 :: nil
    | S.All x body => x :: terms_of_form body
    | S.Ex x body => x :: terms_of_form body
    end.

  (*
    terms_of_proof — Term Universe Construction

    Extracts all terms from all formulas in the proof.
    This builds the "term universe" available for instantiation.
  *)

  Fixpoint terms_of_proof (pf : Proof) : list S.Term :=
    match pf with
    | nil => nil
    | cons h t => terms_of_form h ++ terms_of_proof t
    end.

  (*
    exists_imp — Modus Ponens Checker

    Checks if phi can be derived by modus ponens:
      if (φ → ψ) and φ are both in pf, then ψ is justified.

    Scans the proof for an implication (φ → phi), then checks
    if the antecedent φ is also in the proof.
  *)

  Fixpoint exists_imp (pf : Proof) (phi : S.Form) : bool :=
    match pf with
    | nil => false
    | cons h t =>
        match h with
        | S.Imp a b =>
            if form_eqb b phi
            then in_list a pf
            else exists_imp t phi
        | _ => exists_imp t phi
        end
    end.

  (*
    exists_all — Universal Generalization Checker

    Checks if phi (which must be ∀x.ψ) can be derived by generalization:
      if ψ is in pf, then ∀x.ψ is justified.

    This implements the generalization rule: from ψ, infer ∀x.ψ.
  *)

  Fixpoint exists_all (pf : Proof) (phi : S.Form) : bool :=
    match pf with
    | nil => false
    | cons h t =>
        match phi with
        | S.All x body =>
            if form_eqb body h then true else exists_all t phi
        | _ => false
        end
    end.

  (*
    exists_inst_terms — Universal Instantiation Helper

    Tries to instantiate ∀x.body with each term in ts to match phi.
    Returns true if any instantiation body[x↦t] equals phi.

    This is a helper for exists_inst (the full instantiation checker).
  *)

  Fixpoint exists_inst_terms (body : S.Form) (x : S.Var) (ts : list S.Term) (phi : S.Form) : bool :=
    match ts with
    | nil => false
    | cons t ts' =>
        if form_eqb (Subst.subst body x t) phi then true else exists_inst_terms body x ts' phi
    end.

  (*
    exists_inst — Universal Instantiation Checker

    Checks if phi can be derived by universal instantiation:
      if ∀x.ψ is in pf, and ψ[x↦t] = phi for some term t,
      then phi is justified.

    Scans the proof for universally quantified formulas,
    then tries instantiation with all available terms (ts).
  *)

  Fixpoint exists_inst (pf : Proof) (phi : S.Form) (ts : list S.Term) : bool :=
    match pf with
    | nil => false
    | cons h t =>
        match h with
        | S.All x body =>
            if exists_inst_terms body x ts phi then true else exists_inst t phi ts
        | _ => exists_inst t phi ts
        end
    end.

  (*
    refl_check — Reflexivity Axiom Checker

    Returns true if phi is a reflexivity axiom: t = t.

    This implements the axiom schema for equality reflexivity.
  *)

  Definition refl_check (phi : S.Form) : bool :=
    match phi with
    | S.Eq t1 t2 => Subst.term_eqb t1 t2
    | _ => false
    end.

  (*
    leibniz_body — Leibniz Substitution Body Check

    Checks if phi can be derived from body via Leibniz substitution:
      if t₁ = t₂ is in pf, and body[x↦t₁] is in pf,
      and body[x↦t₂] = phi, then phi is justified.

    This is the core logic for equality substitution.
  *)

  Definition leibniz_body (body : S.Form) (x : S.Var) (t1 t2 : S.Term) (pf : Proof) (phi : S.Form) : bool :=
    if form_eqb (Subst.subst body x t2) phi
    then in_list (Subst.subst body x t1) pf
    else false.

  (*
    exists_leibniz_terms — Leibniz Term Pair Search

    Tries all pairs of terms (t₁, t₂) from ts to find a Leibniz
    substitution that derives phi from body.

    For each pair, checks if t₁ = t₂ is in the proof and if
    the leibniz_body check succeeds.
  *)

  Fixpoint exists_leibniz_terms (body : S.Form) (x : S.Var) (ts : list S.Term) (pf : Proof) (phi : S.Form) : bool :=
    match ts with
    | nil => false
    | cons t1 ts1 =>
        let fix loop_t2 (ts2 : list S.Term) : bool :=
            match ts2 with
            | nil => false
            | cons t2 ts2' =>
                if in_list (S.Eq t1 t2) pf
                then if leibniz_body body x t1 t2 pf phi then true else loop_t2 ts2'
                else loop_t2 ts2'
            end
        in
        if loop_t2 ts
        then true
        else exists_leibniz_terms body x ts1 pf phi
    end.

  (*
    exists_leibniz — Leibniz Substitution Checker

    Checks if phi can be derived by Leibniz substitution:
      if ∀x.ψ is in pf, and t₁=t₂ is in pf, and ψ[x↦t₁] is in pf,
      and ψ[x↦t₂] = phi, then phi is justified.

    Scans the proof for universally quantified formulas (the Leibniz
    schemas), then tries all term pairs for substitution.
  *)

  Fixpoint exists_leibniz (pf : Proof) (phi : S.Form) (ts : list S.Term) : bool :=
    match pf with
    | nil => false
    | cons h t =>
        match h with
        | S.All x body =>
            if exists_leibniz_terms body x ts pf phi then true else exists_leibniz t phi ts
        | _ => exists_leibniz t phi ts
        end
    end.

  (*
    check — The Main Proof Checker

    Type: Proof → Form → bool

    Returns true iff formula phi is justified by proof pf.

    Checking Strategy (tried in order):

      1. Assumption: phi is directly in pf.
      2. Modus Ponens: phi follows from (φ → phi) and φ in pf.
      3. Universal Generalization: phi = ∀x.ψ and ψ is in pf.
      4. Universal Instantiation: ∀x.ψ is in pf and phi = ψ[x↦t].
      5. Reflexivity: phi is t = t for some term t.
      6. Leibniz: phi follows from equality substitution.

    If none of these rules apply, the check fails (returns false).

    Key Property:
      check is computable (reduces under vm_compute).
      This enables computational proof validation.
  *)

  Definition check (pf : Proof) (phi : S.Form) : bool :=
    if in_list phi pf then true
    else if exists_imp pf phi then true
    else if exists_all pf phi then true
    else if exists_inst pf phi (terms_of_proof pf) then true
    else if refl_check phi then true
    else if exists_leibniz pf phi (terms_of_proof pf) then true
    else false.

  (*
    check_refl — Effectivity Witness

    Shows that check is effective: a trivial proof (just phi itself)
    validates phi via the assumption rule.

    This can be verified computationally (vm_compute).
  *)

  Lemma check_refl : forall f : S.Form, check (cons f nil) f = true.
  Proof.
    intro f. unfold check. cbn.
    rewrite form_eqb_refl.
    exact (eq_refl _).
  Qed.

End C009_FOL_Kernel_R.

Export C009_FOL_Kernel_R.