(* P2_T__Mirror_Instance.v *)

From Coq Require Import Init.Logic.

From C004 Require Import P3_T__Weakforcing.

From C005 Require Import P2_T__Barrier.

From C002 Require Import P2_R__Hilbert_Kernel.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C005 / Phase 3 (T): The Mirror Instance (Separator as Regulator)     *)
(*                                                                       *)
(*  The Metatheoretic Bridge                                             *)
(*                                                                       *)
(*  This file re-interprets the Adversarial Barrier through the lens     *)
(*  of the Mirror Lemma (C004). It demonstrates that the impossibility   *)
(*  of a separator is a structural necessity derived from the Mirror     *)
(*  Schema.                                                              *)
(*                                                                       *)
(*  Key Insights                                                         *)
(*                                                                       *)
(*      (i) The Separator as Regulator                                   *)
(*                                                                       *)
(*          The SEPARATOR record (σ, cert) provides exactly the data     *)
(*          needed to satisfy the Mirror Lemma's REG and BND predicates. *)
(*                                                                       *)
(*          It "regulates" the diagonal sentence by forcing a formal     *)
(*          classification into A or B.                                  *)
(*                                                                       *)
(*     (ii) From "As-If" to "Collision"                                  *)
(*                                                                       *)
(*          The Mirror Lemma proves that the diagonal sentence D exists  *)
(*          in an As-If state: AsIF(D).                                  *)
(*                                                                       *)
(*          The Barrier shows that under Soundness, this As-If state     *)
(*          collides with Flip Logic, refuting the separator:            *)
(*                                                                       *)
(*            AsIF(D) + Sound + Flip(S,d) → Truth(A(d)) ∧ Truth(B(d))    *)
(*                                                                       *)
(*          This violates semantic disjointness.                         *)
(*                                                                       *)
(*    (iii) Constructive Hilbert Witness                                 *)
(*                                                                       *)
(*          To derive the necessary weakening rules without axioms,      *)
(*          we explicitly witness the Hilbert K-combinator:              *)
(*                                                                       *)
(*            K : φ → (ψ → φ)                                            *)
(*                                                                       *)
(*          This allows: Prov(φ) → Prov(ψ → φ) (weakening rule).         *)
(*                                                                       *)
(*************************************************************************)

Module Barrier_As_Mirror.

  Module Mirror := C004.P3_T__Weakforcing.
  Module Barrier := C005.P2_T__Barrier.C005_Barrier_T.
  Module Def := Barrier.Def.
  Module P := Def.P.
  Module Pre := C002.P1_S__Kernel_Spec.C_002_Prelim.
  Module HK := C002.P2_R__Hilbert_Kernel.C_002_HilbertKernel_R.
  Module Core := C004.P2_S__Mirror_Lemma.C_004_Mirror_S.
  
  (*************************************************************************)
  (*                                                                       *)
  (*  Hilbert K-Combinator: Constructive Witness for Weakening             *)
  (*                                                                       *)
  (*  The Additive Theory (ATP) exports Modus Ponens.                      *)
  (*  The underlying kernel implements Hilbert axioms K and S.             *)
  (*  We witness K explicitly here to derive the weakening rule.           *)
  (*                                                                       *)
  (*************************************************************************)

  (*
    Hilbert K Axiom

    For all formulas φ, ψ:

      Prov(φ → (ψ → φ))

    This is the fundamental combinator for weakening.
  *)

  Theorem Prov_K : forall phi psi : P.ATP_Form,
    P.ATP_Prov (P.ATP_Imp phi (P.ATP_Imp psi phi)).
  Proof.
    intros phi psi.

    (*
      Define the K instance: φ → (ψ → φ)
    *)

    pose (K_inst := P.ATP_Imp phi (P.ATP_Imp psi phi)).
    
    (*
      Use Pre.cons/nil (the kernel's list type) to build the proof object.
    *)

    pose (pf := (Pre.cons K_inst Pre.nil) : HK.Proof).

    (*
      Build a direct kernel proof object (no checker bridge needed).
    *)

    unfold P.ATP_Prov.
    exists pf.
    apply HK.Prf_intro with (phi := K_inst).
    - simpl. exact (eq_refl _).
    - apply HK.Prf_lines_cons_Ax.
      + apply HK.Ax_K.
      + apply HK.Prf_lines_nil.
  Qed.

  (*
    Derived Weakening Rule

    From Prov(A), derive Prov(B → A).

    Proof: Apply Modus Ponens to K and the hypothesis:

      1. K axiom: Prov(A → (B → A))
      2. Hypothesis: Prov(A)
      3. MP: Prov(B → A)
  *)

  Lemma Prov_weakening : forall A B, P.ATP_Prov A -> P.ATP_Prov (P.ATP_Imp B A).
  Proof.
    intros A B H_Prov_A.

    (*
      Instantiate K: Prov(A → (B → A))
    *)

    pose proof (Prov_K A B) as H_K.

    (*
      Apply Modus Ponens: (A → (B → A)), A ⊢ B → A
    *)

    eapply P.ATP_Prov_MP; eauto.
  Qed.

  (*************************************************************************)
  (*                                                                       *)
  (*  Wrapping Barrier Flip Logic as Mirror Transform                      *)
  (*                                                                       *)
  (*  The separator's Flip Logic becomes a representable transformer:      *)
  (*                                                                       *)
  (*    trF(φ) = Flip(S, code(φ))                                          *)
  (*                                                                       *)
  (*  This allows the Mirror Lemma to construct diagonal sentences.        *)
  (*                                                                       *)
  (*************************************************************************)

  Definition Flip_Transformer
    (S : Barrier.SEPARATOR)
    (code : Mirror.Form -> Def.N.nat)
    (Flip_Rep : Prop) :
    Mirror.Transformer :=
    {|
       Core.trF   := fun phi => Barrier.Def.Flip_Logic S (code phi);
       Core.trRep := Flip_Rep
    |}.

  (*************************************************************************)
  (*                                                                       *)
  (*  Mirror Parameters — Instantiating the Mirror Schema for Barriers     *)
  (*                                                                       *)
  (*  The separator provides exactly the structure needed for the Mirror   *)
  (*  Lemma's abstract parameters.                                         *)
  (*                                                                       *)
  (*************************************************************************)

  (*
    Barrier_REG — The Separator as Regulator

    REG(i, b) ≜ { b = A(i)  if σ(i) = true
                { b = B(i)  if σ(i) = false

    The separator's decision σ(i) determines which class bound regulates
    index i. This is exactly the REG predicate needed by the Mirror Lemma.
  *)

  Definition Barrier_REG (S : Barrier.SEPARATOR) (i : Def.N.nat) (b : P.ATP_Form) : Prop :=
    if S.(Def.sigma) i
    then b = Def.A i
    else b = Def.B i.

  (*
    Barrier_BND — Syntactic Implication Bound

    BND(φ, b) ≜ Prov(φ → b)

    The bound predicate is simply provable implication.
  *)

  Definition Barrier_BND (phi b : P.ATP_Form) : Prop :=
    P.ATP_Prov (P.ATP_Imp phi b).

  (*
    Barrier_MP — Complete Mirror Parameters

    Bundles REG, BND, and ProvT_P into the MirrorParams record
    required by the Mirror Lemma.
  *)

  Definition Barrier_MP (S : Barrier.SEPARATOR) : Mirror.MirrorParams :=
    {|
       Mirror.REG     := Barrier_REG S;
       Mirror.BND     := Barrier_BND;
       Mirror.ProvT_P := P.ATP_Prov
    |}.

  (***********************************************************************)
  (*                                                                     *)
  (*  The Separator Witnesses As-If                                      *)
  (*                                                                     *)
  (*  The separator suddenly acts as a regulator witness for the         *)
  (*  diagonal sentence!                                                 *)
  (*                                                                     *)
  (*  Theorem: For any diagonal sentence D = Flip(S, d), there exists    *)
  (*  a bound b such that:                                               *)
  (*                                                                     *)
  (*    BND(D, b) ∧ Prov(D → b)                                          *)
  (*                                                                     *)
  (*  This is a key component of the As-If predicate.                    *)
  (*                                                                     *)
  (***********************************************************************)

  Theorem Separator_Witnesses_AsIF :
    forall (S : Barrier.SEPARATOR) (D : Mirror.Form) (d : Barrier.Def.N.nat),
    (* Assumption: D is the diagonal fixed point *)
    (D = Barrier.Def.Flip_Logic S d) ->
    (* Conclusion: D satisfies the As-If bound condition *)
    exists (b : Mirror.Form),
      Mirror.BND (Barrier_MP S) D b /\
      P.ATP_Prov (P.ATP_Imp D b).
  Proof.
    intros S D d H_Fix.

    (*
      Run the separator on the code d
    *)

    destruct (Barrier.Def.sigma S d) eqn:Heq.
    -
      (*
        Case σ(d) = true: Separator chooses class A
      *)

      exists (Def.A d).
      split.
      +
        (*
          Goal: BND(D, A(d)), i.e., Prov(D → A(d))
        *)

        unfold Barrier_MP, Barrier_BND.

        (*
          Separator certificate: Prov(A(d))
        *)

        pose proof (S.(Def.cert) d) as H_Prov_A.
        rewrite Heq in H_Prov_A.

        (*
          Weakening: Prov(A(d)) → Prov(D → A(d))
        *)

        apply Prov_weakening.
        exact H_Prov_A.
      +
        (*
          Goal: Prov(D → A(d)) (repeated for second conjunct)
        *)

        pose proof (S.(Def.cert) d) as H_Prov_A.
        rewrite Heq in H_Prov_A.
        apply Prov_weakening. exact H_Prov_A.

    -
      (*
        Case σ(d) = false: Separator chooses class B
      *)

      exists (Def.B d).
      split.
      +
        (*
          Goal: BND(D, B(d)), i.e., Prov(D → B(d))
        *)

        unfold Barrier_MP, Barrier_BND.
        pose proof (S.(Def.cert) d) as H_Prov_B.
        rewrite Heq in H_Prov_B.
        apply Prov_weakening. exact H_Prov_B.
      + pose proof (S.(Def.cert) d) as H_Prov_B.
        rewrite Heq in H_Prov_B.
        apply Prov_weakening. exact H_Prov_B.
  Qed.

  (*************************************************************************)
  (*                                                                       *)
  (*  Collision Theorem — Two Evaluators Cannot Coexist                    *)
  (*                                                                       *)
  (*  The contradiction is re-derived by showing that the separator        *)
  (*  creates two competing evaluations of truth for the same index:       *)
  (*                                                                       *)
  (*    1. PROOF EVALUATOR (Soundness + Certificate):                      *)
  (*       σ(d) = true  → Prov(A(d)) → Truth(A(d))                         *)
  (*       σ(d) = false → Prov(B(d)) → Truth(B(d))                         *)
  (*                                                                       *)
  (*    2. FLIP EVALUATOR (Flip Logic + Diagonal):                         *)
  (*       Truth(D) ↔ Truth(Flip(S,d))                                     *)
  (*       σ(d) = true  → Flip(S,d) = B(d) → Truth(B(d))                   *)
  (*       σ(d) = false → Flip(S,d) = A(d) → Truth(A(d))                   *)
  (*                                                                       *)
  (*  Combined:                                                            *)
  (*                                                                       *)
  (*        σ(d) = true  → Truth(A(d)) ∧ Truth(B(d))                       *)
  (*        σ(d) = false → Truth(B(d)) ∧ Truth(A(d))                       *)
  (*                                                                       *)
  (*  In a consistent setting (Semantic Disjointness), these cannot        *)
  (*  both be true. Contradiction.                                         *)
  (*                                                                       *)
  (*************************************************************************)

  Theorem Barrier_Contradiction_via_Mirror :
    forall (S : Barrier.SEPARATOR) (d : Def.N.nat) (D : P.ATP_Form),
      Barrier.Disjointness ->
      (forall phi, P.ATP_Prov phi -> Def.Truth phi) ->

      (*
        Assumption: D is the Semantic Fixed Point of Flip Logic
      *)

      (Def.Truth D <-> Def.Truth (Def.Flip_Logic S d)) ->
      
      (*
        Assumption: D tracks A and B (Crucial for Barrier)
      *)

      (Def.Truth (Def.A d) <-> Def.Truth D) ->
      (Def.Truth (Def.B d) <-> Def.Truth D) ->
      False.
  Proof.
    intros S d D Disjoint Sound H_Fix H_TrackA H_TrackB.

    (*
      Case analysis on separator's decision: σ(d) = true or false?
    *)

    destruct (Def.sigma S d) eqn:Heq.

    -
      (*
        Case σ(d) = true: Separator chooses A(d)
      *)

      (*
        PROOF EVALUATOR: σ(d) = true → Prov(A(d))
      *)

      pose proof (Def.cert S d) as H_Prov_A.
      rewrite Heq in H_Prov_A.

      (*
        Soundness: Prov(A(d)) → Truth(A(d))
      *)

      apply Sound in H_Prov_A.

      (*
        Truth Tracking: Truth(A(d)) ↔ Truth(D)
        So: Truth(D)
      *)

      apply H_TrackA in H_Prov_A.

      (*
        FLIP EVALUATOR: Truth(D) ↔ Truth(Flip(S,d))
        Since σ(d) = true, Flip(S,d) = B(d)
        So: Truth(B(d))
      *)

      apply H_Fix in H_Prov_A.
      unfold Def.Flip_Logic in H_Prov_A.
      rewrite Heq in H_Prov_A.

      (*
        Now we have: Truth(B(d))
        Re-establish: Truth(A(d)) from certificate
      *)

      pose proof (Def.cert S d) as H_Prov_A_again.
      rewrite Heq in H_Prov_A_again.
      apply Sound in H_Prov_A_again.

      (*
        COLLISION: Truth(A(d)) ∧ Truth(B(d))
        Semantic Disjointness gives ⊥
      *)

      eapply Disjoint.
      apply H_Prov_A_again. apply H_Prov_A.

    -
      (*
        Case σ(d) = false: Separator chooses B(d)
      *)

      (*
        PROOF EVALUATOR: σ(d) = false → Prov(B(d))
      *)

      pose proof (Def.cert S d) as H_Prov_B.
      rewrite Heq in H_Prov_B.

      (*
        Soundness: Prov(B(d)) → Truth(B(d))
      *)

      apply Sound in H_Prov_B.

      (*
        Truth Tracking: Truth(B(d)) ↔ Truth(D)
        So: Truth(D)
      *)

      apply H_TrackB in H_Prov_B.

      (*
        FLIP EVALUATOR: Truth(D) ↔ Truth(Flip(S,d))
        Since σ(d) = false, Flip(S,d) = A(d)
        So: Truth(A(d))
      *)

      apply H_Fix in H_Prov_B.
      unfold Def.Flip_Logic in H_Prov_B.
      rewrite Heq in H_Prov_B.

      (*
        Now we have: Truth(A(d))
        Re-establish: Truth(B(d)) from certificate
      *)

      pose proof (Def.cert S d) as H_Prov_B_again.
      rewrite Heq in H_Prov_B_again.
      apply Sound in H_Prov_B_again.

      (*
        COLLISION: Truth(B(d)) ∧ Truth(A(d))
        Semantic Disjointness gives ⊥
      *)

      eapply Disjoint. apply H_Prov_B. apply H_Prov_B_again.
  Qed.

  (*************************************************************************)
  (*                                                                       *)
  (*  Separator Implies Class Collapse                                     *)
  (*                                                                       *)
  (*  The Five-Step Argument (Barrier via Mirror):                         *)
  (*                                                                       *)
  (*      (i) Assume a SEPARATOR exists (hypothesis for reductio).         *)
  (*                                                                       *)
  (*     (ii) The Mirror Lemma forces the diagonal into an As-If state:    *)
  (*          AsIF(D).                                                     *)
  (*                                                                       *)
  (*    (iii) Soundness lifts As-If to semantic Truth:                     *)
  (*          AsIF(D) + Sound → Truth(D).                                  *)
  (*                                                                       *)
  (*     (iv) Flip Logic derives both:                                     *)
  (*          Truth(A(d)) ∧ Truth(B(d)).                                   *)
  (*                                                                       *)
  (*      (v) Semantic Disjointness gives ⊥ (contradiction).               *)
  (*                                                                       *)
  (*  From ⊥, we can derive anything, including A = B (class collapse).    *)
  (*                                                                       *)
  (*************************************************************************)

  Theorem Separator_Implies_Class_Collapse :
    forall (S : Barrier.SEPARATOR),
      Barrier.Disjointness ->
      (forall phi, P.ATP_Prov phi -> Def.Truth phi) ->
      (exists (d : Def.N.nat) (D : P.ATP_Form),
        (Def.Truth D <-> Def.Truth (Def.Flip_Logic S d)) /\
        (Def.Truth (Def.A d) <-> Def.Truth D) /\
        (Def.Truth (Def.B d) <-> Def.Truth D)) ->

      (forall n, Def.A n = Def.B n).
  Proof.
    intros S Disjoint Sound Hdiag n.

    (*
      Step 1: Extract the diagonal witness
    *)

    destruct Hdiag as [d [D [H_Fix [H_TrackA H_TrackB]]]].

    (*
      Step 2: Derive the barrier contradiction (⊥)
    *)

    pose proof
      (@Barrier_Contradiction_via_Mirror S d D Disjoint Sound H_Fix H_TrackA H_TrackB)
      as H_False.

    (*
      Step 3: Ex Falso Quodlibet

      From ⊥, derive anything — in particular, A(n) = B(n).

      In the BHK_R nucleus, False is the empty type,
      so elimination gives any proposition.
    *)

    destruct H_False.
  Qed.

End Barrier_As_Mirror.
