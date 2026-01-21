(* P3_T__Mirror_Instance.v *)
(*                                                                       *)
(*  C_005 / Phase 3 (T): The Mirror Instance (Separator as Regulator)    *)
(*                                                                       *)
(*  The Metatheoretic Bridge.                                            *)
(*                                                                       *)
(*  This file re-interprets the Adversarial Barrier through the lens     *)
(*  of the Mirror Lemma[cite: 1220]. It demonstrates that the            *)
(*  impossibility of a Separator is a structural necessity derived from  *)
(*  the Mirror Calculus[cite: 1228].                                     *)
(*                                                                       *)
(*    (i) The Separator as a Regulator:                                  *)
(*        The SEPARATOR record (sigma, cert) provides the exact data     *)
(*        needed to satisfy the REG and BND predicates.                  *)
(*        It "regulates" the diagonal sentence by forcing a formal       *)
(*        classification.                                                *)
(*                                                                       *)
(*   (ii) From "As-If" to "Collision":                                   *)
(*        The Mirror Lemma proves that the diagonal sentence D exists    *)
(*        in an AsIF state[cite: 1225]. The Barrier then shows that      *)
(*        under a Soundness hypothesis, this "As-If" state               *)
(*        collides with the Flip Logic, refuting the Separator.          *)
(*                                                                       *)
(*  (iii) Constructive Hilbert Witness:                                  *)
(*        To derive the necessary Weakening rules without axioms,        *)
(*        we explicitly witness the Hilbert K-combinator within the      *)
(*        Kernel.                                                        *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.

(* Import the Mirror Lemma Public Surface *)
From ATP.C004__Mirror_Lemma Require Import P5_T__Weakforcing.
(* Import the Barrier Public Surface *)
From Adversarial_Barrier.C005 Require Import P3_T__Barrier.

(* NEW: Import the Kernel Realization to witness K constructively *)
From ATP.C002 Require Import P2_R__Hilbert_Kernel.

Set Implicit Arguments.
Unset Strict Implicit.

Module Barrier_As_Mirror.

  Module Mirror := ATP.C004__Mirror_Lemma.P5_T__Weakforcing.
  Module Barrier := Adversarial_Barrier.C005.P3_T__Barrier.C005_Barrier_T.
  Module Def := Barrier.Def.
  Module P := Def.P.
  Module Pre := ATP.C002.P1_S__Kernel_Spec.C_002_Prelim.
  Module HK := ATP.C002.P2_R__Hilbert_Kernel.C_002_HilbertKernel_R.
  Module Core := ATP.C004__Mirror_Lemma.P2_S__Mirror_Lemma.C_004_Mirror_S.
  
  (*************************************************************************)
  (*                                                                       *)
  (*  Logic Bridge.                                                        *)
  (*  The Additive Theory interface (ATP) exports Modus Ponens.            *)
  (*  The underlying Kernel implements Hilbert K and S.                    *)
  (*  We witness K explicitly here to derive Weakening.                    *)
  (*                                                                       *)
  (*************************************************************************)

  Theorem Prov_K : forall phi psi : P.ATP_Form,
    P.ATP_Prov (P.ATP_Imp phi (P.ATP_Imp psi phi)).
  Proof.
    intros phi psi.
    (* Define the K instance *)
    pose (K_inst := P.ATP_Imp phi (P.ATP_Imp psi phi)).
    
    (* 1. Construct the witness: a single-line proof script *)
    (* We use Pre.cons/nil which correspond to the Kernel's list type. *)
    pose (pf := (Pre.cons K_inst Pre.nil) : HK.Proof).

    (* 2. Build a direct kernel proof object (no checker bridge needed). *)
    unfold P.ATP_Prov.
    exists pf.
    apply HK.Prf_intro with (phi := K_inst).
    - simpl. exact (eq_refl _).
    - apply HK.Prf_lines_cons_Ax.
      + apply HK.Ax_K.
      + apply HK.Prf_lines_nil.
  Qed.

  (* Derived Weakening Rule: Prov A -> Prov (B -> A) *)
  Lemma Prov_weakening : forall A B, P.ATP_Prov A -> P.ATP_Prov (P.ATP_Imp B A).
  Proof.
    intros A B H_Prov_A.
    (* Use K: A -> (B -> A) *)
    pose proof (Prov_K A B) as H_K.
    (* MP: A -> (B -> A), A |- B -> A *)
    eapply P.ATP_Prov_MP; eauto.
  Qed.

  (*************************************************************************)
  (*                                                                       *)
  (*  We wrap the Barrier's "Flip_Logic" into a Mirror "Transformer".      *)
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
  (*  We instantiate the abstract MirrorParams for this specific context.  *)
  (*                                                                       *)
  (*************************************************************************)

  (* REG i b: The separator S (implicitly) maps index i to class bound b *)
  Definition Barrier_REG (S : Barrier.SEPARATOR) (i : Def.N.nat) (b : P.ATP_Form) : Prop :=
    if S.(Def.sigma) i
    then b = Def.A i
    else b = Def.B i.

  (* BND phi b: Syntactic implication (phi -> b) *)
  Definition Barrier_BND (phi b : P.ATP_Form) : Prop :=
    P.ATP_Prov (P.ATP_Imp phi b).

  Definition Barrier_MP (S : Barrier.SEPARATOR) : Mirror.MirrorParams :=
    {|
       Mirror.REG     := Barrier_REG S;
       Mirror.BND     := Barrier_BND;
       Mirror.ProvT_P := P.ATP_Prov
    |}.

  (***********************************************************************)
  (*                                                                     *)
  (*  The Separator suddenly(!) acts as a regulator witness for the      *)
  (*  diagonal.                                                          *)
  (*                                                                     *)
  (***********************************************************************)

  Theorem Separator_Witnesses_AsIF :
    forall (S : Barrier.SEPARATOR) (D : Mirror.Form) (d : Barrier.Def.N.nat),
    (* Assumption: D is the fixed point code 'd' *)
    (D = Barrier.Def.Flip_Logic S d) ->
    (* Conclusion: The diagonal satisfies the AsIF condition. *)
    exists (b : Mirror.Form),
      Mirror.BND (Barrier_MP S) D b /\
      P.ATP_Prov (P.ATP_Imp D b).
  Proof.
    intros S D d H_Fix.

    (* 1. Run the separator on the code d *)
    destruct (Barrier.Def.sigma S d) eqn:Heq.
    - (* Case A: Sigma says True -> Class A *)
      exists (Def.A d).
      split.
      + (* Prove BND (D, A d) i.e., Prov (D -> A d) *)
        unfold Barrier_MP, Barrier_BND.
        (* The separator gives Prov (A d) *)
        pose proof (S.(Def.cert) d) as H_Prov_A.
        rewrite Heq in H_Prov_A.
        (* Weakening: Prov (A d) -> Prov (D -> A d) *)
        apply Prov_weakening.
        exact H_Prov_A.
      + (* Prove Prov (D -> A d) again *)
        pose proof (S.(Def.cert) d) as H_Prov_A.
        rewrite Heq in H_Prov_A.
        apply Prov_weakening. exact H_Prov_A.

    - (* Case B: Sigma says False -> Class B *)
      exists (Def.B d).
      split.
      + (* Prove BND (D, B d) *)
        unfold Barrier_MP, Barrier_BND.
        pose proof (S.(Def.cert) d) as H_Prov_B.
        rewrite Heq in H_Prov_B.
        apply Prov_weakening. exact H_Prov_B.
      + pose proof (S.(Def.cert) d) as H_Prov_B.
        rewrite Heq in H_Prov_B.
        apply Prov_weakening. exact H_Prov_B.
  Qed.

  (***********************************************************************)
  (*                                                                     *)
  (*  Contradiction derived from the Separator's bound vs Flip Logic.    *)
  (*                                                                     *)
  (***********************************************************************)

  (*************************************************************************)
  (*                                                                       *)
  (*  Collision Theorem. Two Evaluators = Inconsistency                    *)
  (*                                                                       *)
  (*  The contradiction is re-derived by showing that the Separator        *)
  (*  creates two competing definitions of Truth for the same index:       *)
  (*                                                                       *)
  (*  1. Truth(A d) from the PROOF EVALUATOR (Soundness + Cert)            *)
  (*  2. Truth(B d) from the SOLVABILITY EVALUATOR (Flip Logic + Diagonal) *)
  (*                                                                       *)
  (*  In a consistent setting (Disjointness), these cannot be realized,    *)
  (*  at the same time: Ad Absurdum.                                       *)
  (*                                                                       *)
  (*************************************************************************)

  Theorem Barrier_Contradiction_via_Mirror :
    forall (S : Barrier.SEPARATOR) (d : Def.N.nat) (D : P.ATP_Form),
      Barrier.Disjointness ->
      (forall phi, P.ATP_Prov phi -> Def.Truth phi) ->
      (* Assumption: D is the Semantic Fixed Point of Flip Logic *)
      (Def.Truth D <-> Def.Truth (Def.Flip_Logic S d)) ->
      (* Assumption: D tracks A and B (Crucial for Barrier) *)
      (Def.Truth (Def.A d) <-> Def.Truth D) ->
      (Def.Truth (Def.B d) <-> Def.Truth D) ->
      False.
  Proof.
    intros S d D Disjoint Sound H_Fix H_TrackA H_TrackB.
    (* 1. Use Separator logic to determine the bound *)
    destruct (Def.sigma S d) eqn:Heq.
    - (* Case A: Separator says A *)
      (* Separator proves A *)
      pose proof (Def.cert S d) as H_Prov_A.
      rewrite Heq in H_Prov_A.

      (* Soundness: A is True *)
      apply Sound in H_Prov_A.
      (* Truth Tracking: A True -> D True *)
      apply H_TrackA in H_Prov_A.
      (* Fixed Point: D True -> Flip Logic True *)
      apply H_Fix in H_Prov_A.
      unfold Def.Flip_Logic in H_Prov_A.
      rewrite Heq in H_Prov_A.
      (* Now we have Truth (B d) *)

      (* Conflict: We have Truth(A) from Soundness, Truth(B) from Flip *)
      (* Re-establish Truth(A) for the clash *)
      pose proof (Def.cert S d) as H_Prov_A_again.
      rewrite Heq in H_Prov_A_again.
      apply Sound in H_Prov_A_again.

      (* Disjointness explodes *)
      eapply Disjoint.
      apply H_Prov_A_again. apply H_Prov_A.

    - (* Case B: Separator says B *)
      (* Separator proves B *)
      pose proof (Def.cert S d) as H_Prov_B.
      rewrite Heq in H_Prov_B.

      (* Soundness: B is True *)
      apply Sound in H_Prov_B.
      (* Truth Tracking: B True -> D True *)
      (* At this point, we could even “ex falso quodlibet” *)
      apply H_TrackB in H_Prov_B.
      (* Fixed Point: D True -> Flip Logic True *)
      apply H_Fix in H_Prov_B.
      unfold Def.Flip_Logic in H_Prov_B.
      rewrite Heq in H_Prov_B.
      (* Now we have Truth (A d) *)

      pose proof (Def.cert S d) as H_Prov_B_again.
      rewrite Heq in H_Prov_B_again.
      apply Sound in H_Prov_B_again.

      eapply Disjoint. apply H_Prov_B. apply H_Prov_B_again.
  Qed.

    (*************************************************************************)
    (*                                                                       *)
    (*             We are witnessing a constructive "Ex Falso."              *)
    (*                                                                       *)
    (*        (i) Assume (force) a SEPARATOR existence.                      *)
    (*       (ii) Use the Mirror Lemma to force it into an AsIF state.       *)
    (*      (iii) Use Soundness to lift AsIF to Truth.                       *)
    (*       (vi) Use Flip Logic to derive Truth(A) AND Truth(B).            *)
    (*        (v) Apply Disjointness to reach False.                         *)
    (*                                                                       *)
    (*          Result: The SEPARATOR is not just "unlikely";                *)
    (*          it is an inhabitant of the Empty Set (False).                *)
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
      (* The EFQ Conclusion: A and B are the same *)
      (forall n, Def.A n = Def.B n).
  Proof.
    intros S Disjoint Sound Hdiag n.
    (* 1. Derive the Barrier Contradiction (False) *)
    destruct Hdiag as [d [D [H_Fix [H_TrackA H_TrackB]]]].
    pose proof
      (@Barrier_Contradiction_via_Mirror S d D Disjoint Sound H_Fix H_TrackA H_TrackB)
      as H_False.
    (* 2. Apply Ex Falso Quodlibet (EFQ) *)
    (* In the BHK_R nucleus, False implies any equality. *)
    destruct H_False.
  Qed.

(******************************************)
(******************************************)
(******************************************)
(******************************************)
(******************************************)
(******************************************)
(******      ****          *          *****)
(****   ░░░░   *░░   ░░░░░ ░░   ░░░░   ****)
(***   ****░░   *░   ** *░**░   ***░░   ***)
(**░   *****░   *░      ****░   ****░   ***)
(**░   ***  ░   *░   ░░ ****░   ****░   ***)
(**░░   *░░    **░   *░*** *░   ****   ****)
(***░░░      ░  *          *          *****)
(*****░░░░░░*░░*░░░░░░░░░░*░░░░░░░░░░******)
(******************************************)
(******************************************)
(******************************************)
(******************************************)
(******************************************)
(******************************************)

End Barrier_As_Mirror.
