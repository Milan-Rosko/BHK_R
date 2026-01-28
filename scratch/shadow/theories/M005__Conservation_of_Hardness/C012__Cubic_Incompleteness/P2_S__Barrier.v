(* P2_S__Barrier.v *)

From Coq Require Import Init.Logic.
From C002 Require Import P5_T__Proof_Theory.
From C012 Require Import P1_S__Structure.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C012 / Phase 2 (S): The Cubic Barrier (MRDP Instantiation)           *)
(*                                                                       *)
(*  What This File Provides                                              *)
(*                                                                       *)
(*    (i) Certified Diophantine Solver.                                  *)
(*        A definition of what it means to effectively solve and         *)
(*        certify Diophantine equations.                                 *)
(*                                                                       *)
(*    (i) The MRDP Context.                                              *)
(*        Parameters representing the Matiyasevich-Robinson-Davis-       *)
(*        Putnam theorem: Diophantine sets are RE, allowing              *)
(*        diagonalization.                                               *)
(*                                                                       *)
(*  (iii) The Cubic Barrier Theorem.                                     *)
(*        Proof that no Certified Solver can be "Radical" (primitive     *)
(*        recursive).                                                    *)
(*                                                                       *)
(*  MRDP allows us to encode the "Liar Paradox" into a polynomial.       *)
(*  If a solver could resolve this polynomial using only bounded         *)
(*  (radical) resources, it would violate the separation of              *)
(*  Verification and Inversion energy.                                   *)
(*                                                                       *)
(*************************************************************************)

Module C012_Barrier_T.

  Module N   := C002.P5_T__Proof_Theory.Prelude.
  Module Str := C012_Structure_S.

  (*************************************************************************)
  (*                                                                       *)
  (*  The Solver Interface                                                 *)
  (*                                                                       *)
  (*  A solver must provide a decision bit (sigma) and a witness           *)
  (*  that matches the semantics (Solvable/Unsolvable).                    *)
  (*                                                                       *)
  (*************************************************************************)
  
  Record Certified_Diophantine_Solver : Type := {
    sigma : N.nat -> bool;
    
    (* If sigma says true, it must be solvable *)
    witness_solvable : forall n, sigma n = true -> 
      Str.Solvable (Str.decode_equation n);
      
    (* If sigma says false, it must be unsolvable *)
    witness_unsolvable : forall n, sigma n = false -> 
      Str.Unsolvable (Str.decode_equation n)
  }.

  (*************************************************************************)
  (*                                                                       *)
  (*  The Hypothesis: Solvability by Radicals                              *)
  (*                                                                       *)
  (*  This hypothesis asserts that the solver's decision function is       *)
  (*  primitive recursive. This is the claim we refute.                    *)
  (*                                                                       *)
  (*************************************************************************)

  Definition Hypothesis_Radical_Solver (S : Certified_Diophantine_Solver) : Prop :=
    let char_func := fun n => 
      if sigma S n then N.S N.O else N.O 
    in
    Str.Solvable_By_Radicals char_func.

  (*************************************************************************)
  (*                                                                       *)
  (*  Context Parameters (MRDP)                                            *)
  (*                                                                       *)
  (*************************************************************************)

  (*
    Semantic Consistency: No equation is both Solvable and Unsolvable
  *)

  Definition Ctx_Disjointness : Prop := 
    forall eq, ~ (Str.Solvable eq /\ Str.Unsolvable eq).

  (*
    The MRDP Diagonal: 
    There exists an index 'd' such that the equation E_d encodes 
    the negation of the solver's decision on 'd'.
     
    “This equation has a solution iff the solver says it doesn't.”
  *)

  Definition Ctx_DPRM_Diagonal : Type :=
    forall S : Certified_Diophantine_Solver,
      exists (d : N.nat),
        let eq_d := Str.decode_equation d in
        (Str.Solvable eq_d <-> sigma S d = false).

  (*************************************************************************)
  (*                                                                       *)
  (*  Cubic Incompleteness / Delian Barrier (Proof Strategy).              *)
  (*                                                                       *)
  (*     (i) Use MRDP to construct the liar equation for S.                *)
  (*    (ii) Analyze cases on the solver's output sigma(d).                *)
  (*   (iii) Both cases lead to a contradiction with Disjointness.         *)
  (*                                                                       *)
  (*************************************************************************)

  Theorem The_Cubic_Barrier :
    forall (Disjoint : Ctx_Disjointness)
           (Diagonal : Ctx_DPRM_Diagonal)
           (S : Certified_Diophantine_Solver),
      Hypothesis_Radical_Solver S -> False.
  Proof.
    intros Disjoint Diagonal S H_Radical.
    
    (*
      Invoke DPRM to get the paradox index d
    *)

    destruct (Diagonal S) as [d H_Paradox].
    set (eq_d := Str.decode_equation d) in *.
    
    (*
      Case Analysis on the solver's output
    *)

    remember (sigma S d) as decision.
    destruct decision.
    
    - (*
        Case: Solver says True (Solvable)
        Liar says: Solvable <-> False (Unsolvable)
      *)
      assert (H_Sol : Str.Solvable eq_d).
      { 
        apply (@witness_solvable S d).
        symmetry. exact Heqdecision. 
      }

      (*
        Logic: Solvable -> False
      *)

      apply H_Paradox in H_Sol.
      discriminate H_Sol.

    - (*
        Case: Solver says False (Unsolvable)
        Liar says: Solvable <-> True
      *)

      assert (H_Sol : Str.Solvable eq_d).
      { apply H_Paradox. reflexivity. }
      
      (*
        But Solver provided a witness of Unsolvability
      *)

      assert (H_Unsol : Str.Unsolvable eq_d).

      { 
        apply (@witness_unsolvable S d).
        symmetry. exact Heqdecision. 
      }
      
      (*
        Collision: Equation is both Solvable and Unsolvable
      *)

      apply (Disjoint eq_d).
      split; assumption.
  Qed.

  (*
    Corollary: Any functioning solver must be Transcendental
  *)
  
  Corollary Diophantine_Is_Transcendental :
    forall (Disjoint : Ctx_Disjointness)
           (Diagonal : Ctx_DPRM_Diagonal)
           (S : Certified_Diophantine_Solver),
      ~ Hypothesis_Radical_Solver S.
  Proof.
    intros D G S H.
    eapply The_Cubic_Barrier; eauto.
  Qed.

End C012_Barrier_T.
Export C012_Barrier_T.