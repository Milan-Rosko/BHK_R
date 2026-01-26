(* P3_R__Fermat_Solver.v *)

From Fermat_Machine.C014 Require Import P1_T__Arithmetic_Surface P2_S__Bridge_Contract P3_S__Machine_Definition.
From Cubic_Incompleteness.C012 Require Import P2_S__Barrier.

Module Fermat_Solver_R.
  Module Barrier := Cubic_Incompleteness.C012.P2_S__Barrier.C012_Barrier_T.
  Import C014_Arithmetic_T.
  Import Machine_Definition.

  (** The Logic of the Solver: 
     If a Fermat Machine exists, it provides a witness for every n > 2. 
     Therefore, the 'sigma' function for the Diophantine solver is simply "True".
     (Assuming the decoded equations correspond 1:1 to Fermat instances).
  *)
  Definition sigma_true : N.nat -> N.bool := fun _ => N.true.

  Lemma sigma_true_not_false : forall n, sigma_true n = N.false -> False.
  Proof. intros n H; discriminate H. Qed.

  (** Extract solvability witness from the Machine *)
  Definition witness_solvable_from_machine 
    (M : N.nat -> Triple) 
    (HM : Fermat_Machine M) 
    (n : N.nat) 
    : Bridge_Contract.Str.Solvable (Bridge_Contract.Str.decode_equation n) :=
    match HM with
    | conj _ H_Solver =>
      (* Apply the machine to get the relation *)
      let H_Rel := H_Solver n (Bridge_Contract.Index_Condition n) in
      (* Bridge the relation to solvability *)
      Bridge_Contract.Fermat_Triple_Implies_Solvable (M n) n H_Rel
    end.

  (** Construct the Certified Solver 
     This effectively says: "I can solve the Diophantine equation corresponding to FLT(n)
     for ALL n, simply by running the Fermat Machine."
  *)
  Definition Fermat_solver (M : N.nat -> Triple) (HM : Fermat_Machine M)
      : Barrier.Certified_Diophantine_Solver :=
      {|
        Barrier.sigma := sigma_true
       ; Barrier.witness_solvable := fun n _ => witness_solvable_from_machine M HM n
       ; Barrier.witness_unsolvable := fun n Hfalse => False_rect _ (sigma_true_not_false n Hfalse)
      |}.

  (** Verify the solver is Radical (computational requirement for the Barrier) *)
  Lemma radical_sigma_true :
      forall (M : N.nat -> Triple) (HM : Fermat_Machine M),
        Barrier.Hypothesis_Radical_Solver (Fermat_solver M HM).
  Proof.
      intros M HM.
      unfold Barrier.Hypothesis_Radical_Solver.
      simpl.
      (* sigma_true is a constant function, which is trivially radical *)
      unfold Bridge_Contract.Str.Solvable_By_Radicals.
      apply Bridge_Contract.Str.Rad.R_Const.
  Qed.

End Fermat_Solver_R.