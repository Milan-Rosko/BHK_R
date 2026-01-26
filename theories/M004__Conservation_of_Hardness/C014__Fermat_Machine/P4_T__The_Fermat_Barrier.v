(* P4_T__The_Fermat_Barrier.v *)

From Fermat_Machine.C014 Require Import P3_S__Machine_Definition P3_R__Fermat_Solver P4_S__Barrier_Interface.
From Cubic_Incompleteness.C012 Require Import P2_S__Barrier.

Module The_Fermat_Barrier.
  Import Fermat_Solver_R.
  Module Barrier := Cubic_Incompleteness.C012.P2_S__Barrier.C012_Barrier_T.

  (** Context Parameters from C012 *)
  Parameter Ctx_Disjoint : Barrier.Ctx_Disjointness.
  Parameter Ctx_DPRM_Diagonal : Barrier.Ctx_DPRM_Diagonal.

  (*
     
     If a Fermat Machine M exists:
     1. Construct S = Fermat_solver(M)
     2. S is Radical (by M's radical property)
     3. Apply The_Cubic_Barrier to S
     4. Contradiction
  *)

  Theorem C012_barrier_machine :
    ~ (exists M, Machine_Definition.Fermat_Machine M).
  Proof.
    intro H_Exists.
    destruct H_Exists as [M HM].
    
    (*
      Lift the machine to a solver
    *)

    set (S := Fermat_solver M HM).
    
    (*
      Prove the solver satisfies the radicality hypothesis
    *)

    pose proof (radical_sigma_true M HM) as Hrad.
    
    (*
      The Cubic Barrier refutes any such solver
    *)
    
    exact (@Barrier.The_Cubic_Barrier Ctx_Disjoint Ctx_DPRM_Diagonal S Hrad).
  Qed.

  Global Instance C012_BEM : Barrier_Interface.BarrierEngine_Machine :=
    {| Barrier_Interface.barrier_machine := C012_barrier_machine |}.

End The_Fermat_Barrier.