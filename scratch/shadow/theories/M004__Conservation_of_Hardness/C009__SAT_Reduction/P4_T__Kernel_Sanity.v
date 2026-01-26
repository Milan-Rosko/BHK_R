(* P4_T__Kernel_Sanity.v *)

From Coq Require Import Init.Logic.
From SAT.C009 Require Import P3_T__FOL.
From SAT.C009 Require Import P3_R__Kernel.

Set Implicit Arguments.
Unset Strict Implicit.

Module Test_FOL_Kernel.

(*************************************************************************)
(*                                                                       *)
(*  C009 / Phase 4 (T): Kernel Sanity Tests (Effectivity Witnesses)      *)
(*                                                                       *)
(*    (i) Scope.                                                         *)
(*                                                                       *)
(*        Regression tests and effectivity witnesses for the FOL kernel. *)
(*        Validates that check correctly recognizes basic proofs.        *)
(*                                                                       *)
(*   (ii) Testing Discipline: Computational Validation.                  *)
(*                                                                       *)
(*        Each test is a vm_compute example showing:                     *)
(*          (i) A proof script pf                                        *)
(*          - A target formula phi                                       *)
(*          - check pf phi = true  (validated by vm_compute)             *)
(*                                                                       *)
(*        This is "proof by computation": the kernel's correctness is    *)
(*        witnessed by successful execution, not by meta-theoretic       *)
(*        soundness proofs.                                              *)
(*                                                                       *)
(*  (iii) Test Coverage.                                                 *)
(*                                                                       *)
(*        The tests cover all major proof rules:                         *)
(*          (a) Reflexivity: t = t                                       *)
(*          (b) Generalization: φ → ∀x.φ                                 *)
(*          (c) Instantiation: ∀x.φ → φ[x↦t]                             *)
(*          (d) Symmetry: x=y → y=x  (via Leibniz)                       *)
(*          (e) Double instantiation: ∀x.x=x → (1=1 ∧ 2=2)               *)
(*          (f) Leibniz with implication bodies                          *)
(*                                                                       *)
(*   (iv) Role in C009.                                                  *)
(*                                                                       *)
(*        Provides computational confidence in the kernel.               *)
(*        These are NOT formal soundness proofs, but effectivity         *)
(*        witnesses: the kernel computes correctly on concrete inputs.   *)
(*                                                                       *)
(*************************************************************************)

  (*
    Minimal parsing-safe sanity stub.
    Ensures the file loads correctly in all build environments.
  *)

  Example sanity_parses : True.
  Proof.
    exact I.
  Qed.

  Import C009_FOL_Public.

  Module K := C009_FOL_Public.Kernel.

  Definition x0 : Var := Prelude.O.
  Definition t0 : Term := Prelude.O.

  (*
    Test. Reflexivity (0 = 0)
  *)

  Definition claim_refl : Form := Eq t0 t0.
  Definition pf_refl : K.Proof := nil.

  Example test_refl : K.check pf_refl claim_refl = true.
  Proof. vm_compute. reflexivity. Qed.

  (*
    Test. Generalization (forall x, x = x)
  *)

  Definition var_x : Var := Prelude.S Prelude.O.
  Definition term_x : Term := Prelude.S Prelude.O.
  Definition claim_gen : Form := All var_x (Eq term_x term_x).

  Definition pf_gen : K.Proof :=
    cons (Eq term_x term_x) nil.

  Example test_gen : K.check pf_gen claim_gen = true.
  Proof. vm_compute. reflexivity. Qed.

  (*
    Test. Instantiation (from forall x, x = x to 0 = 0)
  *)

  Definition claim_inst : Form := Eq t0 t0.

  Definition pf_inst : K.Proof :=
    cons (Eq t0 t0)
    (cons claim_gen nil).

  Example test_inst : K.check pf_inst claim_inst = true.
  Proof. vm_compute. reflexivity. Qed.

  Import C009_FOL_Public.

  Definition O := Prelude.O.
  Definition S := Prelude.S.

  (*
    Variables and Terms are just Nats in this syntax
  *)

  Definition x : Var := O.
  Definition y : Var := S O.
  
  Definition tx : Term := O.
  Definition ty : Term := S O.
  Definition t1 : Term := S (S O).
  Definition t2 : Term := S (S (S O)).


  (*
    Test. Instantiation (from forall x, x = x to 0 = 0)
    Test. Symmetry of Equality: Prove (x = y) -> (y = x)
  *)

  Definition claim_sym : Form := Eq ty tx.

  (*
    The bound variable 'z' used for Leibniz substitution
  *)

  Definition z : Var := S (S O).

  (*
    Leibniz body: z = x
  *)

  Definition body_leibniz : Form := Eq z tx.

  (*
  The raw proof script: Leibniz substitution from x=y and x=x
  *)

  Definition pf_sym : C009_FOL_Kernel_R.Proof :=
    cons (All z body_leibniz)
    (cons (Eq tx ty)
    (cons (Eq tx tx) nil)).

  Example test_symmetry_holds : 
    C009_FOL_Kernel_R.check pf_sym claim_sym = true.
  Proof. vm_compute. reflexivity. Qed.

  (*
    Test. Double Instantiation 
    Goal: (Forall x. x = x) -> (1 = 1) /\ (2 = 2)
  *)

  (*
    Forall x, x=x
  *)

  Definition univ_identity : Form := All x (Eq x x).
  
  (*
    Targets
  *)

  Definition eq_1_1 : Form := Eq t1 t1.
  Definition eq_2_2 : Form := Eq t2 t2.

  Definition pf_axiom_only : C009_FOL_Kernel_R.Proof :=
    (* Dummy equality to register t1 and t2 in the kernel's term scanner *)
    cons (Eq t1 t2) 
    (cons univ_identity nil).

  (*
    Test. Can we derive 1=1?
  *)

  Example test_inst_1 : 
    C009_FOL_Kernel_R.check pf_axiom_only eq_1_1 = true.
  Proof. vm_compute. reflexivity. Qed.

  (*
    Test. Can we derive 2=2 from the SAME script?
  *)

  Example test_inst_2 : 
    C009_FOL_Kernel_R.check pf_axiom_only eq_2_2 = true.
  Proof. vm_compute. reflexivity. Qed.

  (*
    Test. Leibniz with a nontrivial body (implication)
    Goal: from x=y and a Leibniz body, derive (y=x)->(y=x)
  *)

  Definition body_leibniz_imp : Form := Imp (Eq z tx) (Eq z tx).
  Definition claim_leibniz_imp : Form := Imp (Eq ty tx) (Eq ty tx).

  Definition pf_leibniz_imp : C009_FOL_Kernel_R.Proof :=
    cons (All z body_leibniz_imp)
    (cons (Eq tx ty)
    (cons (Imp (Eq tx tx) (Eq tx tx)) nil)).

  Example test_leibniz_imp :
    C009_FOL_Kernel_R.check pf_leibniz_imp claim_leibniz_imp = true.
  Proof. vm_compute. reflexivity. Qed.

End Test_FOL_Kernel.
