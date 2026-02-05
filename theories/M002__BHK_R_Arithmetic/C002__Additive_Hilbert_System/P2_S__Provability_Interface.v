(* P2_S__Provability_Interface.v *)

From Coq Require Import Init.Logic.
From C002 Require Import P1_S__Kernel_Spec.
From C002 Require Import P2_R__Hilbert_Kernel.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C002 / Phase 2 (S) : Provability Interface Binding                   *)
(*                                                                       *)
(*  Role:                                                                *)
(*                                                                       *)
(*  This module binds the abstract notion of "Provability" to the        *)
(*  concrete Hilbert Kernel implementation from Phase R.                 *)
(*                                                                       *)
(*    (i) it binds the abstract notion of "Provability" to               *)
(*        the concrete Hilbert Kernel implementation from Phase R.       *)
(*                                                                       *)
(*   (ii) It defines the 'Prov' predicate as,                            *)
(*                                                                       *)
(*               Prov(phi) <-> exists pf, Prf(pf, phi)                   *)
(*                                                                       *)
(*   This confirms the "Witness-First" discipline: to be provable        *)
(*   means to possess a concrete proof object (a script) that checks.    *)
(*                                                                       *)
(*************************************************************************)

Module C_002_Provability_S.

  Import C_002_Prelim.
  Import C_002_HilbertKernel_R. (* Realizes K, S, EFQ, check, Prf *)

  (*************************************************************************)
  (*                                                                       *)
  (*  We map the abstract Form/Imp/Bot types to the concrete inductive     *)
  (*  types defined in the R-layer.                                        *)
  (*                                                                       *)
  (*************************************************************************)


  Definition Form : Type := C_002_HilbertKernel_R.Form.
  Definition Imp  : Form -> Form -> Form := C_002_HilbertKernel_R.Imp.
  Definition Bot  : Form := C_002_HilbertKernel_R.Bot.

  Definition Prov (phi : Form) : Prop :=
    exists pf : C_002_HilbertKernel_R.Proof, C_002_HilbertKernel_R.Prf pf phi.


  (*************************************************************************)
  (*                                                                       *)
  (*  This lemma allows us to prove 'Prov phi' by simply running the       *)
  (*  kernel checker. If 'check pf phi' returns true, we immediately       *)
  (*  have a witness for 'Prov phi'.                                       *)
  (*                                                                       *)
  (*  Usage: [ apply Prov_from_check ] with [ pf := my_script ].           *)
  (*                                                                       *)
  (*************************************************************************)

  Lemma Prov_from_check :
    forall (pf : C_002_HilbertKernel_R.Proof) (phi : Form),
      C_002_HilbertKernel_R.check pf phi = true ->
      Prov phi.
  Proof.

  (*
    Construct the existential witness
  *)

    intros pf phi Hc.
    exists pf.

    (*
      Use the kernel's internal soundness theorem
    *)

    apply C_002_HilbertKernel_R.check_sound. exact Hc.
  Qed.

End C_002_Provability_S.

Export C_002_Provability_S.
