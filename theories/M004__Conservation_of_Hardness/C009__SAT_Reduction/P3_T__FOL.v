(* P3_T__FOL.v *)

(*************************************************************************)
(*                                                                       *)
(*  C009 / Phase 3 (T): First-Order Logic (Public Surface)               *)
(*                                                                       *)
(*    (i) Scope.                                                         *)
(*                                                                       *)
(*        Stable public API for the First-Order Logic layer.             *)
(*        Aggregates syntax (P1_S__Syntax), substitution                 *)
(*        (P2_R__Substitution), and kernel (P3_R__Kernel) into a         *)
(*        unified interface.                                             *)
(*                                                                       *)
(*   (ii) Design Discipline: Witness-First Provability.                  *)
(*                                                                       *)
(*        The Prov predicate is defined via witnesses:                   *)
(*                                                                       *)
(*          Prov(φ) ≜ ∃pf : Proof. check pf φ = true                     *)
(*                                                                       *)
(*        This aligns with the BHK_R methodology: to prove φ is to       *)
(*        construct a checkable proof script pf.                         *)
(*                                                                       *)
(*  (iii) Public Exports.                                                *)
(*                                                                       *)
(*        (a) Syntax: Form, Term, Var, constructors (Bot, Imp, Eq, ...). *)
(*        (b) Provability: Prov predicate, Prov_from_check bridge.       *)
(*        (c) Kernel: Exposed for effectivity testing (vm_compute).      *)
(*                                                                       *)
(*   (iv) Role in C009.                                                  *)
(*                                                                       *)
(*        (a) Kernel sanity tests (P4_T__Kernel_Sanity)                  *)
(*        (b) Potential future extensions (arithmetic, DPRM)             *)
(*                                                                       *)
(*        NOT used for the SAT reduction itself (which uses ATP_Form).   *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.
From SAT.C009 Require Export P1_S__Syntax.
From SAT.C009 Require Export P2_R__Substitution.
From SAT.C009 Require Export P3_R__Kernel.

Set Implicit Arguments.
Unset Strict Implicit.

Module C009_FOL_Public.

  (*
    Re-export the Arithmetic Nucleus

    Provides access to the BHK_R foundation (nat, O, S, etc.).
  *)

  Module Prelude := BHK_R.C000.P0__BHK.BHK.

  (*
    Syntax — Stable Names for FOL Constructs

    Exposes the syntax module and provides convenient aliases.
  *)

  Module Syntax := C009_FOL_Syntax.

  Definition Form := Syntax.Form.
  Definition Term := Syntax.Term.
  Definition Var  := Syntax.Var.

  (*
    Formula Constructors

    These are the primitive building blocks of FOL formulas.
  *)

  Definition Bot := Syntax.Bot.
  Definition Imp := Syntax.Imp.
  Definition Eq  := Syntax.Eq.
  Definition All := Syntax.All.
  Definition Ex  := Syntax.Ex.
  Definition Not := Syntax.Not.

  (*
    The Provability Predicate

    Type. Form → Prop

    Definition.

      Prov(φ) ≜ ∃pf : Proof. check pf φ = true

    Meaning.

      φ is provable iff there exists a proof script pf that
      validates φ under the kernel checker.

    Design Note:

      This is the witness-first discipline from C002:

         (i) Provability is inhabited by explicit proof artifacts.

        (ii) No abstract derivation trees or axiom schemes.

       (iii) Proof validity is computational (check : Proof → Form → bool).

    Contrast with Abstract Provability:

      In a typical Hilbert-style system, Prov would be an
      inductive type with constructors for axioms and rules.
      Here, we collapse that to a checker function, making
      provability a computational property.
  *)

  Definition Prov (phi : Form) : Prop :=
    exists (pf : C009_FOL_Kernel_R.Proof), C009_FOL_Kernel_R.check pf phi = true.

  (*
    Prov_from_check — Soundness Bridge

    Type: ∀pf φ. check pf φ = true → Prov φ

    Allows users to construct Prov witnesses by computation:
         (i) Build a proof script pf.
        (ii) Run vm_compute to verify check pf φ = true.
       (iii) Apply Prov_from_check to get Prov φ.

    This makes proof construction effective: write the proof,
    validate it computationally, then lift to Prop.
  *)

  Theorem Prov_from_check : forall (pf : C009_FOL_Kernel_R.Proof) (phi : Form),
    C009_FOL_Kernel_R.check pf phi = true -> Prov phi.
  Proof.
    intros pf phi H. exists pf. exact H.
  Qed.

  (*
    Exposes the kernel module directly for regression testing
    and effectivity witnesses (see P4_T__Kernel_Sanity).

    Users can access:
         (i) Kernel.Proof (the proof type)
        (ii) Kernel.check (the checker function)
       (iii) Kernel-specific lemmas (form_eqb_refl, etc.)
  *)

  Module Kernel := C009_FOL_Kernel_R.

End C009_FOL_Public.

Export C009_FOL_Public.

(*
  We export the kernel so effectivity tests can access check directly.
  This is intentional: the kernel is part of the public API for
  computational proof validation.
*)

Export C009_FOL_Kernel_R.

(*************************************************************************)
(*                                                                       *)
(*  Architectural Note: Three-Layer FOL Structure                        *)
(*                                                                       *)
(*    “P1_S__Syntax”                                                     *)
(*    Defines Form, Term, Var (syntax types).                            *)
(*                                                                       *)
(*    “P2_R__Substitution”                                               *)
(*    Defines subst (capture-avoiding substitution).                     *)
(*                                                                       *)
(*    “P3_R__Kernel”                                                     *)
(*    Defines Proof and check (proof validation).                        *)
(*                                                                       *)
(*    “P3_T__FOL” (this file):                                           *)
(*    Aggregates all three layers into a stable public API.              *)
(*    Defines Prov predicate via witness-first discipline.               *)
(*                                                                       *)
(*    Each layer is minimal and focused. The T-layer (public surface)    *)
(*    packages them into a coherent interface without adding new         *)
(*    computational content.                                             *)
(*                                                                       *)
(*************************************************************************)
