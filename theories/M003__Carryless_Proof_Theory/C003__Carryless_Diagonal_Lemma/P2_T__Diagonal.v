(* P2_T__Diagonal.v *)

From Coq Require Import Init.Logic.
From C003 Require Export P1_S__Syntax.
From C003 Require Import P2_R__Backend.
From C003 Require Import P2_R__Compiler.

(*************************************************************************)
(*                                                                       *)
(*  C003 / Phase 5 (T): Public surface for the diagonal operator.        *)
(*                                                                       *)
(*  Guard: do not import any A/TA module here.                           *)
(*                                                                       *)
(*************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.

(*
  Parametric Functor Construction

  We use C003_P1.BACKEND directly to ensure we get the Module Type,
  avoiding any ambiguity if BACKEND is defined elsewhere.
*)

Module Diagonal_Functor (B : C003_P1.BACKEND).

  (*
    Instantiate the compiler with the provided abstract backend B.
  *)

  Module Compiler := C003_Compiler_R.Make(B).
  Module D := Compiler.D.

  (*
    Stable re-exports: syntax, encoding, compilation interface, diag.
  *)

  Definition CExp : Type := D.CExp.
  Definition Template : Type := D.Template.

  (*
    Use B.nat (abstract) instead of a concrete nat
  *)

  Definition eval : CExp -> B.nat -> B.nat := D.eval.

  Definition subst0 : Template -> B.nat -> Template := D.subst0.

  Definition encE : CExp -> B.nat := D.encE.
  Definition encU : Template -> B.nat := D.encU.

  Definition COMPILED (t : Template) : Type := D.COMPILED t.

  (*
    Public wrappers for internal projections.
  *)

  Definition delta_t {t : Template} (c : COMPILED t) : Template := D.delta_t c.
  Definition E_t     {t : Template} (c : COMPILED t) : CExp     := D.E_t c.
  Definition selfpack (n : B.nat) : B.nat := D.selfpack n.

  Definition compile_delta (t : Template) : COMPILED t :=
    Compiler.compile_delta t.

  Definition diag (t : Template) (c : COMPILED t) : Template :=
    D.diag (t := t) c.

  (*
    The Main Diagonal Specification (Code-Level)

    For any template t with compilation c = compile_δ(t):

      ⌈diag(t)⌉ = ⟦Eₜ⟧(selfpack(⌈δₜ⌉))

    This is the Quinean knot: the encoding of the diagonal equals
    the evaluation of Eₜ on the self-packed code of δₜ.
  *)

  Theorem diag_spec_code :
    forall (t : Template) (c : COMPILED t),
      encU (diag (t := t) c)
      =
      eval (E_t c) (selfpack (encU (delta_t c))).
  Proof.
    intros t c.
    unfold E_t, selfpack, delta_t.
    exact (@D.diag_spec_code t c).
  Qed.

End Diagonal_Functor.

(*
  Default Instantiation — Carryless Backend

  This instantiates the Diagonal_Functor with C003_Backend_Carryless,
  preserving the original public API while keeping the functor available
  for parametric uses.
*)

Module Diagonal := Diagonal_Functor(C003_Backend_Carryless).

(*
  Stable re-exports: syntax, encoding, compilation interface, diag.
*)

Definition CExp : Type := Diagonal.CExp.
Definition Template : Type := Diagonal.Template.

Definition eval :
  CExp -> C003_Backend_Carryless.nat -> C003_Backend_Carryless.nat :=
  Diagonal.eval.

Definition subst0 :
  Template -> C003_Backend_Carryless.nat -> Template :=
  Diagonal.subst0.

Definition encE : CExp -> C003_Backend_Carryless.nat := Diagonal.encE.
Definition encU : Template -> C003_Backend_Carryless.nat := Diagonal.encU.

Definition COMPILED (t : Template) : Type := Diagonal.COMPILED t.

Definition compile_delta (t : Template) : COMPILED t :=
  Diagonal.compile_delta t.

Definition diag (t : Template) (c : COMPILED t) : Template :=
  Diagonal.diag (t := t) c.

(*
  Public Re-export of the Diagonal Specification
*)

Theorem diag_spec_code :
  forall (t : Template) (c : COMPILED t),
    encU (diag (t := t) c)
    =
    eval (Diagonal.E_t c) (Diagonal.selfpack (encU (Diagonal.delta_t c))).
Proof.
  exact Diagonal.diag_spec_code.
Qed.

(*
  “Where Did the Incompleteness Go?” (Part One)

  The diagonal construction is total and axiom-free.
  So where did Gödel's incompleteness hide?

  Answer: It retreated to the only place left to hide —
  the inversion law for Carryless Pairing.

  The pairing inversion is:

    (i)   Computationally trivial (effective, total, primitive recursive).
    (ii)  NOT provable in this minimal arithmetic core.

  Crucially, we do NOT need to introduce the inversion lemma (Reflexica)
  for the diagonal computation to work.

  The incompleteness is isolated in the gap between:

    R-layer (realization):  pair/unpair compute correctly
    A-layer (certificate):  inversion law is unprovable here

  This stratification leads us to the "Mirror Lemma" (C004).
*)

(*************************************************************************)
(*                                                                       *)
(*  Conjecture.                                                          *)
(*                                                                       *)
(*  No method of pairing can reduce its inversion law from Π₂            *)
(*  uniformity to a Σ₀ formula (bounded quantifiers only).               *)
(*                                                                       *)
(*************************************************************************)