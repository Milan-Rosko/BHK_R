(* P5_T__Diagonal.v *)

From Coq Require Import Init.Logic.
From Diagonallemma.C003 Require Export P1_S__Syntax.
From Diagonallemma.C003 Require Import P2_R__Backend.
From Diagonallemma.C003 Require Import P2_R__Compiler.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C003 / Phase 5 (T): Public surface for the diagonal operator.        *)
(*                                                                       *)
(*  Guard: do not import any A/TA module here.                           *)
(*  We don't need to introduce this “Lemma.”                             *)
(*                                                                       *)
(*************************************************************************)

Module Diagonal := C003_Compiler_R.D.

(* Stable re-exports: syntax, encoding, compilation interface, diag. *)
Definition CExp : Type := Diagonal.CExp.
Definition Template : Type := Diagonal.Template.

Definition eval : CExp -> C003_Backend_Carryless.nat -> C003_Backend_Carryless.nat :=
  Diagonal.eval.

Definition subst0 : Template -> C003_Backend_Carryless.nat -> Template :=
  Diagonal.subst0.

Definition encE : CExp -> C003_Backend_Carryless.nat := Diagonal.encE.
Definition encU : Template -> C003_Backend_Carryless.nat := Diagonal.encU.

Definition COMPILED (t : Template) : Type := Diagonal.COMPILED t.

Definition compile_delta (t : Template) : COMPILED t :=
  C003_Compiler_R.compile_delta t.

Definition diag (t : Template) (c : COMPILED t) : Template :=
  Diagonal.diag (t := t) c.

Theorem diag_spec_code :
  forall (t : Template) (c : COMPILED t),
    encU (diag (t := t) c)
    =
    eval (Diagonal.E_t c) (Diagonal.selfpack (encU (Diagonal.delta_t c))).
Proof.
  exact Diagonal.diag_spec_code.
Qed.

(*************************************************************************)
(*                                                                       *)
(*  Interlude. Where did the Incompleteness go?                          *)
(*                                                                       *)
(*  It retreated to the only place left to hide:                         *)
(*  ”The Carryless Pairing” inversion law is computationally effective   *)
(*  YET not provable in this minimal core.                               *)
(*                                                                       *)
(*  Crucially, we do not need to introduce this “Lemma” (Reflexica)      *)
(*  for the computation to work. The incompleteness is isolated          *)
(*  in the gap between the R-layer (realization) and the certificate.    *)
(*                                                                       *)
(*   This shall lead us to the next chapter: The Mirror Lemma.           *)
(*                                                                       *)
(*************************************************************************)