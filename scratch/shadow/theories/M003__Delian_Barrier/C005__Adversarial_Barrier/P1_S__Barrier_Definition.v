(* P1_S__Barrier_Definition.v *)

(*************************************************************************)
(*                                                                       *)
(*  C005 / Phase 1 (S): Barrier Vocabulary & The Separator               *)
(*                                                                       *)
(*  What This File Provides                                              *)
(*                                                                       *)
(*     (i) The Semantic Context (A, B, Truth).                           *)
(*                                                                       *)
(*          Two classes of sentences indexed by ℕ:                       *)
(*                                                                       *)
(*            A, B : ℕ → Form                                            *)
(*            Truth : Form → Prop                                        *)
(*                                                                       *)
(*          Crucially, "Truth" is kept abstract. We only require that    *)
(*          reality is consistent (Semantic Disjointness):               *)
(*                                                                       *)
(*            ∀n. Truth(A(n)) ∧ Truth(B(n)) → ⊥                          *)
(*                                                                       *)
(*    (ii) The Target Device: SEPARATOR.                                 *)
(*                                                                       *)
(*          This is the object we will prove impossible.                 *)
(*          It consists of:                                              *)
(*                                                                       *)
(*          (a) An effective decision function σ : ℕ → bool.             *)
(*          (b) An internal certificate proving the decision is          *)
(*              formally justifiable:                                    *)
(*                                                                       *)
(*                σ(n) = true  → Prov(A(n))                              *)
(*                σ(n) = false → Prov(B(n))                              *)
(*                                                                       *)
(*   (iii) The Adversarial Mechanism: "Flip Logic."                      *)
(*                                                                       *)
(*          A function that observes the separator and intentionally     *)
(*          outputs the code for the *opposite* class:                   *)
(*                                                                       *)
(*            Flip(S, n) ≜ if σ(n) then B(n) else A(n)                   *)
(*                                                                       *)
(*          This creates the impredicative leak that drives the barrier. *)
(*                                                                       *)
(*   “Device-First Architecture”.                                        *)
(*                                                                       *)
(*      Solvability is a concrete Record (SEPARATOR), not an abstract    *)
(*      existential predicate (∃x. ...).                                 *)
(*                                                                       *)
(*      This allows the Flip Logic to "run" the separator and observe    *)
(*      its output, creating the diagonal construction.                  *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.
From ATP.C002 Require Import P5_T__Proof_Theory.

Set Implicit Arguments.
Unset Strict Implicit.

Module Type C005_Barrier_Ctx.
  Module N := ATP.C002.P5_T__Proof_Theory.Prelude.
  Module P := ATP.C002.P5_T__Proof_Theory.ATP.

  Parameter A : N.nat -> P.ATP_Form.
  Parameter B : N.nat -> P.ATP_Form.
  Parameter Truth : P.ATP_Form -> Prop.
End C005_Barrier_Ctx.

Module C005_Barrier_Def_F (Ctx : C005_Barrier_Ctx).

  Module N := ATP.C002.P5_T__Proof_Theory.Prelude.
  Module P := ATP.C002.P5_T__Proof_Theory.ATP.

  Definition A : N.nat -> P.ATP_Form := Ctx.A.
  Definition B : N.nat -> P.ATP_Form := Ctx.B.
  Definition Truth : P.ATP_Form -> Prop := Ctx.Truth.

  (*
    Semantic Disjointness — Reality is Consistent

    The two classes A and B are semantically disjoint:

      ∀n. Truth(A(n)) ∧ Truth(B(n)) → ⊥

    This is the only requirement on the semantic model.
  *)

  Definition Semantic_Disjointness : Prop :=
    forall n : N.nat, Truth (A n) -> Truth (B n) -> False.

  (*
    The SEPARATOR — Certified Decision Device

    A separator is a total decision procedure with proof certificates:

      SOLVING (extensional):  σ : ℕ → bool
      PROVING (intensional):  σ(n) = true  → Prov(A(n))
                              σ(n) = false → Prov(B(n))

    This device will be proven impossible via the Adversarial Barrier.
  *)

  Record SEPARATOR : Type := {
    (* Extensional decision function *)
    sigma : N.nat -> N.bool;

    (* Intensional certificate *)
    cert : forall n : N.nat,
      if sigma n
      then P.ATP_Prov (A n)
      else P.ATP_Prov (B n)
  }.

  (*
    Flip Logic — The Adversarial Mechanism

    Observes the separator's decision and returns the opposite class:

      Flip(S, n) ≜ { B(n)  if σ(n) = true
                   { A(n)  if σ(n) = false

    This creates the impredicative loop:
      - S tries to separate A from B
      - Flip(S) outputs whichever class S rejects
      - This forces a contradiction via the Mirror Lemma
  *)

  Definition Flip_Logic (S : SEPARATOR) (n : N.nat) : P.ATP_Form :=
    if S.(sigma) n then B n else A n.

End C005_Barrier_Def_F.

(*
  Main Exported Module — Standalone Barrier Definition

  This module provides the barrier vocabulary without requiring
  a functor instantiation.
*)

Module C005_Barrier_Def_S.

  Module N := ATP.C002.P5_T__Proof_Theory.Prelude.
  Module P := ATP.C002.P5_T__Proof_Theory.ATP.

  (*
    Semantic Context — Two Disjoint Classes

    A, B : ℕ → Form  (indexed sentence classes)
  *)

  Parameter A : N.nat -> P.ATP_Form.
  Parameter B : N.nat -> P.ATP_Form.

  (*
    Truth — Semantic Bridge

    Truth : Form → Prop

    The semantic model for the logic. Kept abstract to ensure
    generality of the barrier construction.
  *)

  Parameter Truth : P.ATP_Form -> Prop.

  (*
    Semantic Disjointness — Reality is Consistent

    ∀n. Truth(A(n)) ∧ Truth(B(n)) → ⊥

    The classes are semantically disjoint: at most one can be true.
  *)

  Definition Semantic_Disjointness : Prop :=
    forall n : N.nat, Truth (A n) -> Truth (B n) -> False.

  (*
    The SEPARATOR — Certified Decision Device

    A separator combines:

      SOLVING:  σ : ℕ → bool        (extensional decision)
      PROVING:  Certificate mapping  (intensional justification)

    For each n ∈ ℕ:

      σ(n) = true  → Prov(A(n))
      σ(n) = false → Prov(B(n))

    This device will be proven impossible via adversarial argument.
  *)

  Record SEPARATOR : Type := {

    (*
      Extensional Decision Function

      σ : ℕ → bool

      Total, effective, computable decision.
    *)

    sigma : N.nat -> N.bool;

    (*
      Intensional Certificate

      For each index n, provides a proof of the chosen class.
    *)

    cert : forall n : N.nat,
      if sigma n
      then P.ATP_Prov (A n)
      else P.ATP_Prov (B n)
  }.

  (*
    Flip Logic — The Adversarial Mechanism

    Flip(S, n) ≜ { B(n)  if σ(n) = true
                 { A(n)  if σ(n) = false

    The impredicative leak:
      - S certifies one class
      - Flip returns the opposite class
      - When Flip is applied to its own encoding, contradiction ensues
  *)

  Definition Flip_Logic (S : SEPARATOR) (n : N.nat) : P.ATP_Form :=
    if S.(sigma) n then B n else A n.

End C005_Barrier_Def_S.

Export C005_Barrier_Def_S.
