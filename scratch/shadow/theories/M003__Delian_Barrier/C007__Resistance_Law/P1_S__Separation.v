(* P1_S__Separation.v *)

From Coq Require Import Init.Logic.
From ATP.C002 Require Import P5_T__Proof_Theory.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C007 / Phase 1 (S): Separation Context                               *)
(*                                                                       *)
(*  What This File Provides                                              *)
(*                                                                       *)
(*    Minimal context for the Resistance Law (diagonal resistance).      *)
(*                                                                       *)
(*    (i)   Two semantic classes A, B : ℕ → Form                         *)
(*    (ii)  Semantic disjointness: Truth(A(n)) ∧ Truth(B(n)) → ⊥         *)
(*    (iii) SEPARATOR: certified decision device                         *)
(*    (iv)  Soundness: Prov(φ) → Truth(φ)                                *)
(*    (v)   Flip Logic: adversarial flip mechanism                       *)
(*                                                                       *)
(*  This is the same context as C005, re-exported for C007.              *)
(*                                                                       *)
(*************************************************************************)

Module C007_Separation_S.

  (*
    Import ATP kernel (Additive Hilbert System from C002).
  *)

  Module Prelude := ATP.C002.P5_T__Proof_Theory.Prelude.
  Module ATP := ATP.C002.P5_T__Proof_Theory.ATP.

  (*
    Type Exports

    nat  : ℕ (natural numbers)
    Form : Formula type
    Prov : Provability predicate
  *)

  Definition nat  : Type := Prelude.nat.
  Definition Form : Type := ATP.ATP_Form.
  Definition Prov : Form -> Prop := ATP.ATP_Prov.

  (*
    Semantic Classes

    A, B : ℕ → Form  (two classes of indexed sentences)
    Truth : Form → Prop  (semantic model)
  *)

  Parameter A : nat -> Form.
  Parameter B : nat -> Form.
  Parameter Truth : Form -> Prop.

  (*
    Semantic Disjointness — Reality is Consistent

    ∀n. Truth(A(n)) ∧ Truth(B(n)) → ⊥

    The two classes are semantically disjoint: at most one can be true.
  *)

  Definition Semantic_Disjointness : Prop :=
    forall n : nat, Truth (A n) -> Truth (B n) -> False.

  (*
    SEPARATOR — Certified Decision Device

    A separator is a total decision procedure σ : ℕ → bool with
    proof certificates:

      σ(n) = true  → Prov(A(n))
      σ(n) = false → Prov(B(n))

    This device will be proven impossible via the Resistance Law.
  *)

  Record SEPARATOR : Type := {
    sigma : nat -> Prelude.bool;
    cert : forall n : nat,
      if sigma n then Prov (A n) else Prov (B n)
  }.

  (*
    Soundness — Provability Implies Truth

    ∀φ. Prov(φ) → Truth(φ)

    The proof system is sound with respect to the semantic model.
  *)

  Definition Soundness : Prop :=
    forall phi : Form, Prov phi -> Truth phi.

  (*
    Flip Logic — The Adversarial Mechanism

    Flip(S, n) ≜ { B(n)  if σ(n) = true
                 { A(n)  if σ(n) = false

    Returns the opposite class from what the separator certifies.
  *)

  Definition Flip_Logic (S : SEPARATOR) (n : nat) : Form :=
    if S.(sigma) n then B n else A n.

End C007_Separation_S.

Export C007_Separation_S.
