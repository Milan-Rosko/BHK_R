(* P0__BHK.v *)

     (*_  /\/\/\/\/\__  /\/\__  /\/\_  /\/\___  /\/\__________  /\/\/\/\/\____*)
    (*_  /\/\__  /\/\  /\/\__  /\/\_  /\/\__ /\/\____________  /\/\__  /\/\__ *)
   (*_  /\/\/\/\/\__  /\/\/\/\/\/\_  /\/\/\/\ ______________  /\/\/\/\/\ ___  *)
  (*_  /\/\__  /\/\  /\/\__  /\/\_  /\/\_  /\/\____________  /\/\  /\/\____   *)
 (*_  /\/\/\/\/\__  /\/\__  /\/\_  /\/\___  /\/\__________  /\/\__  /\/\__    *)
(*______________________________________________  /\/\/\/\_______________     *)
(*                                                                            *)
(*     This defines the “BHK meaning nucleus” shared by all later phase.      *)
(*     The methodology is repository-wide and project-agnostic.               *)
(*                                                                            *)
(*        (i) A proposition is identified with the type of its proof.         *)
(*                                                                            *)
(*       (ii) To prove a proposition is to construct an inhabitant            *)
(*            of that type.                                                   *)
(*                                                                            *)
(*      (iii) Logical connectives and quantifiers are understood via          *)
(*            their introduction forms and corresponding proof objects;       *)
(*            functions, dependent pairs, tagged alternatives, etc.           *)
(*                                                                            *)
(*      In particular, equalities proved below are witnessed                  *)
(*      by computation (definitional equality), not by appeal to              *)
(*      extensional principles or additional axioms. The emphasis is on       *)
(*      explicit constructions whose meaning is stable under reduction.       *)
(*                                                                            *)
(*      BHK remains the informal proof-theoretic semantics, whereas           *)
(*      BHK_R denotes an additional discipline:                               *)
(*                                                                            *)
(*        (i) A minimal inductive core,                                       *)
(*                                                                            *)
(*       (ii) Explicit primitive recursion,                                   *)
(*                                                                            *)
(*      (iii) A fixed phase structure.                                        *)
(*                                                                            *)
(*      The preferred notion of reasoning is kernel conversion:               *)
(*      definitional equality via β, ι, ζ, and transparent δ, together        *)
(*      with explicit recursion on inductive data. Many foundational          *)
(*      equations are therefore stated in conversion-friendly normal          *)
(*      forms and discharged by simplification to eq_refl.                    *)
(*                                                                            *)
(*      Phase structure.                                                      *)
(*                                                                            *)
(*        (i) A construction is the first-class organizing principle          *)
(*            (hence folders start with 'C').                                 *)
(*                                                                            *)
(*       (ii) For each phase,                                                 *)
(*                                                                            *)
(*            (a) Realizations ('R') provide concrete constructions           *)
(*                (Fixpoint/Definition plus explicit proof terms);            *)
(*            (b) BHK proof semantics ('S') package realizations              *)
(*                behind minimal interfaces (typically small records)         *)
(*                and establish interoperability results (translations,       *)
(*                simulations, or extensional agreement on functions);        *)
(*            (c) Theorems ('T') serve as entry/exit points: lemmas and       *)
(*                theorems intended for downstream use.                       *)
(*            (d) Certificates ('A') form a recursive loop.                   *)
(*                                                                            *)
(*      Design.                                                               *)
(*                                                                            *)
(*        (i) No classical axioms (LEM, Compactness) at this level.           *)
(*                                                                            *)
(*       (ii) Avoid large numeric towers and heavyweight libraries.           *)
(*                                                                            *)
(*      (iii) Prefer small “façades” (records/modules) over large             *)
(*            signatures to reduce coupling between realizations and          *)
(*            keep computation explicit, sequential, and intensional.         *)
(*                                                                            *)
(*      In short. We establish meaning once (Phase 0); realize it explicitly  *)
(*      (R files); then relate realizations conservatively (S files),         *)
(*      yielding either a new phase, an export, or both.                      *)
(*                                                                            *)
(*                                                   (c) www.milanrosko.com   *)
(*                                                                            *)
(******************************************************************************)

From Coq Require Import Init.Logic.

Set Implicit Arguments.
Unset Strict Implicit.

Module BHK.

  (*************************************************************************)
  (*                                                                       *)
  (*    We define the Canonical BHK Clauses.                               *)
  (*                                                                       *)
  (*    We map “Rocq types“ to their Constructive Logic interpretation     *)
  (*    and their corresponding computational witnesses.                   *)
  (*                                                                       *)
  (*    Rocq Type              BHK Interpretation     Realizer Structure   *)
  (*    ------------------     ------------------     ------------------   *)
  (*    False                  ∸ (Absurd)             (none)               *)
  (*    and P Q                P ∧ Q                  ⟨p, q⟩               *)
  (*    or  P Q                P ∨ Q                  inl p  |  inr q      *)
  (*    P -> Q                 P → Q                  λx. body             *)
  (*    exists (fun x => P)    ∃x. P(x)               ⟨x, p⟩               *)
  (*    forall (x:A), P        ∀x. P(x)               λx. body             *)
  (*                                                                       *)
  (*    If we have...          we construct by...     to realize...        *)
  (*    ------------------     ------------------     ------------------   *)
  (*    p ⊨ P, q ⊨ Q           conj p q               P ∧ Q                *)
  (*    p ⊨ P                  or_introl p            P ∨ Q                *)
  (*    q ⊨ Q                  or_intror q            P ∨ Q                *)
  (*    x ↦ y where y ⊨ Q      fun x => y             P → Q                *)
  (*    x : A, p ⊨ P(x)        ex_intro x p           ∃x. P(x)             *)
  (*    x ↦ y where y ⊨ P x    fun x => y             ∀x. P(x)             *)
  (*                                                                       *)
  (*               cf. A. S. Troelstra and D. van Dalen:                   *)
  (*                  Constructivism in Mathematics                        *)
  (*                                                                       *)
  (*************************************************************************)


  (*
    A minimal Arithmetic Kernel (nat) with explicit primitive recursion
    This is intentionally not Coq.Init.Datatypes.nat. BHK reading:

      (i) The inductive type nat is a canonical constructive object,

     (ii) O and S are constructors giving the canonical proofs,

    (iii) Induction / recursion corresponds to case analysis on proofs.

    The “goal” is to keep the computational behavior fully transparent
    and independent of any larger library abstractions.
  *)

  Inductive nat : Type :=
    | O : nat
    | S : nat -> nat.

  (*************************************************************************)
  (*                                                                       *)
  (*  Primitive recursive definitions                                      *)
  (*                                                                       *)
  (*     (i) add and mul are not axiomatic relations but algorithms.       *)
  (*    (ii) To know add m n is to be able to compute it by reducing m.    *)
  (*   (iii) These definitions serve as witnesses of existence claims      *)
  (*         about sums and products.                                      *)
  (*                                                                       *)
  (*************************************************************************)

  Fixpoint add (m n : nat) : nat :=
    match m with
    | O => n
    | S m' => S (add m' n)
    end.

  Fixpoint mul (m n : nat) : nat :=
    match m with
    | O => O
    | S m' => add n (mul m' n)
    end.

  (*************************************************************************)
  (*                                                                       *)
  (*     (i) Each theorem below asserts an equality whose proof is         *)
  (*         computationally trivial.                                      *)
  (*    (ii) The proof object is eq_refl, witnessing that both sides       *)
  (*         reduce to the same normal form.                               *)
  (*                                                                       *)
  (*************************************************************************)

  Theorem add_O_l : forall n, add O n = n.
  Proof.
    intro n; simpl; exact (eq_refl _).
  Qed.

  (*************************************************************************)
  (*                                                                       *)
  (*  add (S m) n computes by one step of successor introduction.          *)
  (*  Under BHK, this expresses how a proof of add (S m) n is constructed  *)
  (*  from a proof of add m n.                                             *)
  (*                                                                       *)
  (*************************************************************************)

  Theorem add_S_l : forall m n, add (S m) n = S (add m n).
  Proof.
    intro m; intro n; simpl; exact (eq_refl _).
  Qed.

  (*************************************************************************)
  (*                                                                       *)
  (*  Multiplication with zero reduces immediately.                        *)
  (*  This corresponds to the canonical computation witnessing that        *)
  (*  zero times any number is zero.                                       *)
  (*                                                                       *)
  (*************************************************************************)

  Theorem mul_O_l : forall n, mul O n = O.
  Proof.
    intro n; simpl; exact (eq_refl _).
  Qed.

  (*************************************************************************)
  (*                                                                       *)
  (*  Successor case for multiplication.                                   *)
  (*  The equation expresses the recursive construction of a product:      *)
  (*  (S m) * n is witnessed by n + (m * n).                               *)
  (*                                                                       *)
  (*************************************************************************)

  Theorem mul_S_l : forall m n, mul (S m) n = add n (mul m n).
  Proof.
    intro m; intro n; simpl; exact (eq_refl _).
  Qed.

End BHK.
