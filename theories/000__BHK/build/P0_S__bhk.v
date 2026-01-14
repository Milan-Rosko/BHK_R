(* P0_S__bhk.v *)
From Coq Require Import Init.Logic.

(*************************************************************************)
(*                                                                       *)
(* proofcase / Phase-0 BHK core v0.1                                     *)
(*                                                                       *)
(* This file is the “meaning nucleus” shared by all later phases.        *)
(*                                                                       *)
(* Methodology (repository-wide, project-agnostic).                      *)
(*                                                                       *)
(* 1. Constructive/BHK discipline.                                       *)
(*    We work in a small constructive core. Propositions are read        *)
(*    BHK-style: to prove P is to construct an inhabitant of P, and      *)
(*    the meaning of connectives is given by introduction forms          *)
(*    (functions, pairs, tagged alternatives, dependent pairs, etc.).    *)
(*                                                                       *)
(* 2. Computation as the proof engine.                                   *)
(*    The preferred notion of “reasoning” is kernel conversion:          *)
(*    definitional equality via β, ι, ζ, and transparent δ, together     *)
(*    with explicit recursion on inductive data. Many foundational       *)
(*    equations are therefore stated in conversion-friendly normal       *)
(*    forms and discharged by simplification to eq_refl.                 *)
(*                                                                       *)
(* 3. Phase structure: S vs R files.                                     *)
(*    - Phase 0 (this file, P0_S__...) fixes shared data, recursion,     *)
(*      and conversion laws that later developments rely on. It is       *)
(*      intentionally small and import-friendly.                         *)
(*    - For each later phase n ≥ 1:                                      *)
(*        * Realizations (Pn_R__...) provide concrete constructions      *)
(*          (Fixpoint/Definition + explicit proof terms).                *)
(*        * The semantics/interaction layer (Pn_S__...) packages         *)
(*          realizations behind minimal interfaces (typically small      *)
(*          records) and proves interoperability results between them    *)
(*          (translations, simulations, extensional agreement on         *)
(*          observable functions).                                       *)
(*                                                                       *)
(* 4. Design constraints.                                                *)
(*    - No classical axioms at the top level.                            *)
(*    - Avoid large numeric towers and heavyweight libraries unless a    *)
(*      subproject explicitly opts in.                                   *)
(*    - Prefer small “façades” (records/modules) over large signatures   *)
(*      to reduce coupling between realizations and keep computation     *)
(*      explicit and predictable.                                        *)
(*                                                                       *)
(* In short: establish meaning once (Phase 0), realize it explicitly     *)
(* (R files), then relate realizations conservatively (S files).         *)
(*                                                                       *)
(*************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.

Module BHK.

  (***********************************************************************)
  (*                                                                     *)
  (* A minimal Peano nat and explicit primitive recursion                *)
  (*                                                                     *)
  (* This is intentionally not Coq.Init.Datatypes.nat: we want a small   *)
  (* stable kernel-computational object whose definitional equalities    *)
  (* are predictable across the repository.                              *)
  (*                                                                     *)
  (***********************************************************************)

  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

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

  (***********************************************************************)
  (*                                                                     *)
  (* Conversion-friendly computation laws                                *)
  (*                                                                     *)
  (* These are stated so that later developments can rewrite using       *)
  (* small lemmas whose proofs are pure computation (simpl; eq_refl).    *)
  (*                                                                     *)
  (***********************************************************************)

  Theorem add_O_l : forall n, add O n = n.
  Proof. intro n; simpl; exact (eq_refl _). Qed.

  Theorem add_S_l : forall m n, add (S m) n = S (add m n).
  Proof. intro m; intro n; simpl; exact (eq_refl _). Qed.

  Theorem mul_O_l : forall n, mul O n = O.
  Proof. intro n; simpl; exact (eq_refl _). Qed.

  Theorem mul_S_l : forall m n, mul (S m) n = add n (mul m n).
  Proof. intro m; intro n; simpl; exact (eq_refl _). Qed.

End BHK.

Export BHK.
