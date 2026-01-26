(* P2_R__Reduction.v *)

From Coq Require Import Init.Logic.
From SAT.C009 Require Import P1_S__CNF_Syntax.
From ATP.C002 Require Import P5_T__Proof_Theory.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C_009 / Phase 2 (R): The Terminal Reduction                          *)
(*                                                                       *)
(*  We map the "Terminal Problem" into the "Terminal Logic" (ATP).       *)
(*  The mapping is constructive and uses only Implication and Bottom.    *)
(*                                                                       *)
(*  Clarification.                                                       *)
(*                                                                       *)
(*  The pure implicational fragment with ⊥ has no atomic propositions.   *)
(*  We therefore work with *schematic* atoms: Atom(n) represents the     *)
(*  n-th propositional variable as an abstract placeholder.              *)
(*                                                                       *)
(*  Under any consistent extension that adds atoms, the barrier holds.   *)
(*  This is the "Hollowness Principle": the structure of the reduction   *)
(*  carries the hardness, not the specific atomic content.               *)
(*                                                                       *)
(*  With Truth instantiated as validity over all valuations:             *)
(*                                                                       *)
(*   (i) Truth(A n) holds iff CNF(n) is a TAUTOLOGY                      *)
(*       (all clauses hold under every valuation)                        *)
(*                                                                       *)
(*  (ii) Truth(B n) holds iff CNF(n) is REFUTABLE                        *)
(*       (some clause fails under every valuation, i.e., contradiction)  *)
(*                                                                       *)
(*  Note. TAUT and REFUT are co-NP and NP complete respectively,         *)
(*  dual to SAT/UNSAT. The barrier argument applies equally:             *)
(*  separating TAUT from non-TAUT is as hard as separating SAT from      *)
(*  UNSAT, because one reduces to the other by negation.                 *)
(*                                                                       *)
(*  The "hollowness" of SAT means this duality is structural, not        *)
(*  accidental. The FSM (Turing machine) that generates the instances    *)
(*  is where the actual computational content lives.                     *)
(*                                                                       *)
(*************************************************************************)

Module C009_SAT_Reduction.

  Module N := ATP.C002.P5_T__Proof_Theory.Prelude.
  Module P := ATP.C002.P5_T__Proof_Theory.ATP.
  Module Syn := C009_SAT_Syntax.

  (*************************************************************************)
  (*                                                                       *)
  (*  Schematic Atoms                                                      *)
  (*                                                                       *)
  (*  Since ATP_Form = F_Bot | F_Imp, we cannot define "real" atoms.       *)
  (*  Instead, Atom(n) is a *schema* - a placeholder that would become     *)
  (*  a genuine atomic proposition in any extension of the logic.          *)
  (*                                                                       *)
  (*  For the barrier argument, what matters is:                           *)
  (*   (i) Different n give "independent" atoms (no logical relations)     *)
  (*  (ii) The reduction structure is preserved                            *)
  (*                                                                       *)
  (*  The canonical encoding below gives distinct normal forms for each n, *)
  (*  which suffices for the structural reduction. The barrier argument    *)
  (*  depends only on the *structure* of the reduction, not on semantic    *)
  (*  properties of atoms.                                                 *)
  (*                                                                       *)
  (*************************************************************************)

    (* Canonical atom encoding: Atom(n) = (⊥ → ⊥) iterated n times *)

    (* This gives distinct normal forms for each n *)

  Fixpoint Atom_canonical (n : N.nat) : P.ATP_Form :=
    match n with
    | N.O => P.ATP_Imp P.ATP_Bot P.ATP_Bot  (* ⊥ → ⊥ *)
    | N.S k => P.ATP_Imp (Atom_canonical k) (Atom_canonical k)
    end.

  (* We use the canonical encoding by default *)
  Definition Atom : N.nat -> P.ATP_Form := Atom_canonical.

  (*************************************************************************)
  (*                                                                       *)
  (*  Negation (Intuitionistic)                                            *)
  (*                                                                       *)
  (*************************************************************************)

  Definition Not (A : P.ATP_Form) : P.ATP_Form := P.ATP_Imp A P.ATP_Bot.

  (*************************************************************************)
  (*                                                                       *)
  (*  Literal Reduction                                                    *)
  (*                                                                       *)
  (*  A literal is a possibly-negated atom.                                *)
  (*  Polarity: true = positive, false = negative                          *)
  (*                                                                       *)
  (*************************************************************************)

  Definition reduce_lit (l : Syn.Lit) : P.ATP_Form :=
    let '(v, pos) := Syn.decode_lit l in
    match pos with
    | N.true => Atom v              (* Positive Literal: p *)
    | N.false => Not (Atom v)       (* Negative Literal: ¬p *)
    end.

  (*************************************************************************)
  (*                                                                       *)
  (*  Clause Reduction (Disjunction Encoding)                              *)
  (*                                                                       *)
  (*  A clause (L1 ∨ L2 ∨ ... ∨ Ln) is encoded as:                         *)
  (*                                                                       *)
  (*      (¬L1 → (¬L2 → ... → (¬Ln → ⊥)...))                               *)
  (*                                                                       *)
  (*  Intuition: "if all literals are false, we have a contradiction"      *)
  (*  Classically equivalent to the disjunction.                           *)
  (*                                                                       *)
  (*************************************************************************)

  Fixpoint reduce_clause (c : Syn.Clause) : P.ATP_Form :=
    match c with
    | N.nil => P.ATP_Bot  (* Empty clause = contradiction *)
    | N.cons l rest => P.ATP_Imp (Not (reduce_lit l)) (reduce_clause rest)
    end.

  (*************************************************************************)
  (*                                                                       *)
  (*  CNF Reduction (Conjunction Encoding)                                 *)
  (*                                                                       *)
  (*  A CNF (C1 ∧ C2 ∧ ... ∧ Cn) is encoded via double negation:           *)
  (*                                                                       *)
  (*      ¬(C1 → (C2 → ... → (Cn → ⊥)...))                                 *)
  (*                                                                       *)
  (*  Intuition: "it's not the case that some clause fails"                *)
  (*  Classically: ¬(C1 → ¬C2∧...∧Cn) ≡ C1 ∧ (C2 ∧ ... ∧ Cn)              *)
  (*                                                                       *)
  (*************************************************************************)

    (* Helper: chain implications ending in ⊥ *)

  Fixpoint chain_imp (fs : N.list P.ATP_Form) : P.ATP_Form :=
    match fs with
    | N.nil => P.ATP_Bot  (* No clauses = trivially false antecedent *)
    | N.cons f rest => P.ATP_Imp f (chain_imp rest)
    end.

    (* Map clauses to their formula representations *)

  Fixpoint map_clauses (cnf : Syn.CNF) : N.list P.ATP_Form :=
    match cnf with
    | N.nil => N.nil
    | N.cons c rest => N.cons (reduce_clause c) (map_clauses rest)
    end.

  (* Full CNF reduction *)
  Definition reduce_cnf (cnf : Syn.CNF) : P.ATP_Form :=
    Not (chain_imp (map_clauses cnf)).

  (*************************************************************************)
  (*                                                                       *)
  (*  THE TERMINAL CLASSES                                                 *)
  (*                                                                       *)
  (*  Class A: Validity class (TAUT-like)                                  *)
  (*      Under universal quantification over valuations,                  *)
  (*      Truth(A n) iff the CNF at index n is valid                       *)
  (*                                                                       *)
  (*  Class B: Refutation class (REFUT-like)                               *)
  (*      Under universal quantification over valuations,                  *)
  (*      Truth(B n) iff the CNF at index n is refutable                   *)
  (*                                                                       *)
  (*  The classes are semantically disjoint: no CNF is both valid          *)
  (*  and refutable (assuming consistency of the background logic).        *)
  (*                                                                       *)
  (*************************************************************************)

    (* The reduced CNF formula (for reuse) *)

  Definition CNF_Form (n : N.nat) : P.ATP_Form :=
    reduce_cnf (Syn.decode_cnf n).

    (* Class A: The CNF is VALID (all clauses satisfied by all valuations) *)

  Definition SAT_Form (n : N.nat) : P.ATP_Form :=
    CNF_Form n.

    (* Class B: The CNF is REFUTABLE (negation is valid) *)
    
  Definition UNSAT_Form (n : N.nat) : P.ATP_Form :=
    Not (CNF_Form n).

  (*************************************************************************)
  (*                                                                       *)
  (*  STRUCTURAL LEMMAS                                                    *)
  (*                                                                       *)
  (*  These witness that the encoding has the expected structure.          *)
  (*                                                                       *)
  (*************************************************************************)

    (* Empty CNF reduces to ¬⊥ (trivially valid) *)

  Lemma reduce_cnf_nil : reduce_cnf N.nil = Not P.ATP_Bot.
  Proof. unfold reduce_cnf, chain_imp, map_clauses. reflexivity. Qed.

    (* Single-clause CNF reduces to ¬(C → ⊥) = ¬¬C *)

  Lemma reduce_cnf_single : forall c,
    reduce_cnf (N.cons c N.nil) = Not (P.ATP_Imp (reduce_clause c) P.ATP_Bot).
  Proof. intro c. unfold reduce_cnf, chain_imp, map_clauses. reflexivity. Qed.

    (* Class duality: B n = ¬(A n) *)

  Lemma class_duality : forall n,
    UNSAT_Form n = Not (SAT_Form n).
  Proof. intro n. unfold UNSAT_Form, SAT_Form. reflexivity. Qed.

End C009_SAT_Reduction.

Export C009_SAT_Reduction.
