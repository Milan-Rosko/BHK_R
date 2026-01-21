(* P1_S__Barrier_Definition.v *)

(*************************************************************************)
(*                                                                       *)
(*  C_005 / Phase 1 (S): Barrier Vocabulary & The Separator              *)
(*                                                                       *)
(*  What this file provides.                                             *)
(*                                                                       *)
(*    (i) The Semantic Context (A, B, Truth).                            *)
(*        We postulate two classes of sentences indexed by nat.          *)
(*        Crucially, "Truth" is kept abstract: we only require that      *)
(*        Reality is Consistent (Semantic_Disjointness).                 *)
(*                                                                       *)
(*   (ii) The Target Device: The SEPARATOR.                              *)
(*        This is the object we will prove impossible.                   *)
(*        It consists of:                                                *)
(*                                                                       *)
(*        (a) An effective decision function (sigma : nat -> bool).      *)
(*        (b) An internal certificate (cert) proving the decision        *)
(*            is formally justifiable (Prov (A n) or Prov (B n)).        *)
(*                                                                       *)
(*  (iii) The Adversarial Mechanism: "Flip Logic".                       *)
(*        We define a function that observes the Separator and           *)
(*        intentionally outputs the code for the *opposite* class.       *)
(*        This creates the impredicative leak.                           *)
(*                                                                       *)
(*   Design Discipline.                                                  *)
(*                                                                       *)
(*   Device-First: Solvability is a concrete Record (SEPARATOR),         *)
(*   not an abstract predicate exists x, ...                             *)
(*   This allows the Flip Logic to "run" the separator.                  *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.
From ATP.C002 Require Import P5_T__Proof_Theory.

Set Implicit Arguments.
Unset Strict Implicit.

Module C005_Barrier_Def_S.

  Module N := ATP.C002.P5_T__Proof_Theory.Prelude.
  Module P := ATP.C002.P5_T__Proof_Theory.ATP.

  (***********************************************************************)
  (* Context: Uniform Semantic Classes                                   *)
  (***********************************************************************)

  Parameter A : N.nat -> P.ATP_Form.
  Parameter B : N.nat -> P.ATP_Form.

  (* Truth is the semantic bridge (Model) for the logic. *)
  Parameter Truth : P.ATP_Form -> Prop.

  (* The classes are semantically disjoint: reality is consistent. *)
  Definition Semantic_Disjointness : Prop :=
    forall n : N.nat, Truth (A n) -> Truth (B n) -> False.

  (***********************************************************************)
  (* The Separator Interface                                             *)
  (***********************************************************************)

  Record SEPARATOR : Type := {
    (* SOLVING: extensional total decision *)
    sigma : N.nat -> N.bool;
    (* PROVING: intensional certificates *)
    cert : forall n : N.nat,
      if sigma n
      then P.ATP_Prov (A n)
      else P.ATP_Prov (B n)
  }.

  (***********************************************************************)
  (* The Impredicativity Leak (“Flip Logic”)                             *)
  (***********************************************************************)
  
  Definition Flip_Logic (S : SEPARATOR) (n : N.nat) : P.ATP_Form :=
    if S.(sigma) n then B n else A n.

End C005_Barrier_Def_S.

Export C005_Barrier_Def_S.
