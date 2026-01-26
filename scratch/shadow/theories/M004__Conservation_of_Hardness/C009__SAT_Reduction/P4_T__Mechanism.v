(* P4_T__Mechanism.v *)

From Coq Require Import Init.Logic.

From Diagonallemma.C003 Require Import P2_T__Diagonal.
From Diagonallemma.C003 Require Import P2_R__Backend.
From Carryless_Pairing.C001 Require Import P5_T__Carryless_Pairing.
From SAT.C009 Require Import P3_T__Structural_Integrity.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C009 / Phase 4 (T): The Diagonal Mechanism (Linker Implementation)   *)
(*                                                                       *)
(*    (i) Scope.                                                         *)
(*                                                                       *)
(*        Connects the abstract Diagonal Lemma (C003) with the concrete  *)
(*        arithmetic of Carryless Pairing (C001) to provide the          *)
(*        diagonal witness required by the SAT barrier.                  *)
(*                                                                       *)
(*   (ii) Key Insight.                                                   *)
(*                                                                       *)
(*        The diagonal construction is PARAMETRIC over the backend.      *)
(*        C003 provides the abstract self-reference mechanism, C001      *)
(*        provides the concrete encoding. This file instantiates the     *)
(*        abstract with the concrete to get the SAT diagonal witness.    *)
(*                                                                       *)
(*  (iii) Downstream Use.                                                *)
(*                                                                       *)
(*        The Construct_SAT_Diagonal theorem is used by:                 *)
(*          - P3_T__Structural_Integrity (Hardness_Conservation theorem) *)
(*          - As the Diagonal_Mechanism hypothesis                       *)
(*                                                                       *)
(*************************************************************************)

(*************************************************************************)
(*                                                                       *)
(*  This adapter allows the abstract diagonal construction (C003) to     *)
(*  use the concrete carryless pairing device (C001) for encoding.       *)
(*                                                                       *)
(*************************************************************************)

Module CarrylessBackend <: Diagonallemma.C003.P1_S__Syntax.C003_P1.BACKEND.
  
  (* Short aliases for C001 modules *)
  Module N := Carryless_Pairing.C001.P5_T__Carryless_Pairing.Prelude.
  Module P := Carryless_Pairing.C001.P5_T__Carryless_Pairing.Pairing.

  Definition nat : Type := N.nat.

  (* C001 uses a specific pairing strategy (CarrylessPair) *)
  Definition pair (x y : nat) : nat := 
    P.pair P.CarrylessPair x y.

  Definition unpair (z : nat) : nat * nat :=
    let p := P.unpair P.CarrylessPair z in 
    (P.fst p, P.snd p).

  (* Tag Definitions: specific natural numbers for AST encoding *)
  (* We use standard lambda definable construction. *)
  
  Definition tag_bot     : nat := N.O.
  Definition tag_imp     : nat := N.S N.O.
  Definition tag_hole    : nat := N.S (N.S N.O).
  Definition tag_quote   : nat := N.S (N.S (N.S N.O)).
  Definition tag_var     : nat := N.S (N.S (N.S (N.S N.O))).
  Definition tag_const   : nat := N.S (N.S (N.S (N.S (N.S N.O)))).
  Definition tag_pair    : nat := N.S (N.S (N.S (N.S (N.S (N.S N.O))))).
  Definition tag_unpairL : nat := N.S (N.S (N.S (N.S (N.S (N.S (N.S N.O)))))).
  Definition tag_unpairR : nat := N.S (N.S (N.S (N.S (N.S (N.S (N.S (N.S N.O))))))).

End CarrylessBackend.

(*
  The Functor Instantiation.
  We create the concrete Diagonal theory (Diag) using our Backend
*)

Module Diag := Diagonallemma.C003.P2_T__Diagonal.Diagonal_Functor(CarrylessBackend).

(*
  The Implementation
*)

Module C009_Diagonal_Mechanism_T.

  Module SI := SAT.C009.P3_T__Structural_Integrity.C009_Structural_Integrity_T.
  Module Def := SI.SAT_Def.

  (*
    Representable — Separator Representability Hypothesis

    Type: Certified_SAT_Solver → Prop

    Definition:
      A separator S is representable iff it can be encoded as a
      diagonal template T_flip such that:
        - The diagonal construction diag(T_flip) produces a formula D
        - D satisfies the flip condition and tracking properties

    This is the bridge hypothesis: it assumes the separator can be
    "internalized" into the diagonal mechanism.

    Why a Hypothesis?
      Constructing the template from an arbitrary separator S
      requires meta-theoretic encoding (the separator's decision
      function must be representable as a formula). We postulate
      this as Representable rather than constructing it directly.

    Role:
      Representable is assumed by Construct_SAT_Diagonal.
      When satisfied, it provides the diagonal witness needed
      for Hardness_Conservation (P3_T__Structural_Integrity).
  *)

  Definition Representable (S : SI.Certified_SAT_Solver) : Prop :=
    exists (T_flip : Diag.Template)
           (Compiled : Diag.COMPILED T_flip)
           (Form_of_Template : Diag.Template -> Def.P.ATP_Form),
      let D_t := Diag.diag (t := T_flip) Compiled in
      let d := Diag.encU D_t in
      (Form_of_Template D_t = Def.Flip_Logic S d) /\
      (Def.Truth (Def.A d) <-> Def.Truth (Form_of_Template D_t)) /\
      (Def.Truth (Def.B d) <-> Def.Truth (Form_of_Template D_t)).

  (*
    Theorem: Construct_SAT_Diagonal — The Diagonal Witness Discharger

    Type:
      ∀S : Certified_SAT_Solver.
        Representable S →
        ∃(d, D). (flip and tracking conditions)

    Statement:
      Given a representable separator S, construct the diagonal witness
      (d, D) required by the Hardness_Conservation theorem.

    Proof Strategy:
      1. Destructure Representable S to get:
           - T_flip: the template representing Flip(S, □)
           - Comp: the compilation of T_flip
           - Form_of_Template: interpretation function
      2. Execute the diagonal construction:
           D_t = diag(T_flip)  (the diagonal template)
           d   = encU(D_t)      (the code of D_t)
           D   = Form_of_Template(D_t)  (the formula interpretation)
      3. Verify the witness conditions:
           - Flip condition: D = Flip(S, d)
           - Tracking conditions: A(d) ↔ D and B(d) ↔ D

    Role:
      This theorem is THE linker between:
        - C003 (diagonal construction)
        - C001 (carryless encoding)
        - C009 (SAT hardness)

      It discharges the Diagonal_Mechanism hypothesis in
      Hardness_Conservation (P3_T__Structural_Integrity).
  *)

  Theorem Construct_SAT_Diagonal
    (S : SI.Certified_SAT_Solver)
    (H_Rep : Representable S) :
    exists (d : Def.N.nat) (D : Def.P.ATP_Form),
      (Def.Truth D <-> Def.Truth (Def.Flip_Logic S d)) /\
      (Def.Truth (Def.A d) <-> Def.Truth D) /\
      (Def.Truth (Def.B d) <-> Def.Truth D).
  Proof.

    (*
      Step 1: Destructure the Representable hypothesis
    *)

    destruct H_Rep as [T_flip [Comp [Form_of_Template HRep]]].

    (*
      Step 2: Execute the Diagonal Operator

      The diagonal construction from C003 gives us:
        D_t = diag(T_flip, Comp)

      This is the self-referential template: D_t "talks about"
      its own code via the Quinean knot (selfpack).
    *)

    pose (D_t := Diag.diag (t := T_flip) Comp).

    (*
      Step 3: Compute the code of D_t

      d = encU(D_t) is the Gödel number of the diagonal template.
    *)

    pose (d    := Diag.encU D_t).

    (*
      Step 4: Interpret D_t as a formula

      D = Form_of_Template(D_t) converts the template to an ATP_Form.
      This is the actual formula that will appear in the barrier proof.
    *)

    pose (D    := Form_of_Template D_t).

    (*
      Step 5: Return the witness (d, D)
    *)

    exists d, D.

    (*
      Step 6: Verify the witness conditions
    *)

    destruct HRep as [HFlip [HTrackA HTrackB]].

    split.

    (*
      Condition 1: Flip Property

      Goal: Truth(D) ↔ Truth(Flip(S, d))

      By HFlip (from Representable), we have D = Flip(S, d),
      so this is trivial.
    *)

    - unfold D, d, D_t in *.
      split; intro HT.
      + rewrite HFlip in HT. exact HT.
      + rewrite <- HFlip in HT. exact HT.

    (*
      Condition 2: Tracking Properties

      Goal: Truth(A(d)) ↔ Truth(D) ∧ Truth(B(d)) ↔ Truth(D)

      These are exactly HTrackA and HTrackB from Representable.
    *)

    - split.
      + unfold D, d, D_t in *. exact HTrackA.
      + unfold D, d, D_t in *. exact HTrackB.

    (*
      QED.

      We have constructed (d, D) satisfying all witness conditions.
      This diagonal witness can now be fed to the Adversarial Barrier
      (C005) to derive False from separator existence.
    *)

  Qed.

End C009_Diagonal_Mechanism_T.

(*************************************************************************)
(*                                                                       *)
(*  The Diagonal Mechanism as Linker                                     *)
(*                                                                       *)
(*  Three-Module Integration:                                            *)
(*                                                                       *)
(*    C003 (Diagonal Lemma):                                             *)
(*      Provides abstract self-reference construction.                   *)
(*      Parametric over BACKEND interface.                               *)
(*                                                                       *)
(*    C001 (Carryless Pairing):                                          *)
(*      Provides concrete encoding (pair, unpair, tags).                 *)
(*      Implements BACKEND interface via CarrylessBackend.               *)
(*                                                                       *)
(*    C009 (SAT Reduction):                                              *)
(*      Requires diagonal witness for Hardness_Conservation.             *)
(*      Construct_SAT_Diagonal discharges this requirement.              *)
(*                                                                       *)
(*  The Linker Pattern:                                                  *)
(*                                                                       *)
(*    1. Define abstract interface (C003 BACKEND).                       *)
(*    2. Implement concrete adapter (CarrylessBackend).                  *)
(*    3. Instantiate abstract theory (Diag functor).                     *)
(*    4. Bridge to downstream user (Construct_SAT_Diagonal).             *)
(*                                                                       *)
(*  This is modular impossibility: each layer is minimal, focused, and   *)
(*  compositional. The hardness result emerges from their interaction.   *)
(*                                                                       *)
(*************************************************************************)
