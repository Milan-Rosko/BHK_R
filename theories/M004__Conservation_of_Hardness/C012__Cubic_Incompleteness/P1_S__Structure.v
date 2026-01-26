(* P1_S__Structure.v *)

(*************************************************************************)
(*                                                                       *)
(*  C012 / Phase 1 (S): Cubic Structure (Diophantine Context)            *)
(*                                                                       *)
(*  What This File Provides                                              *)
(*                                                                       *)
(*    (i) Abstract interface for Diophantine Equations.                  *)
(*        We do not need to define polynomials explicitly; we need       *)
(*        only their structural properties:                              *)
(*        (a) They can be indexed (decoded from nat).                    *)
(*        (b) They have Solvable/Unsolvable predicates.                  *)
(*                                                                       *)
(*   (ii) Complexity Class Linkage.                                      *)
(*        Imports the "Radical" (primitive recursive) definition         *)
(*        from C011 to establish the "Cubic Barrier".                    *)
(*                                                                       *)
(*  Role in the Hierarchy                                                *)
(*                                                                       *)
(*  This is the structural substrate for the Cubic Incompleteness        *)
(*  Theorem. It provides the domain-specific vocabulary (Equations)      *)
(*  that will be subjected to the Hardness Conservation Law.             *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.
From ATP.C002 Require Import P5_T__Proof_Theory.
From Quintic_Hardness.C011 Require Import P1_S__Diophantine_Basis.

Set Implicit Arguments.
Unset Strict Implicit.

Module C012_Structure_S.

  Module N := ATP.C002.P5_T__Proof_Theory.Prelude.

  (*
    We reuse the "Radical" complexity class from C011.
    This links Diophantine geometry to the primitive recursive barrier.
  *)

  Module Rad := Quintic_Hardness.C011.P1_S__Diophantine_Basis.C011_Diophantine_S.

  (*************************************************************************)
  (*                                                                       *)
  (* We treat equations as enumerable objects.                             *)
  (*                                                                       *)
  (*************************************************************************)


  (*
    Abstract type for a Diophantine Equation (e.g. P(x,y,z) = 0)
  *)

  Parameter Equation : Type.

  (*
    The decoding function: maps a natural number index to an Equation
  *)
  
  Parameter decode_equation : N.nat -> Equation.

  (*************************************************************************)
  (*                                                                       *)
  (*  Semantics                                                            *)
  (*                                                                       *)
  (*************************************************************************)

  (* Property: The equation has an integer solution *)
  Parameter Solvable : Equation -> Prop.

  (*
    The equation has NO integer solution.
    Remark. We keep this distinct from ~Solvable for constructive clarity
  *)

  Parameter Unsolvable : Equation -> Prop.

  (*************************************************************************)
  (*                                                                       *)
  (*  Complexity Class                                                     *)
  (*                                                                       *)
  (*************************************************************************)

  (*
    We define "Solvable By Radicals" for a characteristic function f.
     
     This links the Diophantine context to the bounded computation 
     class defined in C011. If a solver's characteristic function is
     in this class, it operates using only "verification energy"
     (bounded operations), lacking the "inversion energy" required
     for Diophantine sets (MRDP).
  *)

  Definition Solvable_By_Radicals (f : N.nat -> N.nat) : Prop :=
    Rad.Solvable_By_Radicals f.

End C012_Structure_S.

Export C012_Structure_S.