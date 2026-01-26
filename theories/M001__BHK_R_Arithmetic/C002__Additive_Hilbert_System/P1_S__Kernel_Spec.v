(* P1_S__Kernel_Spec.v *)

From Coq Require Import Init.Logic.
From BHK_R.C000 Require Export P0__Reflexica.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C002 / Phase 1 (S) : Proof Kernel                                    *)
(*                                                                       *)
(*  Role.                                                                *)
(*                                                                       *)
(*    (i) Minimal Dependencies: It relies only on the C000 Nucleus.      *)
(*                                                                       *)
(*   (ii) Checker-First: A proof system is defined primarily by a total  *)
(*        boolean checker ('check').                                     *)
(*                                                                       *)
(*  (iii) Soundness Envelope: The propositional predicate 'Prf' is       *)
(*        derived from the checker via a soundness condition.            *)
(*                                                                       *)
(*  This module defines the architectural contract for a “Proof Kernel”  *)
(*  It establishes the "Checker-First" discipline used throughout C002.  *)
(*                                                                       *)
(*************************************************************************)

(*
  Re-export the C000 Prelude so downstream users have access to 'nat'
*)

Module Prelude := BHK_R.C000.P0__Reflexica.Prelude.
Export Prelude.

Module C_002_Prelim.

  (*
    Local Datatypes.

    To keep the kernel dependency-light, we define minimal local types
    for booleans, options, and lists. This prevents heavy library
    imports from polluting the trusted kernel base.
  *)

  Inductive bool : Type := true | false.

  Inductive option (A : Type) : Type :=
    | Some : A -> option A
    | None : option A.

  (*
    Lists are used to represent proof scripts (linear sequences of formulas)
  *)

  Inductive list (A : Type) : Type :=
    | nil  : list A
    | cons : A -> list A -> list A.

  Arguments nil  {A}.
  Arguments cons {A} _ _.
  Arguments Some {A} _.
  Arguments None {A}.

  (*
    The Proof Kernel Contract.
    Proof kernel contract: checker-first, Prop only as envelope.
  *)

  Record ProofKernel : Type := {

    (*
      The type of formulas (object language)
    *)

    Form  : Type;

    (*
      The type of proof objects (e.g., lists of formulas)
    *)

    Proof : Type;

    (*
      Ground Truth: A total boolean function that validates a proof
    *)
    
    check : Proof -> Form -> bool;

    (*
      The Semantic Envelope: A Prop-level predicate
    *)

    Prf   : Proof -> Form -> Prop;   

    (*
      The Consistency Link: If the checker says 'true', the Prop holds.
      This allows us to use computation (check) to witness logical facts.
    *)

    check_sound :
      forall (p : Proof) (phi : Form),
        check p phi = true -> Prf p phi
  }.

  (*************************************************************************)
  (*                                                                       *)
  (*  This record defines the specific *logical* structure we require:     *)
  (*  An implicational logic with Falsity, closed under Modus Ponens.      *)
  (*                                                                       *)
  (*  Remark. 'Prov' here is the existential projection of 'Prf':          *)
  (*                                                                       *)
  (*               Prov phi <-> exists p, Prf p phi                        *)
  (*                                                                       *)
  (*************************************************************************)

  Record AdditiveProvability : Type := {

    Form_ATP : Type;

    (*
      Connectives
    *)

    Imp : Form_ATP -> Form_ATP -> Form_ATP;
    Bot : Form_ATP;

    (*
      The Provability Predicate
    *)

    Prov : Form_ATP -> Prop;

    (*************************************************************************)
    (*                                                                       *)
    (*  The Closure Principle: Modus Ponens.                                 *)
    (*                                                                       *)
    (*  Only inference rule required at higher levels.                       *)
    (*  Internal rules (K, S, EFQ) are hidden inside 'Prov'.                 *)
    (*                                                                       *)
    (*************************************************************************)

    Prov_MP :
      forall (A B : Form_ATP),
        Prov (Imp A B) -> Prov A -> Prov B
  }.

End C_002_Prelim.

Export C_002_Prelim.
