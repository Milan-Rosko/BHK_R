(* P6_A__Provability_Inclusion.v *)

(*************************************************************************)
(*                                                                       *)
(*  C018 / Phase 6 (A): Provability Inclusion Certificate                *)
(*                                                                       *)
(*  This file provides the certificate type without postulating any      *)
(*  instance.                                                            *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.
From C018 Require Import P1_R__Core.
From C018 Require Import P3_R__Provability_Inclusion.

Set Implicit Arguments.
Unset Strict Implicit.

Module C_018_Provability_Inclusion_A.

  Module SR := C_018_Symbolic_Regulation_R.
  Module PI := C_018_Provability_Inclusion_R.

  (*************************************************************************)
  (*                                                                       *)
  (*  Certificate Type                                                     *)
  (*                                                                       *)
  (*************************************************************************)

  (*
    A certificate for a given regulator is simply an instance of the
    provability inclusion record. No axioms are introduced here.
  *)

  Definition Provability_Inclusion_Certificate
    (R : SR.SymbolicRegulator) : Type :=
    PI.ProvabilityInclusion R.

End C_018_Provability_Inclusion_A.

Export C_018_Provability_Inclusion_A.
