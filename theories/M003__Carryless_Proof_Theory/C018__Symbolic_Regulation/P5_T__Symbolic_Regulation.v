(* P5_T__Symbolic_Regulation.v *)

(*************************************************************************)
(*                                                                       *)
(*  C018 / Phase 5 (T): Symbolic Regulation (Public Surface)             *)
(*                                                                       *)
(*  This file exposes the main symbolic-regulation interfaces.           *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.
From C018 Require Import P2_S__Interfaces.
From C018 Require Import P4_S__Mirror_Bridge.
From C004 Require Import P1_S__Context.
From C004 Require Import P2_R__Mirror_Core.

Set Implicit Arguments.
Unset Strict Implicit.

(*
  Usage: import this file to access both the symbolic core and mirror bridge.
  Example:
  Module SR := C_018_Symbolic_Regulation_T.
  SR.SymbolicRegulator, SR.AsIF, SR.Mir, SR.ToMirrorParams ...
*)

Module C_018_Symbolic_Regulation_T.
  Include C_018_Symbolic_Regulation_S.
End C_018_Symbolic_Regulation_T.

Export C_018_Symbolic_Regulation_T.
Export C_018_Mirror_Bridge_S.

(*************************************************************************)
(*                                                                       *)
(*  Public Bridge Lemma                                                   *)
(*                                                                       *)
(*************************************************************************)

Module C_018_Symbolic_Regulation_Public.

  Import C_004_Context.
  Module SR := C_018_Symbolic_Regulation_T.
  Module Bridge := C_018_Mirror_Bridge_S.

  (*
    Public wrapper: fixed-witness Mirror Lemma for symbolic regulators.
  *)

  Theorem Mirror_fixed_witness :
    forall (R : SR.SymbolicRegulator) (i0 : nat) (b0 : Form),
      C_004_Mirror_Core_R.REG (Bridge.ToMirrorParams R) i0 b0 ->
      (forall phi : Form, C_004_Mirror_Core_R.BND (Bridge.ToMirrorParams R) phi b0) ->
      (forall phi : Form, Prov (Imp phi b0)) ->
      forall phi : Form,
        ~ C_004_Mirror_Core_R.ProvT_P (Bridge.ToMirrorParams R) (NotF phi) ->
        Bridge.AsIF R phi.
  Proof.
    intros R i0 b0 REG0 BND0 PRV0 phi Hnr.
    exact (@Bridge.Mirror_fixed_witness_bridge R i0 b0 REG0 BND0 PRV0 phi Hnr).
  Qed.

  (*
    Public wrapper: AsIF implies its non-refutability fragment.
  *)

  Theorem AsIF_implies_AsIF_simple :
    forall (R : SR.SymbolicRegulator) (phi : Form),
      SR.AsIF R phi -> SR.AsIF_simple R phi.
  Proof.
    intros R phi H.
    exact (@SR.AsIF_implies_AsIF_simple R phi H).
  Qed.

  (*
    Public wrapper: schema form under fixed witnesses.
  *)

  Theorem Mir_schema_fixed_witness :
    forall (R : SR.SymbolicRegulator) (i0 : nat) (b0 : Form),
      C_004_Mirror_Core_R.REG (Bridge.ToMirrorParams R) i0 b0 ->
      (forall phi : Form, C_004_Mirror_Core_R.BND (Bridge.ToMirrorParams R) phi b0) ->
      (forall phi : Form, Prov (Imp phi b0)) ->
      forall phi : Form,
        Bridge.Mir R phi.
  Proof.
    intros R i0 b0 REG0 BND0 PRV0 phi.
    exact (@Bridge.Mir_schema_fixed_witness_bridge R i0 b0 REG0 BND0 PRV0 phi).
  Qed.

End C_018_Symbolic_Regulation_Public.