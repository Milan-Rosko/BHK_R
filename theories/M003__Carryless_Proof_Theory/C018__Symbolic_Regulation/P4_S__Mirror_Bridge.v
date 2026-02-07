(* P4_S__Mirror_Bridge.v *)

(*************************************************************************)
(*                                                                       *)
(*  C018 / Phase 4 (S): Mirror Bridge                                    *)
(*                                                                       *)
(*  Adapts a symbolic regulator into the C004 Mirror interface.          *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.
From C004 Require Import P1_S__Context.
From C004 Require Import P2_R__Mirror_Core.
From C018 Require Import P1_R__Core.

Set Implicit Arguments.
Unset Strict Implicit.

Module C_018_Mirror_Bridge_S.

  Module SR := C_018_Symbolic_Regulation_R.
  Module Mirror := C_004_Mirror_Core_R.
  Import C_004_Context.

  (*************************************************************************)
  (*                                                                       *)
  (*  Bridge Definitions                                                   *)
  (*                                                                       *)
  (*************************************************************************)

  (*
    The bridge is a thin adapter. It translates [ SymbolicRegulator ] into
    [ MirrorParams ] and re-exports AsIF/Mir under the same Form.
  *)

  Definition ToMirrorParams (R : SR.SymbolicRegulator) : Mirror.MirrorParams :=
    SR.SR_to_MirrorParams R.

  Definition AsIF (R : SR.SymbolicRegulator) (phi : Form) : Prop :=
    SR.AsIF R phi.

  Definition Mir (R : SR.SymbolicRegulator) (phi : Form) : Prop :=
    SR.Mir R phi.

  (*************************************************************************)
  (*                                                                       *)
  (*  Fixed‑Witness Bridge                                                 *)
  (*                                                                       *)
  (*************************************************************************)

  (*
    If a fixed witness works for the underlying MirrorParams,
    then it works for the symbolic regulator as well.
  *)

  Theorem Mirror_fixed_witness_bridge :
    forall (R : SR.SymbolicRegulator) (i0 : nat) (b0 : Form),
      Mirror.REG (ToMirrorParams R) i0 b0 ->
      (forall phi : Form, Mirror.BND (ToMirrorParams R) phi b0) ->
      (forall phi : Form, Prov (Imp phi b0)) ->
      forall phi : Form,
        ~ Mirror.ProvT_P (ToMirrorParams R) (NotF phi) ->
        AsIF R phi.
  Proof.
    intros R i0 b0 REG0 BND0 PRV0 phi Hnr.
    unfold AsIF.
    apply (Mirror.Mirror_fixed_witness (MP := ToMirrorParams R)
                                       (i0 := i0) (b0 := b0));
      assumption.
  Qed.

  (*
    Schema form: the Mirror schema holds for all [ phi ] under fixed witnesses.
  *)

  Theorem Mir_schema_fixed_witness_bridge :
    forall (R : SR.SymbolicRegulator) (i0 : nat) (b0 : Form),
      Mirror.REG (ToMirrorParams R) i0 b0 ->
      (forall phi : Form, Mirror.BND (ToMirrorParams R) phi b0) ->
      (forall phi : Form, Prov (Imp phi b0)) ->
      forall phi : Form, Mir R phi.
  Proof.
    intros R i0 b0 REG0 BND0 PRV0 phi.
    exact (@Mirror.Mir_schema_fixed_witness (ToMirrorParams R)
                                            i0 b0 REG0 BND0 PRV0 phi).
  Qed.

End C_018_Mirror_Bridge_S.

Export C_018_Mirror_Bridge_S.
