(* P6_A__Reflexica_Certificate.v *)

From Coq Require Import Init.Logic.
From BHK_R.C000 Require Import P0__Reflexica.
From Carryless_Pairing.C001 Require Export P5_T__Carryless_Pairing.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(**                                                                     **)
(*       Meta-theoretic switch: Reflexica (axiom layer for C001)         *)
(**                                                                     **)
(*************************************************************************)

(*************************************************************************)
(*                                                                       *)
(*  C001 / Phase 6 (A) : Reflexica Certificate (Axiom Layer)             *)
(*                                                                       *)
(*  Role.                                                                *)
(*  This module provides the "Global Inversion Certificate" for the      *)
(*  Carryless Pairing device.                                            *)
(*                                                                       *)
(*  While Phases R, S, and T provide an effective *device* that computes *)
(*  correctly (witnessed by regression tests), they do NOT export a      *)
(*  logical proof that 'unpair' inverts 'pair' for ALL inputs.           *)
(*                                                                       *)
(*  We introduce a guarantee as an explicit Axiom (Reflexica).           *)
(*  Downstream theories (C002+) that require correctness properties      *)
(*  (e.g. injectivity) must import this file.                            *)
(*                                                                       *)
(*    (i) Opt-in: This file is separated from P5_T.                      *)
(*        One can use the device computationally without accepting this. *)
(*                                                                       *)
(*   (ii) Minimal: We assume only the single record instance. All other  *)
(*        theorems (injectivity, projections) are derived constructively *)
(*        from that single point of failure.                             *)
(*                                                                       *)
(*************************************************************************)

Module Carryless_Reflexica.

  Module N := Prelude.
  Module P := Pairing.

  (*************************************************************************)
  (*                                                                       *)
  (* (i) Adapter Signature                                                 *)
  (*                                                                       *)
  (* We adapt the Carryless Pairing device to match the input signature    *)
  (* expected by the generic Reflexica functor.                            *)
  (*                                                                       *)
  (*************************************************************************)

  Module Sig <: P0__Reflexica.Reflexica.PAIRING_SIG.
    Definition nat : Type := N.nat.

  (*************************************************************************)
  (*                                                                       *)
  (*  Remark. Reflexica expects a return type of (nat * nat), so we map    *)
  (*  the device's custom product type to the standard tuple.              *)
  (*                                                                       *)
  (*  We adapt the Carryless Pairing device to match the input signature   *)
  (*  expected by the generic Reflexica functor.                           *)
  (*                                                                       *)
  (*************************************************************************)



    Definition pair : nat -> nat -> nat := P.pair CarrylessPair.
    Definition unpair (z : nat) : nat * nat :=
      let p := P.unpair CarrylessPair z in (P.fst p, P.snd p).
  End Sig.

  Module Cert := P0__Reflexica.Reflexica.Make(Sig).

  Definition REFLEXICA : Prop := Cert.REFLEXICA.

  (*************************************************************************)
  (**                                                                     **)
  (*                                                                       *)
  (*  Certificate                                                          *)
  (*                                                                       *)
  (*  We assert that the Carryless Pairing device satisfies the            *)
  (*  Reflexica record:                                                    *)
  (*                                                                       *)
  (**                                                                     **)
  (*************************************************************************)

  Axiom Reflexica : REFLEXICA.

  Definition unpair_pair_reflexica :
    forall x y : N.nat,
      Sig.unpair (Sig.pair x y) = (x, y) :=
    Cert.unpair_pair_reflexica Reflexica.

  Definition fst_unpair_pair_reflexica :
    forall x y : N.nat,
      fst (Sig.unpair (Sig.pair x y)) = x :=
    Cert.fst_unpair_pair_reflexica Reflexica.

  Definition snd_unpair_pair_reflexica :
    forall x y : N.nat,
      snd (Sig.unpair (Sig.pair x y)) = y :=
    Cert.snd_unpair_pair_reflexica Reflexica.

  Theorem pair_inj_reflexica :
    forall x1 y1 x2 y2 : N.nat,
      P.pair CarrylessPair x1 y1 = P.pair CarrylessPair x2 y2 ->
      x1 = x2 /\ y1 = y2.
  Proof.
    exact (Cert.pair_inj_reflexica Reflexica).
  Qed.

End Carryless_Reflexica.

(*************************************************************************)
(*  Phase-free Reflexica consequences (axiom-dependent public surface).  *)
(*************************************************************************)

Module Reflexica := Carryless_Reflexica.

Module N := Prelude.
Module P := Pairing.

Theorem unpair_pair_public :
  forall x y : N.nat,
    Carryless_Reflexica.Sig.unpair (Carryless_Reflexica.Sig.pair x y) = (x, y).
Proof.
  exact Reflexica.unpair_pair_reflexica.
Qed.

Theorem fst_unpair_pair_public :
  forall x y : N.nat,
    fst (Carryless_Reflexica.Sig.unpair (Carryless_Reflexica.Sig.pair x y)) = x.
Proof.
  exact Reflexica.fst_unpair_pair_reflexica.
Qed.

Theorem snd_unpair_pair_public :
  forall x y : N.nat,
    snd (Carryless_Reflexica.Sig.unpair (Carryless_Reflexica.Sig.pair x y)) = y.
Proof.
  exact Reflexica.snd_unpair_pair_reflexica.
Qed.

Theorem pair_inj_public :
  forall x1 y1 x2 y2 : N.nat,
    P.pair CarrylessPair x1 y1 = P.pair CarrylessPair x2 y2 ->
    x1 = x2 /\ y1 = y2.
Proof.
  exact Reflexica.pair_inj_reflexica.
Qed.
