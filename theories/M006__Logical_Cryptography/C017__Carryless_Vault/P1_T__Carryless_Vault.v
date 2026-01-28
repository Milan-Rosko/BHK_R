From Coq Require Import Init.Logic.

From C013 Require Import P1_T__Trapdoor_Lemma.
From C002 Require Import P5_T__Proof_Theory.
From C001 Require Import P5_T__Carryless_Pairing.
From C001 Require Import P6_A__Reflexica_Certificate.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C017 / Phase 1 (T) : Carryless Vault                                 *)
(*                                                                       *)
(*  This file binds the abstract Reflexica Vault Core (C013) to the      *)
(*  concrete Carryless pairing device (C001).                            *)
(*                                                                       *)
(*  The wager becomes a single inhabitance statement:                    *)
(*                                                                       *)
(*      “Vault_Broken(CarrylessDevice)”                                  *)
(*                                                                       *)
(*  From any such break we extract injectivity of the carryless pairing. *)
(*                                                                       *)
(*************************************************************************)

Module C017_Carryless_Vault.

  Module N  := C001.P5_T__Carryless_Pairing.Prelude.
  Module CP := C001.P5_T__Carryless_Pairing.
  Module CR := C001.P6_A__Reflexica_Certificate.Carryless_Reflexica.
  Module VC := C013.P1_T__Trapdoor_Lemma.Vault_Core.

  (*
    The vault (Concrete Implementation)
  *)
  
  Definition reflexica_pair (xy : N.nat * N.nat) : N.nat :=
    let (x, y) := xy in CR.Sig.pair x y.

  Definition Wythoff_Device : VC.Pairing_Device :=
    {| VC.pair := reflexica_pair |}.

  (*
    The break (Real Implementation of w=0) 
  *)
  Module Trivial_Tier.
    Definition attacker_invert (z : N.nat) : (N.nat * N.nat) :=
      CR.Sig.unpair z.

    Definition Carryless_Witness : VC.Reflexica_Witness Wythoff_Device.
    Proof.
      refine {| VC.unpair := attacker_invert |}.
      intros x y.
      cbn [Wythoff_Device reflexica_pair attacker_invert].
      exact (C001.P6_A__Reflexica_Certificate.unpair_pair_public x y).
    Defined.

    Theorem Vault_Is_Constructive : VC.Vault_Broken Wythoff_Device.
    Proof.
      exists Carryless_Witness.
      exact I.
    Qed.
  End Trivial_Tier.

End C017_Carryless_Vault.

  (*************************************************************************)
  (*                                                                       *)
  (*  We pose that if this specific device is broken,                      *)
  (*  they have proven the uniform injectivity of the Carryless Pairing,   *)
  (*  constructively, which should be 'impossible' if Reflexica holds.     *)
  (*                                                                       *)
  (*************************************************************************)

  (*
    Reflexica = FALSIFIED, DEAD, DESTROYED
  *)

  Theorem Carryless_Is_Injective :
    C017_Carryless_Vault.VC.Injective C017_Carryless_Vault.reflexica_pair.
  Proof.
    apply (C017_Carryless_Vault.VC.vault_broken_implies_injective
             (D:=C017_Carryless_Vault.Wythoff_Device)).
    exact C017_Carryless_Vault.Trivial_Tier.Vault_Is_Constructive.
  Qed.
