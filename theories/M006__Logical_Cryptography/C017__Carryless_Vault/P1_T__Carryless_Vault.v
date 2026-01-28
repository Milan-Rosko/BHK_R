From Coq Require Import Init.Logic.

From C013 Require Import P1_T__Trapdoor_Lemma.
From C002 Require Import P5_T__Proof_Theory.
From C001 Require Import P5_T__Carryless_Pairing.

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
(*      Vault_Broken(CarrylessDevice)                                    *)
(*                                                                       *)
(*  From any such break we extract injectivity of the carryless pairing. *)
(*                                                                       *)
(*************************************************************************)

Module C017_Carryless_Vault.

  Module N := C001.P5_T__Carryless_Pairing.Prelude.
  Module VC := Vault_Core.
  Module CP := C001.P5_T__Carryless_Pairing.
  Module Pairing := CP.Pairing.

  (*
    Instantiate the device.
    Replace [CARRYLESS_PAIR] with the exported pairing identifier from:
      C001.P5_T__Carryless_Pairing
  *)

  Definition carryless_pair : (N.nat * N.nat) -> N.nat :=

    (*
      The concrete pairing function we export.
      Example shapes we might have: Carryless.pair, Pairing.pair, etc.
    *)

    fun xy =>
      let '(x, y) := xy in
      Pairing.pair CP.CarrylessPair x y.

  Definition Carryless_Device : VC.Pairing_Device :=
    {| VC.pair := carryless_pair |}.

  (*
    The concrete falsifiability theorem:
    Any “break” of the carryless vault (i.e., any Reflexica witness)
    yields injectivity of the carryless pairing map.
  *)
  
  Theorem break_implies_injective :
    VC.Vault_Broken Carryless_Device ->
    VC.Injective (VC.pair Carryless_Device).
  Proof.
    exact (VC.vault_broken_implies_injective (D:=Carryless_Device)).
  Qed.

End C017_Carryless_Vault.

Export C017_Carryless_Vault.
