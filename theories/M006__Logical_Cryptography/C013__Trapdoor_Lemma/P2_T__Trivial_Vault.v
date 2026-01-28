(* P2_T__Trivial_Vault *)

From Coq Require Import Init.Logic.
From C001 Require Import P5_T__Carryless_Pairing.
From C001 Require Import P6_A__Reflexica_Certificate.
From C013 Require Import P1_T__Trapdoor_Lemma.

  (*************************************************************************)
  (*                                                                       *)
  (*  C017 / Phase 1 (T) : The Glass Vault                                 *)
  (*                                                                       *)
  (*  A device where pair(x, y) simply encodes (x, y) trivially,           *)
  (*  acting as our non-hard “Ground Truth”                                *)
  (*  Here, we assume a hypothetical Identity map for demonstration.       *)
  (*                                                                       *)
  (*************************************************************************)

Module Trivial_Vault.

  Module N  := C001.P5_T__Carryless_Pairing.Prelude.
  Module CR := C001.P6_A__Reflexica_Certificate.Carryless_Reflexica.
  Module VC := C013.P1_T__Trapdoor_Lemma.Vault_Core.

  (*
    Device: Carryless Pairing
  *)

  Definition carryless_pair (xy : N.nat * N.nat) : N.nat :=
    let (x, y) := xy in CR.Sig.pair x y.

  Definition Glass_Device : VC.Pairing_Device :=
    {| VC.pair := carryless_pair |}.

  (*
    Break (Certified Inverter)
  *)

  Definition carryless_unpair (z : N.nat) : (N.nat * N.nat) :=
    CR.Sig.unpair z.
  
  Definition Test_Witness : VC.Reflexica_Witness Glass_Device.
  Proof.
    refine {| VC.unpair := carryless_unpair |}.
    intros x y.
    cbn [Glass_Device carryless_pair carryless_unpair].
    exact (C001.P6_A__Reflexica_Certificate.unpair_pair_public x y).
  Defined.

End Trivial_Vault.
