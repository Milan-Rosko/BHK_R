(* P1_T__Trapdoor_Theorem.v *)

From Coq Require Import Init.Logic.
From C002 Require Import P5_T__Proof_Theory.
From C011 Require Import P1_S__Diophantine_Basis.
From C012 Require Import P2_S__Barrier.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  Reflexica Vault Core (Pairing Form)                                  *)
(*                                                                       *)
(*  Purpose                                                              *)
(*                                                                       *)
(*  We now package the *logic-core* notion of a cryptographic “break”    *)
(*  for pairing devices. This is the extractable version of the wager:   *)
(*                                                                       *)
(*  “If you can invert the public device uniformly, you have produced    *)
(*      a Reflexica witness, hence you have proven injectivity.”         *)
(*                                                                       *)
(*  This is not probabilistic security. It is a constructive             *)
(*  inhabitance statement designed for extraction:                       *)
(*                                                                       *)
(*   Break(D)  :=  exists (unpair), forall x y, unpair(pair(x,y))=(x,y)  *)
(*                                                                       *)
(*************************************************************************)

  Module Vault_Core.

    (*
      A pairing device is just a public map (ℕ×ℕ → ℕ).
      No invertibility is assumed in the nucleus.
    *)

    Record Pairing_Device : Type := {
      pair : (N.nat * N.nat) -> N.nat
    }.

    (*
      Injectivity is the canonical “pairing theorem façade” we want to
      *derive* only from a certificate.
    *)

    Definition Injective {A B : Type} (f : A -> B) : Prop :=
      forall a1 a2, f a1 = f a2 -> a1 = a2.

    (*
      Reflexica witness (certificate object):
      a total inverter with a left-inverse law on the image.
      This is the explicit uniformity principle the core does not supply.
    *)

    Record Reflexica_Witness (D : Pairing_Device) : Type := {
      unpair : N.nat -> (N.nat * N.nat);
      unpair_sound :
        forall x y : N.nat,
          unpair (D.(pair) (x, y)) = (x, y)
    }.

    (*
      Core extraction: any Reflexica witness yields injectivity of pair.
    *)

    Theorem pair_injective_from_reflexica :
      forall (D : Pairing_Device),
      forall (W : Reflexica_Witness D),
        Injective D.(pair).
    Proof.
      intros D W.
      unfold Injective.
      intros [x1 y1] [x2 y2] H.
      
      (*
        Apply unpair to both sides and rewrite by soundness.
      *)
      
      assert (H' :
        W.(unpair) (D.(pair) (x1, y1)) =
        W.(unpair) (D.(pair) (x2, y2))).
      { now rewrite H. }
      rewrite (W.(unpair_sound) x1 y1) in H'.
      rewrite (W.(unpair_sound) x2 y2) in H'.
      exact H'.
    Qed.

    (*
      Logic-core “break” definition:
      An attacker does not output a bit; it outputs the certificate itself.
      This is the only notion that extracts without meta-assumptions.
    *)

    Definition Vault_Broken (D : Pairing_Device) : Prop :=
      exists W : Reflexica_Witness D, True.

    Theorem vault_broken_implies_injective :
      forall (D : Pairing_Device),
        Vault_Broken D -> Injective D.(pair).
    Proof.
      intros D [W _]. exact (pair_injective_from_reflexica (D:=D) W).
    Qed.

  End Vault_Core.
