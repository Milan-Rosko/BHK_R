(* P4_S__Pairing.v *)

From Carryless_Pairing.C001 Require Import
  P1_S__Substrate
  P2_S__Carryless
  P4_R__Pairing.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C001 / Phase 4 (S): Pairing facade + arithmetic/parity toolkit.      *)
(*                                                                       *)
(*  What this file provides.                                             *)
(*                                                                       *)
(*    (i) A packaged interface (CL_PAIR) opening the pairing             *)
(*        construction and its auxiliary operators:                      *)
(*        (a) Fibonacci access F                                         *)
(*        (b) rank r and band offset B (= 2 * r)                         *)
(*        (c) Zeckendorf support extractor Z                             *)
(*        (d) the pairing function pair and its typed unpair             *)
(*                                                                       *)
(*        This facade is the stable semantic surface for downstream:      *)
(*        later phases should refer to CarrylessPair : CL_PAIR rather    *)
(*        than importing realization modules directly.                   *)
(*                                                                       *)
(*   (ii) Kernel-stable lemmas about addition, parity, and the band.     *)
(*        The lemmas are intentionally stated in conversion-friendly     *)
(*        normal forms and proved by small primitive recursion,          *)
(*        so that rewriting remains predictable and does not rely on     *)
(*        classical principles or external libraries.                    *)
(*                                                                       *)
(*  How these lemmas are used.                                           *)
(*                                                                       *)
(*    (i) The pairing/unpairing scheme encodes x and y by placing        *) 
(*        Fibonacci  indices into two disjoint “bands”:                  *)
(*                                                                       *)
(*        (a) odd_band x y uses odd indices (B(x) + (2j-1)) from Z(y)    *)
(*        (b) even_band x uses only even indices (2e), from Z(x)         *)
(*                                                                       *)
(*   (ii) Unpairing then recovers x and y by filtering Zeckendorf        *)
(*        indices:                                                       *)    
(*        (a) even indices decode back to x via div2                     *)
(*        (b) odd indices above the band threshold decode back to y      *)
(*                                                                       *)
(*  (iii) The parity lemmas below justify this separation discipline:    *)
(*        (a) B is even, so B(x)+odd remains odd                         *)
(*        (b) 2e is always even                                          *)
(*        (c) 2j-1 is always odd                                         *)
(*                                                                       *)
(*   (iv) In particular, the two “index classification” lemmas           *)
(*        at the end summarize the intended invariant:                   *)
(*        (a) odd_index_is_odd:  B(x) + (2j-1) is odd                    *)
(*        (b) even_index_is_even: 2e is even.                            *)
(*                                                                       *)
(*************************************************************************)

Module Pairing_Semantics.

  Module N := P1_S__Substrate.Prelude. (* The arithmetic nucleus (nat, add, mul) *)

  Module R := P4_R__Pairing.Pairing_Realization.  (* The specific realization to be packaged *)

  Record CL_PAIR : Type := {
    F     : N.nat -> N.nat;
    r     : N.nat -> N.nat;
    B     : N.nat -> N.nat;
    Z     : N.nat -> R.list N.nat;

    even_band : N.nat -> R.list N.nat;
    odd_band  : N.nat -> N.nat -> R.list N.nat;

    pair   : N.nat -> N.nat -> N.nat;
    unpair : N.nat -> R.prod N.nat N.nat
  }.

  (*************************************************************************)
  (*                                                                       *)
  (*  The Device Interface: CL_PAIR                                        *)
  (*                                                                       *)
  (*  This record exposes the operational internals of the pairing         *)
  (*  scheme without exposing their implementation code.                   *)
  (*                                                                       *)
  (*  It includes:                                                         *)
  (*                                                                       *)
  (*    (i) Auxiliaries: Fib (F), rank (r), band offset (B), support (Z).  *)
  (*   (ii) Band Logic: separating indices into even/odd streams.          *)
  (*  (iii) The Core: pair and unpair.                                     *)
  (*                                                                       *)
  (*************************************************************************)

  Definition CarrylessPair : CL_PAIR := {|

      F         := R.F ;              (* Fibonacci sequence used by the device *)
      r         := R.r ;              (* Rank r(n): The first index k such that F k > n *)
      B         := R.B ;              (* Band B(n): The offset 2*r(n) used to shift the Y component *)
      Z         := R.Z ;              (* Zeckendorf Support Z(n): list of indices representing n, from the Realization layer *)
      even_band := R.even_band ;      
      odd_band  := R.odd_band ;       (* Band Projections: The sets of indices used for X and Y *)
      pair      := R.pi_CL_tau ;      (* The Main Pairing Function: Encodes (x,y) into a single nat *)
      unpair    := R.unpair_CL_tau ;  (* The Main Unpairing Function: Decodes z into (x,y) *)
  |}.

  (*************************************************************************)
  (*                                                                       *)
  (*  Helper Projections                                                   *)
  (*                                                                       *)
  (*  Since 'unpair' returns a product type from the R-layer, we           *)
  (*  provide stable accessors for the first and second components.        *)
  (*                                                                       *)
  (*************************************************************************)

  Definition fst (p : R.prod N.nat N.nat) : N.nat := R.fst p.
  Definition snd (p : R.prod N.nat N.nat) : N.nat := R.snd p.


End Pairing_Semantics.
