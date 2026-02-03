(* P4_T__Effectivity.v *)

From C001 Require Import P5_T__Carryless_Pairing.
From Coq Require Import Init.Logic.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  This file is intentionally not part of the logical development       *)
(*  chain (C002+). It is an effectivity witness and executable           *)
(*  documentation, not a theory module.                                  *)
(*                                                                       *)
(*   C001.P5_T__Carryless_Pairing                                        *)
(*                                                                       *)
(*   It serves three roles:                                              *)
(*                                                                       *)
(*    (i) Demonstrate that the carryless pairing and unpairing           *)
(*        functions are computationally effective (i.e., reduce by       *)
(*        kernel computation without axioms).                            *)
(*                                                                       *)
(*   (ii) Provide concrete, executable witnesses of correctness          *)
(*        for small values, suitable for vm_compute evaluation.          *)
(*                                                                       *)
(*  (iii) Act as a regression / documentation test that the façade-      *)
(*        level pairing interface (Prelude / Pairing) is wired           *)
(*        correctly to its realization.                                  *)
(*                                                                       *)
(*   Methodology note (BHK_R discipline):                                *)
(*                                                                       *)
(*   All correctness statements here are witnessed by computation, that  *)
(*   is by [ vm_compute ], not by propositional reasoning or axioms.     *)
(*                                                                       *)
(*   In particular:                                                      *)
(*                                                                       *)
(*    (i) [ unpair (pair x y) ] reduces definitionally to (x, y);        *)
(*                                                                       *)
(*   (ii) Fibonacci ranks, bands, and Zeckendorf supports are            *)
(*        observed as concrete normal forms.                             *)
(*                                                                       *)
(*************************************************************************)

Module Test_Pairing_Small.

  Module N := Prelude.
  Module P := Pairing.
  Module R := P.R.

  (* This allows us to write readable constants (e.g., "5") in tests. *)

  Fixpoint of_nat (n : Coq.Init.Datatypes.nat) : N.nat :=
    match n with
    | Coq.Init.Datatypes.O => N.O
    | Coq.Init.Datatypes.S k => N.S (of_nat k)
    end.

  (*
    Local list constructors for the project's list type.
  *)

  Definition lnil : R.list N.nat := R.nil.
  Definition lcons (a : Coq.Init.Datatypes.nat) (xs : R.list N.nat) : R.list N.nat :=
    R.cons (of_nat a) xs.
  Definition l1 (a : Coq.Init.Datatypes.nat) : R.list N.nat := lcons a lnil.
  Definition l2 (a b : Coq.Init.Datatypes.nat) : R.list N.nat := lcons a (l1 b).

  (*
    Project-pair projection without relying on any external libraries.
  *)

  Definition fst {A B} (p : R.prod A B) : A :=
    match p with R.pair a _ => a end.
  Definition snd {A B} (p : R.prod A B) : B :=
    match p with R.pair _ b => b end.

  (*************************************************************************)
  (*                                                                       *)
  (*  TEST 1: x=1, y=1                                                     *)
  (*  Expected: pair(1,1)=37; Z(1)={2}; r(1)=3; B=6;                       *)
  (*           even_band={4}; odd_band={9};                                *)
  (*           Z(pair)= {9,4}; unpair(pair)= (1,1).                        *)
  (*                                                                       *)
  (*  We verify the entire pipeline,                                       *)
  (*                                                                       *)
  (*    (i) Zeckendorf support Z(1);                                       *)
  (*                                                                       *)
  (*   (ii) Rank r(1) and Band B(1);                                       *)
  (*                                                                       *)
  (*  (iii) Even/Odd band construction;                                    *)
  (*                                                                       *)
  (*   (iv) final pairing value and Unpairing round-trip.                  *)
  (*                                                                       *)
  (*************************************************************************)

  (*
    Remark. Convenience embedding of Coq's built-in nat into the
  *)

  Definition x11 : N.nat := of_nat 1.
  Definition y11 : N.nat := of_nat 1.

  (*
    Check exact value: [ pair(1,1) ] should correspond to [ index 37 ].
  *)

  Example test_pair_1_1_value :
    P.pair CarrylessPair x11 y11 = of_nat 37.
  Proof. vm_compute. reflexivity. Qed.

  (*
    Verify internals: Z(1) = [2]
  *)

  Example test_Z_1 :
    P.Z CarrylessPair x11 = l1 2.
  Proof. vm_compute. reflexivity. Qed.

  (*
    Verify internals: rank r(1) = 3
  *)

  Example test_r_1 :
    P.r CarrylessPair x11 = of_nat 3.
  Proof. vm_compute. reflexivity. Qed.

  (*
    Verify internals: band offset B(1) = 6
  *)

  Example test_B_1 :
    P.B CarrylessPair x11 = of_nat 6.
  Proof. vm_compute. reflexivity. Qed.

  (*
    Verify round-trip: [ unpair(pair(1,1)) ] reduces to [ (1,1) ]
  *)

  Example test_even_band_1 :
    P.even_band CarrylessPair x11 = l1 4.
  Proof. vm_compute. reflexivity. Qed.

  Example test_odd_band_1_1 :
    P.odd_band CarrylessPair x11 y11 = l1 9.
  Proof. vm_compute. reflexivity. Qed.

  Example test_Z_pair_1_1 :
    P.Z CarrylessPair (P.pair CarrylessPair x11 y11) = l2 9 4.
  Proof. vm_compute. reflexivity. Qed.

  Example test_unpair_pair_1_1_fst :
    fst (P.unpair CarrylessPair (P.pair CarrylessPair x11 y11)) = x11.
  Proof. vm_compute. reflexivity. Qed.

  Example test_unpair_pair_1_1_snd :
    snd (P.unpair CarrylessPair (P.pair CarrylessPair x11 y11)) = y11.
  Proof. vm_compute. reflexivity. Qed.

  (*
    TEST 2: x=5, y=3
    Expected: pair(5,3) = 4236; unpair(pair) = (5,3).
  *)

  Definition x53 : N.nat := of_nat 5.
  Definition y53 : N.nat := of_nat 3.

  (*
    Check value
  *)

  Example test_pair_5_3_value :
    P.pair CarrylessPair x53 y53 = of_nat 4236.
  Proof. vm_compute. reflexivity. Qed.

  (*
    Check round-trip
  *)

  Example test_unpair_pair_5_3_fst :
    fst (P.unpair CarrylessPair (P.pair CarrylessPair x53 y53)) = x53.
  Proof. vm_compute. reflexivity. Qed.

  Example test_unpair_pair_5_3_snd :
    snd (P.unpair CarrylessPair (P.pair CarrylessPair x53 y53)) = y53.
  Proof. vm_compute. reflexivity. Qed.

End Test_Pairing_Small.
