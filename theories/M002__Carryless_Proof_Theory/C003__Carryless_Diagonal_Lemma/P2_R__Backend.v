(* P2_R__Backend.v *)

From Coq Require Import Init.Logic.
From Diagonallemma.C003 Require Import P1_S__Syntax.
From Carryless_Pairing.C001 Require Import P5_T__Carryless_Pairing.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C003 / Phase 2 (R): Carryless backend instantiation.                 *)
(*                                                                       *)
(*  Provides an effective nat + pair/unpair device sourced from C001.    *)
(*  No Reflexica certificate is assumed.                                 *)
(*                                                                       *)
(*************************************************************************)

Module C003_Backend_Carryless <: C003_P1.BACKEND.
  Module N := Prelude.
  Module P := Pairing.

  Definition nat : Type := N.nat.
  Definition O : nat := N.O.
  Definition S : nat -> nat := N.S.

  Definition pair (x y : nat) : nat :=
    P.pair CarrylessPair x y.

  Definition unpair (z : nat) : nat * nat :=
    let p := P.unpair CarrylessPair z in (P.fst p, P.snd p).

  (*
    Tag Assignment (Small Numerals)

    Tags are assigned as small natural numbers using successor notation.
    N.O is zero, N.S is the successor function.

      ⊥ ↦ 0,  → ↦ 1,  □ ↦ 2,  ⌜⌝ ↦ 3
      var ↦ 4,  const ↦ 5,  pair ↦ 6,  unpairₗ ↦ 7,  unpairᵣ ↦ 8
  *)

  Definition tag_bot : nat := N.O.
  Definition tag_imp : nat := N.S N.O.
  Definition tag_hole : nat := N.S (N.S N.O).
  Definition tag_quote : nat := N.S (N.S (N.S N.O)).

  Definition tag_var : nat := N.S (N.S (N.S (N.S N.O))).
  Definition tag_const : nat := N.S (N.S (N.S (N.S (N.S N.O)))).
  Definition tag_pair : nat := N.S (N.S (N.S (N.S (N.S (N.S N.O))))).
  Definition tag_unpairL : nat := N.S (N.S (N.S (N.S (N.S (N.S (N.S N.O)))))).
  Definition tag_unpairR : nat := N.S (N.S (N.S (N.S (N.S (N.S (N.S (N.S N.O))))))).
End C003_Backend_Carryless.
