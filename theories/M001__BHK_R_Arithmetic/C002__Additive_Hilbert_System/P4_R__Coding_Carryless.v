(* P4_R__Coding_Carryless.v *)

From Coq Require Import Init.Logic.

From ATP.C002 Require Import P1_S__Kernel_Spec.
From ATP.C002 Require Import P4_R__Coding_Nucleus.

From Carryless_Pairing.C001 Require Import P5_T__Carryless_Pairing.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C_002 / Phase 4 (R): Canonical codec (uses C_001 pairing).           *)
(*                                                                       *)
(*  Role: code-as-nat codec whose pairing/unpairing are sourced from     *)
(*  C_001 CarrylessPair.                                                 *)
(*                                                                       *)
(*************************************************************************)

Module C_002_Coding_R.

  Import C_002_Prelim.
  Module CN := C_002_Coding_Nucleus_R.

  Module CP := Carryless_Pairing.C001.P5_T__Carryless_Pairing.
  Module N  := CP.Prelude.
  Module P  := CP.Pairing.
  Module R  := P.R.

  Definition Atom : Type := N.nat.
  Definition Code : Type := N.nat.

  Definition atom0 : Atom := N.O.
  Definition atomS : Atom -> Atom := N.S.

  Definition atomPred (a : Atom) : Atom :=
    match a with
    | N.O => N.O
    | N.S a' => a'
    end.

  Fixpoint atom_eqb (m n : Atom) : bool :=
    match m, n with
    | N.O, N.O => true
    | N.S m', N.S n' => atom_eqb m' n'
    | _, _ => false
    end.

  Definition tag_bot : Atom := N.O.
  Definition tag_imp : Atom := N.S N.O.
  Definition tag_sep : Atom := N.S (N.S N.O).

  Definition pairC (x y : Code) : Code :=
    P.pair CP.CarrylessPair x y.

  Definition unpairC (z : Code) : option (Code * Code) :=
    let p := P.unpair CP.CarrylessPair z in
    Some (P.fst p, P.snd p).

  (*
    Sequence coding via pairing (S-head, 0-terminator).
  *)

  Fixpoint enc_seq (xs : list Atom) : Code :=
    match xs with
    | nil => N.O
    | cons a xs' => pairC (atomS a) (enc_seq xs')
    end.

  Definition unpair_fuel (fuel : N.nat) (z : Code) : option (Code * Code) :=
    match fuel with
    | N.O => None
    | N.S _ => unpairC z
    end.

  Fixpoint dec_seq_fuel (fuel : N.nat) (z : Code) : option (list Atom) :=
    match fuel with
    | N.O => None
    | N.S fuel' =>
        match atom_eqb z N.O with
        | true => Some nil
        | false =>
            match unpair_fuel fuel z with
            | None => None
            | Some (h, t) =>
                match h with
                | N.O => None
                | N.S a =>
                    match dec_seq_fuel fuel' t with
                    | None => None
                    | Some xs => Some (cons a xs)
                    end
                end
            end
        end
    end.

  Definition Codec : CN.CODEC :=
    {|
      CN.Atom := Atom;
      CN.Code := Code;

      CN.atom0 := atom0;
      CN.atomS := atomS;
      CN.atomPred := atomPred;

      CN.atom_eqb := atom_eqb;

      CN.tag_bot := tag_bot;
      CN.tag_imp := tag_imp;
      CN.tag_sep := tag_sep;

      CN.pairC := pairC;
      CN.unpairC := unpairC;

      CN.enc_seq := enc_seq;
      CN.dec_seq_fuel := dec_seq_fuel
    |}.

End C_002_Coding_R.

Export C_002_Coding_R.
