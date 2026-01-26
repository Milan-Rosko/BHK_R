(* P4_R__Coding_Nucleus.v *)

From Coq Require Import Init.Logic.
From ATP.C002 Require Import P1_S__Kernel_Spec.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C_002 / Phase 4 (R): Coding nucleus interface.                       *)
(*                                                                       *)
(*  This file stabilizes the coding dependency surface for downstream    *)
(*  developments (C_003+). It is interface-only: no realization imports, *)
(*  no axioms, and all partiality made explicit via option and fuel.     *)
(*                                                                       *)
(*    (i) Atom and Code are abstract.                                    *)
(*   (ii) Pairing on codes is abstract (may be unused by some codecs).   *)
(*  (iii) Sequence decoding is fuelled explicitly.                       *)
(*   (iv) CODEC_OK packages a codec plus explicit constructive           *)
(*        witnesses for the basic sequence round-trip property.          *)
(*                                                                       *)
(*************************************************************************)

Module C_002_Coding_Nucleus_R.

  Import C_002_Prelim.

  Record CODEC : Type := {
    Atom : Type;
    Code : Type;

    atom0    : Atom;
    atomS    : Atom -> Atom;
    atomPred : Atom -> Atom;

    atom_eqb : Atom -> Atom -> bool;

    (*
      reserved tags
    *)

    tag_bot : Atom;
    tag_imp : Atom;
    tag_sep : Atom;

    pairC   : Code -> Code -> Code;
    unpairC : Code -> option (Code * Code);

    (*
      sequences of atoms encoded as codes
    *)
    
    enc_seq : list Atom -> Code;
    dec_seq_fuel : Atom -> Code -> option (list Atom)
  }.

  Record CODEC_OK : Type := {
    C : CODEC;

    atom_eqb_refl :
      forall a : C.(Atom), C.(atom_eqb) a a = true;

    atom_eqb_sound :
      forall a b : C.(Atom), C.(atom_eqb) a b = true -> a = b;

    fuel_seq : list (C.(Atom)) -> C.(Atom);

    dec_seq_enc_seq :
      forall xs : list (C.(Atom)),
        C.(dec_seq_fuel) (fuel_seq xs) (C.(enc_seq) xs) = Some xs;

    tag_bot_eq : C.(atom_eqb) C.(tag_bot) C.(tag_bot) = true;
    tag_imp_eq : C.(atom_eqb) C.(tag_imp) C.(tag_imp) = true;
    tag_sep_eq : C.(atom_eqb) C.(tag_sep) C.(tag_sep) = true;
    tag_imp_bot_neq : C.(atom_eqb) C.(tag_imp) C.(tag_bot) = false
  }.

End C_002_Coding_Nucleus_R.

Export C_002_Coding_Nucleus_R.

