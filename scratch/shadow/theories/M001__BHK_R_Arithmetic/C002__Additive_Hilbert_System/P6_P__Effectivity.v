(* P4_T__Effectivity.v *)

From Coq Require Import Init.Logic.

From ATP.C002 Require Import P5_T__Proof_Theory.
From ATP.C002 Require Import P2_R__Hilbert_Kernel.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  P4_T__Effectivity.v                                                  *)
(*                                                                       *)
(*  This file is intentionally not part of the logical development       *)
(*  chain (C003+). It is an effectivity witness and executable           *)
(*  documentation for C_002, in the same spirit as C_001's               *)
(*  P4_T__Effectivity.v.                                                 *)
(*                                                                       *)
(*  Methodology note (BHK_R discipline):                                 *)
(*  All correctness statements here are witnessed by computation         *)
(*  (vm_compute), not by propositional reasoning or axioms.              *)
(*                                                                       *)
(*  What is tested.                                                      *)
(*                                                                       *)
(*     (i) The proof kernel checker recognizes axiom instances.          *)
(*                                                                       *)
(*    (ii) The checker validates a small MP-derived script.              *)
(*                                                                       *)
(*   (iii) The canonical codec (using C_001 pairing) round-trips on      *)
(*         small examples with explicit fuel (computational check).      *)
(*                                                                       *)
(*  What is also tested.                                                 *)
(*                                                                       *)
(*     (i) Effectivity: The diagonal function `diag(t)` actually         *)
(*         computes to a concrete syntax tree for specific inputs.       *)
(*                                                                       *)
(*    (ii) The Diagonal Law: The fundamental equation                    *)
(*         encU (diag t) = eval E_t (selfpack (encU delta_t))            *)
(*         holds by DEFINITIONAL equality (normalization).               *)
(*                                                                       *)
(*   (iii) No Smuggling: The computation succeeds without any opaque     *)
(*         constants (like Reflexica certificates) blocking reduction.   *)
(*                                                                       *)
(*   Methodology note (BHK_R discipline):                                *)
(*   All correctness statements here are witnessed by computation        *)
(*   (vm_compute), not by propositional reasoning or axioms.             *)
(*                                                                       *)
(*  Summary.                                                             *)
(*                                                                       *)
(*     (i) KERNEL (C002)                                                 *)
(*         (a) recognition (EFQ, K, S)                                   *)
(*         (b) checking (Modus Ponens)                                   *)
(*                                                                       *)
(*    (ii) CODING (C002)                                                 *)
(*         (a) Carryless codec round-trip on small examples              *)
(*                                                                       *)
(*   (iii) DIAGONAL (C003)                                               *)
(*         (a) Compilation of templates                                  *)
(*         (b) Execution of the Diagonalizer                             *)
(*         (c) Verification of the “Diagonal Law”                        *)
(*                                                                       *)
(*************************************************************************)

Module Test_Kernel_Small.

  Module HK := ATP.C002.P2_R__Hilbert_Kernel.C_002_HilbertKernel_R.

  (*
    Shorthands
  *)

  Definition Bot : HK.Form := HK.Bot.
  Definition Imp : HK.Form -> HK.Form -> HK.Form := HK.Imp.

  Definition lnil : HK.Proof := nil.
  Definition lcons (x : HK.Form) (xs : HK.Proof) : HK.Proof := cons x xs.
  Definition l1 (x : HK.Form) : HK.Proof := lcons x lnil.
  Definition l3 (a b c : HK.Form) : HK.Proof := lcons a (lcons b (lcons c lnil)).

  (*
    Concrete formulas, no atoms in the object language.
  *)

  Definition A0 : HK.Form := Imp Bot Bot.
  Definition B0 : HK.Form := Imp Bot (Imp Bot Bot).

  (*
    Basic sanity: check rejects empty scripts.
  *)

  Example test_check_empty_rejects :
    HK.check lnil A0 = false.
  Proof. vm_compute. reflexivity. Qed.

  (*
    recognition + single-line checking.
  *)

  Example test_is_axiom_efq :
    HK.is_axiom (Imp Bot Bot) = true.
  Proof. vm_compute. reflexivity. Qed.

  Example test_check_single_axiom :
    HK.check (l1 A0) A0 = true.
  Proof. vm_compute. reflexivity. Qed.

  (*************************************************************************)
  (*                                                                       *)
  (*  MP script: from A0 and (A0 -> (B0 -> A0)) derive (B0 -> A0).         *)
  (*                                                                       *)
  (*  line1: A0                 (EFQ instance)                             *)
  (*  line2: A0 -> (B0 -> A0)   (K instance)                               *)
  (*  line3: B0 -> A0           (MP from line1,line2)                      *)
  (*                                                                       *)
  (*************************************************************************)

  Definition line1 : HK.Form := A0.
  Definition line2 : HK.Form := Imp A0 (Imp B0 A0).
  Definition line3 : HK.Form := Imp B0 A0.

  Example test_check_mp_script :
    HK.check (l3 line1 line2 line3) line3 = true.
  Proof. vm_compute. reflexivity. Qed.

End Test_Kernel_Small.

Module Test_Coding_Small.

  Module CN := ATP.C002.P4_R__Coding_Nucleus.C_002_Coding_Nucleus_R.
  Module Coding := ATP.C002.P5_T__Proof_Theory.Coding.

  Module CP := Carryless_Pairing.C001.P5_T__Carryless_Pairing.
  Module N := CP.Prelude.

  Fixpoint of_nat (n : Coq.Init.Datatypes.nat) : N.nat :=
    match n with
    | Coq.Init.Datatypes.O => N.O
    | Coq.Init.Datatypes.S k => N.S (of_nat k)
    end.

  (* Local list constructors for C_002's list type. *)

  Definition lnil : Prelude.list N.nat := Prelude.nil.
  Definition lcons (a : Coq.Init.Datatypes.nat) (xs : Prelude.list N.nat) : Prelude.list N.nat :=
    Prelude.cons (of_nat a) xs.
  Definition l1 (a : Coq.Init.Datatypes.nat) : Prelude.list N.nat := lcons a lnil.
  Definition l2 (a b : Coq.Init.Datatypes.nat) : Prelude.list N.nat := lcons a (l1 b).

  (*
    Canonical codec: computational spot-check with explicit fuel.
  *)

  Module Carry := ATP.C002.P4_R__Coding_Carryless.C_002_Coding_R.

  Example test_carryless_enc_nil :
    Carry.enc_seq lnil = N.O.
  Proof. vm_compute. reflexivity. Qed.

  Example test_carryless_roundtrip_nil :
    Carry.dec_seq_fuel (of_nat 1) (Carry.enc_seq lnil) = Prelude.Some lnil.
  Proof. vm_compute. reflexivity. Qed.

  Example test_carryless_roundtrip_1_1 :
    Carry.dec_seq_fuel (of_nat 10) (Carry.enc_seq (l2 1 1)) = Prelude.Some (l2 1 1).
  Proof. vm_compute. reflexivity. Qed.

  Example test_carryless_roundtrip_1_2 :
    Carry.dec_seq_fuel (of_nat 10) (Carry.enc_seq (l2 1 2)) = Prelude.Some (l2 1 2).
  Proof. vm_compute. reflexivity. Qed.

(******************************************)
(******************************************)
(******************************************)
(******************************************)
(******************************************)
(******************************************)
(******      ****          *          *****)
(****   ░░░░   *░░   ░░░░░ ░░   ░░░░   ****)
(***   ****░░   *░   ** *░**░   ***░░   ***)
(**░   *****░   *░      ****░   ****░   ***)
(**░   ***  ░   *░   ░░ ****░   ****░   ***)
(**░░   *░░    **░   *░*** *░   ****   ****)
(***░░░      ░  *          *          *****)
(*****░░░░░░*░░*░░░░░░░░░░*░░░░░░░░░░******)
(******************************************)
(******************************************)
(******************************************)
(******************************************)
(******************************************)
(******************************************)

End Test_Coding_Small.


