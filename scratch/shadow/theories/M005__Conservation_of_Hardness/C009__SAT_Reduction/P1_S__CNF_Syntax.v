(* P1_S__CNF_Syntax.v *)

(*************************************************************************)
(*                                                                       *)
(*  C_009 / Phase 1 (S): CNF Syntax (Arithmetized)                       *)
(*                                                                       *)
(*  We define the "Terminal Problem" (SAT) strictly within the           *)
(*  arithmetic nucleus.                                                  *)
(*                                                                       *)
(*  STRUCTURAL NOTE (The Golden Ratio Connection):                       *)
(*  We utilize the C001/C002 infrastructure which relies on Carryless    *)
(*  Pairing for encoding. This means the "texture" of our SAT instances  *)
(*  is defined by Zeckendorf sums.                                       *)
(*                                                                       *)
(*  Since Zeckendorf is grounded in Fibonacci numbers (and thus Phi),    *)
(*  this binds the combinatorial hardness of SAT to the arithmetic       *)
(*  hardness of the Golden Ratio, which is worst case entropy.           *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.
From C002 Require Import P5_T__Proof_Theory.
From C001 Require Import P5_T__Carryless_Pairing.

Set Implicit Arguments.
Unset Strict Implicit.

Module C009_SAT_Syntax.

  Module N := C002.P5_T__Proof_Theory.Prelude.
  Module Pairing := C001.P5_T__Carryless_Pairing.

  (*************************************************************************)
  (*                                                                       *)
  (*  The Prelude provides 'list' but not 'map'. We define it locally      *)
  (*  to keep the nucleus minimal.                                         *)
  (*                                                                       *)
  (*************************************************************************)

  Fixpoint map {A B : Type} (f : A -> B) (xs : N.list A) : N.list B :=
    match xs with
    | N.nil => N.nil
    | N.cons x xs' => N.cons (f x) (map f xs')
    end.

  (*************************************************************************)
  (*                                                                       *)
  (*  A literal is a natural number encoding (variable_index, polarity).   *)
  (*  We use the carryless pairing to pack these two values.               *)
  (*                                                                       *)
  (*  Convention:                                                          *)
  (*    fst (unpair lit) = variable index                                  *)
  (*    snd (unpair lit) = 0 for positive, non-zero for negative           *)
  (*                                                                       *)
  (*************************************************************************)
  
  Definition Lit : Type := N.nat.

  (*************************************************************************)
  (*                                                                       *)
  (*  Clauses and CNF formulas are encoded as lists using the canonical    *)
  (*  sequence codec from C002/C001.                                       *)
  (*                                                                       *)
  (*************************************************************************)
  
  Definition Clause : Type := N.list Lit.
  Definition CNF : Type := N.list Clause.

  (*************************************************************************)
  (*                                                                       *)
  (*  These connect to the C001 carryless pairing device.                  *)
  (*  The codec witnesses (Reflexica) ensure round-trip correctness.       *)
  (*                                                                       *)
  (*************************************************************************)

  (* Literal decoding: extract (variable, polarity) from packed nat *)
  Definition decode_lit (l : Lit) : (N.nat * N.bool) :=
    let p := Pairing.unpair Pairing.CarrylessPair l in
    let var := Pairing.R.fst p in
    let pol_nat := Pairing.R.snd p in
    (* polarity: 0 = positive (true), non-zero = negative (false) *)
    let pol := match pol_nat with
               | N.O => N.true
               | N.S _ => N.false
               end in
    (var, pol).

  (* Encode a literal from (variable, polarity) *)
  Definition encode_lit (var : N.nat) (pos : N.bool) : Lit :=
    let pol_nat := match pos with
                   | N.true => N.O
                   | N.false => N.S N.O
                   end in
    Pairing.pair Pairing.CarrylessPair var pol_nat.

  (*************************************************************************)
  (*                                                                       *)
  (*  CNF decoding uses the sequence codec from C002.                      *)
  (*  We expose this as a parameter to allow different codec strategies,   *)
  (*  but the canonical implementation uses carryless pairing.             *)
  (*                                                                       *)
  (*************************************************************************)

  (* Abstract sequence decoder - to be instantiated with carryless codec *)
  Parameter decode_seq : N.nat -> N.list N.nat.
  
  (* Decode a clause (list of literals) from a nat *)
  Definition decode_clause (n : N.nat) : Clause := decode_seq n.

  (* Decode a CNF: first decode to list of clause-codes, then decode each *)
  Definition decode_cnf (n : N.nat) : CNF :=
    let clause_codes := decode_seq n in
    map decode_clause clause_codes.

  (*************************************************************************)
  (*                                                                       *)
  (*  These examples demonstrate that the encoding is computationally      *)
  (*  effective (reduces under vm_compute).                                *)
  (*                                                                       *)
  (*************************************************************************)

  (* Example: encode and decode a positive literal for variable 0 *)
  Example lit_roundtrip_pos_0 :
    decode_lit (encode_lit N.O N.true) = (N.O, N.true).
  Proof. vm_compute. reflexivity. Qed.

  (* Example: encode and decode a negative literal for variable 1 *)
  Example lit_roundtrip_neg_1 :
    decode_lit (encode_lit (N.S N.O) N.false) = (N.S N.O, N.false).
  Proof. vm_compute. reflexivity. Qed.

End C009_SAT_Syntax.

Export C009_SAT_Syntax.
