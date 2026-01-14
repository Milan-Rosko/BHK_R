(* P1_S__PCC.v — semantics/interaction: specification + packaging of realizations. *)
Require Import P0_S__bhk.
Require Import P1_R__PCC.
Import BHK.

Set Implicit Arguments.
Unset Strict Implicit.

Module PCC_S.

  (*************************************************************************)
  (*                                                                       *)
  (* Semantics/interaction layer: small interface + packaging              *)
  (*                                                                       *)
  (* This file stabilizes what is “observable” and packages a chosen       *)
  (* realization behind a minimal certificate-carrying interface.          *)
  (*                                                                       *)
  (*************************************************************************)

  (* Generic proof-carrying package: code + certificate *)
  Record PCC (A : Type) (Spec : A -> Prop) : Type := {
    code : A;
    cert : Spec code
  }.

  (* A “specification” for a unary function on nat *)
  Definition Spec_add_O_r (f : nat -> nat) : Prop :=
    forall n : nat, f n = n.

  (* Packaged artifact (uses the realization) *)
  Definition Add_O_r_PCC : @PCC (nat -> nat) Spec_add_O_r :=
    {| code := PCC_R.add_to_O
     ; cert := PCC_R.add_O_r
    |}.

End PCC_S.

Export PCC_S.
