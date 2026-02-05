(* P3_S__Injectivity.v *)

From C001 Require
Import P1_S__Substrate P3_R__Injectivity.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C001 / Phase 3 (S) : Injectivity Semantics                           *)
(*                                                                       *)
(*  This module defines the semantic interface for the structural        *)
(*  properties of the arithmetic nucleus. It packages the critical       *)
(*  constructor laws for 'nat':                                          *)
(*                                                                       *)
(*   (i)    Injectivity of S (S m = S n -> m = n)                        *)
(*                                                                       *)
(*   (ii)   Discrimination (O <> S n)                                    *)
(*                                                                       *)
(*  By wrapping these into a Record, we ensure that downstream logic     *)
(*  depends only on these named properties, not on raw match terms.      *)
(*                                                                       *)
(*  This record specifies the minimal inductive properties required      *)
(*  for 'nat' to function as a data structure. These are the             *)
(*  “Peano axiom fragments” for the constructors O and S.                *)
(*                                                                       *)
(*************************************************************************)

Module NatInj_Semantics.

  Module N := P1_S__Substrate.Prelude.
  Module R := Injectivity_Realization.
  
  Record NAT_INJ : Prop := {

    (*
      The interface downstream users rely on
    *)

    S_inj : forall m n : N.nat, N.S m = N.S n -> m = n;

    (*
      O and S are disjoint images: Zero is never a Successor
    *)

    O_S_discr : forall n : N.nat, N.O <> N.S n;

    (*
      Symmetric disjointness: Successor is never Zero
    *)

    S_O_discr : forall n : N.nat, N.S n <> N.O
  }.

  (*************************************************************************)
  (*                                                                       *)
  (*  We bind the interface to the realization. The proofs in 'R'          *)
  (*  utilize 'match' (or elementary destructors) to witness these laws    *)
  (*  constructively.                                                      *)
  (*                                                                       *)
  (*************************************************************************)

    Definition StandardNatInj : NAT_INJ :=
    {|
      S_inj     := R.StandardNatInj.S_inj;
      O_S_discr := R.StandardNatInj.O_S_discr;
      S_O_discr := R.StandardNatInj.S_O_discr
    |}.

  (*************************************************************************)
  (*                                                                       *)
  (*  These definitions project the fields of the canonical instance       *)
  (*  into top-level functions. Phase T (Public Surface) will export       *)
  (*  these to give downstream users easy access to the laws.              *)
  (*                                                                       *)
  (*************************************************************************)

  (*
    Stable projections for Phase T
  *)

  Definition S_inj_interop : forall m n, N.S m = N.S n -> m = n :=
    fun m n H => @S_inj StandardNatInj m n H.

  Definition O_S_discr_interop : forall n, N.O <> N.S n :=
    fun n => @O_S_discr StandardNatInj n.

  Definition S_O_discr_interop : forall n, N.S n <> N.O :=
    fun n => @S_O_discr StandardNatInj n.

End NatInj_Semantics.
