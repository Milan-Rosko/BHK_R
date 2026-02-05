(* P5_T__Carryless_Pairing.v *)

From Coq Require Import Init.Logic.
From C001 Require Export
  P1_S__Substrate
  P2_S__Carryless
  P3_S__Injectivity
  P4_S__Pairing.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C001 / Phase 5 (T): Carryless Pairing (Public Surface)               *)
(*                                                                       *)
(*  This is the phase-free entry point for C001. It exposes the stable   *)
(*  facades and canonical instances required by downstream developments  *)
(*  (C002+), hiding all internal realization details.                    *)
(*                                                                       *)
(*  Policy,                                                              *)
(*                                                                       *)
(*   (i)    Single Canonical Reality: We export exactly one effective    *)
(*          realization for Fibonacci (StandardFib) and one for          *)
(*          (StandardNatInj). No redundant "A/B" implementations exist.  *)
(*                                                                       *)
(*   (ii)   Device Access: The Pairing device is exposed via the         *)
(*          [ CL_PAIR ] interface, backed by the Zeckendorf realization. *)
(*                                                                       *)
(*   (iii)  No Axioms: All theorems here are proven by kernel            *)
(*          computation (eq_refl) or direct destructor elimination.      *)
(*          The Global Inversion Law is NOT present here;                *)
(*                                                                       *)
(*************************************************************************)

(*
  Stable Conceptual Namespaces
*)

Module Prelude := C001.P1_S__Substrate.Prelude.
Module Fib     := C001.P2_S__Carryless.Carryless_Semantics.
Module NatInj  := C001.P3_S__Injectivity.NatInj_Semantics.
Module Pairing := C001.P4_S__Pairing.Pairing_Semantics.

(*  
  Facade Types
*)

Definition FIB : Type := Fib.FIB.
Definition NAT_INJ : Prop := NatInj.NAT_INJ.
Definition CL_PAIR : Type := Pairing.CL_PAIR.

(*
  Single, effective realization for each concept
*)

(*
  The efficient accumulator-based Fibonacci
*)

Definition StandardFib : FIB := Fib.StandardFib.

(*
  The match-based constructor laws
*)

Definition StandardNatInj : NAT_INJ := NatInj.StandardNatInj.

(*
  The Zeckendorf carryless pairing device
*)

Definition CarrylessPair : CL_PAIR := Pairing.CarrylessPair.

(*
  Constructive destructors for the arithmetic nucleus
  Injectivity: S m = S n -> m = n
*)

Theorem S_inj_public :
  forall m n : Prelude.nat, Prelude.S m = Prelude.S n -> m = n.
Proof.
  exact NatInj.S_inj_interop.
Qed.

(*
  Discrimination: O <> S n
*)

Theorem O_not_S_public :
  forall n : Prelude.nat, Prelude.O <> Prelude.S n.
Proof.
  exact NatInj.O_S_discr_interop.
Qed.

(*
  Discrimination: S n <> O
*)

Theorem S_not_O_public :
  forall n : Prelude.nat, Prelude.S n <> Prelude.O.
Proof.
  exact NatInj.S_O_discr_interop.
Qed.
