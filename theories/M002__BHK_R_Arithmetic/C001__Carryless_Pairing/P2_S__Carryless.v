(* P2_S__Carryless.v *)

From C001 Require Import
  P1_S__Substrate (* The arithmetic nucleus (nat, add, mul) *)
  P2_R__Carryless. (* The specific realization to be packaged *)

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C001 / Phase 2 (S) : Carryless Semantics (Fibonacci)                 *)
(*                                                                       *)
(*  Role.                                                                *)
(*  This module acts as the semantic stabilization layer for the         *)
(*  Fibonacci sequence. It packages the raw computational realization    *)
(*  (Phase R) behind a clean, mathematical interface (Record FIB).       *)
(*                                                                       *)
(*  This ensures downstream consumers (like the Pairing logic) depend    *)
(*  on the abstract properties of Fibonacci numbers, not the specific    *)
(*  recursive implementation details (e.g. accumulators) used in R.      *)
(*                                                                       *)
(*************************************************************************)

Module Carryless_Semantics.

  (*
    Short aliases for the Nucleus (N) and Realization (R)
  *)

  Module N := P1_S__Substrate.Prelude.
  Module R := P2_R__Carryless.Fib_Realization.


  (*
    A "Fibonacci sequence" is defined here as any function satisfying the
    standard recurrence laws. This Type Class-style record allows us to prove
    theorems based on the specification alone.
  *)

  Record FIB : Type := { 
    fib : N.nat -> N.nat;

    (*
      The operation: maps a natural number to a natural number
    *)
    
    fib_0  : fib N.O = N.O; (* Law: F(0) = 0 *)
    fib_1  : fib (N.S N.O) = N.S N.O; 
    fib_SS : forall n, fib (N.S (N.S n)) = N.add (fib n) (fib (N.S n))

    (*
      Law: F(n+2) = F(n) + F(n+1).
      This recurrence defines the sequence structure used for Zeckendorf
    *)
  }.

  (*************************************************************************)
  (*                                                                       *)
  (*  Canonical Instance                                                   *)
  (*                                                                       *)
  (*  We bind the interface to the efficient realization provided by       *)
  (*  Phase R. This is the single "official" Fibonacci sequence used       *)
  (*  by the carryless pairing device.                                     *)
  (*                                                                       *)
  (*  Note: While R.Fib.fib might use tail-recursion or accumulators,      *)
  (*  StandardFib exposes it simply as satisfying the FIB laws.            *)
  (*                                                                       *)
  (*************************************************************************)

  Definition StandardFib : FIB :=
    {| fib    := R.Fib.fib
     ; fib_0  := R.Fib.fib_0
     ; fib_1  := R.Fib.fib_1
     ; fib_SS := R.Fib.fib_SS
    |}.

End Carryless_Semantics.
