(* P2_S__Interfaces.v *)

(*************************************************************************)
(*                                                                       *)
(*  C018 / Phase 2 (S): Interfaces                                       *)
(*                                                                       *)
(*  This facade re-exports the symbolic regulation core.                 *)
(*  Use it when you want a stable import surface.                        *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.
From C018 Require Import P1_R__Core.

Set Implicit Arguments.
Unset Strict Implicit.

Module C_018_Symbolic_Regulation_S.
  Include C_018_Symbolic_Regulation_R.
End C_018_Symbolic_Regulation_S.

Export C_018_Symbolic_Regulation_S.
