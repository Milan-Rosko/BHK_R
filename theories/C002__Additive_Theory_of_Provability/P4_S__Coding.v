(* P4_S__Coding.v *)

From Coq Require Import Init.Logic.

From ATP.C002 Require Import P1_S__Kernel_Spec.

From ATP.C002 Require Import P4_R__Coding_Nucleus.
From ATP.C002 Require Import P4_R__Coding_Carryless.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C_002 / Phase 4 (S): Coding façade.                                  *)
(*                                                                       *)
(*  Role: stable surface for coding infrastructure used by downstream    *)
(*  developments.                                                        *)
(*                                                                       *)
(*  Policy.                                                              *)
(*    - We expose the effective codec device.                            *)
(*    - We do NOT expose a CODEC_OK witness in Phase T.                  *)
(*                                                                       *)
(*************************************************************************)

Module C_002_Coding_S.

  Import C_002_Prelim.
  Module CN := ATP.C002.P4_R__Coding_Nucleus.C_002_Coding_Nucleus_R.

  Module R := ATP.C002.P4_R__Coding_Carryless.C_002_Coding_R.

  Definition CODEC : Type := CN.CODEC.

  Definition CanonicalCodec : CODEC := R.Codec.

End C_002_Coding_S.

Export C_002_Coding_S.
Export C_002_Coding_Nucleus_R.
