(* P2_R__Mirror_Transport.v *)

From Coq Require Import Init.Logic.
From C004 Require Import P1_S__Context.
From C004 Require Import P2_R__Mirror_Core.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C_004 / Phase 2 (R): Mirror Transport (Recursive Extension)          *)
(*                                                                       *)
(*  What this file provides.                                             *)
(*                                                                       *)
(*   (i)    The "Mirror Point" Functional (MirrorPointF).                *)
(*          This function maps a formula phi to the implication:         *)
(*                                                                       *)
(*              MirF(phi) := (notF ProvT(notF phi)) -> phi,              *)
(*                                                                       *)
(*          Intuitively: "If I am non-refutable, then I am true."        *)
(*                                                                       *)
(*   (i)    The Fixed Point (theta). We use the Diagonal Device          *)
(*          (from C003) to find the fixed point of the Mirror Lemma.     *)
(*                                                                       *)
(*                  theta <-> ( ~Prov(~theta) -> theta )                 *)
(*                                                                       *)
(*   (i)    The Transport Lemma. We prove that the diagonal logic holds  *)
(*          inside the proof system. This allows us to "transport" the   *)
(*          Mirror property recursive definition.                        *)
(*                                                                       *)
(*************************************************************************)

Module C_004_Recursive_Mirror_R.

  Import C_004_Context.
  Module Core := C004.P2_R__Mirror_Core.C_004_Mirror_Core_R.
  Import Core.

  (*
    Abstract object-language provability former
  *)
  
  Record ProvFormer : Type := {
    ProvT_F : Form -> Form
  }.

  Section RecursiveMirrorPoint.

    Context (MP : MirrorParams).
    Context (PF : ProvFormer).
    Context (D  : DiagDevice).

    (*
      MirF(phi) := (notF ProvT_F(notF phi)) -> phi
    *)

    Definition MirrorPointF (phi : Form) : Form :=
      Imp (NotF (PF.(ProvT_F) (NotF phi))) phi.

    (*
      Evidence that MirF is representable (supplied downstream).
    *)
    
    Variable MirrorPointF_rep : Prop.

    Definition MirrorPointT : Transformer :=
      {| trF := MirrorPointF; trRep := MirrorPointF_rep |}.

    Definition theta : Form := D.(diag) MirrorPointT.

    Theorem Recursive_Mirror_Lemma :
      Prov (Imp theta (MirrorPointF theta)) /\ Prov (Imp (MirrorPointF theta) theta).
    Proof.
      split.
      - exact (D.(diag_fwd) MirrorPointT).
      - exact (D.(diag_bwd) MirrorPointT).
    Qed.

  End RecursiveMirrorPoint.

End C_004_Recursive_Mirror_R.

Export C_004_Recursive_Mirror_R.
