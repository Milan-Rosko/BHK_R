(* P0__Reflexica.v *)

     (*_  /\/\/\/\/\__  /\/\__  /\/\_  /\/\___  /\/\__________  /\/\/\/\/\____ *)
    (*_  /\/\__  /\/\  /\/\__  /\/\_  /\/\__ /\/\____________  /\/\__  /\/\__  *)
   (*_  /\/\/\/\/\__  /\/\/\/\/\/\_  /\/\/\/\ ______________  /\/\/\/\/\ ___   *)
  (*_  /\/\__  /\/\  /\/\__  /\/\_  /\/\_  /\/\____________  /\/\  /\/\____    *)
 (*_  /\/\/\/\/\__  /\/\__  /\/\_  /\/\___  /\/\__________  /\/\__  /\/\__     *)
(*______________________________________________  /\/\/\/\_______________      *)
(*                                                                             *)
(*     “Reflexica“                                                             *)
(*                                                                             *)
(*     We define the repository-wide notion of an opt-in “global               *)
(*     inversion certificate” for an effective coding device.                  *)
(*                                                                             *)
(*     It must remain parametric and must not depend on any later              *)
(*     constructions. The guiding discipline is:                               *)
(*                                                                             *)
(*        (i) Effective computation lives in R/S layers of                     *)
(*            later constructions (definitions compute).                       *)
(*                                                                             *)
(*       (ii) Uniform correctness laws that are not derivable                  *)
(*            in pure core are isolated behind a single named                  *)
(*            inhabitant, never assumed implicitly.                            *)
(*                                                                             *)
(*     Axiom.                                                                  *)
(*                                                                             *)
(*     We assume, as our first realization, that our effective                 *)
(*     “Carryless Pairing” operation (pi, pi^-1), that is                      *)
(*                                                                             *)
(*            forall x y, unpair (pair x y) = (x, y)                           *)
(*            --------------------------------------                           *)
(*                                                                             *)
(*     Holds. We justify it by geometry,                                       *)
(*     cf. arXiv:2510.08934, Page 5.                                           *)
(*                                                                             *)
(**                                                                           **)
(*******************************************************************************)

From Coq Require Import Init.Logic.
From BHK_R.C000 Require Export P0__BHK.

Set Implicit Arguments.
Unset Strict Implicit.

  Module Reflexica.

  (*************************************************************************)
  (*                                                                       *)
  (*  Remark: we use the canonical product nat * nat, which has            *)
  (*  definitional projections fst and snd, avoiding additional            *)
  (*  “pair type” bureaucracy in the base layer.                           *)
  (*                                                                       *)
  (*************************************************************************)

  Module Type PAIRING_SIG.
    Parameter nat : Type.

    (* The coding operations under certification. *)

    Parameter pair   : nat -> nat -> nat.
    Parameter unpair : nat -> nat * nat.

  End PAIRING_SIG.

  (*************************************************************************)
  (*                                                                       *)
  (*  Proof-theoretic role.                                                *)
  (*                                                                       *)
  (*  Many constructions can implement pair/unpair effectively (total      *)
  (*  recursion), but cannot prove the global inversion law inside the     *)
  (*  pure BHK_R core without additional structure.                        *)
  (*                                                                       *)
  (*  Reflexica packages exactly one missing inhabitant, so that later     *)
  (*  developments can depend on it explicitly and locally, rather than    *)
  (*  importing untracked arithmetic or classical principles.              *)
  (*                                                                       *)
  (*************************************************************************)

  Module Make (P : PAIRING_SIG).

    (*************************************************************************)
    (*                                                                       *)
    (*  A construction that wants certified inversion provides an            *)
    (*  inhabitant of REFLEXICA. Typical usage in later constructions:       *)
    (*                                                                       *)
    (*     Module C := Reflexica.Make(MyPairing).                            *)
    (*     Parameter R : C.REFLEXICA.                                        *)
    (*                                                                       *)
    (*  The certificate can later be replaced by an explicit constructive    *)
    (*  proof without changing downstream APIs.                              *)
    (*                                                                       *)
    (*************************************************************************)

    Record REFLEXICA : Prop := {
      unpair_pair :
        forall x y : P.nat,
          P.unpair (P.pair x y) = (x, y)
    }.

    (*************************************************************************)
    (*                                                                       *)
    (*  Exported form of the certificate field.                              *)
    (*                                                                       *)
    (*  This is merely a projection, but naming it makes downstream          *)
    (*  dependencies explicit: “this proof uses Reflexica”.                  *)
    (*                                                                       *)
    (*************************************************************************)

    Definition unpair_pair_reflexica (r : REFLEXICA) :
      forall x y : P.nat, P.unpair (P.pair x y) = (x, y) :=
      unpair_pair r.

    (*************************************************************************)
    (*                                                                       *)
    (*  Derived projections.                                                 *)
    (*                                                                       *)
    (*  From the certified round-trip we immediately obtain the ability      *)
    (*  to recover components of the original pair by applying fst/snd.      *)
    (*                                                                       *)
    (*  These lemmas are often the only facts downstream users need.         *)
    (*                                                                       *)
    (*************************************************************************)
    
    Definition fst_unpair_pair_reflexica (r : REFLEXICA) :
      forall x y : P.nat, fst (P.unpair (P.pair x y)) = x :=
      fun x y =>
        eq_trans (f_equal fst (unpair_pair_reflexica r x y))
                 (eq_refl x).

    Definition snd_unpair_pair_reflexica (r : REFLEXICA) :
      forall x y : P.nat, snd (P.unpair (P.pair x y)) = y :=
      fun x y =>
        eq_trans (f_equal snd (unpair_pair_reflexica r x y))
                 (eq_refl y).

    (*************************************************************************)
    (*                                                                       *)
    (*  Injectivity on the image.                                            *)
    (*                                                                       *)
    (*  The certificate implies that pair is injective:                      *)
    (*                                                                       *)
    (*      pair x1 y1 = pair x2 y2  ->  x1 = x2  /\  y1 = y2                *)
    (*                                                                       *)
    (*  This is a “decode both sides” argument, our “Univalence Axiom”       *)
    (*                                                                       *)
    (*  We keep the proof term elementary (f_equal + rewriting)              *)
    (*  to remain aligned with the BHK_R style.                              *)
    (*                                                                       *)
    (*************************************************************************)

    Theorem pair_inj_reflexica (r : REFLEXICA) :
      forall x1 y1 x2 y2 : P.nat,
        P.pair x1 y1 = P.pair x2 y2 ->
        x1 = x2 /\ y1 = y2.

    Proof.
      intros x1 y1 x2 y2 H.
      split.
      - pose proof (f_equal P.unpair H) as Hu.
        pose proof (f_equal fst Hu) as Hf.
        rewrite (fst_unpair_pair_reflexica r x1 y1) in Hf.
        rewrite (fst_unpair_pair_reflexica r x2 y2) in Hf.
        exact Hf.
      - pose proof (f_equal P.unpair H) as Hu.
        pose proof (f_equal snd Hu) as Hs.
        rewrite (snd_unpair_pair_reflexica r x1 y1) in Hs.
        rewrite (snd_unpair_pair_reflexica r x2 y2) in Hs.
        exact Hs.

    Qed.

  End Make.

End Reflexica.

(*************************************************************************)
(*                                                                       *)
(*  C000 / Phase 0 (T): “Simple” BHK_R public surface.                   *)
(*                                                                       *)
(*  Policy: re-export only the arithmetic nucleus and the Reflexica      *)
(*  interface, without assuming any certificate.                         *)
(*                                                                       *)
(*************************************************************************)

Module Prelude := BHK_R.C000.P0__BHK.BHK.

