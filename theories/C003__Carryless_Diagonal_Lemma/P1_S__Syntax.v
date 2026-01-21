(* P1_S__Syntax.v *)
(*                                                                       *)
(*  C003 / Phase P1: Carryless Diagonal Operator (axiom-free skeleton)   *)
(*                                                                       *)
(*  This file is intentionally “P1”: it pins the public, certificate-free *)
(*  *shape* of the diagonal pipeline without committing to any particular *)
(*  encoding backend beyond an effective pair/unpair device.             *)
(*                                                                       *)
(*  Discipline:                                                          *)
(*    - Total definitions only (Fixpoint / Definition).                  *)
(*    - No decoding theorems.                                            *)
(*    - Quotation is syntactically inert under substitution.             *)
(*    - Correctness exported is code-level (an equality in nat).          *)
(*                                                                       *)
(*  This file is designed to be instantiated using C001’s effective      *)
(*  carryless pairing device (no Reflexica certificate required).        *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.

Set Implicit Arguments.
Unset Strict Implicit.

Module C003_P1.

  (*************************************************************************)
  (*                                                                       *)
  (*  Minimal backend signature                                             *)
  (*                                                                       *)
  (*  C003 depends only on:                                                 *)
  (*    (i) a nat type, and                                                 *)
  (*   (ii) an effective pair/unpair device over nat.                       *)
  (*                                                                       *)
  (*  No inversion law is assumed here (no Reflexica import).               *)
  (*                                                                       *)
  (*************************************************************************)

  Module Type BACKEND.
    Parameter nat : Type.

    Parameter pair   : nat -> nat -> nat.
    Parameter unpair : nat -> nat * nat.

    (* tags pinned here *)
    Parameter tag_bot tag_imp tag_hole tag_quote : nat.
    Parameter tag_var tag_const tag_pair tag_unpairL tag_unpairR : nat.
  End BACKEND.

  Module Make (B : BACKEND).

    Definition tag_bot : B.nat := B.tag_bot.
    Definition tag_imp : B.nat := B.tag_imp.
    Definition tag_hole : B.nat := B.tag_hole.
    Definition tag_quote : B.nat := B.tag_quote.

    Definition tag_var : B.nat := B.tag_var.
    Definition tag_const : B.nat := B.tag_const.
    Definition tag_pair : B.nat := B.tag_pair.
    Definition tag_unpairL : B.nat := B.tag_unpairL.
    Definition tag_unpairR : B.nat := B.tag_unpairR.

    (*************************************************************************)
    (*                                                                       *)
    (*  Syntax: code expressions (total)                                     *)
    (*                                                                       *)
    (*  These expressions are a tiny “arithmetic DSL” used only to describe  *)
    (*  how a nat input w is unpacked into two components and recombined.    *)
    (*                                                                       *)
    (*    Var          : the input w                                          *)
    (*    Pair e1 e2   : pair (eval e1 w) (eval e2 w)                        *)
    (*    UnpairL e    : fst (unpair (eval e w))                             *)
    (*    UnpairR e    : snd (unpair (eval e w))                             *)
    (*                                                                       *)
    (*  Note: this is purely operational; it does not assert any decoding    *)
    (*  theorem about pair/unpair.                                           *)
    (*                                                                       *)
    (*************************************************************************)

    Inductive CExp : Type :=
      | Var     : CExp
      | Const   : B.nat -> CExp
      | Pair    : CExp -> CExp -> CExp
      | UnpairL : CExp -> CExp
      | UnpairR : CExp -> CExp.

    Fixpoint eval (e : CExp) (w : B.nat) : B.nat :=
      match e with
      | Var => w
      | Const n => n
      | Pair e1 e2 => B.pair (eval e1 w) (eval e2 w)
      | UnpairL e' => fst (B.unpair (eval e' w))
      | UnpairR e' => snd (B.unpair (eval e' w))
      end.

    (*************************************************************************)
    (*                                                                       *)
    (*  Syntax: single-hole templates with inert quotation                   *)
    (*                                                                       *)
    (*    Bot          : falsity                                              *)
    (*    Imp a b      : implication                                          *)
    (*    Hole         : the unique substitution site                         *)
    (*    Quote0 e     : inert quotation of a code expression (syntactic)     *)
    (*                                                                       *)
    (*  Key invariant: substitution does not recurse under Quote0.            *)
    (*                                                                       *)
    (*************************************************************************)

    Inductive Template : Type :=
      | Bot   : Template
      | Imp   : Template -> Template -> Template
      | Hole  : Template
      | Quote0 : CExp -> Template.

    (*************************************************************************)
    (*                                                                       *)
    (*  Packed substitution (Quote0-inert)                                   *)
    (*                                                                       *)
    (*  The input w is treated operationally as a packed pair w ≡ <v,s>.      *)
    (*  The hole is filled by quoting the left component v as a literal:     *)
    (*                                                                       *)
    (*      Quote0 (Const v),  where v = fst (unpair w).                     *)
    (*                                                                       *)
    (*  This computes v from w, then injects it as data (not as an expression). *)
    (*                                                                       *)
    (*  This is axiom-free and total.                                        *)
    (*                                                                       *)
    (*************************************************************************)

    Fixpoint subst0 (t : Template) (w : B.nat) : Template :=
      match t with
      | Bot => Bot
      | Imp a b => Imp (subst0 a w) (subst0 b w)
      | Hole =>
          let v := fst (B.unpair w) in
          Quote0 (Const v)
      | Quote0 e => Quote0 e
      end.

    Theorem subst0_quote_inert : forall e w, subst0 (Quote0 e) w = Quote0 e.
    Proof. intros; exact (eq_refl _). Qed.

    (*************************************************************************)
    (*                                                                       *)
    (*  Encoding (total, structural)                                         *)
    (*                                                                       *)
    (*  We give a minimal, purely structural encoder into nat using only     *)
    (*  pair as a constructor.                                               *)
    (*                                                                       *)
    (*  Tags are kept abstractly as small constants. For a concrete backend   *)
    (*  (C001), these can be chosen as small numerals in the ambient nat.     *)
    (*                                                                       *)
    (*************************************************************************)

    Fixpoint encE (e : CExp) : B.nat :=
      match e with
      | Var => B.pair tag_var tag_bot
      | Const n => B.pair tag_const n
      | Pair e1 e2 => B.pair tag_pair (B.pair (encE e1) (encE e2))
      | UnpairL e' => B.pair tag_unpairL (encE e')
      | UnpairR e' => B.pair tag_unpairR (encE e')
      end.

    Fixpoint encU (t : Template) : B.nat :=
      match t with
      | Bot => B.pair tag_bot tag_bot
      | Imp a b => B.pair tag_imp (B.pair (encU a) (encU b))
      | Hole => B.pair tag_hole tag_bot
      | Quote0 e => B.pair tag_quote (encE e)
      end.

    (*************************************************************************)
    (*                                                                       *)
    (*  Delta compilation interface                                          *)
    (*                                                                       *)
    (*  C003’s diagonal operator is expressed via a compilation artifact     *)
    (*  compile_delta t = (delta_t, E_t) plus one invariant:                 *)
    (*                                                                       *)
    (*     encU (subst0 delta_t w) = eval E_t w                              *)
    (*                                                                       *)
    (*  This invariant is intended to be proved by unfolding and computation *)
    (*  once delta_t and E_t are defined (in P2 / realization).              *)
    (*                                                                       *)
    (*  P1 pins only the *shape* of this interface.                          *)
    (*                                                                       *)
    (*************************************************************************)

    Record COMPILED (t : Template) : Type := {
      delta_t : Template;
      E_t     : CExp;
      compile_inv :
        forall w : B.nat,
          encU (subst0 delta_t w) = eval E_t w
    }.

    (*************************************************************************)
    (*                                                                       *)
    (*  Diagonal operator (knot-tying without decoding)                      *)
    (*                                                                       *)
    (*  The self-packed argument is w := <n,n>.                              *)
    (*  We define diag(t) by substituting into delta_t using this self-pack. *)
    (*                                                                       *)
    (*  Exported property is code-level and follows directly from compile_inv.*)
    (*                                                                       *)
    (*************************************************************************)

    Definition selfpack (n : B.nat) : B.nat := B.pair n n.

    Definition diag (t : Template) (c : COMPILED t) : Template :=
      subst0 (delta_t c) (selfpack (encU (delta_t c))).

    Theorem diag_spec_code :
      forall (t : Template) (c : COMPILED t),
        encU (diag (t := t) c)
        =
        eval (E_t c) (selfpack (encU (delta_t c))).
    Proof.
      intros t c.
      unfold diag.
      exact (compile_inv c (selfpack (encU (delta_t c)))).
    Qed.

  End Make.

End C003_P1.
