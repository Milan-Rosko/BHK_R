(* P1_S__Syntax.v *)

From Coq Require Import Init.Logic.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C003 / Phase P1: Carryless Diagonal Operator (axiom-free skeleton)   *)
(*                                                                       *)
(*                                                                       *)
(*  This file is designed to be instantiated using C001’s effective      *)
(*  carryless pairing device (no Reflexica certificate required).        *)
(*                                                                       *)
(*  Discipline:                                                          *)
(*                                                                       *)
(*   (i)    Total definitions only (Fixpoint / Definition).              *)
(*                                                                       *)
(*   (ii)   No decoding theorems.                                        *)
(*                                                                       *)
(*   (iii)  Quotation is syntactically inert under substitution:         *)
(*                                                                       *)
(*                         subst₀(⌜e⌝, w) = ⌜e⌝.                         *)
(*                                                                       *)
(*   (iv)   Correctness exported is code-level (an equality in ℕ).       *)
(*                                                                       *)
(*************************************************************************)

Module C003_P1.

  (*
    Minimal backend signature. C003 depends only on a nat type
    and an effective pair/unpair device over ℕ.

    No inversion law is assumed here (no Reflexica import).
  *)

  Module Type BACKEND.
    Parameter nat : Type.

    Parameter pair   : nat -> nat -> nat.
    Parameter unpair : nat -> nat * nat.

    (*
      Syntax tags (small constant naturals):

        Logic:  ⊥, →, □, ⌜ ⌝
        Arith:  var, const, pair, unpairₗ, unpairᵣ
    *)
    
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

    (*
      Code Expressions (CExp) — Arithmetic DSL over ℕ

      A tiny total language describing how an input w ∈ ℕ is unpacked
      into components and recombined via pairing primitives.

      Operational Semantics:

        ⟦Var⟧(w)          ≜  w
        ⟦Const n⟧(w)      ≜  n
        ⟦Pair e₁ e₂⟧(w)   ≜  pair(⟦e₁⟧(w), ⟦e₂⟧(w))
        ⟦UnpairL e⟧(w)    ≜  π₁(unpair(⟦e⟧(w)))
        ⟦UnpairR e⟧(w)    ≜  π₂(unpair(⟦e⟧(w)))

      Note: This is purely operational. No decoding theorem about
      pair/unpair inversion is assumed here.
    *)

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

    (*
      Template Language — Single-Hole Formulas with Inert Quotation

      Constructors:

        Bot          —  ⊥  (falsity)
        Imp a b      —  a → b  (implication)
        Hole         —  □  (unique substitution site)
        Quote0 e     —  ⌜e⌝  (inert quotation of code expression)

      Key Invariant:

        Substitution does NOT recurse under Quote0.
        Quotation is syntactically inert: subst(⌜e⌝, w) = ⌜e⌝.
    *)

    Inductive Template : Type :=
      | Bot   : Template
      | Imp   : Template -> Template -> Template
      | Hole  : Template
      | Quote0 : CExp -> Template.

    (*
      Packed Substitution (Quote0-Inert)

      The input w is treated operationally as a packed pair w ≡ ⟨v,s⟩.

      The hole □ is filled by quoting the left component v as literal data:

        subst₀(□, w)  ≜  ⌜const v⌝,  where v = π₁(unpair(w)).

      This computes v from w, then injects it as data (not as expression).

      Properties:

        (i)  Total and axiom-free (structural recursion only).
        (ii) Quote0-inert: subst₀(⌜e⌝, w) = ⌜e⌝ (quotation blocks descent).
    *)

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

    (*
      Gödel Encoding — Structural and Total

      We give a minimal encoder into ℕ using only pairing as constructor.

      Tags are kept abstract as small constants. For concrete backend (C001),
      these can be instantiated as small numerals.

      Encoding Functions:

        encE : CExp → ℕ       (code expressions)
        encU : Template → ℕ   (formulas/templates)

      Both are total, structural, and axiom-free.
    *)

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

    (*
      Delta Compilation Interface

      The diagonal operator δ is expressed via compilation:

        compile_δ(t) = (δₜ, Eₜ)

      where δₜ is a template and Eₜ is a code expression, satisfying:

        Compilation Invariant:

          ∀w. encU(subst₀(δₜ, w)) = ⟦Eₜ⟧(w)

      This invariant is proved by computational unfolding once δₜ and Eₜ
      are explicitly constructed (in Phase P2 — Realization).

      Phase P1 pins only the *interface shape* (axiom-free skeleton).
    *)

    Record COMPILED (t : Template) : Type := {
      delta_t : Template;
      E_t     : CExp;
      compile_inv :
        forall w : B.nat,
          encU (subst0 delta_t w) = eval E_t w
    }.

    (*
      Diagonal Operator — Knot-Tying Without Decoding

      The self-packed argument (Quinean knot):

        selfpack(n) ≜ ⟨n, n⟩

      The diagonal is defined by substitution into δₜ using the self-pack:

        diag(t) ≜ subst₀(δₜ, selfpack(⌈δₜ⌉))

      Exported Code-Level Specification:

        ⌈diag(t)⌉ = ⟦Eₜ⟧(selfpack(⌈δₜ⌉))

      This follows immediately from the compilation invariant.
      No decoding theorem is required.
    *)

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
