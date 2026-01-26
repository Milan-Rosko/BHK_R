(* P2_R__Substitution.v *)

(*************************************************************************)
(*                                                                       *)
(*  C009 / Phase 2 (R): Substitution (Realization)                       *)
(*                                                                       *)
(*    (i) Scope.                                                         *)
(*        Provides structural substitution for FOL formulas.             *)
(*        Supports capture-avoiding substitution for quantified          *)
(*        formulas.                                                      *)
(*                                                                       *)
(*   (ii) Operations.                                                    *)
(*                                                                       *)
(*        (a) [ nat_eqb  : ℕ → ℕ → bool ]                                *)
(*            Decidable equality for natural numbers.                    *)
(*        (b) [ term_eqb : Term → Term → bool ]                          *)
(*            Decidable equality for terms (aliased to nat_eqb).         *)
(*        (c) [ subst : Form → Var → Term → Form ]                       *)
(*            Capture-avoiding substitution: subst(φ, x, t) replaces     *)
(*            free occurrences of variable x with term t in formula φ.   *)
(*                                                                       *)
(*  (iii) Substitution Semantics.                                        *)
(*                                                                       *)
(*        The substitution subst(φ, x, t) is defined structurally:       *)
(*                                                                       *)
(*        subst(⊥, x, t)       = ⊥                                      *)
(*        subst(φ → ψ, x, t)   = subst(φ, x, t) → subst(ψ, x, t)         *)
(*        subst(t₁ = t₂, x, t) = t₁[x↦t] = t₂[x↦t]                       *)
(*        subst(∀y.φ, x, t)    = ∀y. (if x=y then φ else subst(φ,x,t))   *)
(*        subst(∃y.φ, x, t)    = ∃y. (if x=y then φ else subst(φ,x,t))   *)
(*                                                                       *)
(*        The quantifier cases implement capture-avoidance:              *)
(*        if the bound variable y equals the substitution target x,      *)
(*        we stop recursing (x is shadowed by the binder).               *)
(*                                                                       *)
(*   (iv) This substitution does NOT perform α-renaming to avoid         *)
(*        variable capture. Instead, it relies on the caller to          *)
(*        ensure t does not contain free variables that would be         *)
(*        captured by binders in φ.                                      *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.
From SAT.C009 Require Import P1_S__Syntax.

Set Implicit Arguments.
Unset Strict Implicit.

Module C009_FOL_Subst_R.

  Module S := C009_FOL_Syntax.
  Module N := S.N.

  (*
    nat_eqb — Decidable Equality for Naturals

    Compares two natural numbers for syntactic equality.
    Returns true iff the numbers are structurally identical.

    This is used for variable and term comparison.
  *)

  Fixpoint nat_eqb (a b : N.nat) : bool :=
    match a, b with
    | N.O, N.O => true
    | N.S a', N.S b' => nat_eqb a' b'
    | _, _ => false
    end.

  (*
    term_eqb — Decidable Equality for Terms

    Since terms are ℕ, this is just an alias for nat_eqb.
    We provide it as a separate definition for semantic clarity.
  *)

  Definition term_eqb : S.Term -> S.Term -> bool := nat_eqb.

  (*
    subst — Capture-Avoiding Substitution

    Type: Form → Var → Term → Form

    Usage: subst φ x t

    Replaces free occurrences of variable x with term t in formula φ.

    Structural Cases:

      Bot:
        ⊥ contains no variables, so substitution is the identity.

      Imp:
        (φ → ψ)[x↦t] = φ[x↦t] → ψ[x↦t]
        Recurse into both subformulas.

      Eq:
        (t₁ = t₂)[x↦t] = t₁[x↦t] = t₂[x↦t]
        Replace each term if it equals x.

      All / Ex:
        (∀y.φ)[x↦t] = ∀y. (if x=y then φ else φ[x↦t])
        (∃y.φ)[x↦t] = ∃y. (if x=y then φ else φ[x↦t])

        Capture-avoidance: if the bound variable y equals x,
        then x is shadowed and we don't recurse.
        Otherwise, we recurse into the body.

    Limitation:
      This does NOT perform α-renaming. If t contains free
      variables that would be captured by quantifiers in φ,
      the result is capture (incorrect substitution).

      This is acceptable for the kernel's use case: we only
      substitute closed terms or fresh variables.
  *)

  Fixpoint subst (f : S.Form) (x : S.Var) (t : S.Term) : S.Form :=
    match f with
    | S.Bot => S.Bot

    | S.Imp a b => S.Imp (subst a x t) (subst b x t)

    | S.Eq t1 t2 =>

        (*
          Replace t1 with t if t1 equals x, otherwise keep t1.
          Same for t2.
        *)

        let t1' := if term_eqb t1 x then t else t1 in
        let t2' := if term_eqb t2 x then t else t2 in
        S.Eq t1' t2'

    | S.All v body =>

        (*
          If the bound variable v equals x, x is shadowed.
          Don't recurse. Otherwise, recurse into the body.
        *)

        if term_eqb v x then S.All v body else S.All v (subst body x t)

    | S.Ex v body =>

        (*
          Same as All case.
        *)
        
        if term_eqb v x then S.Ex v body else S.Ex v (subst body x t)
    end.

End C009_FOL_Subst_R.

Export C009_FOL_Subst_R.
