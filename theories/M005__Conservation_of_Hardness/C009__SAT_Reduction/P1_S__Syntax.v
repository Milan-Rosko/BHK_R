(* P1_S__Syntax.v *)

(*************************************************************************)
(*                                                                       *)
(*  C009 / Phase 1 (S): First-Order Logic Syntax                         *)
(*                                                                       *)
(*    (i) Scope.                                                         *)
(*                                                                       *)
(*        Minimal first-order logic syntax over the BHK_R nucleus.       *)
(*        Provides the foundation for FOL proof kernel (P3_R__Kernel).   *)
(*                                                                       *)
(*   (ii) Language.                                                      *)
(*                                                                       *)
(*        Terms:   ℕ (variables and constants are both naturals)         *)
(*        Formulas:                                                      *)
(*          ⊥       (falsity)                                            *)
(*          φ → ψ   (implication)                                        *)
(*          t = s   (equality)                                           *)
(*          ∀x.φ    (universal quantification)                           *)
(*          ∃x.φ    (existential quantification)                         *)
(*                                                                       *)
(*  (iii) Design Discipline.                                             *)
(*                                                                       *)
(*        (a) Terms are ℕ: no complex term structure (function symbols). *)
(*        (b) Variables are ℕ: identified by natural number indices.     *)
(*        (c) Minimal connectives: only ⊥ and → are primitive.           *)
(*        (d) Other connectives (¬, ∧, ∨) are defined constructions.     *)
(*                                                                       *)
(*   (iv) Role in C009.                                                  *)
(*                                                                       *)
(*        This syntax layer is used for:                                 *)
(*          - Substitution operations (P2_R__Substitution)               *)
(*          - FOL proof kernel (P3_R__Kernel)                            *)
(*          - Public FOL interface (P3_T__FOL)                           *)
(*                                                                       *)
(*        It is NOT used for the SAT reduction itself, which works       *)
(*        directly with the ATP_Form from C002.                          *)
(*                                                                       *)
(*************************************************************************)

From Coq Require Import Init.Logic.
From C000 Require Import P0__BHK.

Set Implicit Arguments.
Unset Strict Implicit.

Module C009_FOL_Syntax.

  (*
    Import the BHK_R arithmetic nucleus.
  *)

  Module N := C000.P0__BHK.BHK.

  (*
    Terms and Variables — Both are ℕ

    Terms:
      In a richer FOL, terms would be built from variables,
      constants, and function symbols. Here we collapse all
      terms to ℕ, treating them as atomic identifiers.

    Variables:
      Variables are also ℕ. The distinction between "variable"
      and "constant" is purely semantic (by usage convention),
      not syntactic.

    This simplification is deliberate: we want a minimal FOL
    substrate for the proof kernel, not a full arithmetic theory.
  *)

  Definition Term := N.nat.
  Definition Var  := N.nat.

  (*
    Formula Language — Minimal First-Order Logic

    Constructors:

      Bot        —  ⊥  (falsity)
      Imp φ ψ    —  φ → ψ  (implication)
      Eq t s     —  t = s  (equality)
      All x φ    —  ∀x. φ  (universal quantification)
      Ex x φ     —  ∃x. φ  (existential quantification)

    Design Notes:

      (i) No disjunction, conjunction, or negation primitives.
          These are defined as abbreviations (e.g., ¬φ ≜ φ → ⊥).

      (ii) Equality is primitive to support Leibniz substitution
           in the proof kernel (P3_R__Kernel).

      (iii) Both universal and existential quantification are
            primitive to support full FOL reasoning (though the
            current kernel focuses on universal instantiation).
  *)

  Inductive Form : Type :=
    | Bot : Form
    | Imp : Form -> Form -> Form
    | Eq  : Term -> Term -> Form
    | All : Var -> Form -> Form
    | Ex  : Var -> Form -> Form.

  (*
    Negation — Defined Abbreviation

    ¬φ ≜ φ → ⊥

    Intuitionistic negation: "if φ holds, we can derive a contradiction."
  *)

  Definition Not (f : Form) : Form := Imp f Bot.

End C009_FOL_Syntax.

Export C009_FOL_Syntax.

(*************************************************************************)
(*                                                                       *)
(*  Design Philosophy: Minimalism and Explicitness                       *)
(*                                                                       *)
(*  Why such a minimal FOL syntax?                                       *)
(*                                                                       *)
(*    (i) The SAT reduction (P2_R__Reduction) doesn't need FOL.          *)
(*        It works directly with ATP_Form (pure implicational logic).    *)
(*                                                                       *)
(*   (ii) The FOL layer exists to support potential future extensions:   *)
(*         - Arithmetization of FOL itself                               *)
(*         - Richer encoding of Turing machines                          *)
(*         - DPRM-style reductions (Diophantine encoding)                *)
(*                                                                       *)
(*  (iii) By keeping the syntax minimal, we avoid committing to a        *)
(*         specific arithmetic theory (PA, HA, etc.). The kernel can     *)
(*         be instantiated with different truth semantics.               *)
(*                                                                       *)
(*   (iv) This is "syntax as interface": the type Form is a stable       *)
(*         API, but the interpretation (Prov, Truth) is parametric.      *)
(*                                                                       *)
(*************************************************************************)
