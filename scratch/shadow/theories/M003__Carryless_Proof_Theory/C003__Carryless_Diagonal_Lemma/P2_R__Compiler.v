(* P2_R__Compiler.v *)

From Coq Require Import Init.Logic.
From C003 Require Import P1_S__Syntax.
From C003 Require Import P2_R__Backend.

Set Implicit Arguments.
Unset Strict Implicit.

(*************************************************************************)
(*                                                                       *)
(*  C003 / Phase 2 (R): Compiler artifact (total, certificate-free).     *)
(*                                                                       *)
(*  This phase provides a concrete, total compile_delta that produces    *)
(*  a COMPILED witness for any template via a structural compiler.       *)
(*                                                                       *)
(*  The compiled expression computes the code of subst0 t w. The only    *)
(*  w-dependence is in the Hole case, via UnpairL Var.                   *)
(*                                                                       *)
(*************************************************************************)

Module C003_Compiler_R.

  Module Make (B : C003_P1.BACKEND).

    Module D := C003_P1.Make(B).

    (*
      Structural compiler: computes encU (subst0 t w).
    *)

    Fixpoint compU (t : D.Template) : D.CExp :=
      match t with
      | D.Bot => D.Const (D.encU D.Bot)
      | D.Imp a b =>
          D.Pair
            (D.Const D.tag_imp)
            (D.Pair (compU a) (compU b))
      | D.Hole =>
          D.Pair
            (D.Const D.tag_quote)
            (D.Pair (D.Const D.tag_const) (D.UnpairL D.Var))
      | D.Quote0 e => D.Const (D.encU (D.Quote0 e))
      end.

    (*
      Compile artifact: delta_t := t, E_t := compU t.
    *)

    Definition compile_delta (t : D.Template) : D.COMPILED t :=
      {| D.delta_t := t
       ; D.E_t := compU t
       ; D.compile_inv :=
           let fix compile_inv (u : D.Template) :
               forall w : B.nat,
                 D.encU (D.subst0 u w) = D.eval (compU u) w :=
               match u with
               | D.Bot =>
                   fun w => eq_refl _
               | D.Imp u1 u2 =>
                   fun w =>
                     let IH1 := compile_inv u1 w in
                     let IH2 := compile_inv u2 w in
                     f_equal2
                       (fun x y => B.pair D.tag_imp (B.pair x y))
                       IH1 IH2
               | D.Hole =>

                    (*
                      Hole: both sides reduce to pair tag_quote (pair tag_const (fst (unpair w))).
                    *)
                    
                   fun w => eq_refl _
               | D.Quote0 e =>
                   fun w => eq_refl _
               end
           in
           compile_inv t
      |}.

  End Make.

  Module Default := Make(C003_Backend_Carryless).
  Module D := Default.D.
  Definition compile_delta := Default.compile_delta.

End C003_Compiler_R.
