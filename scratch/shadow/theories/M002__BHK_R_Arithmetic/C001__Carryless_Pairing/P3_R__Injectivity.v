(* P3_R__Injectivity.v *)

From C001 Require Import P1_S__Substrate.

Set Implicit Arguments.
Unset Strict Implicit.

(*
  We provide the standard realization of injectivity and discrimination
  using direct elimination on the equality witness (match H with...).
*)

Module Injectivity_Realization.
  Module N := P1_S__Substrate.Prelude.

  Module StandardNatInj.

    (* 
      Injectivity: S m = S n -> m = n
    *)

    Definition S_inj (m n : N.nat) (H : N.S m = N.S n) : m = n :=
      match H with
      | eq_refl => eq_refl
      end.

    (*
      Discrimination: O <> S n
    *)

    Definition O_S_discr (n : N.nat) : N.O <> N.S n :=
      fun H =>
        match H in (_ = t) return (match t with N.O => True | N.S _ => False end) with
        | eq_refl => I
        end.

    (*
      Discrimination: S n <> O
    *)
    
    Definition S_O_discr (n : N.nat) : N.S n <> N.O :=
      fun H =>
        match H in (_ = t) return (match t with N.O => False | N.S _ => True end) with
        | eq_refl => I
        end.
  End StandardNatInj.

End Injectivity_Realization.
