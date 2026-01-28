(* P1_R__Peano_Arithmetic.v *)

Require Import C000.P0__BHK.
Module N := C000.P0__BHK.BHK.

Section Peano_Realization.

  (*
    Power function: n^m (Primitive Recursive)
  *)

  Fixpoint pow (n m : N.nat) : N.nat :=
    match m with
    | N.O => N.S N.O
    | N.S m' => N.mul n (pow n m')
    end.

  (*
    Boolean Less-than-or-equal
  *)

  Fixpoint leb (n m : N.nat) : bool :=
    match n, m with
    | N.O, _ => true
    | N.S n', N.O => false
    | N.S n', N.S m' => leb n' m'
    end.

  (*
    Max function for height proxies
  *)
  
  Fixpoint maxN (x y : N.nat) : N.nat :=
    match x, y with
    | N.O, _ => y
    | _, N.O => x
    | N.S x', N.S y' => N.S (maxN x' y')
    end.

  Definition two   : N.nat := N.S (N.S N.O).
  Definition three : N.nat := N.S two.
  Definition four  : N.nat := N.S three.

End Peano_Realization.
