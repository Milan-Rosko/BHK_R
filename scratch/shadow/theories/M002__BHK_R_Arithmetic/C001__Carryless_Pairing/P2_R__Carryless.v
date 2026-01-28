(* P2_R__Carryless.v *)

From C001 Require Import P1_S__Substrate.

Set Implicit Arguments.
Unset Strict Implicit.

Module Fib_Realization.

  Module N := P1_S__Substrate.Prelude.

  Module Fib.

    (*
      Internal product and pair-recursive computation,
      structurally recursive and kernel-computational.
    *)

    Inductive prod (A B : Type) : Type :=
    | pair : A -> B -> prod A B.
    Arguments pair {A B} _ _.

    Definition fst {A B : Type} (p : prod A B) : A :=
      match p with
      | pair a _ => a
      end.

    Definition snd {A B : Type} (p : prod A B) : B :=
      match p with
      | pair _ b => b
      end.

    Definition step (p : prod N.nat N.nat) : prod N.nat N.nat :=
      match p with
      | pair a b => pair b (N.add a b)
      end.

    Fixpoint fib_pair (n : N.nat) : prod N.nat N.nat :=
      match n with
      | N.O => pair N.O (N.S N.O)
      | N.S n' => step (fib_pair n')
      end.

    Definition fib (n : N.nat) : N.nat := fst (fib_pair n).

    Definition fib_0 : fib N.O = N.O := eq_refl N.O.
    Definition fib_1 : fib (N.S N.O) = N.S N.O := eq_refl (N.S N.O).

    Definition fib_S (n : N.nat) : fib (N.S n) = snd (fib_pair n) :=
      match fib_pair n as p return fst (step p) = snd p with
      | pair a b => eq_refl b
      end.

    Definition snd_step (p : prod N.nat N.nat) :
      snd (step p) = N.add (fst p) (snd p) :=
      match p with
      | pair a b => eq_refl (N.add a b)
      end.

    Definition fib_SS : forall n, fib (N.S (N.S n)) = N.add (fib n) (fib (N.S n)) :=
      fun n =>
        let H0 : fib (N.S (N.S n)) = snd (fib_pair (N.S n)) := fib_S (N.S n) in
        let H1 : snd (fib_pair (N.S n)) = snd (step (fib_pair n)) :=
          eq_refl (snd (step (fib_pair n))) in
        let H2 : snd (step (fib_pair n)) =
                 N.add (fst (fib_pair n)) (snd (fib_pair n)) :=
          snd_step (fib_pair n) in
        let H3 : N.add (fst (fib_pair n)) (snd (fib_pair n)) =
                 N.add (fib n) (snd (fib_pair n)) :=
          eq_refl (N.add (fib n) (snd (fib_pair n))) in
        let H4 : N.add (fib n) (snd (fib_pair n)) =
                 N.add (fib n) (fib (N.S n)) :=
          f_equal (fun t => N.add (fib n) t) (eq_sym (fib_S n)) in
        eq_trans
          (eq_trans (eq_trans (eq_trans H0 H1) H2) (eq_trans H3 H4))
          (eq_refl (N.add (fib n) (fib (N.S n)))).

  End Fib.

End Fib_Realization.
