(* P1_R__carryless__B.v *)
Require Import P0_S__bhk.

Set Implicit Arguments.
Unset Strict Implicit.

Module CarrylessB.

  Module Fib.

    (*****************************************************************)
    (* Internal product and pair-recursive computation               *)
    (* This is structurally recursive and kernel-computational.      *)
    (*****************************************************************)
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

    Definition step (p : prod nat nat) : prod nat nat :=
      match p with
      | pair a b => pair b (add a b)
      end.

    Fixpoint fib_pair (n : nat) : prod nat nat :=
      match n with
      | O => pair O (S O)
      | S n' => step (fib_pair n')
      end.

    Definition fib (n : nat) : nat := fst (fib_pair n).

    (*****************************************************************)
    (* Round-01 observable laws                                      *)
    (*****************************************************************)
    Definition fib_0 : fib O = O := eq_refl O.
    Definition fib_1 : fib (S O) = S O := eq_refl (S O).

    Definition fib_S (n : nat) : fib (S n) = snd (fib_pair n) :=
      match fib_pair n as p return fst (step p) = snd p with
      | pair a b => eq_refl b
      end.

    Definition snd_step (p : prod nat nat) :
      snd (step p) = add (fst p) (snd p) :=
      match p with
      | pair a b => eq_refl (add a b)
      end.

    (* Same normal form used in the semantics file: fib(S(S n)) = fib(n) + fib(S n) *)
    Definition fib_SS : forall n, fib (S (S n)) = add (fib n) (fib (S n)) :=
      fun n =>
        let H0 : fib (S (S n)) = snd (fib_pair (S n)) := fib_S (S n) in
        let H1 : snd (fib_pair (S n)) = snd (step (fib_pair n)) :=
          eq_refl (snd (step (fib_pair n))) in
        let H2 : snd (step (fib_pair n)) =
                 add (fst (fib_pair n)) (snd (fib_pair n)) :=
          snd_step (fib_pair n) in
        let H3 : add (fst (fib_pair n)) (snd (fib_pair n)) =
                 add (fib n) (snd (fib_pair n)) :=
          eq_refl (add (fib n) (snd (fib_pair n))) in
        let H4 : add (fib n) (snd (fib_pair n)) =
                 add (fib n) (fib (S n)) :=
          f_equal (fun t => add (fib n) t) (eq_sym (fib_S n)) in
        eq_trans
          (eq_trans (eq_trans (eq_trans H0 H1) H2) (eq_trans H3 H4))
          (eq_refl (add (fib n) (fib (S n)))).

  End Fib.

End CarrylessB.
