(* P1_S__carryless.v *)
Require Import P0_S__bhk.
Require Import P1_R__carryless__A.
Require Import P1_R__carryless__B.

Set Implicit Arguments.
Unset Strict Implicit.

Module Carryless_P1_Semantics.

Record FIB_P1 : Type := {
  fib : nat -> nat;
  fib_0  : fib O = O;
  fib_1  : fib (S O) = S O;
  fib_SS : forall n, fib (S (S n)) = add (fib n) (fib (S n))
}.

Definition FibA : FIB_P1 :=
  {| fib    := CarrylessA.Fib.fib
   ; fib_0  := CarrylessA.Fib.fib_0
   ; fib_1  := CarrylessA.Fib.fib_1
   ; fib_SS := CarrylessA.Fib.fib_SS
  |}.

Definition FibB : FIB_P1 :=
  {| fib    := CarrylessB.Fib.fib
   ; fib_0  := CarrylessB.Fib.fib_0
   ; fib_1  := CarrylessB.Fib.fib_1
   ; fib_SS := CarrylessB.Fib.fib_SS
  |}.

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

Definition cong_add
  (a a' b b' : nat) (Ha : a = a') (Hb : b = b') : add a b = add a' b' :=
  match Ha, Hb with
  | eq_refl, eq_refl => eq_refl (add a b)
  end.

Fixpoint fib_eq_pair (n : nat)
  : prod (fib FibA n = fib FibB n) (fib FibA (S n) = fib FibB (S n)) :=
  match n with
  | O =>
      pair
        (eq_trans (fib_0 FibA) (eq_sym (fib_0 FibB)))
        (eq_trans (fib_1 FibA) (eq_sym (fib_1 FibB)))
  | S n' =>
      let p := fib_eq_pair n' in
      let Hn := fst p in
      let HSn := snd p in
      let HSsn : fib FibA (S (S n')) = fib FibB (S (S n')) :=
        eq_trans
          (fib_SS FibA n')
          (eq_trans
             (@cong_add
                (fib FibA n') (fib FibB n')
                (fib FibA (S n')) (fib FibB (S n'))
                Hn HSn)
             (eq_sym (fib_SS FibB n')))
      in
      pair HSn HSsn
  end.

Definition fibA_eq_fibB (n : nat) : fib FibA n = fib FibB n :=
  fst (fib_eq_pair n).

Theorem fib_interop :
  forall n, CarrylessA.Fib.fib n = CarrylessB.Fib.fib n.
Proof.
  exact fibA_eq_fibB.
Qed.

End Carryless_P1_Semantics.