(* theories/M004__Conservation_of_Hardness/C014__Fermat_Machine/P2_R__Z_Isomorphism.v *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From Fermat_Machine.C014 Require Import P1_R__Peano_Arithmetic.

Module Z_Bridge.
  Module N := P1_R__Peano_Arithmetic.N.

  Fixpoint to_Z (n : N.nat) : Z :=
    match n with
    | N.O => 0%Z
    | N.S n' => Z.succ (to_Z n')
    end.

  Lemma to_Z_nonneg : forall n, (0 <= to_Z n)%Z.
  Proof. induction n; simpl; lia. Qed.

  Lemma Bridge_Iso_Add : forall n m, to_Z (N.add n m) = Z.add (to_Z n) (to_Z m).
  Proof.
    induction n; intro m; simpl.
    - reflexivity.
    - rewrite IHn. rewrite <- Z.add_succ_l. reflexivity.
  Qed.

  Lemma Bridge_Iso_Mul : forall n m, to_Z (N.mul n m) = Z.mul (to_Z n) (to_Z m).
  Proof.
    induction n; intro m; simpl.
    - reflexivity.
    - rewrite Bridge_Iso_Add. rewrite IHn. rewrite Z.add_comm.
      rewrite <- Z.mul_succ_l. reflexivity.
  Qed.

  Lemma Bridge_Iso_Pow : forall n m, to_Z (pow n m) = Z.pow (to_Z n) (to_Z m).
  Proof.
    intros n m; induction m; simpl.
    - simpl. change (Z.pow (to_Z n) 0) with 1%Z. reflexivity.
    - rewrite Bridge_Iso_Mul. rewrite IHm.
      rewrite Z.pow_succ_r; [reflexivity | apply to_Z_nonneg].
  Qed.
End Z_Bridge.