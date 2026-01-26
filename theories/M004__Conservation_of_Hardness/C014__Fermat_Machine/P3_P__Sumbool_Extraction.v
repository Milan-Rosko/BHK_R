(* P3_P__Sumbool_Extraction.v *)

From Fermat_Machine.C014 Require Import P1_T__Arithmetic_Surface P1_R__Peano_Arithmetic.
Require Import Coq.Arith.PeanoNat.

Module Sumbool_Extraction.
  Import C014_Arithmetic_T.
  Import P1_R__Peano_Arithmetic.

  (*
    Decidable Equality for N.nat
  *)

  Lemma N_eq_dec : forall n m : N.nat, {n = m} + {n <> m}.
  Proof.
    induction n as [| n' IHn]; intros [| m'].
    - left. reflexivity.
    - right. intro H. discriminate H.
    - right. intro H. discriminate H.
    - destruct (IHn m') as [Heq | Hneq].
      + left. rewrite Heq. reflexivity.
      + right. intro H. apply Hneq. injection H. auto.
  Defined.

  (*
    Computational Checker for Fermat Relation
  *)

  Definition Fermat_Check_Witness (n : N.nat) (t : Fermat_Interface.Triple) :
    {Fermat_Relation n t} + {~ Fermat_Relation n t}.
  Proof.
    destruct t as [[a b] c].

    (*
      Check n > 2
    *)
    
    destruct (leb three n) eqn:Hdim.
    - (*
        n >= 3, i.e., n > 2
      *)
      assert (H_Dim : gt n two).
      { unfold gt, lt. exact Hdim. }
      
      (*
        Check a <> 0
      *)

      destruct (N_eq_dec a N.O) as [Ha0 | Ha_nz].
      { right. intro H. destruct H as [_ [Ha _]]. apply Ha. exact Ha0. }

      (*
        Check b <> 0
      *)
      destruct (N_eq_dec b N.O) as [Hb0 | Hb_nz].
      { right. intro H. destruct H as [_ [_ [Hb _]]]. apply Hb. exact Hb0. }

      (*
        Check c <> 0
      *)
      destruct (N_eq_dec c N.O) as [Hc0 | Hc_nz].
      { right. intro H. destruct H as [_ [_ [_ [Hc _]]]]. apply Hc. exact Hc0. }

      (*
        Check Equation
      *)
      destruct (N_eq_dec (N.add (pow a n) (pow b n)) (pow c n)) as [Heq | Hneq].
      + 
        (*
          All checks pass
        *)

        left. repeat split; assumption.

      + (*
          Equation fails
        *)
        right. intro H. destruct H as [_ [_ [_ [_ Heq']]]]. apply Hneq. exact Heq'.
    
    - (*
        n < 
      *)

      right. intro H. destruct H as [Hgt _].
      unfold gt, lt in Hgt. rewrite Hdim in Hgt. discriminate Hgt.
  Defined.

End Sumbool_Extraction.