(* P2_T__Sumbool_Extraction.v *)

From Fermat_Machine.C014 Require Import P1_T__Fermat_Machine.
Require Extraction.
Require Import Coq.Arith.PeanoNat.

Extraction Language OCaml.

(*************************************************************************)
(*                                                                       *)
(*  Decidable Equality for N.nat                                         *)
(*                                                                       *)
(*************************************************************************)

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

(*************************************************************************)
(*                                                                       *)
(*  Decidable Fermat Relation                                            *)
(*                                                                       *)
(*************************************************************************)

Definition Fermat_Check_Witness (n : N.nat) (t : Triple) :
  {Fermat_Relation n t} + {~ Fermat_Relation n t}.
Proof.
  destruct t as [[a b] c].
  unfold Fermat_Relation.
  destruct (leb (N.S two) n) eqn:Hdim.
  - assert (Hgt : gt n two).
    { unfold gt, lt. exact Hdim. }
    destruct (N_eq_dec a N.O) as [Ha0 | Ha_nz].
    + right. intro H. destruct H as [_ [Ha _]]. apply Ha. exact Ha0.
    + destruct (N_eq_dec b N.O) as [Hb0 | Hb_nz].
      * right. intro H. destruct H as [_ [_ [Hb _]]]. apply Hb. exact Hb0.
      * destruct (N_eq_dec c N.O) as [Hc0 | Hc_nz].
        -- right. intro H. destruct H as [_ [_ [_ [Hc _]]]]. apply Hc. exact Hc0.
        -- destruct (N_eq_dec (N.add (pow a n) (pow b n)) (pow c n)) as [Heq | Hneq].
           ++ left. repeat split; try exact Hgt; try exact Ha_nz; try exact Hb_nz; try exact Hc_nz; exact Heq.
           ++ right. intro H. destruct H as [_ [_ [_ [_ Heq']]]]. apply Hneq. exact Heq'.
  - right. intro H. destruct H as [Hgt _].
    unfold gt, lt in Hgt. rewrite Hdim in Hgt. discriminate Hgt.
Defined.

(* Extracting the decider reveals the "knowledge" of the barrier. *)
Recursive Extraction N_eq_dec Fermat_Check_Witness.
