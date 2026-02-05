(* P3_R__Additive_Laws.v *)

From Coq Require Import Init.Logic.

From C002 Require Import P1_S__Kernel_Spec.
From C002 Require Import P2_R__Hilbert_Kernel.
From C002 Require Import P2_S__Provability_Interface.

Set Implicit Arguments.
Unset Strict Implicit.

Module C_002_Additive_Laws_R.

  Import C_002_Prelim.
  Import C_002_HilbertKernel_R.
  Import C_002_Provability_S.

  (*
    List operations on local lists
  *)

  Fixpoint app {A : Type} (xs ys : list A) : list A :=
    match xs with
    | nil => ys
    | cons x xs' => cons x (app xs' ys)
    end.

  Notation "xs ++ ys" := (app xs ys) (at level 60, right associativity).

  Definition sing {A : Type} (x : A) : list A := cons x nil.

  (*
    Context extension matching Prf_lines' operational growth
  *)

  Fixpoint extend_ctx (ctx : list Form) (pf : Proof) : list Form :=
    match pf with
    | nil => ctx
    | cons line rest => extend_ctx (cons line ctx) rest
    end.

  Lemma extend_ctx_app :
    forall (ctx : list Form) (pf1 pf2 : Proof),
      extend_ctx ctx (pf1 ++ pf2) = extend_ctx (extend_ctx ctx pf1) pf2.
  Proof.
    intros ctx pf1 pf2. revert ctx.
    induction pf1 as [|x xs IH]; intro ctx.
    - simpl. exact (eq_refl _).
    - simpl. apply IH.
  Qed.

  (*
    Weakening for Prf_lines
  *)

  Definition incl (xs ys : list Form) : Prop :=
    forall x, In x xs -> In x ys.

  Lemma incl_cons :
    forall a xs ys, incl xs ys -> incl (cons a xs) (cons a ys).
  Proof.
    intros a xs ys Hinc x Hin.
    inversion Hin.
    - subst. apply In_here.
    - apply In_there. apply Hinc. exact H0.
  Qed.

  Lemma Prf_lines_weaken :
    forall (ctx1 ctx2 : list Form) (pf : Proof),
      incl ctx1 ctx2 ->
      Prf_lines ctx1 pf ->
      Prf_lines ctx2 pf.
  Proof.
    intros ctx1 ctx2 pf Hinc Hpf.
    revert ctx2 Hinc.
    induction Hpf; intros ctx2 Hinc.
    - constructor.
    - apply Prf_lines_cons_Ax; try assumption.
      apply IHHpf with (ctx2 := cons line ctx2).
      apply incl_cons. exact Hinc.
    - apply Prf_lines_cons_MP with (psi := psi).
      + apply Hinc. exact H.
      + apply Hinc. exact H0.
      + apply IHHpf with (ctx2 := cons line ctx2).
        apply incl_cons. exact Hinc.
  Qed.

  Lemma Prf_lines_app :
    forall (ctx : list Form) (pf1 pf2 : Proof),
      Prf_lines ctx pf1 ->
      Prf_lines (extend_ctx ctx pf1) pf2 ->
      Prf_lines ctx (pf1 ++ pf2).
  Proof.
    intros ctx pf1 pf2 H1 H2.
    revert pf2 H2.
    induction H1 as
      [ ctx0
      | ctx0 line rest Hax Hrest IH
      | ctx0 psi line rest HinPsi HinImp Hrest IH
      ]; intros pf2 H2'.
    - simpl. exact H2'.
    - simpl. apply Prf_lines_cons_Ax; try exact Hax.
      apply IH. exact H2'.
    - simpl. apply Prf_lines_cons_MP with (psi := psi); try assumption.
      apply IH. exact H2'.
  Qed.

  (*
    Membership is preserved when extending contexts
  *)

  Lemma In_extend_ctx :
    forall x ctx pf,
      In x ctx -> In x (extend_ctx ctx pf).
  Proof.
    intros x ctx pf Hin. revert ctx Hin.
    induction pf as [|line rest IH]; intros ctx Hin.
    - simpl. exact Hin.
    - simpl. apply IH. apply In_there. exact Hin.
  Qed.

  Lemma last_opt_in_extend_ctx :
    forall (ctx : list Form) (pf : Proof) (phi : Form),
      last_opt pf = Some phi ->
      In phi (extend_ctx ctx pf).
  Proof.
    intros ctx pf phi Hlast.
    revert ctx phi Hlast.
    induction pf as [|line rest IH]; intros ctx phi Hlast.
    - simpl in Hlast. discriminate Hlast.
    - destruct rest as [|r rs].
      + simpl in Hlast. inversion Hlast. subst. simpl. apply In_here.
      + simpl in Hlast. simpl. apply IH with (ctx := cons line ctx). exact Hlast.
  Qed.

  Lemma last_opt_app :
    forall (pf1 pf2 : Proof) (phi : Form),
      last_opt pf2 = Some phi ->
      last_opt (pf1 ++ pf2) = Some phi.
  Proof.
    induction pf1 as [|x xs IH]; intros pf2 phi H.
    - simpl. exact H.
    - simpl.
      destruct xs as [|y ys].
      + destruct pf2 as [|p ps].
        * simpl in H. discriminate H.
        * simpl. exact H.
      + simpl. apply IH. exact H.
  Qed.

  (*
    Additive closure: Prov (A->B) -> Prov A -> Prov B
  *)

  Definition compose_MP (pfAB pfA : Proof) (B : Form) : Proof :=
    (pfAB ++ pfA) ++ sing B.

  Theorem Prov_MP :
    forall (A B : Form),
      Prov (Imp A B) ->
      Prov A ->
      Prov B.
  Proof.
    intros A B [pfAB HpfAB] [pfA HpfA].
    inversion HpfAB as [pfAB0 phiAB HlastAB HlinesAB]. subst pfAB0 phiAB.
    inversion HpfA  as [pfA0  phiA  HlastA  HlinesA ]. subst pfA0  phiA.

    exists (compose_MP pfAB pfA B).
    apply Prf_intro with (phi := B).
    - unfold compose_MP. apply last_opt_app. simpl. exact (eq_refl _).
    - unfold compose_MP.

      (*
        First derive pfAB ++ pfA from nil.
      *)

      assert (HpfABpfA : Prf_lines nil (pfAB ++ pfA)).
      {
        apply Prf_lines_app with (pf1 := pfAB) (pf2 := pfA).
        - exact HlinesAB.
        - apply Prf_lines_weaken with (ctx1 := nil).
          + intros x Hin. inversion Hin.
          + exact HlinesA.
      }

      (*
        Append final line B by MP from A and (A->B) present in ctx.
      *)
      
      apply Prf_lines_app with (pf1 := pfAB ++ pfA) (pf2 := sing B).
      + exact HpfABpfA.
      + apply Prf_lines_cons_MP with (psi := A).
        * rewrite extend_ctx_app.
          apply last_opt_in_extend_ctx with (ctx := extend_ctx nil pfAB).
          exact HlastA.
        * rewrite extend_ctx_app.
          apply In_extend_ctx.
          apply last_opt_in_extend_ctx with (ctx := nil).
          exact HlastAB.
        * constructor.
  Qed.

End C_002_Additive_Laws_R.

Export C_002_Additive_Laws_R.
