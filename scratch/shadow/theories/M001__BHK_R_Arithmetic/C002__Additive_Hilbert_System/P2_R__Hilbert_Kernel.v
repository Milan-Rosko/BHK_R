(* P2_R__Hilbert_Kernel.v *)

From Coq Require Import Init.Logic.
From ATP.C002 Require Import P1_S__Kernel_Spec.

Set Implicit Arguments.
Unset Strict Implicit.

Module C_002_HilbertKernel_R.

  Import C_002_Prelim.

  (*
    Object language.
  *)

  Inductive Form : Type :=
    | F_Bot : Form
    | F_Imp : Form -> Form -> Form.

  Definition Imp (A B : Form) : Form := F_Imp A B.
  Definition Bot : Form := F_Bot.

  (*
    Membership over local lists
  *)

  Inductive In {A : Type} (x : A) : list A -> Prop :=
    | In_here  : forall xs, In x (cons x xs)
    | In_there : forall y xs, In x xs -> In x (cons y xs).

  (*
    Boolean combinators (local bool)
  *)

  Definition orb (b1 b2 : bool) : bool :=
    match b1 with true => true | false => b2 end.

  Definition andb (b1 b2 : bool) : bool :=
    match b1 with true => b2 | false => false end.

  Lemma andb_true_elim :
    forall b1 b2, andb b1 b2 = true -> b1 = true /\ b2 = true.
  Proof.
    intros b1 b2 H. destruct b1.
    - simpl in H. split; [exact (eq_refl _)| exact H].
    - simpl in H. discriminate H.
  Qed.

  Lemma orb_true_elim :
    forall b1 b2, orb b1 b2 = true -> b1 = true \/ b2 = true.
  Proof.
    intros b1 b2 H. destruct b1.
    - left. exact (eq_refl _).
    - right. exact H.
  Qed.

  (*
    Boolean equality for formulas
  *)

  Fixpoint form_eqb (A B : Form) : bool :=
    match A, B with
    | F_Bot, F_Bot => true
    | F_Imp A1 A2, F_Imp B1 B2 =>
        andb (form_eqb A1 B1) (form_eqb A2 B2)
    | _, _ => false
    end.

  Lemma form_eqb_refl : forall A, form_eqb A A = true.
  Proof.
    induction A as [|A1 IH1 A2 IH2].
    - simpl. exact (eq_refl _).
    - simpl. rewrite IH1. exact IH2.
  Qed.

  Lemma form_eqb_true_eq : forall A B, form_eqb A B = true -> A = B.
  Proof.
    induction A as [|A1 IH1 A2 IH2]; intros B H.
    - destruct B; [exact (eq_refl _)| simpl in H; discriminate H].
      (* 'Hilbert looks like the Architect' *)
    - destruct B; [simpl in H; discriminate H|].
      simpl in H.
      apply andb_true_elim in H as [H1 H2].
      apply IH1 in H1; subst.
      apply IH2 in H2; subst.
      exact (eq_refl _).
  Qed.

  (*
    K, S, EFQ
  *)

  Inductive Ax : Form -> Prop :=
    | Ax_K   : forall A B, Ax (Imp A (Imp B A))
    | Ax_S   : forall A B C,
        Ax (Imp (Imp A (Imp B C)) (Imp (Imp A B) (Imp A C)))
    | Ax_EFQ : forall A, Ax (Imp Bot A).

  (*
    Boolean axiom recognizers
  *)

  Definition is_K (phi : Form) : bool :=
    match phi with
    | F_Imp A (F_Imp _ A') => form_eqb A A'
    | _ => false
    end.

  Definition is_EFQ (phi : Form) : bool :=
    match phi with
    | F_Imp F_Bot _ => true
    | _ => false
    end.

  Definition is_S (phi : Form) : bool :=
    match phi with
    | F_Imp (F_Imp A (F_Imp B C))
            (F_Imp (F_Imp A1 B1) (F_Imp A2 C2)) =>
        andb (andb (form_eqb A A1) (form_eqb A A2))
             (andb (form_eqb B B1) (form_eqb C C2))
    | _ => false
    end.

  Definition is_axiom (phi : Form) : bool :=
    orb (is_EFQ phi) (orb (is_K phi) (is_S phi)).

  Lemma is_K_sound : forall phi, is_K phi = true -> Ax phi.
  Proof.
    intros phi H.
    destruct phi as [|A R]; simpl in H; try discriminate H.
    destruct R as [|B A']; simpl in H; try discriminate H.
    apply form_eqb_true_eq in H; subst.
    apply Ax_K.
  Qed.

  Lemma is_EFQ_sound : forall phi, is_EFQ phi = true -> Ax phi.
  Proof.
    intros phi H. destruct phi as [|L R]; simpl in H; try discriminate H.
    destruct L; simpl in H; try discriminate H.
    apply Ax_EFQ.
  Qed.

  Lemma is_S_sound : forall phi, is_S phi = true -> Ax phi.
  Proof.
    intros phi H.
    destruct phi as [|L R]; simpl in H; try discriminate H.
    destruct L as [|A LR]; simpl in H; try discriminate H.
    destruct LR as [|B C]; simpl in H; try discriminate H.
    destruct R as [|R1 R2]; simpl in H; try discriminate H.
    destruct R1 as [|A1 B1]; simpl in H; try discriminate H.
    destruct R2 as [|A2 C2]; simpl in H; try discriminate H.
    apply andb_true_elim in H as [Hleft Hright].
    apply andb_true_elim in Hleft as [HA1 HA2].
    apply andb_true_elim in Hright as [HB1 HC2].
    apply form_eqb_true_eq in HA1; subst A1.
    apply form_eqb_true_eq in HA2; subst A2.
    apply form_eqb_true_eq in HB1; subst B1.
    apply form_eqb_true_eq in HC2; subst C2.
    apply Ax_S.
  Qed.

  Lemma is_axiom_sound : forall phi, is_axiom phi = true -> Ax phi.
  Proof.
    intros phi H.
    unfold is_axiom in H.
    apply orb_true_elim in H as [HE|Hrest].
    - apply is_EFQ_sound. exact HE.
    - apply orb_true_elim in Hrest as [HK|HS].
      + apply is_K_sound. exact HK.
      + apply is_S_sound. exact HS.
  Qed.

  (*
    Proof scripts: linear lists of formulas
  *)

  Definition Proof : Type := list Form.

  (*
    Boolean list search + soundness
  *)

  Fixpoint existsb {A : Type} (p : A -> bool) (xs : list A) : bool :=
    match xs with
    | nil => false
    | cons x xs' => orb (p x) (existsb p xs')
    end.

  Lemma existsb_sound :
    forall (A : Type) (p : A -> bool) (xs : list A),
      existsb p xs = true ->
      exists x : A, In x xs /\ p x = true.
  Proof.
    intros A p xs H.
    induction xs as [|x xs IH].
    - simpl in H. discriminate H.
    - simpl in H.
      unfold orb in H.
      destruct (p x) eqn:Px.
      + exists x. split; [apply In_here| exact Px].
      + specialize (IH H).
        destruct IH as [y [Hyin Hyp]].
        exists y. split; [apply In_there; exact Hyin| exact Hyp].
  Qed.

  (*
    MP witness: ctx contains psi and (psi -> phi)
  *)

  Definition mp_witness (ctx : list Form) (phi : Form) : bool :=
    existsb
      (fun psi =>
         existsb
           (fun chi =>
              match chi with
              | F_Imp X Y =>
                  andb (form_eqb X psi) (form_eqb Y phi)
              | _ => false
              end)
           ctx)
      ctx.

  Lemma mp_witness_sound :
    forall (ctx : list Form) (phi : Form),
      mp_witness ctx phi = true ->
      exists psi : Form, In psi ctx /\ In (Imp psi phi) ctx.
  Proof.
    intros ctx phi Hmw.
    unfold mp_witness in Hmw.
    pose proof (existsb_sound
                  (A := Form)
                  (p := fun psi =>
                          existsb
                            (fun chi =>
                               match chi with
                               | F_Imp X Y =>
                                   andb (form_eqb X psi) (form_eqb Y phi)
                               | _ => false
                               end)
                            ctx)
                  (xs := ctx)
                  Hmw) as Hpsi.
    destruct Hpsi as [psi [HinPsi Hinner]].

    pose proof (existsb_sound
                  (A := Form)
                  (p := fun chi =>
                          match chi with
                          | F_Imp X Y =>
                              andb (form_eqb X psi) (form_eqb Y phi)
                          | _ => false
                          end)
                  (xs := ctx)
                  Hinner) as Hchi.
    destruct Hchi as [chi [HinChi Hchi_ok]].

    destruct chi as [|X Y].
    - simpl in Hchi_ok. discriminate Hchi_ok.
    - simpl in Hchi_ok.
      apply andb_true_elim in Hchi_ok as [HX HY].
      apply form_eqb_true_eq in HX; subst X.
      apply form_eqb_true_eq in HY; subst Y.
      exists psi. split; [exact HinPsi| exact HinChi].
  Qed.

  (*
    Sequential checker
  *)

  Fixpoint check_lines (ctx : list Form) (pf : Proof) : bool :=
    match pf with
    | nil => true
    | cons line rest =>
        let ok_line := orb (is_axiom line) (mp_witness ctx line) in
        andb ok_line (check_lines (cons line ctx) rest)
    end.

  Fixpoint last_opt (pf : Proof) : option Form :=
    match pf with
    | nil => @None Form
    | cons x nil => Some x
    | cons _ xs => last_opt xs
    end.

  Definition check (pf : Proof) (goal : Form) : bool :=
    match last_opt pf with
    | @None _ => false
    | Some last => andb (check_lines nil pf) (form_eqb last goal)
    end.

  (*
    Prop-level derivability mirroring check_lines
  *)

  Inductive Prf_lines : list Form -> Proof -> Prop :=
    | Prf_lines_nil :
        forall ctx, Prf_lines ctx nil
    | Prf_lines_cons_Ax :
        forall ctx line rest,
          Ax line ->
          Prf_lines (cons line ctx) rest ->
          Prf_lines ctx (cons line rest)
    | Prf_lines_cons_MP :
        forall ctx psi line rest,
          In psi ctx ->
          In (Imp psi line) ctx ->
          Prf_lines (cons line ctx) rest ->
          Prf_lines ctx (cons line rest).

  Inductive Prf : Proof -> Form -> Prop :=
    | Prf_intro :
        forall pf phi,
          last_opt pf = Some phi ->
          Prf_lines nil pf ->
          Prf pf phi.

  (*
    Soundness of check_lines and check
  *)

  Lemma check_lines_sound :
    forall ctx pf,
      check_lines ctx pf = true ->
      Prf_lines ctx pf.
  Proof.
    intros ctx pf H.
    revert ctx H.
    induction pf as [|line rest IH]; intros ctx H.
    - constructor.
    - simpl in H.
      apply andb_true_elim in H as [Hok Hrest].
      unfold orb in Hok.
      destruct (is_axiom line) eqn:HAx.
      + apply Prf_lines_cons_Ax.
        * apply is_axiom_sound. exact HAx.
        * apply IH. exact Hrest.
      + pose proof (mp_witness_sound (ctx := ctx) (phi := line) Hok) as Hw.
        destruct Hw as [psi [HinPsi HinImp]].
        apply Prf_lines_cons_MP with (psi := psi).
        * exact HinPsi.
        * exact HinImp.
        * apply IH. exact Hrest.
  Qed.

  Theorem check_sound :
    forall (pf : Proof) (phi : Form),
      check pf phi = true -> Prf pf phi.
  Proof.
    intros pf phi H.
    unfold check in H.
    destruct (last_opt pf) as [last|] eqn:Hlast.
    - simpl in H.
      apply andb_true_elim in H as [Hlines Heq].
      apply form_eqb_true_eq in Heq; subst phi.
      apply Prf_intro with (phi := last).
      + exact Hlast.
      + apply check_lines_sound. exact Hlines.
    - simpl in H. discriminate H.
  Qed.

  (*
    Package the ProofKernel contract
  *)

  Definition HilbertKernel : ProofKernel :=
    {|
      C_002_Prelim.Form := Form;
      C_002_Prelim.Proof := Proof;
      C_002_Prelim.check := check;
      C_002_Prelim.Prf := Prf;
      C_002_Prelim.check_sound := check_sound
    |}.

End C_002_HilbertKernel_R.

Export C_002_HilbertKernel_R.
