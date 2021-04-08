Require Import Coq.Program.Equality.
Require Import Language Notations Auxiliaries Subtyping.
Require Import Strings.String.

Set Printing Parentheses.

Lemma tred_ord_toplike : forall (e e' : trm) (A : typ),
    ordinary A -> toplike A -> typedred e A e' -> e' = (trm_anno trm_top typ_top).
Proof.
  intros e e' A H_ord H_top H_tred.
  dependent induction H_tred; subst; eauto.
  - inversion H_top.
  - inversion H_top. contradiction.
  - inversion H_ord.
Qed.

Lemma tred_toplike :
  forall (A : typ),
    toplike A -> forall e1 e2 e1' e2' : trm, typedred e1 A e1' -> typedred e2 A e2' -> e1' = e2'.
Proof.
  intros A Htop.
  dependent induction Htop; intros e1 e2 e1' e2' H_tred1 H_tred2.
  - eapply tred_ord_toplike in H_tred1. eapply tred_ord_toplike in H_tred2.
    rewrite H_tred1. rewrite H_tred2. reflexivity.
    constructor. constructor. constructor. constructor.
  - inversion H_tred1; subst; eauto 3.
    + inversion H0.
    + inversion H0.
    + inversion H0.
    + inversion H_tred2; subst; eauto 3.
      * inversion H0.
      * inversion H0.
      * inversion H0.
      * assert (Heq1: v1 = v0).
        eapply IHHtop1; eauto 3.
        assert (Heq2: v2 = v3).
        eapply IHHtop2; eauto 3.
        rewrite Heq1. rewrite Heq2. reflexivity.
  - assert (HAB: toplike (typ_arrow A B)).
    constructor. assumption.
    eapply tred_ord_toplike in H_tred2; eauto.
    eapply tred_ord_toplike in H_tred1; eauto.
    rewrite H_tred1. rewrite H_tred2. reflexivity.
Qed.

Lemma toplike_sub_top :
  forall (A : typ),
    toplike A <-> sub typ_top A.
Proof.
  intro A. split.
  - intro H. induction H.
    + constructor.
    + constructor. assumption. assumption.
    + constructor. assumption.
  - intro H. induction A; eauto.
    + inversion H; subst; eauto.
    + inversion H; subst. constructor.
      apply IHA2. assumption.
    + constructor; inversion H; subst.
      apply IHA1. assumption.
      apply IHA2. assumption.
Qed.

Lemma tred_sub :
  forall (A B : typ) (v1 v2 : trm),
    value v1 -> typedred v1 A v2 ->
    typing nil nil infer_mode v1 B ->
    sub B A.
Proof.
  intros A B v1 v2 Hval Hred Htyp.
  generalize dependent B.
  induction Hred; eauto.
  - intros B Htyp.
    inversion Htyp; subst.
    inversion H3; subst. constructor.
  - intros B Htyp.
    eapply toplike_sub_top in H.
    eapply sub_transitivity; eauto 3.
  - intros B0 Htyp.
    inversion Hval; subst; clear Hval.
    inversion Htyp; subst; clear Htyp.
    inversion H7; subst; clear H7.
    eapply sub_arrow; eauto 3.
  - intros B0 Htyp.
    inversion Hval; subst; clear Hval.
    inversion Htyp; subst; clear Htyp.
    + apply sub_and_l.
      eapply IHHred; eauto 3.
    + apply sub_and_l.
      eapply IHHred; eauto 3.
  - intros B0 Htyp.
    inversion Hval; subst; clear Hval.
    inversion Htyp; subst; clear Htyp.
    + apply sub_and_r.
      eapply IHHred; eauto 3.
    + apply sub_and_r.
      eapply IHHred; eauto 3.
Qed.

Lemma disjoint_value_consistent :
  forall (A B : typ) (v1 v2 : trm),
    disjoint_spec A B -> value v1 -> value v2 ->
    typing nil nil infer_mode v1 A ->
    typing nil nil infer_mode v2 B ->
    consistency_spec v1 v2.
Proof.
  intros A B v1 v2 Hdis Hv1 Hv2 Htyp1 Htyp2.
  unfold consistency_spec.
  intros A0 e1' e2'. intros Hred1 Hred2.
  assert (Hsub1: sub A A0).
  eapply tred_sub. apply Hv1. apply Hred1. apply Htyp1.
  assert (Hsub2: sub B A0).
  eapply tred_sub. apply Hv2. apply Hred2. apply Htyp2.
  assert (Htop : toplike A0).
  unfold disjoint_spec in Hdis.
  apply Hdis. assumption. assumption.
  eapply tred_toplike. apply Htop. apply Hred1. apply Hred2.
Qed.

Lemma consistent_value_disjoint :
  forall (A B : typ) (v1 v2 : trm),
    value v1 -> value v2 ->
    consistency_spec v1 v2 ->
    typing nil nil infer_mode v1 A ->
    typing nil nil infer_mode v2 B ->
    disjoint_spec A B.
Proof.
Admitted.

Lemma tred_determinism :
  forall (v v1 v2 : trm) (A : typ),
    value v -> (exists B, typing nil nil infer_mode v B) ->
    typedred v A v1 -> typedred v A v2 -> v1 = v2.
Proof.
  intros v v1 v2 A Hval Htyp Hred1.
  generalize dependent v2.
  induction Hred1.
  - intros v2 Hred2.
    inversion Hred2; subst.
    + reflexivity.
    + inversion H.
  - intros v2 Hred2.
    inversion Hred2; subst; clear Hred2; eauto.
    + inversion H.
    + inversion H. contradiction.
    + symmetry. eapply tred_ord_toplike; eauto.
    + symmetry. eapply tred_ord_toplike; eauto.
    + inversion H0.
  - intros v2 Hred2.
    inversion Hred2; subst; clear Hred2.
    + inversion H2. contradiction.
    + reflexivity.
  - intros v0 Hred2.
    inversion Hred2; subst; eauto.
    + eapply tred_ord_toplike; eauto 3.
    + eapply IHHred1; eauto.
      * inversion Hval; assumption.
      * destruct Htyp. inversion H0; subst.
        exists A0. assumption.
        exists A0. assumption.
    + destruct Htyp.
      inversion H0; subst.
      * inversion Hval; subst; clear Hval.
        assert (Hcons: consistency_spec v1 v2).
        eapply disjoint_value_consistent; eauto 3.
        unfold consistency_spec in Hcons.
        eapply Hcons; eauto 3.
      * unfold consistency_spec in H10.
        eapply H10; eauto 3.
    + inversion H.
  - intros v0 Hred2.
    inversion Hred2; subst; eauto.
    + eapply tred_ord_toplike; eauto 3.
    + destruct Htyp.
      inversion H0; subst; eauto.
      * inversion Hval; subst; clear Hval.
        assert(Hcons: consistency_spec v1 v2).
        eapply disjoint_value_consistent; eauto 3.
        unfold consistency_spec in Hcons.
        symmetry. eapply Hcons; eauto 3.
      * unfold consistency_spec in H10.
        symmetry. eapply H10; eauto 3.
    + inversion Hval; subst; clear Hval.
      eapply IHHred1.
      * assumption.
      * destruct Htyp. inversion H0; subst.
        exists B. assumption.
        exists B. assumption.
      * assumption.
    + inversion H.
  - intros v0 Hred2.
    inversion Hred2; subst; clear Hred2.
    + inversion H0.
    + inversion H0.
    + inversion H0.
    + assert (Heq1: v1 = v3).
      eapply IHHred1_1; eauto 3.
      assert (Heq2: v2 = v4).
      eapply IHHred1_2; eauto 3.
      rewrite Heq1. rewrite Heq2. reflexivity.
Qed.

Lemma tred_value :
  forall (v v' : trm) (A : typ),
    value v -> typedred v A v' -> value v'.
Proof.
  intros v v' A Hval Hred.
  induction Hred; eauto.
  + apply IHHred. inversion Hval; eauto.
  + apply IHHred. inversion Hval; eauto.
Qed.

Lemma tred_transitivity : forall (v1 v2 v3 : trm) (A B : typ),
    value v1 -> typedred v1 A v2 -> typedred v2 B v3 -> typedred v1 B v3.
Proof.
  intros v1 v2 v3 A B Hval Hred1 Hred2.
  generalize dependent v3.
  generalize dependent B.
  dependent induction Hred1; eauto.
  - intros B v3 Hred2. dependent induction Hred2; eauto.
  - intros B0 v3 Hred2. dependent induction Hred2; eauto.
    + constructor. assumption. assumption.
      pose proof (sub_transitivity D B D0) as Hsub.
      eapply Hsub; eauto 3.
  - intros B v3 Hred2.
    inversion Hval; subst; clear Hval.
    induction Hred2; eauto.
  - intros B v3 Hred2. inversion Hval; subst; clear Hval.
    induction Hred2; eauto.
  - intros B0 v0 Hred2.
    generalize dependent v0.
    induction B0; intros v0 Hred2; eauto.
    + inversion Hred2; subst; clear Hred2; eauto.
    + inversion Hred2; subst; clear Hred2; eauto.
    + inversion Hred2; subst; clear Hred2; eauto.
    + inversion Hred2; subst; clear Hred2; eauto.
Qed.

Lemma tred_consistency :
  forall (v v1 v2 : trm) (A B C : typ),
    value v -> typing nil nil infer_mode v C ->
    typedred v A v1 ->
    typedred v B v2 ->
    consistency_spec v1 v2.
Proof.
  intros v v1 v2 A B C Hval Htyp Hred1 Hred2.
  unfold consistency_spec.
  intros D v1' v2' Hred1' Hred2'.
  assert (Htrans1: typedred v D v1').
  eapply tred_transitivity. apply Hval. apply Hred1. apply Hred1'.
  assert (Htrans2: typedred v D v2').
  eapply tred_transitivity. apply Hval. apply Hred2. apply Hred2'.
  eapply tred_determinism; eauto 3.
Qed.

Lemma tred_typing :
  forall (v v' : trm) (A : typ),
    value v ->
    (exists (B : typ), typing nil nil infer_mode v B) ->
    typedred v A v' ->
    (exists (C : typ), typing nil nil infer_mode v' C).
Proof.
  intros v v' A Hval Htyp Hred.
  induction Hred.
  - exists typ_int. constructor; eauto 3.
  - exists typ_top. constructor; eauto 3.
  - destruct Htyp.
    inversion H2; subst.
    inversion H7; subst.
    exists (typ_arrow A D).
    eapply typing_anno; eauto 3.
    (* so we need checked subsumption here *)
    assert (Hsub: sub (typ_arrow A B) (typ_arrow A D)).
    apply sub_arrow. apply sub_reflexivity. assumption.
    eapply typing_sub_check. apply H8. apply Hsub.
  - apply IHHred. inversion Hval; subst. assumption.
    destruct Htyp. inversion H0; subst.
    + exists A0. assumption.
    + exists A0. assumption.
  - apply IHHred. inversion Hval; subst. assumption.
    destruct Htyp. inversion H0; subst.
    + exists B. assumption.
    + exists B. assumption.
  - assert (Htypl: exists (D : typ), typing nil nil infer_mode v1 D).
    apply IHHred1. assumption. assumption.
    assert (Htypr: exists (E : typ), typing nil nil infer_mode v2 E).
    apply IHHred2. assumption. assumption.
    destruct Htypl. destruct Htypr.
    assert(Hval1: value v1). eapply tred_value. apply Hval. apply Hred1.
    assert(Hval2: value v2). eapply tred_value. apply Hval. apply Hred2.
    exists (typ_and x x0). apply typing_merge_value; eauto 3.
    (* well typed value *)
    destruct Htyp.
    eapply tred_consistency.
    + apply Hval.
    + apply H1.
    + apply Hred1.
    + apply Hred2.
Qed.

Lemma papp_determinism :
  forall (v1 v2 e1 e2 : trm),
    value v1 -> value v2 ->
    (exists (A : typ), typing nil nil infer_mode v1 A) ->
    (exists (B : typ), typing nil nil infer_mode v2 B) ->
    papp v1 v2 e1 -> papp v1 v2 e2 -> e1 = e2.
Proof.
  intros v1 v2 e1 e2 Hval1 Hval2 Htyp1 Htyp2 Hp1.
  generalize dependent e2.
  dependent induction Hp1.
  - intros e2 Hp2. inversion Hp2. reflexivity.
  - intros e2 Hp2. inversion Hp2. reflexivity.
  - intros e2 Hp2. inversion Hp2; subst.
    assert (Hequal: v' = v'0).
    eapply tred_determinism; eauto 3.
    rewrite Hequal. reflexivity.
  - intros e2 Hp2.
    apply IHHp1; eauto.
    + eapply tred_value. apply Hval1. apply H2.
    + eapply tred_typing. apply Hval1. apply Htyp1. apply H2.
    +
      dependent destruction H0.
      dependent destruction H1.
      * dependent destruction H2.

      inversion H1; subst.
Admitted.

Lemma app_check_typing :
  forall (e1 e2 : trm) (A : typ),
    typing nil nil check_mode (trm_app e1 e2) A ->
    (exists B, typing nil nil infer_mode e1 B) /\
    (exists C, typing nil nil infer_mode e2 C).
Proof.
Admitted.

Lemma value_cannot_step_further :
  forall (v : trm),
    value v -> forall (e : trm), not (step v e).
Proof.
  intros v Hval.
  induction v.
  - inversion Hval.
  - inversion Hval.
  - inversion Hval.
  - inversion Hval.
  - unfold not. intros. inversion H.
  - inversion Hval.
  - inversion Hval; subst.
    intros. unfold not. intros.
    inversion H; subst.
    + eapply IHv1; eauto 3.
    + eapply IHv2; eauto 3.
  - inversion Hval; subst; clear Hval.
    induction H0.
    + intros. unfold not. intros.
      inversion H; subst.
      * inversion H2.
      * apply H2. constructor. constructor.
    + intros. unfold not. intros.
      inversion H; subst.
      * inversion H2.
      * apply H2. constructor. constructor.
    + intros. unfold not. intros.
      inversion H; subst; clear H.
      Focus 2.
      * apply H2. constructor. constructor.
      * (* that's the problem *)
        inversion H4; subst.
Admitted.

Lemma step_determinism :
  forall (e e1 e2 : trm) (A : typ),
    typing nil nil check_mode e A ->
    step e e1 -> step e e2 -> e1 = e2.
Proof.
  intros e e1 e2 A Htyp Hred1.
  generalize dependent e2.
  generalize dependent A.
  induction Hred1.
  - intros A Htyp e2 Hred2.
    inversion Hred2; subst.
    reflexivity.
  - intros A Htyp e2 Hred2.
    inversion Hred2; subst.
    apply app_check_typing in Htyp. destruct Htyp as [Htyp1 Htyp2].
    + eapply papp_determinism.
      apply H. apply H0.
      apply Htyp1. apply Htyp2. apply H1. apply H7.
    + (* value cannot step further *)
