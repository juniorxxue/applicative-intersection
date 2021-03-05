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
    + inversion H1.
    + inversion H3.
    + inversion H3.
    + inversion H_tred2; subst; eauto 3.
      * inversion H4.
      * inversion H8.
      * inversion H8.
      * assert (Heq1: (trm_anno p1 D) = (trm_anno p0 D0)).
        eapply IHHtop1; eauto 3.
        assert (Heq2: (trm_anno p2 E) = (trm_anno p3 E0)).
        eapply IHHtop2; eauto 3.
        eapply anno_equal_split in Heq1.
        destruct Heq1 as [Heq11 Heq12].
        eapply anno_equal_split in Heq2.
        destruct Heq2 as [Heq21 Heq22].
        rewrite Heq11. rewrite Heq12. rewrite Heq21. rewrite Heq22. reflexivity.
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
    eapply toplike_sub_top in H0.
    eapply sub_transitivity.
    constructor. assumption.
  - intros B0 Htyp.
    inversion Hval; subst; clear Hval.
    inversion Htyp; subst; clear Htyp.
    inversion H7; subst.
    apply sub_arrow. assumption. assumption.
  - intros B0 Htyp.
    inversion Htyp; subst; clear Htyp.
    inversion H7; subst; clear H7.
    apply sub_and_l.
    eapply IHHred. constructor. assumption.
    inversion H8; subst.
    + inversion H3.
    + apply typing_anno. constructor. assumption.
  - intros B0 Htyp.
    inversion Htyp; subst; clear Htyp.
    inversion H7; subst; clear H7.
    apply sub_and_r.
    eapply IHHred. constructor. assumption.
    inversion H8; subst.
    + inversion H3.
    + apply typing_anno. constructor. assumption.
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

Lemma tred_determinism :
  forall (v v1 v2 : trm) (A : typ),
    value v -> (exists B, typing nil nil infer_mode v B) ->
    typedred v A v1 -> typedred v A v2 -> v1 = v2.
Proof.
  intros v v1 v2 A Hval Htyp Hred1.
  generalize dependent v2.
  induction Hred1.
  - intros v2 Hred2. inversion Hred2; subst.
    + reflexivity.
    + inversion H0.
  - intros v2 Hred2.
    inversion Hred2; subst; clear Hred2.
    + inversion H0.
    + reflexivity.
    + inversion H0. contradiction.
    + symmetry. eapply tred_ord_toplike; eauto.
    + symmetry. eapply tred_ord_toplike; eauto.
    + inversion H1.
  - intros v2 Hred2.
    inversion Hred2; subst; clear Hred2.
    + inversion H3. contradiction.
    + reflexivity.
  - intros v2 Hred2.
    inversion Hred2; subst; eauto.
    + eapply tred_ord_toplike; eauto 3.
    + eapply IHHred1.
      * constructor. assumption.
      * destruct Htyp. inversion H3; subst.
        inversion H14; subst. inversion H4.
        exists A. eapply typing_anno. constructor. assumption.
      * assumption.
    + destruct Htyp. inversion H3; subst. inversion H14; subst; clear H14. inversion H4.
      assert(Hcons: consistency_spec (trm_anno p1 A) (trm_anno p2 B)).
      eapply disjoint_value_consistent; eauto 3.
      unfold consistency_spec in Hcons.
      eapply Hcons. apply Hred1. apply H12.
    + inversion H2.
  - intros v2 Hred2.
    inversion Hred2; subst; eauto.
    + eapply tred_ord_toplike; eauto 3.
    + destruct Htyp. inversion H3; subst. inversion H14; subst; clear H14. inversion H4.
      assert(Hcons: consistency_spec (trm_anno p1 A) (trm_anno p2 B)).
      eapply disjoint_value_consistent; eauto 3.
      unfold consistency_spec in Hcons.
      symmetry.
      eapply Hcons. apply H12. apply Hred1.
    + eapply IHHred1.
      * constructor. assumption.
      * destruct Htyp. inversion H3; subst.
        inversion H14; subst. inversion H4.
        exists B. eapply typing_anno. constructor. assumption.
      * assumption.
    + inversion H2.
  - intros v2 Hred2.
    inversion Hred2; subst; clear Hred2.
    + inversion H4.
    + inversion H10.
    + inversion H10.
    + assert (Heq1: (trm_anno p1 D) = (trm_anno p0 D0)).
      eapply IHHred1_1; eauto 3.
      assert (Heq2: (trm_anno p2 E) = (trm_anno p3 E0)).
      eapply IHHred1_2; eauto 3.
      eapply anno_equal_split in Heq1. destruct Heq1 as [Heq11 Heq12].
      eapply anno_equal_split in Heq2. destruct Heq2 as [Heq21 Heq22].
      rewrite Heq11. rewrite Heq12. rewrite Heq21. rewrite Heq22.
      reflexivity.
Qed.

Lemma tred_value :
  forall (v v' : trm) (A : typ),
    value v -> typedred v A v' -> value v'.
Proof.
  intros v v' A Hval Hred.
  induction Hred; eauto.
Qed.

Lemma tred_typing :
  forall (v v' : trm) (A : typ),
    value v ->
    (exists (B : typ), typing nil nil infer_mode v B) ->
    typedred v A v' ->
    (exists (C : typ), typing nil nil infer_mode v' C).
Proof.
  intros v v' A Hval Htyp Hred.
  induction Hred; eauto.
  - destruct Htyp.
    inversion H2; subst. inversion H7; subst.
    exists (typ_arrow A D). apply typing_anno; eauto 3.

Lemma papp_determinism :
  forall (v1 v2 e1 e2 : trm),
    value v1 -> value v2 ->
    (exists (A : typ), typing nil nil infer_mode v1 A) ->
    (exists (B : typ), typing nil nil infer_mode v2 B) ->
    papp v1 v2 e1 -> papp v1 v2 e2 -> e1 = e2.
Proof.
  intros v1 v2 e1 e2 Hval1 Hval2 Htyp1 Htyp2 Hp1.
  generalize dependent e2.
  induction Hp1.
  - intros e2 Hp2. inversion Hp2. reflexivity.
  - intros e2 Hp2. inversion Hp2. reflexivity.
  - intros e2 Hp2. inversion Hp2; subst.
    assert (Hequal: v' = v'0).
    eapply tred_determinism; eauto 3.
    rewrite Hequal. reflexivity.
  - intros e2 Hp2. inversion Hp2; subst; clear Hp2.
    apply IHHp1.
    + eapply tred_value. apply Hval1. apply H0.
    + apply Hval2.
    +


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
  - intros A0 Htyp e2 Hred2.
    inversion Hred2; subst.
Admitted.
