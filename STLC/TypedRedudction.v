Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language Subtyping.

Lemma tred_ord_toplike_normal : forall (e e' : trm) (A : typ),
    ordinary A -> toplike A -> typedred e A e' -> e' = trm_top.
Proof.
  intros e e' A H_ord H_top H_tred.
  dependent induction H_tred; subst; eauto.
  - inversion H_top.
  - destruct H0. inversion H_top; subst.
    assumption.
  - inversion H_ord.
Qed.

Lemma tred_toplike :
  forall (A : typ),
    toplike A -> forall e1 e2 e1' e2' : trm, typedred e1 A e1' -> typedred e2 A e2' -> e1' = e2'.
Proof.
  intros A Htop.
  dependent induction Htop; intros e1 e2 e1' e2' H_tred1 H_tred2.
  - apply tred_ord_toplike_normal with (A:=typ_top) in H_tred1; auto; subst.
    apply tred_ord_toplike_normal with (A:=typ_top) in H_tred2; auto; subst.
  - inversion H_tred1; subst; eauto.
    + inversion H1.
    + inversion H_tred2; subst; eauto; inversion H0. (* ordinary (typ_and A B) is wrong*)
    + inversion H0.
    + inversion H_tred2; subst; eauto; try (inversion H0); try (inversion H1).
      assert (Heq1: e3 = e5).
      pose proof (IHHtop1 e1 e2 e3 e5) as IHHtop1'.
      apply IHHtop1'. assumption. assumption.
      assert (Heq2: e4 = e6).
      pose proof (IHHtop2 e1 e2 e4 e6) as IHHtop2'.
      apply IHHtop2'. assumption. assumption.
      rewrite Heq1. rewrite Heq2. reflexivity.
  - assert (HAB: toplike (typ_arrow A B)).
    constructor. assumption.
    apply tred_ord_toplike_normal with (A:=(typ_arrow A B)) in H_tred2.
    apply tred_ord_toplike_normal with (A:=(typ_arrow A B)) in H_tred1.
    rewrite H_tred1. rewrite H_tred2. reflexivity.
    constructor. assumption. constructor. assumption.
Qed.

Lemma toplike_sub_top : forall (A : typ),
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

Lemma tred_to_sub: forall (e e' : trm) (A B : typ),
    value e -> typedred e A e' -> typing nil nil infer_mode e B -> sub B A.
Proof.
  intros.
  induction H0; eauto.
  - inversion H1. constructor.
  - apply toplike_sub_top in H2.
    pose proof (sub_transitivity typ_top B A) as sub_trans'.
    assert (H_sub1: sub B typ_top).
    constructor. apply sub_trans' in H_sub1. assumption. assumption.
  - inversion H.
  - inversion H; subst; clear H.
    apply IHtypedred in H5. assumption.
Admitted.

Lemma tred_transitivity : forall (e1 e2 e3: trm) (A B : typ),
    value e1 -> typedred e1 A e2 -> typedred e2 B e3 -> typedred e1 B e3.
Proof.
  intros e1 e2 e3 A B Hval Hred1 Hred2.
  dependent induction Hred1; eauto.
  - dependent induction Hred2; eauto.
    + constructor. assumption. assumption. assumption.
    + assert (Htop : trm_top = trm_top).
      reflexivity. constructor.
      * apply IHHred2_1 in Htop. assumption.
      * apply IHHred2_2 in Htop. assumption.
  - dependent induction Hred2; eauto.
    + constructor. constructor. assumption. assumption.
    + constructor. assumption. assumption. assumption.
      pose proof (sub_transitivity D B0 D0) as Hsub.
      apply Hsub in H2. assumption. assumption.
    + constructor.
      * pose proof (IHHred2_1 D) as IHHred2_1'.
        apply IHHred2_1'. assumption. assumption. assumption. assumption. assumption.
        reflexivity.
      * pose proof (IHHred2_2 D) as IHHred2_2'.
        apply IHHred2_2'. assumption. assumption. assumption. assumption. assumption.
        reflexivity.
  - inversion Hval; subst; clear Hval. constructor. apply IHHred1. assumption. assumption.
    dependent induction Hred2; eauto.
Admitted.