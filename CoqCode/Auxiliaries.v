Require Import Metalib.Metatheory.
Require Import Subtyping Language Notations.
Require Import Coq.Program.Equality.

Lemma anno_equal_split :
  forall (e1 e2 : trm) (A B : typ),
    (trm_anno e1 A) = (trm_anno e2 B) -> (e1 = e2) /\ (A = B).
Proof.
  intros.
  induction e1; inversion H; eauto.
Qed.

Lemma anno_equal_split2 :
  forall (e1 e2 : trm) (A B : typ),
    (e1 = e2) /\ (A = B) -> (trm_anno e1 A) = (trm_anno e2 B).
Proof.
  intros.
  destruct H.
  rewrite H0.
  rewrite H. reflexivity.
Qed.

(*aux lemma for sub_to_app *)
Lemma toplike_sub_top :
  forall (A : typ),
    sub typ_top A <-> toplike A.
Proof.
  intros A. split.
  - induction A; eauto.
    + intros. inversion H.
    + intros. dependent destruction H. constructor. auto.
    + intros. dependent destruction H. constructor.
      eapply IHA1; eauto. eapply IHA2; eauto.
  - intros. induction H; eauto.
Qed.

Lemma toplike_sub_toplike :
  forall (A B : typ),
    toplike A ->
    sub A B ->
    toplike B.
Proof.
  intros A B Htop Hsub.
  dependent induction Hsub; eauto.
  - apply tl_arrow. apply IHHsub2. inversion Htop; subst. assumption.
  - inversion Htop; subst. apply IHHsub. assumption.
  - inversion Htop; subst. apply IHHsub. assumption.
Qed.

Lemma typing_sub_check_merge :
  forall (e : trm) (A B C: typ) (T : ctx),
    typing T nil check_mode e A ->
    sub A B -> sub A C ->
    typing T nil check_mode e (typ_and B C).
Proof.
Admitted.

Lemma typing_sub_check :
  forall (T : ctx) (v : trm) (A : typ),
    typing T nil check_mode v A -> forall B,
    sub A B ->
    typing T nil check_mode v B.
Proof.
  intros T e A Htyp.
  dependent induction Htyp; intros.
  - dependent destruction H2.
    + eapply typing_abs_top; eauto.
    + eapply typing_abs_top; eauto. constructor. eapply toplike_sub_top; eauto.
    + eapply typing_abs; eauto.
      eapply sub_transitivity; eauto.
    + assert (Hchk: typing T nil check_mode (trm_abs A e) (typ_arrow B C)).
      eapply typing_abs; eauto.
      eapply typing_sub_check_merge; eauto.
  - eapply typing_abs_top; eauto. eapply toplike_sub_toplike; eauto. 
  - eapply typing_app2; eauto.
    eapply IHHtyp2; eauto.
    eapply sub_arrow; eauto.
    eapply sub_reflexivity.
  - eapply typing_sub. apply Htyp.
    eapply sub_transitivity; eauto.
Qed.

Lemma toplike_sub :
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
