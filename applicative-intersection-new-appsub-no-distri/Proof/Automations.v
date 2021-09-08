Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language LibTactics.

Lemma ptype_construction :
  forall (A B : typ) (v1 v2 : trm),
    ptype v1 A -> ptype v2 B ->
    ptype (trm_merge v1 v2) (typ_and A B).
Proof.
  intros.
  eapply ptype_merge; eauto.
Qed.

Ltac inversion_ordinary :=
  match goal with
  | [H: ordinary (_ & _) |- _] => inversion H
  end.

Ltac inversion_toplike :=
  match goal with
  | [H: toplike typ_int |- _] => inversion H
  | [H1: toplike (typ_arrow ?A ?B), H2: not (toplike ?B) |- _] => (inversion H1; contradiction)
  end.

Ltac simpl_as :=
  match goal with
  | [H: appsub nil ?A ?B |- _] => dependent destruction H
  end.

Lemma toplike_false :
  forall (A : typ),
    toplike A -> sub A typ_int -> False.
Proof.
  induction A; introv Htl Hsub; try solve [inversion Htl | inversion Hsub].
  dependent destruction Htl.
  dependent destruction Hsub; eauto.
Qed.

Ltac inversion_toplike_sub :=
  match goal with
  | [H1: toplike ?A, H2: sub ?A typ_int |- _] => (eapply toplike_false in H1; eauto; inversion H1)
  end.


Lemma toplike_or_not_toplike :
  forall (A : typ),
    toplike A \/ not (toplike A).
Proof.
  intros A.
  dependent induction A; eauto; try solve [right; intros Hcontra; inversion Hcontra].
  - destruct IHA1; destruct IHA2; eauto;
      try solve [right; intros H1; dependent destruction H1; contradiction].
  - destruct IHA1; destruct IHA2; eauto;
      try solve [right; intros H1; dependent destruction H1; contradiction].
Qed.

Lemma pvalue_cannot_be_value :
  forall (e : trm),
    pvalue e -> value e -> False.
Proof.
  intros e Hp Hv.
  dependent destruction Hp; try solve [inversion Hv].
Qed.

Lemma pvalue_or_not_pvalue :
  forall (e : trm),
    pvalue e \/ not (pvalue e).
Proof.
  intros e.
  dependent induction e; eauto; try solve [right; intro H; inversion H].
Qed.

Lemma value_or_not_value :
  forall (e : trm),
    value e \/ not (value e).
Proof.
  intros e.
  dependent induction e; eauto; try solve [right; unfold not; intros; inversion H].
  - destruct IHe1; destruct IHe2; eauto;
      try solve [right; unfold not; intros; dependent destruction H1; contradiction].
  - destruct IHe.
    + right. unfold not. intros. dependent destruction H0.
      eapply pvalue_cannot_be_value; eauto.
    + assert (Hp: pvalue e \/ not (pvalue e)).
      eapply pvalue_or_not_pvalue.
      destruct Hp.
      * left. constructor. assumption.
      * right. unfold not. intros. dependent destruction H1. contradiction.
Qed.

Hint Resolve value_or_not_value : core.

Lemma rvalue_or_not_rvalue :
  forall (e : trm),
    rvalue e \/ not (rvalue e).
Proof.
  intros e.
  dependent induction e; eauto.
  - right. intros H. inversion H. inversion H0.
  - right. intros H. inversion H. inversion H0.
  - right. intros H. inversion H. inversion H0.
  - right. intros H. inversion H. inversion H0.
  - destruct IHe1; destruct IHe2; eauto.
    + admit.
Abort.
