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

Lemma toplike_or_not_toplike :
  forall (A : typ),
    toplike A \/ not (toplike A).
Proof.
  intros A.
  dependent induction A; eauto;
    try solve [right; intros Hcontra; inversion Hcontra].
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
