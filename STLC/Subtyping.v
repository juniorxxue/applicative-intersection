Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language.

Theorem sub_reflexivity :
  forall t, sub t t.
Proof.
  induction t.
  - apply sub_Int.
  - apply sub_Top.
  - apply sub_Arrow.
    + apply IHt1.
    + apply IHt2.
  - apply sub_And.
    + apply sub_AndL. apply IHt1.
    + apply sub_AndR. apply IHt2.
Qed.

Lemma lemma_sub_and:
  forall t1 t2 t3, sub t1 (typ_and t2 t3) -> sub t1 t2 /\ sub t1 t3.
Proof.
  intros t1 t2 t3 H.
  dependent induction H; eauto.
  destruct (IHsub t2 t3); split; constructor; eauto.
  destruct (IHsub t2 t3); split.
  apply sub_AndR. assumption.
  apply sub_AndR. assumption.
Qed.

Theorem sub_transitivity :
  forall t2 t1 t3, sub t1 t2 -> sub t2 t3 -> sub t1 t3.
Proof.
  induction t2; intros; eauto.
  - induction t1; eauto.
    + inversion H.
    + inversion H.
    + inversion H; eauto.
  - induction t3; eauto.
    + induction t1; eauto.
      inversion H0.
    + inversion H0; subst. constructor. assumption.
    + inversion H0.
      constructor.
      apply IHt3_1.
      assumption.
      apply IHt3_2.
      assumption.
  - dependent induction H0; eauto.
    clear IHsub1 IHsub2.
    dependent induction H; eauto.
  - apply lemma_sub_and in H.
    destruct H.
    dependent induction H0; eauto.
Qed.
