Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language Subtyping Auxiliaries Notations Deterministic Automations.

Lemma typing_check_merge_distro :
  forall (v : trm) (A B : typ),
    typing nil nil check_mode v (typ_and A B) ->
    (typing nil nil check_mode v A) /\ (typing nil nil check_mode v B).
Proof.
  intros. split.
  - eapply typing_sub_check.
    eapply H. apply sub_and_l. eapply sub_reflexivity.
  - eapply typing_sub_check.
    eapply H. apply sub_and_r. eapply sub_reflexivity.
Qed.

Lemma sub_type_and_distro :
  forall (A B C : typ),
    ordinary C ->
    sub (typ_and A B) C ->
    sub A C \/ sub B C.
Proof.
  intros.
  dependent induction H0; eauto.
  inversion H.
Qed.

Lemma typing_int_checked_by_toplike :
  forall (n : nat) (A : typ),
    toplike A ->
    typing nil nil check_mode (trm_nat n) A.
Admitted.

Theorem tred_preservation :
  forall (v v' : trm) (A: typ),
    value v ->
    typing nil nil check_mode v A ->
    typedred v A v' ->
    typing nil nil infer_mode v' A.
Proof.
  intros v v' A Hv Htyp Hred.
  dependent induction Hred.
  - eapply typing_anno; eauto.
  - eapply typing_anno; eauto.
    eapply typing_int_checked_by_toplike; eauto.
  - apply typing_anno; eauto.
    dependent destruction Htyp.
    dependent destruction Htyp.
    eapply typing_sub_check; eauto.
  - dependent destruction Hv.
    dependent destruction Htyp.
    dependent destruction Htyp.
    + apply IHHred; eauto.
      eapply typing_sub.
      eapply Htyp1.
      eapply tred_sub. apply Hv1. apply Hred. apply Htyp1.
    + apply IHHred; eauto.
      eapply typing_sub.
      eapply Htyp1.
      eapply tred_sub. apply Hv1. apply Hred. apply Htyp1.
  - dependent destruction Hv.
    dependent destruction Htyp.
    dependent destruction Htyp.
    + apply IHHred; eauto.
      eapply typing_sub.
      apply Htyp2.
      eapply tred_sub. apply Hv2. apply Hred. apply Htyp2.
    + apply IHHred; eauto.
      eapply typing_sub.
      apply Htyp2.
      eapply tred_sub. apply Hv2. apply Hred. apply Htyp2.
  - eapply typing_merge_value.
    + eapply tred_value; eauto.
    + eapply tred_value; eauto.
    + eapply IHHred1. assumption.
      eapply typing_check_merge_distro in Htyp. destruct Htyp.
      assumption.
    + eapply IHHred2. assumption.
      eapply typing_check_merge_distro in Htyp. destruct Htyp.
      assumption.
    + dependent destruction Htyp.
      * inversion Hv.
      * inversion Hv. 
      * eapply tred_consistency; eauto.
Qed.

Lemma papp_preservation_infer:
  forall (v vl e : trm) (A B : typ) (S : arg),
    value v -> value vl ->
    papp v vl e ->
    typing nil nil infer_mode vl A ->
    typing nil (cons A S) infer_mode v (typ_arrow A B) ->
    typing nil S infer_mode e B.
Proof.
  intros.
  dependent induction H1.
Admitted.

Lemma papp_preservation_check :
  forall (v vl e : trm) (A B : typ),
    value v -> value vl ->
    papp v vl e ->
    typing nil nil check_mode v (typ_arrow A B) ->
    typing nil nil infer_mode vl A ->
    typing nil nil check_mode e B.
Proof.
  intros v vl e A B Hv Hvl Hp Htyp1 Htyp2.
  generalize dependent A. generalize dependent B.
  dependent induction Hp; intros.
Admitted.   

Lemma appsub_typing :
  forall (e : trm) (A B : typ) (S : arg),
    typing nil nil infer_mode e A ->
    appsub S A B ->
    typing nil S infer_mode e B.
Proof.
  intros e A B S Htyp Has.
  generalize dependent  e.
  dependent induction Has; intros; eauto.
Admitted.

Theorem preservation :
  forall (e e' : trm) (A : typ) (dir : mode) (S : arg),
    typing nil S dir e A ->
    step e e' ->
    typing nil S dir e' A.
Proof.
  intros e e' A dir S Htyp Hred.
  generalize dependent e'.
  dependent induction Htyp; intros; try solve [inversion Hred].
  - dependent destruction Hred.
    eapply typing_anno; eauto.
  - dependent destruction Hred.
    + assert (Htyp2: typing nil nil infer_mode v' A).
      eapply tred_preservation; eauto.
      eapply appsub_typing; eauto.
    + eapply typing_anno. assumption.
      eapply IHHtyp; eauto.
  - dependent destruction Hred.
    + eapply papp_preservation_infer with (v:=e1) (vl:=e2); eauto.
    + eapply typing_app1; eauto.
    + eapply typing_app1; eauto.
  - dependent destruction Hred.
    + eapply papp_preservation_check with (v:=e1) (vl:=e2); eauto.
    + eapply typing_app2; eauto.
    + eapply typing_app2; eauto.
  - assert (Htyp2: typing nil nil infer_mode e' B).
    eapply IHHtyp; eauto.
    eapply typing_sub; eauto.
  - dependent destruction Hred.
    + eapply typing_merge; eauto.
    + eapply typing_merge; eauto.
  - assert (Hval: value (trm_merge v1 v2)).
    constructor; eauto.
    apply value_cannot_step_further with (e:=e') in Hval.
    destruct Hval. assumption.
  - assert (Htyp2: typing nil S infer_mode e' B).
    eapply IHHtyp; eauto.
    dependent destruction Hred.
    + eapply typing_merge_pick; eauto.
    + eapply typing_merge_pick; eauto.
Qed.

Theorem tred_progress :
  forall (v : trm) (A : typ),
    value v -> typing nil nil check_mode v A ->
    exists v', typedred v A v'.
Proof.
  intros v A Hv Htyp.
  dependent induction A.
  - dependent destruction Htyp; try solve [inversion Hv].
Admitted.

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

(* this lemma really does make sense to me *)
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

Theorem progress :
  forall (e : trm) (A : typ) (S : arg),
    typing nil S infer_mode e A ->
    value e \/ exists e', step e e'.
Proof.
  intros e A S Htyp.
  dependent induction Htyp.
  - right. exists (trm_anno (trm_nat n) typ_int).
    apply step_int_anno.
  - inversion H0.
Admitted.
