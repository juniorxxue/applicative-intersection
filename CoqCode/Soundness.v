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
  - apply typing_anno; eauto 3.
    dependent destruction Htyp.
    inversion H0.
    dependent destruction Htyp.
    eapply typing_sub_check; eauto.
  - dependent destruction Hv.
    dependent destruction Htyp.
    inversion H0.
    dependent destruction Htyp.
    + apply IHHred; eauto 3.
      eapply typing_sub.
      eapply Htyp1.
      eapply tred_sub. apply Hv1. apply Hred. apply Htyp1.
    + apply IHHred; eauto 3.
      eapply typing_sub.
      eapply Htyp1.
      eapply tred_sub. apply Hv1. apply Hred. apply Htyp1.
  - dependent destruction Hv.
    dependent destruction Htyp.
    inversion H0.
    dependent destruction Htyp.
    + apply IHHred; eauto 3.
      eapply typing_sub.
      apply Htyp2.
      eapply tred_sub. apply Hv2. apply Hred. apply Htyp2.
    + apply IHHred; eauto 3.
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
      * dependent destruction H0; try solve [inversion Hv].
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
  intros v vl e A B S Hv Hvl Hp Htyp1 Htyp2.
  dependent induction Htyp1.
  - dependent induction Htyp2; try solve [inversion Hv | inversion Hvl].
  - dependent induction Htyp2; try solve [inversion Hv | inversion Hvl].
  - dependent induction Htyp2; try solve [inversion Hv | inversion Hvl].
    + clear IHHtyp1. clear IHHtyp2.
      dependent destruction H.
      admit.
    + admit.
  - dependent induction Htyp2; try solve [inversion Hv | inversion Hvl].
  - dependent induction Htyp2; try solve [inversion Hv | inversion Hvl].
    + admit.
    + admit.
  - dependent induction Htyp2; try solve [inversion Hv | inversion Hvl].
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
  dependent induction Htyp1.
  - inversion Hv.
  - eapply pvalue_cannot_be_value in H0; eauto 3. inversion H0.
  - inversion Hv.
  - dependent induction Htyp2; try solve [inversion Hv | inversion Hvl].
    + clear IHHtyp1. clear IHHtyp2.
      dependent destruction H0.
      dependent destruction Hp.
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
  - dependent destruction H0.
    + dependent destruction Hred.
      eapply typing_sub; eauto.
    + dependent destruction Hred. 
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
