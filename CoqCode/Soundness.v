Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language Subtyping Auxiliaries Notations Deterministic.

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
  - admit. (* appsub and toplike *)
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
      admit.
    + apply IHHred; eauto.
      eapply typing_sub.
      eapply Htyp1.
      admit.
  - dependent destruction Hv.
    dependent destruction Htyp.
    dependent destruction Htyp.
    + apply IHHred; eauto.
      eapply typing_sub.
      apply Htyp2.
      admit.
    + apply IHHred; eauto.
      eapply typing_sub.
      apply Htyp2.
      admit.
  - eapply typing_merge_value.
    + eapply tred_value; eauto.
    + eapply tred_value; eauto.
    + eapply IHHred1. assumption.
      admit.
    + eapply IHHred2. assumption.
      admit.
    + eapply tred_consistency; eauto.
Admitted.

Lemma papp_preservation :
  forall (r v e : trm) (A B : typ) (S : arg),
    rvalue r -> value v ->
    papp r v e ->
    typing nil nil infer_mode v A ->
    typing nil (cons A S) infer_mode r (typ_arrow A B) ->
    typing nil S infer_mode e B.
Proof.
  intros r v e A B Hr Hv Hp Htyp1 Htyp2.
  generalize dependent A.
  generalize dependent B.
  dependent induction Hp; intros.
Admitted.

Lemma papp_preservation_dir :
  forall (r v e : trm) (A B : typ) (S : arg) (dir : mode),
    rvalue r -> value v ->
    papp r v e ->
    typing nil nil infer_mode v A ->
    typing nil (cons A S) dir r (typ_arrow A B) ->
    typing nil S dir e B.
Proof.
  intros. 
Admitted.
  
Lemma papp_preservation_check :
  forall (r v e : trm) (A B : typ),
    rvalue r -> value v ->
    papp r v e ->
    typing nil nil infer_mode v A ->
    typing nil nil check_mode r (typ_arrow A B) ->
    typing nil nil check_mode e B.
Proof.
Admitted.

Theorem preservation :
  forall (e e' : trm) (A : typ) (dir : mode) (S : arg),
    typing nil S dir e A ->
    step e e' ->
    typing nil S dir e' A.
Proof.
  intros e e' A dir S Htyp Hred.
  generalize dependent e'.
  dependent induction Htyp; intros.
  - dependent destruction Hred.
    eapply typing_anno; eauto.
  - dependent destruction Hred.
    eapply typing_anno; eauto.
  - dependent destruction Hred.
  - dependent destruction Hred.
  - dependent destruction Hred.
  - dependent destruction Hred.
  - dependent destruction Hred.
    + assert (Htyp2: typing nil nil infer_mode v' A).
      eapply tred_preservation; eauto.
      admit. (* Htyp2, H *)
    + eapply typing_anno. assumption.
      eapply IHHtyp; eauto.
  - dependent destruction Hred.
    + eapply papp_preservation; eauto.
    + eapply typing_app1; eauto.
    + eapply typing_app1; eauto.
  - dependent destruction Hred.
    + eapply papp_preservation_check; eauto.
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
    + admit.
    + 
    (*
      The problem is
      reduction of merge picking appears at papp
      typing of merge picking appears at merge
     *)
Admitted.

Theorem tred_progress :
  forall (v : trm) (A : typ),
    value v -> typing nil nil check_mode v A ->
    exists v', typedred v A v'.
Proof.
  intros v A Hv Htyp.
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
  forall (e : trm) (dir : mode) (A : typ) (S : arg),
    typing nil S dir e A ->
    value e \/ exists e', step e e'.
Proof.
  intros e dir A S Htyp.
  dependent induction Htyp.
  - right. exists (trm_anno (trm_nat n) typ_int).
    apply step_int_anno.
  - right. exists (trm_anno trm_top typ_top).
    apply step_top_anno.
  - inversion H0.
  - right. admit. (* \x : A . e --> \x : A . e : A -> B ??? *)
  - right. admit.
  - right. admit.
  - destruct IHHtyp; eauto.
    + right. assert (Hv: value e); eauto.
      eapply tred_progress in H0; eauto.
      destruct H0. exists x. eapply step_anno_value; eauto.
    + destruct H0.
      assert (Hval : value (trm_anno e A) \/ not (value (trm_anno e A))).
      eapply value_or_not_value.
      destruct Hval.
      * left. assumption.
      * right. exists (trm_anno x A). eapply step_anno. assumption. assumption.
  - right. destruct IHHtyp1; destruct IHHtyp2; eauto.
    + admit. (* the diff from snow's is her system has a arrTyp relation ? *)
    + admit.
    + admit.
    + admit.
  - admit. (* same as previous one *)
  - destruct IHHtyp; eauto.
  - destruct IHHtyp1; destruct IHHtyp2; eauto.
Admitted.
(* the typing merge has some problems with reduction *)
