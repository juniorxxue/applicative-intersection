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
  - inversion Hvl.
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
  - eapply pvalue_cannot_be_value in H0; eauto 3. inversion H0.
  - inversion Hv.
  - dependent induction Htyp2; try solve [inversion Hv | inversion Hvl].
    + clear IHHtyp1. clear IHHtyp2.
      dependent destruction H0.
      dependent destruction Hp.
Admitted.

Lemma appsub_typing :
  forall (v : trm) (A B : typ) (S : arg),
    value v ->
    typing nil nil infer_mode v A ->
    appsub S A B ->
    typing nil S infer_mode v B.
Proof.
  intros v A B S Hval Htyp Has.
  dependent destruction Htyp; try solve [inversion Hval].
  - dependent destruction H.
    eapply typing_anno; eauto.
  - dependent destruction Has.
    + eapply typing_merge; eauto.
    + eapply typing_merge_pick.
      assert (Htyp: typing nil S infer_mode (trm_merge e1 e2) (typ_and A B0)).
      admit. eapply Htyp. eapply as_and_l; eauto.
    + eapply typing_merge_pick.
      assert (Htyp: typing nil S infer_mode (trm_merge e1 e2) (typ_and A B0)).
      admit. eapply Htyp. eapply as_and_r; eauto.
  - dependent destruction Has.
    + eapply typing_merge_value; eauto.
    + eapply typing_merge_pick.
      assert (Htyp: typing nil S infer_mode (trm_merge v1 v2) (typ_and A B0)).
      admit. eapply Htyp. eapply as_and_l; eauto.
    + eapply typing_merge_pick.
      assert (Htyp: typing nil S infer_mode (trm_merge v1 v2) (typ_and A B0)).
      admit. eapply Htyp. eapply as_and_r; eauto.
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
      eapply tred_value; eauto.
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

Lemma value_check_merge :
  forall (v : trm) (A B : typ),
    value v -> typing nil nil check_mode v (typ_and A B) ->
    typing nil nil check_mode v A /\
    typing nil nil check_mode v B.
Proof.
  intros v A B Hv Htyp.
  split.
  eapply typing_sub_check. eapply Htyp.
  eapply sub_and_l. eapply sub_reflexivity.
  eapply typing_sub_check. eapply Htyp.
  eapply sub_and_r. eapply sub_reflexivity.
Qed.

Lemma toplike_cannot_subtype_int :
  forall (A : typ),
    toplike A -> sub A typ_int -> False.
Proof.
  intros.
  dependent induction H; try solve [inversion H0].
  dependent destruction H1.
  eapply IHtoplike1; eauto.
  eapply IHtoplike2; eauto.
Qed.

Lemma abs_cannot_check_by_int :
  forall (A : typ) (e : trm),
    typing nil nil check_mode (trm_abs A e) typ_int -> False.
Proof.
  intros.
  dependent induction H.
  - inversion H.
  - dependent destruction H.
    dependent destruction H0.
Qed.

Theorem tred_progress :
  forall (v : trm) (A : typ),
    value v -> typing nil nil check_mode v A ->
    exists v', typedred v A v'.
Proof.
  intros v A Hv Htyp.
  dependent induction A.
  - dependent induction Hv.
    + dependent induction H.
      * dependent destruction Htyp.
        inversion H.
        dependent destruction Htyp. dependent destruction H.
        dependent destruction Htyp.
        eapply toplike_cannot_subtype_int in H; eauto. contradiction.        
        dependent destruction Htyp.
        (* how A plays a role in system *)
        admit.
      * dependent destruction Htyp.
        inversion H0.
        dependent destruction Htyp. dependent destruction H.
        assert (Hcontra: typing nil nil check_mode (trm_abs A0 e) typ_int).
        eapply typing_sub_check; eauto.
        eapply abs_cannot_check_by_int in Hcontra. contradiction.
    + dependent destruction Htyp.
      * inversion H.
      * dependent destruction Htyp.
        dependent destruction H0.
        (* case 1 *)
        assert (exists v', typedred v1 typ_int v').
        eapply IHHv1.
        eapply typing_sub; eauto.
        destruct H1. exists x. eapply tred_merge_l; eauto.
        (* case 2 *)
        assert (exists v', typedred v2 typ_int v').
        eapply IHHv2.
        eapply typing_sub; eauto.
        destruct H1. exists x. eapply tred_merge_r; eauto.
        (* the same *)
        dependent destruction H2.
        (* case 1 *)
        assert (exists v', typedred v1 typ_int v').
        eapply IHHv1.
        eapply typing_sub; eauto.
        destruct H3. exists x. eapply tred_merge_l; eauto.
        (* case 2 *)
        assert (exists v', typedred v2 typ_int v').
        eapply IHHv2.
        eapply typing_sub; eauto.
        destruct H3. exists x. eapply tred_merge_r; eauto.
  - exists (trm_anno (trm_nat 1) typ_top). eapply tred_top; eauto.
  - clear IHA1. clear IHA2.
    dependent induction Hv.
    + dependent induction H.
      * dependent destruction Htyp. inversion H0.
        dependent destruction Htyp. dependent destruction H.
        assert (Hchk: typing nil nil check_mode (trm_nat n) (typ_arrow A1 A2)).
        eapply typing_sub_check; eauto.
        dependent destruction Hchk.
        (* case 1 *)
        exists (trm_anno (trm_nat 1) (typ_arrow A1 A2)).
        eapply tred_top; eauto.
        (* case 2 *)
        dependent destruction Hchk.
        dependent destruction H1.
         exists (trm_anno (trm_nat 1) (typ_arrow A1 A2)).
         eapply tred_top; eauto. constructor. eapply toplike_sub_top; eauto.
      * dependent destruction Htyp. inversion H0.
        dependent destruction Htyp. dependent destruction H.
        dependent induction H0.
        (* case 1 *)
        exists (trm_anno (trm_nat 1) (typ_arrow A1 A2)).
        eapply tred_top; eauto. constructor. eapply toplike_sub_top; eauto.
        (* case 2 *)
        exists (trm_anno (trm_abs A0 e) (typ_arrow A1 A2)).
        eapply tred_arrow_anno; eauto.
        admit.
        (* case 3 *)
        dependent destruction Htyp.
        dependent destruction H.
        exists (trm_anno (trm_nat 1) (typ_arrow A1 A2)).
        eapply tred_top; eauto. eapply toplike_sub_toplike. eapply H. eapply H0.
        dependent destruction Htyp. dependent destruction H1.
        admit.
        (* case 4 *)
        dependent destruction Htyp.
        dependent destruction H.
        exists (trm_anno (trm_nat 1) (typ_arrow A1 A2)).
        eapply tred_top; eauto. eapply toplike_sub_toplike. eapply H1. eapply H0.
        dependent destruction Htyp. dependent destruction H1.
        admit.
    + dependent destruction Htyp.
      * exists (trm_anno (trm_nat 1) (typ_arrow A1 A2)). eapply tred_top; eauto.
      * dependent destruction Htyp.
        (* case 1 *)
        dependent destruction H0.
        exists (trm_anno (trm_nat 1) (typ_arrow A1 A2)). eapply tred_top; eauto.
        assert (Htred1: exists v', typedred v1 (typ_arrow A1 A2) v').
        eapply IHHv1; eauto. destruct Htred1.
        exists x. eapply tred_merge_l; eauto.
        assert (Htred2: exists v', typedred v2 (typ_arrow A1 A2) v').
        eapply IHHv2; eauto. destruct Htred2.
        exists x. eapply tred_merge_r; eauto.
        (* case 2 *)
        dependent destruction H2.
        exists (trm_anno (trm_nat 1) (typ_arrow A1 A2)). eapply tred_top; eauto.
        constructor. eapply toplike_sub_top; eauto.
        assert (Htred1: exists v', typedred v1 (typ_arrow A1 A2) v').
        eapply IHHv1; eauto. destruct Htred1.
        exists x. eapply tred_merge_l; eauto.
        assert (Htred2: exists v', typedred v2 (typ_arrow A1 A2) v').
        eapply IHHv2; eauto. destruct Htred2.
        exists x. eapply tred_merge_r; eauto.
  (* case 2 *)
  - assert (exists v', typedred v A1 v').
    eapply IHA1; eauto 3.
    eapply value_check_merge in Htyp.
    destruct Htyp. assumption. assumption.
    assert (exists v', typedred v A2 v').
    eapply IHA2; eauto 3.
    eapply value_check_merge in Htyp.
    destruct Htyp. assumption. assumption.
    destruct H. destruct H0.
    exists (trm_merge x x0). eapply tred_and; eauto.
Admitted.

Theorem progress :
  forall (e : trm) (A : typ) (S : arg) (dir : mode),
    typing nil nil dir e A ->
    value e \/ (exists e', step e e') \/
    (exists (e' : trm) (A : typ), e = (trm_abs A e')).
Proof.
  intros e A S dir Htyp.
  dependent induction Htyp.
  - right. left. exists (trm_anno (trm_nat n) typ_int).
    apply step_int_anno.
  - inversion H0.
  - right. right.
    exists e. exists A. reflexivity.
  - dependent induction H0.
    + right. left.
      exists (trm_anno (trm_nat n) typ_int).
      eapply step_int_anno.
    + right. right.
      exists e. exists A0. reflexivity.
  - dependent destruction H.
    assert (IHHtyp1: value e \/ (exists e' : trm, step e e') \/ (exists (e' : trm) (A : typ), e = trm_abs A e')).
    eapply IHHtyp; eauto.
    destruct IHHtyp1.
    + right. left.
      assert (Htred: exists e', typedred e A e').
      eapply tred_progress; eauto.
      destruct Htred.
      exists x. eapply step_anno_value; eauto.
    + destruct H.
      * right. left.
        destruct H.
        exists (trm_anno x A).
        eapply step_anno; eauto.
        intro Hval. dependent destruction Hval.
        admit.
      * destruct H. destruct H.
        left. eapply value_anno. rewrite H.
        eapply pvalue_abs.
  - right. left.
    admit.
  - right. left.
    destruct IHHtyp1; eauto.
    + admit.
    + destruct H.
      * destruct H.
        exists (trm_app e1 x). eapply step_app_v; eauto.
        admit.
      * admit.
  - destruct IHHtyp; eauto.
Admitted.
