Require Import Coq.Program.Equality.
Require Import Language Notations Auxiliaries Subtyping Automations.
Require Import Strings.String.

Set Printing Parentheses.

Lemma tred_ord_toplike : forall (e e' : trm) (A : typ),
    ordinary A -> toplike A -> typedred e A e' -> e' = (trm_anno (trm_nat 1) A).
Proof.
  intros e e' A H_ord H_top H_tred.
  dependent induction H_tred; subst; eauto.
  - inversion H_top.
  - inversion H_top. contradiction.
  - inversion H_ord.
Qed.

Lemma tred_toplike :
  forall (A : typ),
    toplike A ->
    forall e1 e2 e1' e2' : trm, typedred e1 A e1' -> typedred e2 A e2' -> e1' = e2'.
Proof.
  intros A Htop.
  dependent induction Htop; intros e1 e2 e1' e2' H_tred1 H_tred2.
  - eapply tred_ord_toplike in H_tred1. eapply tred_ord_toplike in H_tred2.
    rewrite H_tred1. rewrite H_tred2. reflexivity.
    constructor. constructor. constructor. constructor.
  - inversion H_tred1; subst; eauto 3.
    + inversion H0.
    + inversion H0.
    + inversion H0.
    + inversion H_tred2; subst; eauto 3.
      * inversion H0.
      * inversion H0.
      * inversion H0.
      * assert (Heq1: v1 = v0).
        eapply IHHtop1; eauto 3.
        assert (Heq2: v2 = v3).
        eapply IHHtop2; eauto 3.
        rewrite Heq1. rewrite Heq2. reflexivity.
  - assert (HAB: toplike (typ_arrow A B)).
    constructor. assumption.
    eapply tred_ord_toplike in H_tred2; eauto.
    eapply tred_ord_toplike in H_tred1; eauto.
    rewrite H_tred1. rewrite H_tred2. reflexivity.
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
    eapply toplike_sub in H.
    eapply sub_transitivity; eauto 3.
  - intros B0 Htyp.
    inversion Hval; subst; clear Hval.
    inversion Htyp; subst; clear Htyp.
    inversion H7; subst; clear H7.
    + eapply sub_arrow; eauto 3.
    (* + dependent destruction H2. eapply toplike_sub_toplike in H2; eauto. contradiction. *)
  - intros B0 Htyp.
    inversion Hval; subst; clear Hval.
    inversion Htyp; subst; clear Htyp.
    + apply sub_and_l.
      eapply IHHred; eauto 3.
    + apply sub_and_l.
      eapply IHHred; eauto 3.
  - intros B0 Htyp.
    inversion Hval; subst; clear Hval.
    inversion Htyp; subst; clear Htyp.
    + apply sub_and_r.
      eapply IHHred; eauto 3.
    + apply sub_and_r.
      eapply IHHred; eauto 3.
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
  - intros v2 Hred2.
    inversion Hred2; subst.
    + reflexivity.
    + inversion H.
  - intros v2 Hred2.
    inversion Hred2; subst; clear Hred2; eauto.
    + inversion H.
    + inversion H. contradiction.
    + symmetry. eapply tred_ord_toplike; eauto.
    + symmetry. eapply tred_ord_toplike; eauto.
    + inversion H0.
  - intros v2 Hred2.
    inversion Hred2; subst; clear Hred2.
    + inversion H2. contradiction.
    + reflexivity.
  - intros v0 Hred2.
    inversion Hred2; subst; eauto.
    + eapply tred_ord_toplike; eauto 3.
    + eapply IHHred1; eauto.
      * inversion Hval; assumption.
      * destruct Htyp. inversion H0; subst.
        exists A0. assumption.
        exists A0. assumption.
    + destruct Htyp.
      inversion H0; subst.
      * inversion Hval; subst; clear Hval.
        assert (Hcons: consistency_spec v1 v2).
        eapply disjoint_value_consistent; eauto 3.
        eapply Hcons; eauto 3.
      * eapply H11; eauto 3.
    + inversion H.
  - intros v0 Hred2.
    inversion Hred2; subst; eauto.
    + eapply tred_ord_toplike; eauto 3.
    + destruct Htyp.
      inversion H0; subst; eauto.
      * inversion Hval; subst; clear Hval.
        assert(Hcons: consistency_spec v1 v2).
        eapply disjoint_value_consistent; eauto 3.
        unfold consistency_spec in Hcons.
        symmetry. eapply Hcons; eauto 3.
      * unfold consistency_spec in H10.
        symmetry. eapply H11; eauto.
    + inversion Hval; subst; clear Hval.
      eapply IHHred1.
      * assumption.
      * destruct Htyp. inversion H0; subst.
        exists B. assumption.
        exists B. assumption.
      * assumption.
    + inversion H.
  - intros v0 Hred2.
    inversion Hred2; subst; clear Hred2.
    + inversion H0.
    + inversion H0.
    + inversion H0.
    + assert (Heq1: v1 = v3).
      eapply IHHred1_1; eauto 3.
      assert (Heq2: v2 = v4).
      eapply IHHred1_2; eauto 3.
      rewrite Heq1. rewrite Heq2. reflexivity.
Qed.

Lemma tred_value :
  forall (v v' : trm) (A : typ),
    value v -> typedred v A v' -> value v'.
Proof.
  intros v v' A Hval Hred.
  induction Hred; eauto.
  + apply IHHred. inversion Hval; eauto.
  + apply IHHred. inversion Hval; eauto.
Qed.

Lemma tred_transitivity : forall (v1 v2 v3 : trm) (A B : typ),
    value v1 -> typedred v1 A v2 -> typedred v2 B v3 -> typedred v1 B v3.
Proof.
  intros v1 v2 v3 A B Hval Hred1 Hred2.
  generalize dependent v3.
  generalize dependent B.
  dependent induction Hred1; eauto.
  - intros B v3 Hred2. dependent induction Hred2; eauto.
  - intros B0 v3 Hred2. dependent induction Hred2; eauto.
    + constructor. assumption.
      eapply sub_transitivity; eauto.
      eapply sub_transitivity; eauto.
  - intros B v3 Hred2.
    inversion Hval; subst; clear Hval.
    induction Hred2; eauto.
  - intros B v3 Hred2. inversion Hval; subst; clear Hval.
    induction Hred2; eauto.
  - intros B0 v0 Hred2.
    generalize dependent v0.
    induction B0; intros v0 Hred2; eauto.
    + inversion Hred2; subst; clear Hred2; eauto.
    + inversion Hred2; subst; clear Hred2; eauto.
    + inversion Hred2; subst; clear Hred2; eauto.
    + inversion Hred2; subst; clear Hred2; eauto.
Qed.

Lemma tred_consistency :
  forall (v v1 v2 : trm) (A B C : typ),
    value v -> typing nil nil infer_mode v C ->
    typedred v A v1 ->
    typedred v B v2 ->
    consistency_spec v1 v2.
Proof.
  intros v v1 v2 A B C Hval Htyp Hred1 Hred2.
  unfold consistency_spec.
  intros D v1' v2' Hred1' Hred2'.
  assert (Htrans1: typedred v D v1').
  eapply tred_transitivity. apply Hval. apply Hred1. apply Hred1'.
  assert (Htrans2: typedred v D v2').
  eapply tred_transitivity. apply Hval. apply Hred2. apply Hred2'.
  eapply tred_determinism; eauto 3.
Qed.

Lemma typing_merge_inversion:
  forall (v1 v2 : trm),
    (exists (A : typ), typing nil nil infer_mode (trm_merge v1 v2) A) ->
    (exists (B : typ), typing nil nil infer_mode v1 B) /\
    (exists (C : typ), typing nil nil infer_mode v2 C).
Proof.
  intros v1 v2 Htyp.
  destruct Htyp.
  inversion H; subst.
  - split. eauto. eauto.
  - split. eauto. eauto.
Qed.

Lemma ptype_determinsm :
  forall (e : trm) (A B : typ),
    ptype e A -> ptype e B -> A = B.
Proof.
  intros e A B Hp1 Hp2.
  generalize dependent B.
  dependent induction Hp1.
  - intros. inversion Hp2. reflexivity.
  - intros. inversion Hp2. reflexivity.
  - intros. inversion Hp2; subst.
    assert (A = A0).
    eapply IHHp1_1; eauto.
    assert (B = B1).
    eapply IHHp1_2; eauto.
    rewrite H. rewrite H0. reflexivity.
Qed.

Lemma appsub_determinism :
  forall (A : typ) (B1 B2 : typ) (S : arg),
    appsub S A B1 ->
    appsub S A B2 ->
    B1 = B2.
Proof.
  intros A B1 B2 S Has1 Has2.
  generalize dependent B2.
  dependent induction Has1; intros.
  - dependent destruction Has2.
    + reflexivity.
  - dependent destruction Has2.
    + assert (Heq: D = D0).
      eapply IHHas1; eauto.
      rewrite Heq. reflexivity.
  - dependent destruction Has2.
    + eapply IHHas1; eauto.
    + admit. 
  - dependent destruction Has2.
    + admit.
    + eapply IHHas1; eauto.
Admitted.

Lemma ptype_merge_same :
  forall (v1 v2 : trm) (A : typ),
    value v1 -> value v2 -> ptype (trm_merge v1 v2) (typ_and A A) ->
    v1 = v2.
Proof.
  intros v1 v2 A Hv1 Hv2 Hp.
  dependent destruction Hp.
Admitted.

Lemma papp_determinism :
  forall (v vl e1 e2 : trm),
    value v -> value vl ->
    (exists (B : typ), typing nil nil infer_mode vl B) ->
    papp v vl e1 -> papp v vl e2 -> e1 = e2.
Proof.
 intros v vl e1 e2 Hrv Hv Htyp Hp1 Hp2.
  generalize dependent e2.
  dependent induction Hp1.
  - intros. inversion Hp2; subst.
    + assert (A = A0). eapply ptype_determinsm; eauto.
      rewrite H3. reflexivity.
    + dependent destruction H. dependent destruction H0. contradiction.
    + assert (Heq: A = C). eapply ptype_determinsm; eauto. subst.
      contradiction.
    + assert (Heq: A = C). eapply ptype_determinsm; eauto. subst.
      contradiction.
  - intros. dependent destruction Hp2.
    + dependent destruction H1. dependent destruction H2. contradiction.
    + assert (v' = v'0). eapply tred_determinism; eauto.
      rewrite H3; eauto.
  - intros. apply IHHp1; eauto.
    + dependent destruction Hrv. assumption.
    + dependent destruction Hp2; eauto.
      * assert (Heq: A0 = C). eapply ptype_determinsm; eauto. subst.
        contradiction.
      * assert (B = B0). eapply ptype_determinsm; eauto. subst.
        assert (C = C0). eapply ptype_determinsm; eauto. subst.
        assert (A = A0). eapply appsub_determinism; eauto. subst.
        dependent destruction H6.
        assert (A = B).
        assert (A = A0). eapply ptype_determinsm; eauto. subst.
        assert (B = A0). eapply ptype_determinsm; eauto. subst.
        reflexivity. subst.
        dependent destruction Hrv.
        assert (v1 = v2). eapply ptype_merge_same; eauto. subst. eauto.
  - intros. apply IHHp1; eauto.
    + dependent destruction Hrv. assumption.
    + dependent destruction Hp2; eauto.
      * assert (Heq: A0 = C). eapply ptype_determinsm; eauto. subst.
        contradiction.
      * assert (B = B0). eapply ptype_determinsm; eauto. subst.
        assert (C = C0). eapply ptype_determinsm; eauto. subst.
        assert (A = A0). eapply appsub_determinism; eauto. subst.
        dependent destruction H6.
        assert (A = B).
        assert (A = A0). eapply ptype_determinsm; eauto. subst.
        assert (B = A0). eapply ptype_determinsm; eauto. subst.
        reflexivity. subst.
        dependent destruction Hrv.
        assert (v1 = v2). eapply ptype_merge_same; eauto. subst. eauto.
Qed.

Lemma value_cannot_step_further :
  forall (v : trm),
    value v -> forall (e : trm), not (step v e).
Proof.
  intros v Hval.
  induction v.
  - inversion Hval.
  - inversion Hval.
  - inversion Hval.
  - unfold not. intros. inversion H.
  - inversion Hval.
  - inversion Hval; subst.
    intros. unfold not. intros.
    inversion H; subst.
    + eapply IHv1; eauto 3.
    + eapply IHv2; eauto 3.
  - inversion Hval; subst; clear Hval.
    induction H0.
    + intros. unfold not. intros.
      inversion H; subst.
      * inversion H2.
      * apply H2. constructor. constructor.
    + intros. unfold not. intros.
      inversion H; subst.
      * inversion H2.
      * apply H2. constructor. constructor.
Qed.

Lemma app_check_inversion :
  forall (v vl : trm) (A : typ),
    value v -> value vl -> typing nil nil check_mode (trm_app v vl) A ->
    exists (B : typ), typing nil nil infer_mode vl B.
Proof.
  intros r vl A Hrv Hv Hchk.
  dependent destruction Hchk.
  - inversion H0.
  - exists A. auto.
  - dependent destruction Hchk.
    exists A0. eauto.
Qed.

(* aux lemma for anno_check_to_infer *)
Lemma value_with_anno_is_not_value :
  forall (v : trm) (A : typ),
    value v -> not (value (trm_anno v A)).
Proof.
  intros v A Hv.
  unfold not. intro.
  dependent destruction H.
  dependent induction H.
  - inversion Hv.
  - inversion Hv.
Qed.

(* this case have conflict with typing rule: any value can be checked by lemma *)
(* current workaround is add a premise not-toplike *)
Lemma anno_check_to_infer :
  forall (v : trm) (A B : typ),
    value v -> typing nil nil check_mode (trm_anno v A) B ->
    (exists (C : typ), typing nil nil infer_mode v C).
Proof.
  intros v A B Hv Htyp.
  dependent destruction Htyp.
  inversion H0.
  dependent destruction Htyp.
  dependent destruction Htyp.
  - inversion Hv.
  - dependent destruction H1; try solve [inversion Hv].
  - inversion Hv. 
  - exists B0; eauto.
Qed.

(* aux lemma for step_determinism *)
Lemma lambda_typing1 :
  forall (e : trm) (A B : typ),
    typing nil (cons A nil) infer_mode e B ->
    (exists C, typing nil nil check_mode e C).
Proof.
  intros e A B Htyp.
  dependent induction Htyp.
  - dependent destruction H.
    + dependent destruction H0.
      exists (typ_arrow A0 A1). eapply typing_sub; eauto.
      eapply sub_reflexivity.
    + clear IHHtyp. exists (typ_and A0 B). eapply typing_sub; eauto.
      eapply sub_reflexivity.
    + clear IHHtyp. exists (typ_and A0 B). eapply typing_sub; eauto.
      eapply sub_reflexivity.
  - exists B. eapply typing_app2.
    + eapply Htyp1.
    + admit.
  - clear IHHtyp1 IHHtyp2.
    exists B. eapply typing_sub; eauto.
Admitted.

Lemma lambda_typing2 :
  forall (e : trm) (A B : typ),
    typing nil (cons A nil) infer_mode e (typ_arrow A B) ->
    typing nil nil check_mode e (typ_arrow A B).
Proof.
  intros e A B Htyp.
  dependent induction Htyp.
  - clear IHHtyp. eapply typing_sub; eauto.
    admit. (* trivial *)
  - eapply typing_app2; eauto 3.
    admit.
  - eapply typing_sub; eauto.
    admit. (* trivial *)
Admitted.

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
  - intros A Htyp e2 Hred2.
    inversion Hred2; subst. (* papp and 2 congruence rules *)
    + eapply app_check_inversion in Htyp; eauto.
      apply papp_determinism with (v:=v) (vl:=vl); eauto.
    + eapply value_cannot_step_further in H5. inversion H5. auto.
    + eapply value_cannot_step_further in H6. inversion H6. auto.
  - intros A0 Htyp e2 Hred2.
    dependent destruction Hred2.
    + eapply tred_determinism; eauto 3.
      eapply anno_check_to_infer in Htyp; eauto.
    + eapply value_cannot_step_further in Hred2; eauto. contradiction.
  - intros A0 Htyp e2 Hred2.
    dependent destruction Hred2.
    + eapply value_cannot_step_further in Hred1. contradiction.
      auto.
    + assert (Heq: e' = e'0).
      dependent destruction Htyp.
      * inversion H1.
      * dependent destruction Htyp.
        eapply IHHred1; eauto.
      * rewrite Heq. reflexivity.
  - intros A Htyp e0 Hred2.
    dependent destruction Hred2.
    + eapply value_cannot_step_further in Hred1; eauto. contradiction.
    + assert (Heq: e1' = e1'0).
      dependent destruction Htyp.
      * inversion H0.
      * eapply IHHred1; eauto 3.
      * dependent destruction Htyp.
        assert (exists C, typing nil nil check_mode e1 C).
        eapply lambda_typing1; eauto 3.
        destruct H0.
        eapply IHHred1; eauto 3.        
      * rewrite Heq; eauto.
    + eapply value_cannot_step_further in Hred1. contradiction. assumption.
  - intros A Htyp e0 Hred2.
    dependent destruction Hred2.
    + eapply value_cannot_step_further in Hred1. contradiction. assumption.
    + eapply value_cannot_step_further in Hred2. contradiction. assumption.
    + assert (Heq: e2' = e2'0).
      dependent destruction Htyp.
      * inversion H1.
      * eapply IHHred1; eauto 3.
      * dependent destruction Htyp.
        eapply IHHred1; eauto 3.
      * rewrite Heq. reflexivity.
  - intros A Htyp e0 Hred2.
    dependent destruction Hred2.
    + assert (Heq: e1' = e1'0).
      dependent destruction Htyp.
      inversion H0.
      dependent destruction Htyp.
      * eapply IHHred1; eauto.
      * eapply IHHred1; eauto.
      * rewrite Heq. reflexivity.
    + eapply value_cannot_step_further in Hred1. contradiction. assumption.
  - intros A Htyp e0 Hred2.
    dependent destruction Hred2.
    + eapply value_cannot_step_further in Hred2.
      contradiction. assumption.
    + assert (Heq: e2' = e2'0).
      dependent destruction Htyp.
      inversion H1.
      dependent destruction Htyp.
      * eapply IHHred1; eauto.
      * eapply IHHred1; eauto.
      * rewrite Heq. reflexivity.
Qed.
