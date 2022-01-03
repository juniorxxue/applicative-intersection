Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language.
Require Import Strings.String.

Set Printing Parentheses.

Lemma sub_reflexivity:
  forall (A : typ), sub A A.
Proof.
  intros.
  dependent induction A; eauto.
Qed.

Hint Resolve sub_reflexivity : core.

Lemma sub_and_inversion:
  forall (A B C : typ), sub A (typ_and B C) -> sub A B /\ sub A C.
Proof.
  intros A B C H.
  dependent induction H; eauto.
  destruct (IHsub B C); eauto.
  destruct (IHsub B C); eauto.
Qed.

Lemma sub_transitivity:
  forall (B A C : typ),
    sub A B -> sub B C -> sub A C.
Proof.
  dependent induction B; intros; eauto.
  - dependent induction H; eauto.
  - dependent induction H; eauto.
    dependent induction H0; eauto.
  - dependent induction H0; eauto.
    clear IHsub1 IHsub2.
    dependent induction H; eauto.
  - eapply sub_and_inversion in H. destruct H.
    dependent induction H0; eauto.
Qed.

Lemma sub_toplike1:
  forall (A B : typ),
    toplike A -> sub B A.
Proof.
  intros.
  generalize dependent B.
  dependent induction H; eauto.
Qed.

Lemma sub_toplike2:
  forall (A : typ),
    sub typ_top A -> toplike A.
Proof.
  intros.
  dependent induction H; eauto.
Qed.

Hint Resolve sub_toplike1 : core.
Hint Resolve sub_toplike2 : core.

(* aux lemma for tred_determinism *)
Lemma tred_ord_toplike :
  forall (v v' : trm) (A : typ),
    ordinary A -> toplike A -> typedred v A v' ->
    v' = (trm_anno (trm_int 1) A).
Proof.
  intros.
  dependent induction H1; eauto; try solve [inversion H | inversion H0]; subst.
  dependent destruction H0. contradiction.
Qed.

(* aux lemma for disjoint_value_consistent *)
Lemma tred_sub :
  forall (A B : typ) (v v' : trm),
    value v -> typedred v A v' ->
    typing nil nil v B ->
    sub B A.
Proof.
  intros.
  generalize dependent B.
  dependent induction H0; eauto; intros.
  - dependent destruction H1.
    dependent destruction H2.
    eapply sub_reflexivity.
  - dependent destruction H2.
    dependent destruction H4; eauto.
  - dependent destruction H.
    dependent destruction H3.
    eapply sub_and_l. eapply IHtypedred; eauto.
    eapply sub_and_l. eapply IHtypedred; eauto.
  - dependent destruction H.
    dependent destruction H3.
    eapply sub_and_r. eapply IHtypedred; eauto.
    eapply sub_and_r. eapply IHtypedred; eauto.
Qed.

(* aux lemma for disjoint_value_consistent *)
Lemma tred_determinism_toplike :
  forall (A : typ),
    toplike A ->
    forall (e1 e2 e1' e2' : trm), typedred e1 A e1' -> typedred e2 A e2' -> e1' = e2'.
Proof.
  intros A Htop.
  dependent induction Htop; intros; eauto.
  - eapply tred_ord_toplike in H; eauto.
    eapply tred_ord_toplike in H0; eauto.
    rewrite H. rewrite H0. reflexivity.
  - dependent destruction H; eauto.
    + inversion H0.
    + inversion H0.
    + inversion H0.
    + dependent destruction H1.
      * inversion H2.
      * inversion H2.
      * inversion H2.
      * assert (Heq1: v1 = v0). eapply IHHtop1; eauto 3.
        assert (Heq2: v2 = v3). eapply IHHtop2; eauto 3.
        rewrite Heq1. rewrite Heq2. reflexivity.
  - assert (Htl: toplike (typ_arrow A B)).
    eapply tl_arrow; eauto.
    eapply tred_ord_toplike in H; eauto.
    eapply tred_ord_toplike in H0; eauto.
    rewrite H. rewrite H0. reflexivity.
Qed.


(* aux lemma for tred_determinism *)
Lemma disjoint_value_consistent :
  forall (A B : typ) (v1 v2 : trm),
    disjoint_spec A B -> value v1 -> value v2 ->
    typing nil nil v1 A -> typing nil nil v2 B ->
    consistency_spec v1 v2.
Proof.
  intros. unfold consistency_spec.
  intros.
  unfold disjoint_spec in H.
  assert (Hsub1: sub A A0). eapply tred_sub. apply H0. apply H4. apply H2.
  assert (Hsub2: sub B A0). eapply tred_sub. apply H1. apply H5. apply H3.
  assert (Htl: toplike A0). eapply H; eauto.
  eapply tred_determinism_toplike; eauto.
Qed.

Theorem tred_determinism :
  forall (v v1 v2 : trm) (A : typ),
    value v -> (exists B, typing nil nil v B) ->
    typedred v A v1 -> typedred v A v2 -> v1 = v2.
Proof.
  intros v v1 v2 A Hv Htyp Hred1.
  generalize dependent v2.
  dependent induction Hred1; eauto.
  - intros v2 Hred2.
    dependent induction Hred2; eauto.
    inversion H.
  - intros v2 Hred2.
    dependent destruction Hred2; eauto; try solve [inversion H | inversion H0].
    + dependent destruction H. contradiction.
    + symmetry. eapply tred_ord_toplike; eauto.
    + symmetry. eapply tred_ord_toplike; eauto.
  - intros v2 Hred2.
    dependent destruction Hred2; eauto; subst.
    + dependent destruction H1. contradiction.
  - intros v0 Hred2.
    dependent destruction Hv.
    dependent destruction Htyp.
    dependent destruction Hred2; eauto; subst.
    + eapply tred_ord_toplike; eauto.
    + dependent destruction H; eauto.
    + dependent destruction H.
      * assert (Hcon: consistency_spec v1 v2).
        eapply disjoint_value_consistent; eauto 3.
        eapply Hcon; eauto 3.
      * eapply H3; eauto 3.
    + inversion H0.
  - intros v0 Hred2.
    dependent destruction Hv.
    dependent destruction Htyp.
    dependent destruction Hred2; eauto; subst.
    + eapply tred_ord_toplike; eauto.
    + dependent destruction H.
      * assert (Hcon: consistency_spec v1 v2).
        eapply disjoint_value_consistent; eauto 3.
        symmetry.
        eapply Hcon; eauto 3.
      * symmetry. eapply H3; eauto 3.
    + dependent destruction H; eauto.
    + inversion H0.
  - intros v0 Hred2.
    dependent destruction Hred2; eauto.
    + inversion H0.
    + inversion H.
    + inversion H.
    + assert (Heq1: v1 = v0). eapply IHHred1_1; eauto 3.
      assert (Heq2: v2 = v3). eapply IHHred1_2; eauto 3.
      rewrite Heq1. rewrite Heq2. reflexivity.
Qed.

Lemma ptype_determinism :
  forall (e : trm) (A B : typ),
    ptype e A -> ptype e B -> A = B.
Proof.
  intros. generalize dependent B.
  dependent induction H; eauto; intros.
  - dependent destruction H0; eauto.
  - dependent destruction H0; eauto.
  - dependent destruction H1; eauto.
    assert (A = A0); eauto.
    assert (B = B0); eauto.
    rewrite H1. rewrite H2. reflexivity.
Qed.

Hint Resolve ptype_determinism : core.

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
    value v1 -> value v2 ->
    (exists A, typing nil nil (trm_merge v1 v2) A) ->
    ptype (trm_merge v1 v2) (typ_and A A) ->
    v1 = v2.
Proof.
  intros v1 v2 A Hv1 Hv2 Htyp Hptyp.
  destruct Htyp.
Admitted.

Lemma typing_app_go_deeper :
  forall (v1 v2 vl : trm),
    value v1 -> value v2 -> value vl ->
    (exists A, typing nil nil (trm_app (trm_merge v1 v2) vl) A) ->
    (exists B, typing nil nil (trm_app v1 vl) B) \/
    (exists C, typing nil nil (trm_app v2 vl) C).
Proof.
Admitted.

Lemma papp_determinism:
  forall (v vl e1 e2 : trm),
    value v -> value vl ->
    (exists A, typing nil nil vl A) ->
    papp v vl e1 -> papp v vl e2 -> e1 = e2.
Proof.
  intros v vl e1 e2 Hv Hv1 Htyp Hp1 Hp2.
  generalize dependent e2.
  dependent induction Hp1; eauto; intros.
  - dependent destruction Hp2; eauto.
    + assert (A = A0); eauto. rewrite H3. reflexivity.
    + dependent destruction H. dependent destruction H0. contradiction.
    + assert (A = C); eauto. subst. contradiction.
    + assert (A = C); eauto. subst. contradiction.
  - dependent destruction Hp2.
    + dependent destruction H1. dependent destruction H2. contradiction.
    + assert (v' = v'0). eapply tred_determinism; eauto.
      destruct Htyp. dependent destruction H3; eauto.
  - dependent destruction Hv.
    eapply IHHp1; eauto.
    dependent destruction Hp2; eauto.
    + assert (A0 = C). eapply ptype_determinism; eauto. subst.
      contradiction.
    + assert (C = C0). eapply ptype_determinism; eauto. subst.
      dependent destruction H6.
      assert (A1 = B1). admit. subst.
      eapply ptype_merge_same in H1; eauto.
      (* ptype_merge_same premises is not enought here *)
Admitted.

Lemma papp_determinism2 :
  forall (v vl e1 e2 : trm),
    value v -> value vl ->
    (exists A, typing nil nil v A) ->
    (exists B, typing nil nil vl B) ->
    papp v vl e1 -> papp v vl e2 -> e1 = e2.
Proof.
  intros v vl e1 e2 Hv Hvl Htyp1 Htyp2 Hp1 Hp2.
  generalize dependent e2.
  dependent induction Hp1; eauto; intros.
  - dependent destruction Hp2; eauto.
    + assert (A = A0); eauto. rewrite H3. reflexivity.
    + dependent destruction H. dependent destruction H0. contradiction.
    + assert (A = C); eauto. subst. contradiction.
    + assert (A = C); eauto. subst. contradiction.
  - dependent destruction Hp2.
    + dependent destruction H1. dependent destruction H2. contradiction.
    + assert (v' = v'0). eapply tred_determinism; eauto.
      destruct Htyp1. dependent destruction H3; eauto.
  - dependent destruction Hv.
    eapply IHHp1; eauto.
    dependent destruction Hp2; eauto.
    + assert (A0 = C). eapply ptype_determinism; eauto. subst.
      contradiction.
    + assert (C = C0). eapply ptype_determinism; eauto. subst.
      dependent destruction H6.
      assert (A1 = B1). admit. subst.
      eapply ptype_merge_same in H1; eauto.
      (* ptype_merge_same premises is not enought here *)
Admitted.

Lemma value_cannot_step_further:
  forall (v : trm),
    value v -> forall (e : trm), not (step v e).
Proof.
  intros v Hv.
  dependent induction v; intros; try solve [inversion Hv | eauto].
  - dependent destruction Hv. intros Hm.
    dependent destruction Hm.
    + eapply IHv1; eauto.
    + eapply IHv2; eauto.
  - dependent destruction Hv.
    induction H; eauto.
    + intros Hs.
      dependent destruction Hs; eauto.
      dependent destruction H.
    + intros Hs.
      dependent destruction Hs; eauto.
      dependent destruction H.
Qed.

Lemma stack_and_unstack1:
  forall (e : trm) (A B : typ),
    typing nil (cons A nil) e (typ_arrow A B) ->
    (exists C, typing nil nil e C).
Proof.
  intros.
  dependent induction e; try solve [inversion H | dependent destruction H; eauto].
  (* dependent destruction H. *)
Admitted.

Theorem determinism:
  forall (e e1 e2 : trm) (A : typ) (S : arg),
    typing nil nil e A ->
    step e e1 -> step e e2 -> e1 = e2.
Proof.
  intros e e1 e2 A S Htyp Hstep1.
  generalize dependent e2.
  generalize dependent A.
  dependent induction Hstep1; intros. 
  - dependent destruction H; eauto.
  - dependent destruction H2; eauto.
    + eapply papp_determinism with (v:=v) (vl:=vl); eauto.
      dependent destruction Htyp; eauto.
    + eapply value_cannot_step_further in H2; eauto. inversion H2.
    + eapply value_cannot_step_further in H3; eauto. inversion H3.
  - dependent destruction H1.
    + eapply tred_determinism; eauto.
      dependent destruction Htyp; eauto.
    + eapply value_cannot_step_further in H2; eauto. inversion H2.
  - dependent destruction H0.
    + eapply value_cannot_step_further in Hstep1; eauto. inversion Hstep1.
    + assert (Heq: e' = e'0).
      dependent destruction Htyp.
      eapply IHHstep1; eauto.
      dependent destruction Htyp; eauto.
      rewrite Heq. reflexivity.
  - dependent destruction H.
    + eapply value_cannot_step_further in Hstep1; eauto. inversion Hstep1.
    + dependent destruction Htyp; eauto.
      eapply stack_and_unstack1 in Htyp2. destruct Htyp2.
      assert (Heq: e1' = e1'0). eapply IHHstep1; eauto.
      rewrite Heq. reflexivity.
    + eapply value_cannot_step_further in Hstep1; eauto. inversion Hstep1.
  - dependent destruction H0.
    + eapply value_cannot_step_further in Hstep1; eauto. inversion Hstep1.
    + eapply value_cannot_step_further in H0; eauto. inversion H0.
    + assert (Heq: e2' = e2'0).
      dependent destruction Htyp.
      eapply IHHstep1; eauto.
      rewrite Heq. reflexivity.
  - dependent destruction H.
    + assert (e1' = e1'0).
      dependent destruction Htyp; eapply IHHstep1; eauto.
      rewrite H0. reflexivity.
    + eapply value_cannot_step_further in Hstep1; eauto. inversion Hstep1.
  - dependent destruction H0.
    + eapply value_cannot_step_further in H0; eauto. inversion H0.
    + assert (e2' = e2'0).
      dependent destruction Htyp; eapply IHHstep1; eauto.
      rewrite H2. reflexivity.
Qed.

Lemma appsub_typing :
  forall (v : trm) (S : arg) (A B : typ),
    value v -> typing nil nil v A ->
    appsub S A B ->
    typing nil S v B.
Proof.
  intros v S A B Hv Htyp Has.
  dependent induction Hv.
  - dependent destruction Htyp.
    dependent destruction H1.
    eapply typing_anno; eauto.
  - clear IHHv1 IHHv2.
    dependent induction S.
    + dependent destruction Has; eauto.
    + eapply typing_merge_pick; eauto.
Qed.

Lemma tred_value :
  forall (v v' : trm) (A : typ),
    value v -> typedred v A v' -> value v'.
Proof.
  intros.
  dependent induction H0; try solve [eauto | dependent destruction H; eauto].
Qed.

Hint Resolve tred_value : core.

Lemma tred_transitivity :
  forall (v1 v2 v3 : trm) (A B : typ),
    value v1 ->
    typedred v1 A v2 ->
    typedred v2 B v3 ->
    typedred v1 B v3.
Proof.
  intros.
  generalize dependent v3.
  generalize dependent B.
  dependent induction H0; eauto; intros.
  - dependent induction H2; eauto.
  - dependent induction H2; eauto 4.
    eapply tred_arrow_anno; eauto.
    eapply sub_transitivity; eauto.
  - dependent destruction H.
    dependent induction H3; eauto.
  - dependent destruction H.
    dependent induction H3; eauto.
  - generalize dependent v3.
    induction B0; intros v0 Hred2; try solve [eauto | dependent destruction Hred2; eauto].
Qed.
   
Lemma tred_consistency :
  forall (v v1 v2 : trm) (A B C : typ),
    value v -> typing nil nil v C ->
    typedred v A v1 ->
    typedred v B v2 ->
    consistency_spec v1 v2.
Proof.
  intros.
  unfold consistency_spec; intros.
  assert (typedred v A0 e1').
  eapply tred_transitivity with (v1:=v) (v2:=v1) (v3:=e1'); eauto.
  assert (typedred v A0 e2').
  eapply tred_transitivity with (v1:=v) (v2:=v2) (v3:=e2'); eauto.
  eapply tred_determinism; eauto.
Qed.

Theorem tred_preservation:
  forall (v v': trm) (A B: typ),
    value v ->
    typing nil nil v B ->
    sub B A ->
    typedred v A v' ->
    typing nil nil v' A.
Proof.
  intros v v' A B Hv Htyp Hsub Hred.
  generalize dependent B.
  dependent induction Hred; eauto; intros.
  - dependent destruction Htyp.
    dependent destruction H2.
    eapply typing_anno; eauto.
    eapply sub_transitivity; eauto.
  - dependent destruction Hv.
    dependent destruction Htyp; eapply IHHred; eauto.
    + eapply tred_sub. apply Hv1. apply Hred. apply Htyp1.
    + eapply tred_sub. apply Hv1. apply Hred. apply Htyp1.
  - dependent destruction Hv.
    dependent destruction Htyp; eapply IHHred; eauto.
    + eapply tred_sub. apply Hv2. apply Hred. apply Htyp2.
    + eapply tred_sub. apply Hv2. apply Hred. apply Htyp2.
  - eapply typing_merge_value; eauto.
    + eapply IHHred1; eauto.
      eapply tred_sub. apply Hv. apply Hred1. apply Htyp.
    + eapply IHHred2; eauto.
      eapply tred_sub. apply Hv. apply Hred2. apply Htyp.
    + eapply tred_consistency; eauto.
Qed.

Lemma papp_preservation :
  forall (e e1 e2 : trm) (A B : typ) (S : arg),
    value e1 -> value e2 ->
    typing nil nil e2 A ->
    typing nil (cons A S) e1 (typ_arrow A B) ->
    papp e1 e2 e ->
    typing nil S e B.
Proof.
Admitted.

Theorem preservation :
  forall (e e' : trm) (A : typ) (S : arg),
    typing nil S e A ->
    step e e' ->
    typing nil S e' A.
Proof.
  intros e e' A S Htyp Hred.
  generalize dependent e'.
  dependent induction Htyp; intros; try solve [inversion Hred].
  - dependent destruction Hred.
    eapply typing_anno; eauto.
  - dependent destruction Hred; eauto.
    assert (typing nil nil v' A).
    eapply tred_preservation; eauto.
    eapply appsub_typing; eauto.
  - dependent destruction Hred; eauto.
    eapply papp_preservation with (e:=e) (e1:=e1) (e2:=e2); eauto.
  - dependent destruction Hred.
    + eapply typing_merge; eauto.
    + eapply typing_merge; eauto.
  - assert (value (trm_merge v1 v2)); eauto.
    apply value_cannot_step_further in Hred; eauto. inversion Hred.
  - assert (typing nil nil e' B); eauto.
    dependent destruction Hred; eauto.
Qed.

Lemma toplike_or_not_toplike :
  forall (A : typ),
    toplike A \/ not (toplike A).
Proof.
  intros A.
  dependent induction A; eauto; try solve [right; intros Hcontra; inversion Hcontra].
  - destruct IHA1; destruct IHA2; eauto.
    + right. intros H1. dependent destruction H1. contradiction.
    + right. intros H1. dependent destruction H1. contradiction.
  - destruct IHA1; destruct IHA2; eauto.
    + right. intros H1. dependent destruction H1. contradiction.
    + right. intros H1. dependent destruction H1. contradiction.
    + right. intros H1. dependent destruction H1. contradiction.
Qed.

Hint Resolve toplike_or_not_toplike : core.

Theorem tred_progress :
  forall (v : trm) (A : typ),
    value v -> typing nil nil v A ->
    exists v', typedred v A v'.
Proof.
  intros v A Hv Htyp.
  dependent induction A; eauto.
  - dependent induction Hv; eauto.
    + dependent induction H; eauto.
      * dependent destruction Htyp.
        dependent destruction Htyp.
        dependent destruction H1.
        exists (trm_anno (trm_int n) typ_int); eauto.
      * dependent destruction Htyp.
        dependent destruction Htyp.
        dependent destruction H1.
        dependent destruction H0.
    + dependent destruction Htyp.
  - clear IHA1 IHA2.
    dependent induction Hv.
    + dependent induction H.
      * dependent destruction Htyp.
        dependent destruction Htyp.
        dependent destruction H1.
        dependent destruction H0.
        exists (trm_anno (trm_int 1) (typ_arrow A1 A2)).
        eapply tred_top; eauto.
      * dependent destruction Htyp.
        dependent destruction Htyp.
        dependent destruction H1.
        assert (toplike A2 \/ not (toplike A2)); eauto.
        destruct H1.
        (* case top *)
        exists (trm_anno (trm_int 1) (typ_arrow A1 A2)).
        eapply tred_top; eauto.
        (* case not top *)
        exists (trm_anno (trm_abs A0 e) (typ_arrow A1 A2)).
        eapply tred_arrow_anno; eauto.
    + dependent destruction Htyp.
  - clear IHA1 IHA2.
Admitted.
(* the problem appear at case And *)
(* admitted since it might not a real-used one, refer to tred_preservation *)
