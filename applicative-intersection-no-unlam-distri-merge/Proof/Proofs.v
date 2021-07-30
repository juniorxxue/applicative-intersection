Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language LibTactics.
Require Import Strings.String.

Set Printing Parentheses.

Lemma sub_reflexivity:
  forall (A : typ), sub A A.
Proof.
  induction A; eauto.
Qed.

Hint Resolve sub_reflexivity : core.

Lemma sub_and_inversion1:
  forall (A B C : typ), sub A (typ_and B C) -> sub A B /\ sub A C.
Proof.
  introv Sub.
  dependent induction Sub; eauto.
  destruct (IHSub B C); eauto.
  destruct (IHSub B C); eauto.
Qed.

Lemma sub_and_inversion2:
  forall (A B C : typ), sub (typ_and A B) C -> sub A C \/ sub B C \/ exists C1 C2, C = typ_and C1 C2.
Proof.
  introv Hsub.
  dependent induction Hsub; eauto.
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
  - eapply sub_and_inversion1 in H. destruct H.
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

Ltac inversion_ordinary :=
  match goal with
  | [H: ordinary (_ & _) |- _] => inversion H
  end.

Ltac inversion_toplike :=
  match goal with
  | [H: toplike typ_int |- _] => inversion H
  | [H1: toplike (typ_arrow ?A ?B), H2: not (toplike ?B) |- _] => (inversion H1; contradiction)
  end.

(* aux lemma for tred_determinism *)
Lemma tred_ord_toplike :
  forall (v v' : trm) (A : typ),
    ordinary A -> toplike A -> typedred v A v' ->
    v' = (trm_anno (trm_int 1) A).
Proof.
  induction 3; eauto; try solve [inversion_toplike | inversion_ordinary].
Qed.

Hint Resolve tred_ord_toplike : core.

Ltac simpl_as :=
  match goal with
  | [H: appsub nil ?A ?B |- _] => dependent destruction H
  end.

(* aux lemma for disjoint_value_consistent *)
Lemma tred_sub :
  forall (A : typ) (v v' : trm),
    value v -> typedred v A v' -> forall (B : typ),
    typing nil nil v B ->
    sub B A.
Proof.
  introv Hv Hred.
  dependent induction Hred; eauto; introv Htyp.
  - dependent destruction Htyp.
    dependent destruction Htyp.
    simpl_as.
    assumption.
  - dependent destruction Htyp.
    simpl_as; eauto.
  - dependent destruction Hv.
    dependent destruction Htyp;
    eapply sub_and_l; eapply IHHred; eauto.
  - dependent destruction Hv.
    dependent destruction Htyp;
    eapply sub_and_r; eapply IHHred; eauto.
Qed.

Ltac rewrite_then_refl :=
  match goal with
  | [H1: ?e1 = ?expr, H2: ?e2 = ?expr |- ?e1 = ?e2] => (rewrite H1; rewrite H2; reflexivity)
  | [H1: ?e1 = ?e0, H2: ?e2 = ?e3 |- (trm_merge ?e1 ?e2) = (trm_merge ?e0 ?e3)] => (rewrite H1; rewrite H2; reflexivity)
  | [H1: ?A = ?A0, H2: ?B = ?B0 |- (?A & ?B) = (?A0 & ?B0)] => (rewrite H1; rewrite H2; reflexivity)
  end.

(* aux lemma for disjoint_value_consistent *)
Lemma tred_determinism_toplike :
  forall (A : typ),
    toplike A ->
    forall (e1 e2 e1' e2' : trm), typedred e1 A e1' -> typedred e2 A e2' -> e1' = e2'.
Proof.
  intros A Htop.
  dependent induction Htop; introv Hred1 Hred2.
  - eapply tred_ord_toplike in Hred1; eauto.
    eapply tred_ord_toplike in Hred2; eauto.
    rewrite_then_refl.
  - dependent destruction Hred1; eauto; try solve [inversion_ordinary].
    dependent destruction Hred2; try solve [inversion_ordinary].
    assert (v1 = v0). eapply IHHtop1; eauto 3.
    assert (v2 = v3). eapply IHHtop2; eauto 3.
    rewrite_then_refl.
  - assert (toplike (typ_arrow A B)); eauto.
    eapply tred_ord_toplike in Hred1; eauto.
    eapply tred_ord_toplike in Hred2; eauto.
    rewrite_then_refl.
Qed.

(* aux lemma for tred_determinism *)
Lemma disjoint_value_consistent :
  forall (A B : typ) (v1 v2 : trm),
    disjoint_spec A B -> value v1 -> value v2 ->
    typing nil nil v1 A -> typing nil nil v2 B ->
    consistency_spec v1 v2.
Proof.
  intros. unfold consistency_spec. intros.
  unfold disjoint_spec in *.
  assert (sub A A0). eapply tred_sub with (v:=v1); eauto.
  assert (sub B A0). eapply tred_sub with (v:=v2); eauto.
  assert (toplike A0); eauto.
  eapply tred_determinism_toplike; eauto.
Qed.

Hint Resolve disjoint_value_consistent : core.

Theorem tred_determinism :
  forall (v v1 v2 : trm) (A : typ),
    value v -> (exists B, typing nil nil v B) ->
    typedred v A v1 -> typedred v A v2 -> v1 = v2.
Proof.
  introv Hv Htyp Hred1.
  generalize dependent v2.
  dependent induction Hred1; eauto; introv Hred2.
  - dependent induction Hred2; try solve [inversion_toplike]; eauto.
  - dependent destruction Hred2; try solve [inversion_toplike | inversion_ordinary]; eauto.
    + symmetry. eapply tred_ord_toplike; eauto.
    + symmetry. eapply tred_ord_toplike; eauto.
  - dependent destruction Hred2; try solve [inversion_toplike]; eauto.
  - dependent destruction Hv.
    dependent destruction Htyp.
    dependent destruction Hred2; try solve [inversion_ordinary]; eauto.
    + dependent destruction H; eauto.
    + dependent destruction H; eauto.
      assert (consistency_spec v1 v2).
      eapply disjoint_value_consistent; eauto 3. eauto.
  - dependent destruction Hv.
    dependent destruction Htyp.
    dependent destruction Hred2; try solve [inversion_ordinary]; eauto.
    + dependent destruction H; eauto.
      * assert (consistency_spec v1 v2); eauto.
        symmetry. eauto.
      * symmetry. eauto.
    + dependent destruction H; eauto.
  - dependent destruction Hred2; try solve [inversion_ordinary]; eauto.
    assert (v1 = v0); eauto.
    assert (v2 = v3); eauto.
    rewrite_then_refl.
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
    rewrite_then_refl.
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

Lemma disjoint_spec_same :
  forall (A : typ),
    not (toplike A) ->
    disjoint_spec A A -> False.
Proof.
  intros.
  induction A; eauto.
Qed.


Lemma ptype_merge_same :
  forall (v1 v2 : trm) (A : typ),
    value v1 -> value v2 ->
    (exists A, typing nil nil (trm_merge v1 v2) A) ->
(*    ptype v1 A -> ptype v2 A *)
    ptype (trm_merge v1 v2) (typ_and A A) ->
    v1 = v2.
Proof.
  introv Hv1 Hv2 Htyp Hptyp.
  destruct Htyp.
  dependent destruction Hptyp.
  dependent destruction H.
  - induction Hv1. induction Hv2; eauto.
    + dependent destruction Hptyp2.
      dependent destruction Hptyp1.
      dependent destruction H0. dependent destruction H4.
      dependent destruction H5. dependent destruction H6.
      eapply disjoint_spec_same in H; eauto. contradiction. admit.
Admitted.

Lemma value_ptype_int :
  forall (v : trm) (A : typ),
    (exists B, typing nil nil v B) ->
    sub A typ_int -> sub typ_int A ->
    value v -> ptype v A ->
    exists n, v = (trm_anno (trm_int n) A).
Proof.
  introv Htyp Hsub1 Hsub2 Hv Hptyp.
  induction Hv; intros.
  - induction H.
    + dependent destruction Hptyp.
      exists n; eauto.
    + dependent destruction Hptyp.
      destruct Htyp. dependent destruction H.
      simpl_as. dependent destruction H.
      assert (sub (typ_arrow A1 B) typ_int).
      eapply sub_transitivity; eauto.
      inversion H1.
  - dependent destruction Hptyp.
    clear IHHv1 IHHv2.
    (* v = 1,,1 *)
Admitted.

Lemma ptype_merge_same':
  forall (v1 : trm) (A : typ),
    not (toplike A) ->
    (exists B, typing nil nil v1 B) ->
    value v1 -> ptype v1 A -> forall (v2 : trm),
        (exists C, typing nil nil v2 C) ->
        value v2 -> ptype v2 A ->
        consistency_spec v1 v2 ->
        v1 = v2.
Proof.
  introv Htl Htyp1 Hv1 Hptyp1.
  dependent induction Hptyp1; eauto.
  - inversion Hv1.
  - introv Htyp2 Hv2 Hptyp2 Hcons. dependent destruction Hv1.
    dependent induction H.
    + destruct Htyp1. dependent destruction H.
      dependent destruction H. simpl_as.
      (* v2 = n : An *)
      admit.
    + destruct Htyp1. dependent destruction H.
      dependent destruction H. simpl_as.
Admitted.

Ltac simpl_deter :=
  repeat
    match goal with
    | [H1: ptype ?v ?A1, H2: ptype ?v ?A2 |- _] => (eapply ptype_determinism in H1; eauto; subst)
    | [H1: appsub ?S ?A ?B1, H2: appsub ?S ?A ?B2 |- _] => (eapply appsub_determinism in H1; eauto; subst)
    end.

Lemma papp_determinism :
  forall (v vl e1 e2 : trm),
    value v -> value vl ->
    (exists A, typing nil nil v A) ->
    (exists B, typing nil nil vl B) ->
    papp v vl e1 -> papp v vl e2 -> e1 = e2.
Proof.
  introv Hv Hvl Htyp1 Htyp2 Hp1 Hp2.
  generalize dependent e2.
  dependent induction Hp1; eauto; intros.
  - dependent destruction Hp2; try solve [inversion Hv]; eauto.
    + assert (A = A0); eauto. rewrite H3; eauto.
    + dependent destruction H. dependent destruction H0. contradiction.
    + assert (A = C); eauto. subst. contradiction.
    + assert (A = C); eauto. subst. contradiction.
  - dependent destruction Hp2.
    + dependent destruction H1. dependent destruction H2. contradiction.
    + assert (v' = v'0). eapply tred_determinism; eauto.
      destruct Htyp1. dependent destruction H3; eauto.
  - dependent destruction Hv.
    dependent destruction Htyp1.
    eapply IHHp1; eauto.
    dependent destruction H; eauto.
    dependent destruction Hp2; eauto.
    + simpl_deter. contradiction.
    + simpl_deter.
      match goal with
      | [H: ptype (trm_merge ?v1 ?v2) ?A |- _] => dependent destruction H
      end.
      simpl_deter.
      assert (Heq: v1 = v2). eapply ptype_merge_same; eauto.
      rewrite Heq; eauto.
  - dependent destruction Hv.
    dependent destruction Htyp1.
    eapply IHHp1; eauto.
    dependent destruction H; eauto.
    dependent destruction Hp2; eauto.
    + simpl_deter. contradiction.
    + simpl_deter.
      match goal with
      | [H: ptype (trm_merge ?v1 ?v2) ?A |- _] => dependent destruction H
      end.
      simpl_deter.
      assert (Heq: v1 = v2). eapply ptype_merge_same; eauto.
      rewrite <- Heq; eauto.
Qed.

Lemma value_cannot_step_further:
  forall (v : trm),
    value v -> forall (e : trm), not (step v e).
Proof.
  intros v Hv.
  dependent induction v; intros; try solve [inversion Hv]; eauto.
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

Lemma stack_and_unstack:
  forall (e : trm) (A B : typ) (S : arg),
    typing nil (cons A S) e (typ_arrow A B) ->
    (exists C, typing nil nil e C).
Proof.
  intros.
  dependent induction H; eauto.
  assert (exists C, typing nil nil e1 C); eauto.
  dependent destruction H0; eauto.
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
  - dependent destruction H; eauto.
  - dependent destruction H2; eauto.
    + dependent destruction Htyp; eauto.
      eapply stack_and_unstack in Htyp2.
      eapply papp_determinism with (v:=v) (vl:=vl); eauto.
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
      eapply stack_and_unstack in Htyp2. destruct Htyp2.
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
  dependent induction v; try solve [inversion Hv]; eauto.
  - (* typing nil nil v1 A is impossible here *) dependent destruction Htyp.
    dependent destruction Hv.
    + dependent destruction Has; eauto.
    + dependent destruction Has; eauto.
  - dependent destruction Htyp. simpl_as.
    eapply typing_anno; eauto.
Qed.

Lemma tred_value :
  forall (v v' : trm) (A : typ),
    value v -> typedred v A v' -> value v'.
Proof.
  intros.
  dependent induction H0; try solve [eauto | dependent destruction H; eauto].
Qed.

Hint Resolve tred_value : core.

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
  dependent induction H0; eauto; introv Hred2.
  - dependent induction Hred2; eauto.
  - dependent induction Hred2; try solve [inversion_toplike_sub]; eauto.
  - dependent induction Hred2; eauto 4.
    eapply tred_arrow_anno; eauto;
    eapply sub_transitivity; eauto.
  - dependent destruction H.
    dependent induction Hred2; eauto.
  - dependent destruction H.
    dependent induction Hred2; eauto.
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
    typedred v A v' ->
    typing nil nil v' A.
Proof.
  intros v v' A B Hv Htyp Hred.
  assert (Hsub: sub B A). eapply tred_sub; eauto.
  generalize dependent B.
  dependent induction Hred; eauto; intros.
  - dependent destruction Htyp.
    dependent destruction Htyp.
    simpl_as.
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
    + eapply tred_consistency; eauto.
    + eapply IHHred1; eauto.
      eapply tred_sub. apply Hv. apply Hred1. apply Htyp.
    + eapply IHHred2; eauto.
      eapply tred_sub. apply Hv. apply Hred2. apply Htyp.
Qed.

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

Hint Resolve toplike_or_not_toplike : core.

Lemma papp_pre_helper1:
  forall (S : arg) (A0 A B : typ),
    toplike A0 -> appsub (cons A S) A0 (typ_arrow A B) -> appsub S A0 B.
Proof.
  (* . |- Int -> Top <: Top *)
Abort.

Lemma papp_preservation :
  forall (e e1 e2 : trm) (A B : typ) (S : arg),
    value e1 -> value e2 ->
    typing nil nil e2 A ->
    typing nil (cons A S) e1 (typ_arrow A B) ->
    papp e1 e2 e ->
    typing nil S e B.
Proof.
  introv Hv1 Hv2 Htyp1 Htyp2 Hp.
  dependent destruction Htyp2; eauto.
  - inversion Hv1.
  - dependent destruction Hv1. induction H.
    + dependent destruction Htyp2.
      dependent destruction Hp.
      dependent destruction H2.
      eapply typing_anno; eauto.
Admitted.

Lemma appsub_toplike :
  forall (S : arg) (A B : typ),
    toplike A ->
    appsub S A B ->
    toplike B.
Proof.
  introv Htl Has.
  dependent induction Has; eauto.
  - dependent destruction Htl.
    constructor; eauto.
  - dependent destruction Htl; eauto.
  - dependent destruction Htl; eauto.
Qed.

Lemma papp_preservation_no_toplike :
  forall (e e1 e2 : trm) (A B : typ) (S : arg),
    value e1 -> value e2 ->
    typing nil nil e2 A ->
    not (toplike (typ_arrow A B)) ->
    typing nil (cons A S) e1 (typ_arrow A B) ->
    papp e1 e2 e ->
    typing nil S e B.
Proof.
  introv Hv1 Hv2 Htl Htyp1 Htyp2 Hp.
  dependent destruction Htyp2; eauto.
  - inversion Hv1.
  - dependent destruction Hv1. induction H.
    + dependent destruction Htyp2.
      dependent destruction Hp.
      dependent destruction H2.
      eapply typing_anno; eauto.
      assert (toplike (typ_arrow A B)). eapply appsub_toplike; eauto.
      contradiction.
    + dependent destruction Htyp2.
      dependent destruction Hp.
      * dependent destruction H2.        
        assert (toplike (typ_arrow A B)). eapply appsub_toplike; eauto.
        contradiction.
          * dependent destruction H0.
        admit.
        dependent destruction H1.
        eapply typing_anno; eauto.
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
  - dependent destruction Hred.
    eapply typing_anno; eauto.
  - dependent destruction Hred.
    eapply typing_anno; eauto.
  - dependent destruction Hred; eauto.
    assert (typing nil nil v' A).
    eapply tred_preservation; eauto.
    eapply appsub_typing; eauto.
  - dependent destruction Hred; eauto.
    (* destruct (toplike_or_not_toplike (typ_arrow A B)); eauto. *)
    eapply papp_preservation with (e:=e) (e1:=e1) (e2:=e2); eauto.
  - dependent destruction Hred.
    + eapply typing_merge; eauto.
    + eapply typing_merge; eauto.
  - assert (value (trm_merge v1 v2)); eauto.
    apply value_cannot_step_further in Hred; eauto. inversion Hred.
  - dependent destruction Hred;
      eapply typing_merge_pick_l; eauto.
  - dependent destruction Hred;
      eapply typing_merge_pick_r; eauto.
Qed.

Theorem tred_progress :
  forall (v : trm) (A B : typ),
    value v -> typing nil nil v A ->
    sub A B ->
    exists v', typedred v B v'.
Proof.
  introv Hv Htyp Hsub.
  generalize dependent A.
  induction B; introv Htyp Hsub; eauto.
  - dependent induction Htyp; try solve [inversion Hv].
    + simpl_as. dependent destruction Hv.
      dependent destruction H.
      * clear IHHtyp. dependent destruction Htyp.
        exists (trm_anno (trm_int n) typ_int); eauto.
      * clear IHHtyp.
        dependent destruction Htyp.
        assert (sub (typ_arrow A0 B) typ_int). eapply sub_transitivity; eauto.
        inversion H1.
    + dependent destruction Hv.
      dependent destruction Hsub.
      * assert (exists v', typedred e1 typ_int v'); eauto.
        destruct H0; eauto.
      * assert (exists v', typedred e2 typ_int v'); eauto.
        destruct H0; eauto.
    + dependent destruction Hv.
      dependent destruction Hsub.
      * assert (exists v', typedred v1 typ_int v'); eauto.
        destruct H2; eauto.
      * assert (exists v', typedred v2 typ_int v'); eauto.
        destruct H2; eauto.
  - destruct (toplike_or_not_toplike B2).
    + exists (trm_anno (trm_int 1) (typ_arrow B1 B2)).
      eapply tred_top; eauto.
    + clear IHB1 IHB2.
      dependent induction Htyp; try solve [inversion Hv].
      * simpl_as.
        dependent destruction Hv.
        dependent induction H.
        (* case 1 *)
        dependent destruction Htyp.
        assert (sub typ_int (typ_arrow B1 B2)).
        eapply sub_transitivity; eauto.
        dependent destruction H2.
        assert (toplike B2); eauto.
        (* case 2 *)
        dependent destruction Htyp.
        exists (trm_anno (trm_abs e A0 B) (typ_arrow B1 B2)); eauto.
      * dependent destruction Hv.
        eapply sub_and_inversion2 in Hsub.
        destruct Hsub.
        (* case 1 *)
        assert (exists v', typedred e1 (typ_arrow B1 B2) v'); eauto.
        destruct H2. exists x; eauto.
        destruct H1.
        (* case 2 *)
        assert (exists v', typedred e2 (typ_arrow B1 B2) v'); eauto.
        destruct H2. exists x; eauto.
        (* case 3 *)
        destruct H1. destruct H1. inversion H1.
      * dependent destruction Hv.
        eapply sub_and_inversion2 in Hsub.
        destruct Hsub.
        (* case 1 *)
        assert (exists v', typedred v1 (typ_arrow B1 B2) v'); eauto.
        destruct H4. exists x; eauto.
        destruct H3.
        (* case 2 *)
        assert (exists v', typedred v2 (typ_arrow B1 B2) v'); eauto.
        destruct H4. exists x; eauto.
        (* case 3 *)
        destruct H3. destruct H3. inversion H3.
  - eapply sub_and_inversion1 in Hsub.
    destruct Hsub.
    assert (exists v', typedred v B1 v'); eauto.
    assert (exists v', typedred v B2 v'); eauto.
    destruct H1. destruct H2.
    exists (trm_merge x x0); eauto.
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

Lemma papp_progress :
  forall (e1 e2 : trm) (A B : typ),
    value e2 -> typing nil (cons A nil) e1 (typ_arrow A B) ->
    typing nil nil e2 A ->
    exists e', papp e1 e2 e'.
Proof.
Admitted.

Lemma not_value_arrow_inversion :
  forall (e : trm) (S : arg) (A B : typ),
    typing nil (cons A S) e (typ_arrow A B) ->
    not (value e) ->
    exists e', step e e'.
Proof.
  introv Htyp Hnot.
  induction e; try solve [inversion Htyp]; eauto.
  - admit.
Admitted.


Theorem progress_obslete :
  forall (e : trm) (A : typ),
    typing nil nil e A ->
    value e \/ (exists e', step e e').
Proof.
  intros e A Htyp.
  dependent induction Htyp; eauto.
  - inversion H0.
  - simpl_as.
    destruct IHHtyp; eauto.
    + dependent destruction H0.
      * right.
        assert (exists v', typedred (trm_anno e A0) A v').
        eapply tred_progress; eauto.
        destruct H1. exists x. eapply step_anno_value; eauto.
      * right.
        assert (exists v', typedred (trm_merge v1 v2) A v').
        eapply tred_progress; eauto.
        destruct H0. exists x. eapply step_anno_value; eauto.
    + assert (value (trm_anno e A) \/ not (value (trm_anno e A))); eauto.
      destruct H1.
      * left. auto.
      * right. destruct H0. exists (trm_anno x A).
        eapply step_anno; eauto.
  - assert (value e2 \/ (exists e', step e2 e')); eauto.
    clear IHHtyp1 IHHtyp2. right.
    destruct H.
    + destruct (value_or_not_value e1).
      * assert (exists e', papp e1 e2 e'). eapply papp_progress; eauto.
        destruct H1. exists x. eapply step_papp; eauto.
      * assert (exists e', step e1 e'). eapply not_value_arrow_inversion; eauto.
        destruct H1. exists (trm_app x e2); eauto.
    + destruct (value_or_not_value e1).
      *  destruct H. exists (trm_app e1 x). eapply step_app_r; eauto.
      *  assert (exists e', step e1 e'). eapply not_value_arrow_inversion; eauto.
         destruct H1. exists (trm_app x e2); eauto.
  - destruct IHHtyp1; destruct IHHtyp2; eauto.
    + right. destruct H1. exists (trm_merge e1 x); eauto.
    + right. destruct H0. exists (trm_merge x e2); eauto. 
    + right. destruct H0.
      exists (trm_merge x e2). eapply step_merge_l; eauto.
Qed.


Lemma papp_progress_stack :
  forall (e1 e2 : trm) (A B : typ) (S : arg),
    value e1 -> value e2 ->
    typing nil (cons A S) e1 (typ_arrow A B) ->
    typing nil nil e2 A ->
    exists e', papp e1 e2 e'.
Proof.
  dependent induction e1; introv Hv1 Hv2 Htyp1 Htyp2; try solve [inversion Hv1].
  - dependent destruction Hv1.
    dependent destruction Htyp1.
    + assert (exists e', papp e1_1 e2 e'); eauto.
      destruct H. exists x. admit.
    + assert (exists e', papp e1_2 e2 e'); eauto.
      destruct H. exists x. admit.
  - dependent destruction Htyp1.
    dependent destruction Hv1.
    dependent destruction H.
    + (* n *) dependent destruction Htyp1. clear IHe1.
      admit.
    + (* abs *) dependent destruction Htyp1. clear IHe1.
      admit.
Admitted.

(* a stack-version progress *)
Theorem progress_stack :
  forall (e : trm) (A : typ) (S : arg),
    typing nil S e A ->
    value e \/ (exists e', step e e').
Proof.
  introv Htyp.
  dependent induction Htyp; eauto.
  - inversion H0.
  - destruct IHHtyp; eauto.
    + dependent destruction H1; eauto.
      * right.
        assert (exists v', typedred (trm_anno e A0) A v').
        eapply tred_progress; eauto.
        destruct H2. exists x. eapply step_anno_value; eauto.
      * right.
        assert (exists v', typedred (trm_merge v1 v2) A v').
        eapply tred_progress; eauto.
        destruct H1. exists x. eapply step_anno_value; eauto.
    + assert (value (trm_anno e A) \/ not (value (trm_anno e A))); eauto.
      destruct H2.
      * left. auto.
      * right. destruct H1. exists (trm_anno x A).
        eapply step_anno; eauto.
  - right. destruct IHHtyp1; destruct IHHtyp2; eauto.
    + assert (exists e', papp e1 e2 e'). eapply papp_progress_stack; eauto.
      destruct H1. exists x. eapply step_papp; eauto.
    + destruct H0.
      exists (trm_app x e2); eauto.
    + destruct H.
      exists (trm_app e1 x); eauto.
    + destruct H0.
      exists (trm_app x e2); eauto.
  - destruct IHHtyp1; destruct IHHtyp2; eauto.
    + right. destruct H1. exists (trm_merge e1 x); eauto.
    + right. destruct H0. exists (trm_merge x e2); eauto. 
    + right. destruct H0.
      exists (trm_merge x e2). eapply step_merge_l; eauto.
  - destruct IHHtyp1; destruct IHHtyp2; eauto.
    + right. destruct H0. exists (trm_merge e1 x); eauto.
    + right. destruct H. exists (trm_merge x e2); eauto. 
    + right. destruct H.
      exists (trm_merge x e2). eapply step_merge_l; eauto.
  - destruct IHHtyp1; destruct IHHtyp2; eauto.
    + right. destruct H0. exists (trm_merge x e2); eauto.
    + right. destruct H. exists (trm_merge e1 x); eauto. 
    + right. destruct H0.
      exists (trm_merge x e2). eapply step_merge_l; eauto.
Qed.
  
