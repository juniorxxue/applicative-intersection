Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language Automations Subtyping Tred LibTactics.
Require Import Strings.String.

Set Printing Parentheses.

Lemma ptype_determinism :
  forall (e : trm) (A B : typ),
    ptype e A -> ptype e B -> A = B.
Proof.
  intros. generalize dependent B.
  dependent induction H; eauto; introv Hptyp.
  - dependent destruction Hptyp; eauto.
  - dependent destruction Hptyp; eauto.
    assert (A = A0); eauto.
    assert (B = B0); eauto.
    congruence.
  - dependent destruction Hptyp.
    assert ((typ_arrow A B) = (typ_arrow A0 B0)); eauto.
    dependent induction H7; eauto.
Qed.

Hint Resolve ptype_determinism : core.

Lemma appsub_to_auxas :
  forall (A B : typ) (S : arg),
    appsub S A B ->
    auxas S A.
Proof.
  intros.
  dependent induction H; eauto.
Qed.

Lemma auxas_false :
  forall (A B : typ) (S : arg),
    not (auxas S A) ->
    appsub S A B ->
    False.
Proof.
  intros.
  eapply appsub_to_auxas in H0.
  contradiction.
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
  - dependent destruction Has2; eauto.
  - dependent destruction Has2; eauto.
    assert (Heq: D = D0).
    eapply IHHas1; eauto.
    rewrite Heq. reflexivity.
  - dependent destruction Has2; eauto.
    + eapply auxas_false in H; eauto. inversion H.
  - dependent destruction Has2; eauto.
    + eapply auxas_false in H; eauto. inversion H.
Qed.

Lemma disjoint_spec_same :
  forall (A : typ),
    not (toplike A) ->
    disjoint_spec A A -> False.
Proof.
  intros.
  induction A; eauto.
Qed.

Ltac simpl_deter :=
  repeat
    match goal with
    | [H1: ptype ?v ?A1, H2: ptype ?v ?A2 |- _] => (eapply ptype_determinism in H1; eauto; subst)
    | [H1: appsub ?S ?A ?B1, H2: appsub ?S ?A ?B2 |- _] => (eapply appsub_determinism in H1; eauto; subst)
    end.

Lemma typ_and_equal_false1 :
  forall (A B : typ),
    A = (typ_and A B) -> False.
Proof.
  intros.
  induction A; try solve [inversion H]; eauto.
  dependent destruction H.
  eapply IHA1; eauto.
Qed.

Lemma typ_and_equal_false2 :
  forall (A B : typ),
    B = (typ_and A B) -> False.
Proof.
  intros.
  induction B; try solve [inversion H]; eauto.
  dependent destruction H.
  eapply IHB2; eauto.
Qed.

Ltac solve_equal_false :=
  match goal with
  | [H: (typ_and ?A ?B) = ?A |- _] => (symmetry in H; eapply typ_and_equal_false1 in H; inversion H)
  | [H: (typ_and ?A ?B) = ?B |- _] => (symmetry in H; eapply typ_and_equal_false2 in H; inversion H)
  | [H: ?A = (typ_and ?A ?B) |- _] => (eapply typ_and_equal_false1 in H; inversion H)
  | [H: ?B = (typ_and ?A ?B) |- _] => (eapply typ_and_equal_false2 in H; inversion H)
  end.

Lemma appsub_solve_false :
  forall (S : arg) (A : typ),
    appsub S (typ_and A A) A -> False.
Proof.
  intros. dependent induction H; eauto.
  - eapply typ_and_equal_false1 in x; eauto.
Admitted.

Lemma typing_to_ptype :
  forall (A : typ) (v : trm),
    value v ->
    typing nil nil v A ->
    ptype v A.
Proof.
  introv Hv Htyp.
  generalize dependent A.
  dependent induction Hv; eauto; introv Htyp.
  - dependent destruction Htyp; eauto. simpl_as; eauto.
  - dependent destruction Htyp; eauto.
Qed.

Lemma not_toplike_and_inversion :
  forall (A B : typ),
    not (toplike (typ_and A B)) ->
    not (toplike A) /\ not (toplike B).
Proof.
  intros.
Admitted.

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

Lemma mbeta_determinism:
  forall (e e1 e2 v : trm) (A B C D : typ) (L : argv),
    (exists E, typing nil nil v E) ->
    value v ->
    mbeta (trm_anno (trm_abs e A B) (typ_arrow C D)) (cons v L) e1 ->
    mbeta (trm_anno (trm_abs e A B) (typ_arrow C D)) (cons v L) e2 ->
    e1 = e2.
Proof.
  introv Htyp Hv Hm1 Hm2.
  generalize dependent e2.
  dependent induction Hm1; eauto; introv Hm2.
  - dependent destruction Hm2.
    + assert (v' = v'0). eapply tred_determinism; eauto.
      congruence.
    + inversion Hm2.
  -
Admitted.

      
Lemma papp_determinism:
  forall (v v' e1 e2 : trm) (L : argv) (A B : typ) (S : arg),
    value v ->
    value v' ->
    typing nil nil v' A ->
    typing nil S v B ->
    papp v (cons v' L) e1 ->
    papp v (cons v' L) e2 ->
    e1 = e2.
Proof.
  introv Hv Hv' Htypv' Htypv Hp1 Hp2.
  generalize dependent S.
  generalize dependent A.
  generalize dependent B.
  generalize dependent e2.
  dependent induction Hp1; eauto; intros.
  - dependent destruction Hp2.
    eapply mbeta_determinism; eauto.
  - dependent destruction Hv; eauto.
    eapply IHHp1; eauto.
    dependent destruction Hp2; eauto.
    (* contradiction here *)
    admit. admit.
  - dependent destruction Hv; eauto. eapply IHHp1; eauto.
    dependent destruction Hp2; eauto.
    (* contradiction *)
    admit. admit.
Admitted.

Lemma capp_determinism:
  forall (r v e1 e2 : trm) (L : argv) (A : typ) (S : arg),
    typing nil S (trm_app r v) A ->
    rvalue r -> value v ->
    capp (trm_app r v) L e1 ->
    capp (trm_app r v) L e2 ->
    e1 = e2.
Proof.
  introv Htyp Hr Hv Hcp1 Hcp2.
  generalize dependent e2.
  generalize dependent S.
  generalize dependent A.
  dependent induction Hcp1; eauto; intros.
  - dependent destruction H.
  - dependent destruction Hcp2. inversion H.
    induction Hr.
    + dependent destruction Hcp1; try solve [inversion H].
      dependent destruction Hcp2; try solve [inversion H0].
      eapply papp_determinism; eauto.
Admitted.

Theorem determinism:
  forall (e e1 e2 : trm) (A : typ) (S : arg),
    typing nil S e A ->
    step e e1 -> step e e2 -> e1 = e2.
Proof.
  intros e e1 e2 A S Htyp Hstep1.
  generalize dependent e2.
  generalize dependent A.
  generalize dependent S.
  dependent induction Hstep1; introv Htyp Hstep.
  - dependent destruction Hstep; eauto.
  - dependent destruction Hstep; eauto.
  - dependent destruction Hstep; eauto.
    + assert (B = B0); eauto. congruence.
    + assert (B = B0); eauto. subst. contradiction.
    + contradiction.
    + eapply value_cannot_step_further in Hstep; eauto. inversion Hstep.
  - dependent destruction Hstep; eauto.
    + assert (B = B0); eauto. subst. contradiction.
    + simpl_deter.
      eapply capp_determinism; eauto.
    + contradiction.
    + eapply value_cannot_step_further in Hstep; eauto. inversion Hstep.
  - dependent destruction Hstep.
    + eapply tred_determinism; eauto.
      dependent destruction Htyp; eauto.
    + eapply value_cannot_step_further in Hstep; eauto. inversion Hstep.
  - dependent destruction Hstep.
    + eapply value_cannot_step_further in Hstep1; eauto. inversion Hstep1.
    + assert (Heq: e' = e'0).
      dependent destruction Htyp.
      eapply IHHstep1; eauto.
      rewrite Heq. reflexivity.
  - dependent destruction Hstep.
    + contradiction.
    + contradiction.
    + dependent destruction Htyp; eauto.
      assert (e1' = e1'0); eauto. rewrite H1. reflexivity.
    + contradiction.
  - dependent destruction Hstep.
    + eapply value_cannot_step_further in Hstep1; eauto. inversion Hstep1.
    + eapply value_cannot_step_further in Hstep1; eauto. inversion Hstep1.
    + contradiction.
    + dependent destruction Htyp.
      assert (e2' = e2'0); eauto. rewrite H1. reflexivity.
  - dependent destruction Hstep.
    + assert (e1' = e1'0).
      dependent destruction Htyp; eapply IHHstep1; eauto.
      rewrite H. reflexivity.
    + eapply value_cannot_step_further in Hstep1; eauto. inversion Hstep1.
  - dependent destruction Hstep.
    + eapply value_cannot_step_further in Hstep; eauto. inversion Hstep.
    + assert (e2' = e2'0).
      dependent destruction Htyp; eapply IHHstep1; eauto.
      rewrite H1. reflexivity.
Qed.

Lemma appsub_toplike_preservation :
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

Lemma appsub_type_preservation :
  forall (v : trm) (S : arg) (A B : typ),
    value v -> typing nil nil v A ->
    appsub S A B ->
    typing nil S v B.
Proof.
  intros v S A B Hv Htyp Has.
  dependent induction v; try solve [inversion Hv]; eauto.
  - dependent destruction Hv; eauto.
    dependent destruction Has; eauto.
    + inversion Htyp.
    + dependent destruction Htyp.
      * eapply typing_merge_pick_l; eauto.
        admit. (* disjoint_preservation *)
      * eapply typing_merge_pick_l; eauto.
        admit.
    + dependent destruction Htyp.
      * eapply typing_merge_pick_r; eauto.
        admit.
      * eapply typing_merge_pick_r; eauto.
        admit.
  - dependent destruction Htyp; eauto.
    dependent destruction H0; eauto.
Admitted.

Lemma papp_preservation :
  forall (v v' e : trm) (A : typ) (S : arg),
    typing nil S (trm_app v v') A ->
    papp v (cons v' nil) e ->
    typing nil S e A.
Proof.
Admitted.
    
Lemma capp_preservation :
  forall (r v e : trm) (A : typ) (S : arg),
    typing nil S (trm_app r v) A ->
    capp (trm_app r v) nil e ->
    typing nil S e A.
Proof.
  introv Htyp.
  generalize dependent e.
  dependent induction Htyp; introv Hcp.
  dependent destruction Hcp.
  - inversion H.
  - dependent induction Hcp; eauto.
    + eapply papp_preservation; eauto.
    + admit. (* should be solved by IH *)
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
    dependent destruction H1; eauto.
  - dependent destruction Hred; eauto.
    assert (typing nil nil v' A).
    eapply tred_preservation; eauto.
    eapply appsub_type_preservation; eauto.
  - assert (typing nil S (trm_app e1 e2) B); eauto.
    dependent destruction Hred; eauto.
    + admit.
    + eapply capp_preservation; eauto.
  - dependent destruction Hred.
    + eapply typing_merge; eauto.
    + eapply typing_merge; eauto.
  - assert (value (trm_merge v1 v2)); eauto.
    apply value_cannot_step_further in Hred; eauto. inversion Hred.
  - dependent destruction Hred; eauto.
  - dependent destruction Hred; eauto.
Admitted.

Lemma typing_toplike_ptype :
  forall (S : arg) (A : typ) (v : trm),
    value v ->
    typing nil S v A ->
    toplike A ->
    (exists B, ptype v B /\ toplike B).
Proof.
Admitted.

(* stack version is wrong here *)
(* counter example is Int |- add ,, chk 1 => Int -> Int*)
Theorem progress :
  forall (e : trm) (A : typ) (S : arg),
    typing nil S e A ->
    value e \/ (exists e', step e e').
Proof.
  introv Htyp.
  dependent induction Htyp; eauto.
  - inversion H0.
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
    + destruct (toplike_or_not_toplike B).
      * assert (exists C, ptype e1 C /\ toplike C). eapply typing_toplike_ptype; eauto.
        destruct H2. destruct H2.
        exists (trm_anno (trm_int 1) x).
        eapply step_papp_toplike; eauto.
      * admit.  
    + destruct H0.
      exists (trm_app x e2); eauto.
      eapply step_app_l; eauto. admit.
    + destruct H.
      exists (trm_app e1 x); eauto.
    + destruct H0.
      exists (trm_app x e2); eauto.
      eapply step_app_l; eauto. admit.
  - destruct IHHtyp1; destruct IHHtyp2; eauto.
    + right. destruct H1. exists (trm_merge e1 x); eauto.
    + right. destruct H0. exists (trm_merge x e2); eauto. 
    + right. destruct H0.
      exists (trm_merge x e2). eapply step_merge_l; eauto.
Abort.

(* conflicts about typed reduction *)
(* counter example is r : A is well-typed, it's not a rvalue or further step *)
Theorem progress_rvalue :  
  forall (e : trm) (A : typ) (S : arg),
    typing nil S e A ->
    rvalue e \/ (exists e', step e e').
Proof.
  introv Htyp.
  dependent induction Htyp; eauto.
  - inversion H0.
  - inversion H0.
  - destruct IHHtyp; eauto.
    + dependent destruction H1; eauto.
      dependent destruction H1.
      * right.
        assert (exists v', typedred (trm_anno e A0) A v').
        eapply tred_progress; eauto.
        destruct H2. exists x. eapply step_anno_value; eauto.
      * right.
        assert (exists v', typedred (trm_merge v1 v2) A v').
        eapply tred_progress; eauto.
        destruct H1. exists x. eapply step_anno_value; eauto.
Abort.

(* broken a little bit *)
Theorem progress_no_stack :
  forall (e : trm) (A : typ),
    typing nil nil e A ->
    value e \/ (exists e', step e e').
Proof.
  introv Htyp.
  dependent induction Htyp; eauto.
  - inversion H0.
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
  - right. (* no information about e1 *) clear IHHtyp2.
    destruct IHHtyp1; eauto.
    + destruct (value_or_not_value e1); eauto.
      * (* papp progress *) admit.
      * admit. (* no idea *)
    + destruct H. admit.
  - destruct IHHtyp1; destruct IHHtyp2; eauto.
    + right. destruct H1. exists (trm_merge e1 x); eauto.
    + right. destruct H0. exists (trm_merge x e2); eauto. 
    + right. destruct H0.
      exists (trm_merge x e2). eapply step_merge_l; eauto.
Abort.
