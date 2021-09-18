Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language Automations Subtyping Tred Papp LibTactics.
Require Import Strings.String.

Set Printing Parentheses.

Lemma ptype_determinism :
  forall (e : trm) (A B : typ),
    ptype e A -> ptype e B -> A = B.
Proof.
  intros. generalize dependent B.
  dependent induction H; eauto; intros * Hptyp.
  - dependent destruction Hptyp; eauto.
  - dependent destruction Hptyp; eauto.
    assert (A = A0); eauto.
    assert (B = B0); eauto.
    congruence.
Qed.

Hint Resolve ptype_determinism : core.

(* Hint Rewrite *)

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

Hint Resolve auxas_false : core.

Lemma appsub_determinism :
  forall (A : typ) (B1 B2 : typ) (S : arg),
    appsub S A B1 ->
    appsub S A B2 ->
    B1 = B2.
Proof.
  intros A B1 B2 C Has1 Has2.
  generalize dependent B2.
  dependent induction Has1; intros;
    dependent destruction Has2; try solve [eauto | exfalso; eauto].
  assert (D1 = D0); eauto.
  assert (D2 = D3); eauto.
  congruence.
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
Abort.

Lemma typing_to_ptype :
  forall (A : typ) (v : trm),
    value v ->
    typing nil v A ->
    ptype v A.
Proof.
  introv Hv Htyp.
  generalize dependent A.
  dependent induction Hv; eauto; introv Htyp.
  - dependent destruction Htyp; eauto.
  - dependent destruction Htyp; eauto.
Qed.

Hint Resolve typing_to_ptype : core.

Lemma not_toplike_and_inversion :
  forall (A B : typ),
    not (toplike (typ_and A B)) ->
    not (toplike A) /\ not (toplike B).
Proof.
  intros.
Abort.

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
    + intros Hs.
      dependent destruction Hs; eauto.
      inversion H.
Qed.

Ltac solve_value_cannot :=
  match goal with
  | [H1: value ?v, H2: step ?v ?e |- _] =>
      (eapply value_cannot_step_further in H2; eauto; contradiction)
  end.

Hint Extern 5 => solve_value_cannot : determinism.

Theorem determinism:
  forall (e e1 e2 : trm) (A : typ),
    typing nil e A ->
    step e e1 -> step e e2 -> e1 = e2.
Proof with eauto with determinism.
  intros e e1 e2 A Htyp Hstep1 Hstep2.
  gen e2 A.
  dependent induction Hstep1; intros.
  - dependent destruction Hstep2...
  - dependent destruction Hstep2...
  - dependent destruction Hstep2...
    + assert (A = A0); info_eauto. congruence.
    + assert (A = A0); eauto. subst. contradiction.
  - dependent destruction Hstep2...
    + assert (A = A0); eauto. subst. contradiction.
    + simpl_deter.
      eapply papp_determinism; eauto.
  - dependent destruction Hstep2...
    + dependent destruction Htyp.
      eapply tred_determinism; eauto.
      unfold consistency_spec.
      admit.
  - dependent destruction Hstep2...
    + assert (Heq: e' = e'0).
      dependent destruction Htyp; eauto.
      congruence.
  - dependent destruction Hstep2...
    + dependent destruction Htyp; eauto.
      assert (e1' = e1'0); eauto. congruence.
  - dependent destruction Hstep2...
    + dependent destruction Htyp.
      assert (e2' = e2'0); eauto. congruence.
  - dependent destruction Hstep2...
    + assert (e1' = e1'0).
      dependent destruction Htyp; eapply IHHstep1; eauto.
      congruence.
  - dependent destruction Hstep2...
    assert (e2' = e2'0); eauto.
    dependent destruction Htyp; eauto.
    congruence.
Admitted.

Lemma appsub_toplike_preservation :
  forall (S : arg) (A B : typ),
    toplike A ->
    appsub S A B ->
    toplike B.
Proof.
  introv Htl Has.
Admitted.

Lemma appsub_type_preservation :
  forall (v : trm) (S : arg) (A B : typ),
    value v -> typing nil v A ->
    appsub S A B ->
    typing nil v B.
Proof.
Admitted.

Theorem preservation :
  forall (e e' : trm) (A : typ) (S : arg),
    typing nil e A ->
    step e e' ->
    typing nil e' A.
Proof.
  intros e e' A S Htyp Hred.
  generalize dependent e'.
  dependent induction Htyp; intros; try solve [inversion Hred].
Admitted.

Theorem progress :
  forall (e : trm) (A : typ),
    typing nil e A ->
    value e \/ exists e', step e e'.
Proof.
  introv Htyp.
  dependent induction Htyp; eauto.
  - inversion H0.
  - destruct IHHtyp; eauto.
    + right.
      eapply tred_progress in Htyp; eauto.
      destruct Htyp.
      exists x. eapply step_anno_value; eauto.
    + assert (value (trm_anno e A) \/ not (value (trm_anno e A))).
      eapply value_or_not_value.
      destruct H1; eauto.
      right. destruct H0. exists (trm_anno x A); eauto.
  - right. destruct IHHtyp1; destruct IHHtyp2; eauto.
    + assert (typing nil (trm_app e1 e2) C); eauto.
      eapply papp_progress in H2.
      destruct H2; eauto.
      assert (toplike B \/ not (toplike B)).
      eapply toplike_or_not_toplike.
      destruct H3.
      * exists (trm_anno (trm_int 1) B); eauto.
      * exists x; eauto.
    + destruct H1; eauto.
    + destruct H0; eauto.
    + destruct H1; eauto.
  - destruct IHHtyp1; destruct IHHtyp2; eauto.
    + destruct H1; eauto.
    + destruct H0; eauto.
    + destruct H0; eauto.
Qed.
