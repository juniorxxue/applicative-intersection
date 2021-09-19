Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Language Automations Subtyping LibTactics.
Require Import Strings.String.

Lemma toplike_int_false :
  toplike typ_int -> False.
Proof.
  intros. inversion H.
Qed.

Hint Resolve toplike_int_false : core.

(* aux lemma for tred_determinism *)
Lemma tred_ord_toplike :
  forall (v v' : trm) (A : typ),
    ordinary A -> toplike A -> typedred v A v' ->
    v' = (trm_anno (trm_int 1) A).
Proof.
  induction 3; try solve [eauto | exfalso; eauto].
  inversion H0.
  contradiction.
Qed.

Hint Resolve tred_ord_toplike : core.

(* aux lemma for disjoint_value_consistent *)
Lemma tred_sub :
  forall (A : typ) (v v' : trm),
    value v -> typedred v A v' -> forall (B : typ),
    typing nil v B ->
    sub B A.
Proof.
  introv Hv Hred.
  dependent induction Hred; eauto; introv Htyp.
  - dependent destruction Htyp.
    dependent destruction Htyp; eauto.
  - dependent destruction Htyp; eauto.
  - dependent destruction Hv.
    dependent destruction Htyp;
      eapply sub_and_l; eauto.
  - dependent destruction Hv.
    dependent destruction Htyp;
    eapply sub_and_r; eauto.
Qed.

Theorem tred_determinism :
  forall (v1 v2 v1' v2' : trm) (A B C : typ),
    value v1 -> value v2 ->
    typing nil v1 A -> typing nil v2 B ->
    typedred v1 C v1' -> typedred v2 C v2' ->
    consistency_spec v1 v2 -> v1' = v2'.
Proof.
Admitted.

Lemma tred_value_preservation :
  forall (v v' : trm) (A : typ),
    value v -> typedred v A v' -> value v'.
Proof.
  intros.
  dependent induction H0;
    try solve [eauto | dependent destruction H; eauto].
Qed.

Hint Resolve tred_value_preservation : core.

Lemma tred_transitivity :
  forall (v1 v2 v3 : trm) (A B : typ),
    value v1 ->
    typedred v1 A v2 ->
    typedred v2 B v3 ->
    typedred v1 B v3.
Proof.
Abort.

Lemma tred_consistency :
  forall (v v1 v2 : trm) (A B C : typ),
    value v -> typing nil v C ->
    typedred v A v1 ->
    typedred v B v2 ->
    consistency_spec v1 v2.
Proof.
Abort.

Theorem tred_preservation:
  forall (v v': trm) (A B: typ),
    value v ->
    typing nil v B ->
    typedred v A v' ->
    typing nil v' A.
Proof.
Abort.

Lemma value_int_n_false :
  forall (n : nat), value (trm_int n) -> False.
Proof.
  intros. inversion H.
Qed.

Hint Resolve value_int_n_false : core.

Lemma sub_arrow_int_false :
  forall (A B : typ),
    sub (typ_arrow A B) typ_int -> False.
Proof.
  introv H.
  dependent destruction H; eauto.
Qed.

Hint Resolve sub_arrow_int_false : core.

Theorem splitable_not_toplike_preservation :
  forall (A B C : typ),
    splitable A B C -> not (toplike A) ->
    not (toplike B).
Proof.
Admitted.

Lemma sub_int_arrow_false :
  forall (A B : typ),
    not (toplike B) ->
    sub typ_int (typ_arrow A B) ->
    False.
Proof.
  introv Htl Hsub.
  dependent induction Hsub; eauto.
  - dependent destruction H0. contradiction.
  - dependent destruction H.
    assert (toplike C \/ not (toplike C)).
    eapply toplike_or_not_toplike.
    destruct H0; eauto.
    assert (not (toplike C)).
    eapply splitable_not_toplike_preservation; eauto.
    contradiction.
Qed.

Theorem sub_int_form :
  forall (A : typ),
    sub typ_int A -> not (toplike A) -> ordinary A -> A = typ_int.
Proof.
  introv Hsub Htl Hord.
  dependent induction Hord; eauto.
  - destruct Htl; eauto.
  - dependent destruction Hsub.
    + contradiction.
    + dependent destruction H.
      exfalso; eauto.
Qed.

Theorem tred_progress :
  forall (v : trm) (A B : typ),
    value v -> typing nil v A ->
    sub A B ->
    exists v', typedred v B v'.
Proof.
  introv Hv Htyp Hsub.
  gen v.
  dependent induction Hsub; intros; eauto.
  - dependent destruction Htyp;
      try solve [exfalso; eauto].
    + dependent destruction Hv.
      dependent induction H; eauto.
      dependent destruction Htyp.
      exfalso; eauto.
    + inversion Hv.
  - dependent destruction Htyp.
    + inversion H1.
    + inversion Hv.
    + assert (toplike D \/ not (toplike D)).
      eapply toplike_or_not_toplike.
      destruct H1.
      (* case top *)
      exists (trm_anno (trm_int 1) (typ_arrow B D)); eauto.
      (* case not top *)
      dependent destruction Hv.
      dependent destruction H0.
      (* case int *)
      dependent destruction Htyp.
      eapply sub_int_arrow_false in H1; eauto. contradiction.
      intro Hcontra. eapply sub_toplike_preservation in Hsub2; eauto.
      (* case arrow *)
      dependent destruction Htyp.
      exists (trm_anno (trm_abs e A0 B0) (typ_arrow B D)); eauto.
    + inversion Hv.
  - assert (exists v', typedred v B v'); eauto.
    assert (exists v', typedred v C v'); eauto.
    destruct_conjs; eauto.
  - dependent destruction Htyp; eauto; try solve [inversion Hv].
    + destruct (toplike_or_not_toplike C).
      * exists (trm_anno (trm_int 1) C); eauto.
      * dependent destruction Hv.
        dependent destruction H0.
        (* case int *)
        dependent destruction Htyp.
        dependent destruction H1. inversion H1. dependent destruction H1.
        assert (sub typ_int C). eapply sub_transitivity. eapply H1_. eapply Hsub.
        eapply sub_int_form in H1; eauto. subst.
        eauto.
    (* case arrow *)
        dependent destruction Htyp.
        dependent destruction H1. inversion H1.
        dependent destruction H1.
        assert (sub (typ_arrow A0 B0) C).
        eapply sub_transitivity. eapply H1_. eapply Hsub.
        dependent destruction H1.
        contradiction.
        exists (trm_anno (trm_abs e A0 B0) (typ_arrow  B2 D)); eauto.
        eapply tred_arrow_anno; eauto.
        exfalso; eauto.
    + dependent destruction Hv.
      assert (exists v', typedred e1 C v'); eauto.
      destruct_conjs; eauto.
    + dependent destruction Hv.
      assert (exists v', typedred v1 C v'); eauto.
      destruct_conjs; eauto.
  - dependent destruction Htyp; eauto; try solve [inversion Hv].
    + destruct (toplike_or_not_toplike C).
      * exists (trm_anno (trm_int 1) C); eauto.
      * dependent destruction Hv.
        dependent destruction H0.
        (* case int *)
        dependent destruction Htyp.
        dependent destruction H1. inversion H1. dependent destruction H1.
        assert (sub typ_int C). eapply sub_transitivity. eapply H1_0. eapply Hsub.
        eapply sub_int_form in H1; eauto. subst.
        eauto.
        (* case arrow *)
        dependent destruction Htyp.
        dependent destruction H1. inversion H1.
        dependent destruction H1.
        assert (sub (typ_arrow A0 B0) C).
        eapply sub_transitivity. eapply H1_0. eapply Hsub.
        dependent destruction H1.
        contradiction.
        exists (trm_anno (trm_abs e A0 B0) (typ_arrow  B2 D)); eauto.
        eapply tred_arrow_anno; eauto.
        exfalso; eauto.
    + dependent destruction Hv.
      assert (exists v', typedred e2 C v'); eauto.
      destruct_conjs; eauto.
    + dependent destruction Hv.
      assert (exists v', typedred v2 C v'); eauto.
      destruct_conjs; eauto.
Qed.