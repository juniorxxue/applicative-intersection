Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Language LibTactics.
Require Import Strings.String.
Require Import SubAndTopLike Value.

(* aux lemma for tred_determinism *)
Lemma tred_ord_toplike :
  forall (v v' : trm) (A : typ),
    ordinary A -> toplike A -> typedred v A v' ->
    v' = (trm_anno (trm_int 1) A).
Proof.
  induction 3; eauto.
  - inversion H0.
  - dependent destruction H0. contradiction.
  - exfalso; eauto.
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
    consistent v1 v2 -> v1' = v2'.
Proof.
  introv Hv1 Hv2 Htyp.
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

Theorem tred_preservation:
  forall (v v': trm) (A B: typ),
    value v ->
    typing nil v B ->
    typedred v A v' ->
    (exists C, typing nil v' C /\ isomorphic C A).
Proof.
Admitted.

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
