Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Strings.String.
Require Import Language LibTactics.
Require Import Subtyping Appsub Ptype Disjoint Value Toplike.
Require Import Tred Papp.

Set Printing Parentheses.

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
    eapply papp_determinism. eapply H. eapply H0. eapply H1. eapply H4. eapply Htyp.
  - dependent destruction Hstep2...
    + dependent destruction Htyp.
      eapply tred_determinism; eauto.
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

Theorem preservation :
  forall (e e' : trm) (A: typ),
    typing nil e A ->
    step e e' ->
    (exists B, typing nil e' B /\ isomorphic B A).
Proof.
  intros e e' A Htyp Hred.
  dependent induction Htyp; intros; try solve [inversion Hred].
  - dependent destruction Hred.
    exists typ_int. split; eauto.
  - dependent destruction Hred.
    exists (typ_arrow A B). split; eauto.
  - dependent destruction Hred.
    + eapply tred_preservation in H1; eauto.
    + admit.
  - dependent destruction Hred; eauto.
    + eapply papp_preservation.
      eapply H0. eapply H1. eapply Htyp2. eapply Htyp1. assumption. assumption.
    + admit.
    + admit.
  - admit.
  - admit.
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
  - right. destruct IHHtyp1; destruct IHHtyp2; eauto 3.
    + assert (toplike B \/ not (toplike B)).
      eapply toplike_or_not_toplike.
      destruct H2.
      * exists (trm_anno (trm_int 1) B); eauto.
      * eapply papp_progress in Htyp1; eauto 3.
        destruct Htyp1. exists x; eauto.
    + destruct H1; eauto.
    + destruct H0; eauto.
    + destruct H1; eauto.
  - destruct IHHtyp1; destruct IHHtyp2; eauto.
    + destruct H1; eauto.
    + destruct H0; eauto.
    + destruct H0; eauto.
Qed.
