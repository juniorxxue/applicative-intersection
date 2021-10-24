Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Strings.String.
Require Import Language LibTactics.
Require Import SubAndTopLike Appsub.
Require Import Ptype Disjoint Value.
Require Import Consistent Tred Papp.
Require Import Program.Tactics.
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
  - dependent destruction Hstep2.
    + eapply split_determinism in H; eauto.
      destruct H. subst. reflexivity.
    + inversion H0.
    + destruct H0; eauto.
  - dependent destruction Hstep2...
  - dependent destruction Htyp.
    dependent destruction Htyp.
    dependent destruction Hstep2.
    + eapply split_determinism in H; eauto.
      destruct H. subst. reflexivity.
    + inversion H0.
    + destruct H0; eauto.
  - dependent destruction Hstep2...
    eapply papp_determinism. eapply H. eapply H0. eapply H1. eapply H4. eapply Htyp.
  - dependent destruction Hstep2...
    + inversion H.
    + inversion H.
    + dependent destruction Htyp.
      eapply tred_determinism; eauto.
      eapply consistent_reflexivity; eauto 3.
  - dependent destruction Hstep2...
    + destruct H; eauto.
    + destruct H; eauto.
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
Qed.

Ltac indExpSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : trm |- _ ] => (gen h) end;
  induction i as [|i IH]; [
      intros; match goal with | [ H : _ < 0 |- _ ] => (dependent destruction H) end
    | intros ].

Theorem preservation :
  forall (e e' : trm) (A: typ),
    typing nil e A ->
    step e e' ->
    (exists B, typing nil e' B /\ isomorphic B A).
Proof.
  intros e e' A Htyp Hred.
  gen e'.
  dependent induction Htyp; intros; try solve [inversion Hred].
  - dependent destruction Hred.
    exists typ_int. split; eauto.
  - dependent destruction Hred.
    exists (typ_arrow A B). split; eauto.
  - dependent destruction Hred.
    + dependent destruction Htyp.
      exists (typ_and A1 A2).
      split; eauto.
      dependent induction H1.
      eapply typing_merge_value; eauto 3.
      admit. admit.
      eapply typing_anno; eauto.
      eapply sub_inversion_split_r in H0; eauto.
      destruct_conjs. assumption.
      eapply typing_anno; eauto.
      eapply sub_inversion_split_r in H0; eauto.
      destruct_conjs. assumption.
Abort.
      

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
    + destruct (pvalue_or_not_pvalue e);
        destruct (split_or_ord A); eauto.
      * destruct H1.
        ** right. destruct_conjs.
           exists (trm_merge (trm_anno (trm_int n) H2) (trm_anno (trm_int n) H1)); eauto.
        ** right. destruct_conjs.
           exists (trm_merge (trm_anno (trm_abs e A0 B0) H2) (trm_anno (trm_abs e A0 B0) H1)); eauto.
      * destruct H0.
        right. exists (trm_anno x A); eauto.
      * destruct H0.
        right. exists (trm_anno x A); eauto.
  - right. destruct IHHtyp1; destruct IHHtyp2; eauto 3.
    + eapply papp_progress in Htyp1; eauto.
      destruct_conjs.
      exists Htyp1. eapply step_papp; eauto.
    + destruct H1; eauto.
    + destruct H0; eauto.
    + destruct H1; eauto.
  - destruct IHHtyp1; destruct IHHtyp2; eauto.
    + destruct H1; eauto.
    + destruct H0; eauto.
    + destruct H0; eauto.
Qed.
