Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language LibTactics.
Require Import Disjoint Tred.

Theorem consistent_soundness :
  forall (v1 v2 : trm) (A B : typ),
    value v1 -> value v2 ->
    typing nil v1 A ->
    typing nil v2 B ->
    consistent v1 v2 ->
    consistency_spec v1 v2.
Proof.
  introv Hv1 Hv2 Htyp1 Htyp2 Hcons.
  unfold consistency_spec.
  intros C v1' v2' Hord Htred1 Htred2.
  eapply tred_determinism.
  eapply Hv1. eapply Hv2. eapply Htyp1. eapply Htyp2.
  eapply Htred1. eapply Htred2. assumption.
Qed.

Ltac ind_exp_size s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : trm |- _ ] => (gen h) end;
  induction i as [|i IH]; [
      intros; match goal with | [ H : _ < 0 |- _ ] => (dependent destruction H; eauto) end
    | intros ].

Theorem consistent_completeness :
  forall (v1 v2 : trm) (A B : typ),
    value v1 -> value v2 ->
    typing nil v1 A ->
    typing nil v2 B ->
    consistency_spec v1 v2 ->
    consistent v1 v2.
Proof.
  introv Hv1 Hv2 Htyp1 Htyp2 Hcons.
  gen Hv1 Hv2 Hcons A B.
  ind_exp_size (size_trm v1 + size_trm v2).
  dependent destruction Hv1; dependent destruction Hv2; eauto.
  - dependent destruction H; dependent destruction H0.
    + eapply tred_progress in Htyp1; eauto.
Abort.

Lemma consistent_merge_l :
  forall v1 v2 v,
    consistent (trm_merge v1 v2) v ->
    consistent v1 v /\ consistent v2 v.
Proof.
  introv Hcons.
Abort.

Lemma consistent_symmetry :
  forall (v1 v2 : trm),
    consistent v1 v2 -> consistent v2 v1.
Proof.
  introv Hcon.
  dependent induction Hcon; eauto.
  eapply disjoint_symmetry in H1.
  eapply con_disjoint; eauto 3.
Qed.

Lemma consistent_reflexivity :
  forall (v : trm) (A : typ),
    typing nil v A ->
    value v -> consistent v v.
Proof.
  introv Htyp Hv.
  gen A.
  dependent induction Hv; eauto; intros.
  - dependent destruction Htyp.
    + assert (consistent v1 v2); eauto.
      eapply con_merge_l; eauto.
      eapply con_merge_r; eauto.
      now apply consistent_symmetry.
    + eapply con_merge_l; eauto.
      eapply con_merge_r; eauto.
      now apply consistent_symmetry.
Qed.
