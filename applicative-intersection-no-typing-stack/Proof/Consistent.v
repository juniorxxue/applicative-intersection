Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language LibTactics.
Require Import Tred.

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
