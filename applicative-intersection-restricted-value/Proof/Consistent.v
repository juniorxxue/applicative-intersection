Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language LibTactics.
Require Import Disjoint Tred.
Require Import SubAndTopLike.
Require Import Program.Tactics.

Require Import Psatz. (* lia *)

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

Hint Resolve consistent_reflexivity : core.

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

Lemma disjoint_spec_decidability :
  forall (A B : typ),
    disjoint A B \/ (exists C, not (toplike C) /\ ordinary C /\ sub A C /\ sub B C).
Proof.
  introv. gen B.
  induction A; eauto; intros.
  - induction B; eauto.
    + right. exists typ_int.
      split; try solve [intros Hcontra; inversion Hcontra | eauto].
    + destruct IHB1; destruct IHB2;
        try solve [right; destruct_conjs; eexists; eauto | eauto].
  - clear IHA1.
    induction B; eauto.
    + clear IHB1 IHB2.
      pose proof (IHA2 B2).
      destruct H; eauto.
      destruct_conjs.
      right. exists (typ_arrow (typ_and A1 B1) H).
      split.
      * intros Hcontra. dependent destruction Hcontra. contradiction.
      * repeat split; eauto.
    + destruct IHB1; destruct IHB2;
        try solve [right; destruct_conjs; eexists; eauto | eauto].
  - pose proof (IHA1 B) as H1.
    pose proof (IHA2 B) as H2.
    destruct H1; destruct H2;
      try solve [right; destruct_conjs; eexists; eauto | eauto].
Qed.

Search sub.

Lemma sub_arrow_form :
  forall (A B C : typ),
    not (toplike C) -> ordinary C ->
    sub (typ_arrow A B) C ->
    (exists D E, C = (typ_arrow D E)).
Proof.
  introv nHtl Hord Hsub.
  induction Hord; eauto.
  - destruct nHtl; eauto.
  - dependent destruction Hsub.
    + inversion H0.
    + inversion H.
Qed.

Lemma consistency_spec_abs_inversion :
  forall (T1 T2 A1 A2 B1 B2 C1 C2 : typ) (e1 e2 : trm),
    ordinary C1 -> ordinary C2 ->
    not (toplike C1) -> not (toplike C2) ->
    typing nil (trm_anno (trm_abs e1 A1 B1) C1) T1 ->
    typing nil (trm_anno (trm_abs e2 A2 B2) C2) T2 ->
    consistency_spec (trm_anno (trm_abs e1 A1 B1) C1) (trm_anno (trm_abs e2 A2 B2) C2) ->
    disjoint C1 C2 \/ (e1 = e2 /\ A1 = A2 /\ B1 = B2).
Proof.
  introv Hord1 Hord2 nHtl1 nHtl2 Htyp1 Htyp2 Hcons.
  dependent destruction Htyp1. dependent destruction Htyp2.
  dependent destruction Htyp1. dependent destruction Htyp2.
  assert (exists D E, C1 = (typ_arrow D E)) by (eapply sub_arrow_form; eauto).
  assert (exists D E, C2 = (typ_arrow D E)) by (eapply sub_arrow_form; eauto).
  destruct_conjs. subst.
  unfold consistency_spec in Hcons.
  destruct (disjoint_spec_decidability H7 H5); eauto.
  - right.
    destruct_conjs.
    assert (Htyp1': typing nil (trm_anno (trm_abs e1 A1 B1)
                                         (typ_arrow H3 H7)) (typ_arrow H3 H7)) by eauto.
    assert (exists v', typedred (trm_anno (trm_abs e1 A1 B1)
                                     (typ_arrow H3 H7)) (typ_arrow (typ_and H3 H4) H6) v').
    eapply tred_progress; eauto.
    assert (Htyp2': typing nil (trm_anno (trm_abs e2 A2 B2)
                                         (typ_arrow H4 H5)) (typ_arrow H4 H5)) by eauto.
    assert (exists v', typedred (trm_anno (trm_abs e2 A2 B2)
                                     (typ_arrow H4 H5)) (typ_arrow (typ_and H3 H4) H6) v').
    eapply tred_progress; eauto.
    destruct_conjs.
    pose proof (Hcons (typ_arrow (typ_and H3 H4) H6)).
    assert (H12 = H13). eapply H16; eauto. subst.
    dependent destruction H15.
    + dependent destruction H12. contradiction.
    + dependent destruction H15; eauto.
    + dependent destruction H12. exfalso; eauto.
Qed.

Lemma consistency_spec_merge_l :
  forall (v v1 v2 : trm),
    consistency_spec (trm_merge v1 v2) v ->
    consistency_spec v1 v /\ consistency_spec v2 v.
Proof.
  introv H.
  split; unfold consistency_spec in *; intros; eauto.
Qed.

Lemma consistency_spec_merge_r :
  forall (v v1 v2 : trm),
    consistency_spec v (trm_merge v1 v2) ->
    consistency_spec v v1 /\ consistency_spec v v2.
Proof.
  introv H.
  split; unfold consistency_spec in *; intros; eauto.
Qed.

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
  dependent destruction Hv1; dependent destruction Hv2; eauto; simpl in SizeInd.
  - dependent destruction Htyp1. dependent destruction Htyp2.
    destruct (toplike_or_not_toplike A); destruct (toplike_or_not_toplike A0).
    + assert (disjoint A A0). eapply disjoint_toplike; eauto.
      eauto.
    + assert (disjoint A A0). eapply disjoint_toplike; eauto.
      eauto.
    + assert (disjoint A A0). eapply disjoint_symmetry.
      eapply disjoint_toplike; eauto.
      eauto.
    + dependent destruction H; dependent destruction H1; eauto.
      * dependent destruction Htyp1.
        dependent destruction Htyp2.
        eapply sub_int_form in H3; eauto. subst.
        eapply sub_int_form in H4; eauto. subst.
        assert (Htyp1': typing nil (trm_anno (trm_int n) typ_int) typ_int) by eauto.
        eapply tred_progress in Htyp1'; eauto.
        assert (Htyp2': typing nil (trm_anno (trm_int n0) typ_int) typ_int) by eauto.
        eapply tred_progress in Htyp2'; eauto.
        destruct_conjs.
        assert ((trm_anno (trm_int n) typ_int) = Htyp1').
        assert (value (trm_anno (trm_int n) typ_int)) by eauto.
        eapply tred_determinism; eauto.
        assert ((trm_anno (trm_int n0) typ_int) = Htyp2').
        assert (value (trm_anno (trm_int n0) typ_int)) by eauto.
        eapply tred_determinism; eauto.
        subst.
        unfold consistency_spec in Hcons.
        pose proof (Hcons typ_int (trm_anno (trm_int n) typ_int)
                          (trm_anno (trm_int n0) typ_int) H0 H4 H3).
        now rewrite H7.
      * dependent destruction Htyp1. eapply sub_int_form in H3; eauto. subst.
        dependent destruction Htyp2.
        assert (disjoint typ_int (typ_arrow A1 B)) by eauto.
        assert (disjoint typ_int A0). eapply disjoint_symmetry. eapply disjoint_sub; eauto.
        eauto.
      * dependent destruction Htyp2. eapply sub_int_form in H4; eauto. subst.
        dependent destruction Htyp1.
        assert (disjoint typ_int (typ_arrow A1 B)) by eauto.
        assert (disjoint A typ_int). eapply disjoint_sub; eauto.
        eauto.
      * dependent destruction Htyp1. dependent destruction Htyp2.
        eapply consistency_spec_abs_inversion in Hcons; eauto.
        destruct Hcons; eauto. destruct_conjs. subst. eauto.
  - eapply consistency_spec_merge_r in Hcons.
    destruct_conjs.
    dependent destruction Htyp2.
    + eapply con_merge_r.
      * pose proof (IH (trm_anno e A) v1).
        eapply H4; eauto. simpl. lia.
      * pose proof (IH (trm_anno e A) v2).
        eapply H4; eauto. simpl. lia.
    + eapply con_merge_r.
      * pose proof (IH (trm_anno e A) v1).
        eapply H6; eauto. simpl. lia.
      * pose proof (IH (trm_anno e A) v2).
        eapply H6; eauto. simpl. lia.
  - eapply consistency_spec_merge_l in Hcons.
    destruct_conjs.
    dependent destruction Htyp1.
    + eapply con_merge_l.
      * pose proof (IH v1 (trm_anno e A)).
        eapply H4; eauto. simpl. lia.
      * pose proof (IH v0 (trm_anno e A)).
        eapply H4; eauto. simpl. lia.
    + eapply con_merge_l.
      * pose proof (IH v1 (trm_anno e A)).
        eapply H6; eauto. simpl. lia.
      * pose proof (IH v0 (trm_anno e A)).
        eapply H6; eauto. simpl. lia.
  - eapply consistency_spec_merge_l in Hcons.
    destruct_conjs.
    dependent destruction Htyp1.
    + eapply con_merge_l.
      * pose proof (IH v1 (trm_merge v2 v3)).
        eapply H2; eauto. simpl. lia.
      * pose proof (IH v0 (trm_merge v2 v3)).
        eapply H2; eauto. simpl. lia.
    + eapply con_merge_l.
      * pose proof (IH v1 (trm_merge v2 v3)).
        eapply H4; eauto. simpl. lia.
      * pose proof (IH v0 (trm_merge v2 v3)).
        eapply H4; eauto. simpl. lia.
Qed.

Lemma value_is_uvalue :
  forall (v : trm),
    value v -> uvalue v.
Proof.
  introv Hv.
  induction Hv; eauto.
Qed.

Hint Resolve value_is_uvalue : core.

Lemma tred_consistent_preservation :
  forall (v v1 v2 : trm) (A B C : typ),
    value v ->
    typing nil v A ->
    typedred v B v1 ->
    typedred v C v2 ->
    consistency_spec v1 v2.
Proof.
  introv Hv Htyp Hred1 Hred2.
  unfold consistency_spec.
  introv Hord Hred1' Hred2'.
  Check tred_transitivity.
  pose proof (tred_transitivity v v1 v1' B A0 Hv Hred1 Hred1').
  pose proof (tred_transitivity v v2 v2' C A0 Hv Hred2 Hred2').
  eapply tred_determinism; eauto.
Qed.

(* sorry for put it here *)
Theorem tred_preservation:
  forall (v v': trm) (A B: typ),
    value v ->
    typing nil v B ->
    typedred v A v' ->
    (exists C, typing nil v' C /\ isomorphic C A).
Proof.
  introv Hv Htyp Hred.
  gen B.
  induction Hred; intros; eauto 3.
  - exists typ_int; eauto.
  - exists A; eauto.
  - exists (typ_arrow C D). split; eauto 3.
    dependent destruction Hv. dependent destruction Htyp.
    dependent destruction Htyp.
    assert (sub (typ_arrow A B) (typ_arrow C D)) by (eapply sub_transitivity; eauto).
    eapply typing_anno; eauto.
  - dependent destruction Hv.
    dependent destruction Htyp.
    + now pose proof (IHHred Hv1 A0 Htyp1).
    + now pose proof (IHHred Hv1 A0 Htyp1).
  - dependent destruction Hv.
    dependent destruction Htyp.
    + now pose proof (IHHred Hv2 B Htyp2).
    + now pose proof (IHHred Hv2 B Htyp2).
  - pose proof (IHHred1 Hv B0 Htyp).
    pose proof (IHHred2 Hv B0 Htyp).
    destruct_conjs.
    exists (typ_and H0 H1).
    split.
    eapply typing_merge_uvalue; eauto.
    eapply consistent_completeness; eauto.
    eapply tred_consistent_preservation; eauto.
    eapply iso_and; eauto.
Qed.

Lemma consistent_merge_l :
  forall v1 v2 v,
    consistent (trm_merge v1 v2) v ->
    consistent v1 v /\ consistent v2 v.
Proof.
  introv Hcons.
Abort.
