Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Strings.String.
Require Import Language LN LibTactics.
Require Import SubAndTopLike Appsub. (* Hint Base: subtyping *)
Require Import Ptype Disjoint Value. (* Hint Base: ptype, value, lc *)
Require Import Tred Consistent. (* Hint Base: tred, con *)
Require Import Papp.
Require Import Program.Tactics.

Set Printing Parentheses.

Theorem determinism:
  forall (e e1 e2 : trm) (A : typ),
    typing nil e A ->
    step e e1 -> step e e2 -> e1 = e2.
Proof with eauto with value.
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
    + dependent destruction Htyp.
      eapply tred_determinism; eauto.
  - dependent destruction Hstep2...
    + destruct H; eauto.
    + destruct H; eauto with lc.
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
    + dependent destruction Htyp.
      * assert (e1' = e1'0)...
        assert (e2' = e2'0)...
        congruence.
      * assert (e1' = e1'0)...
        assert (e2' = e2'0)...
        congruence.
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

Inductive step_or_value : trm -> trm -> Prop :=
| sov_v : forall v, value v -> step_or_value v v
| sov_s : forall e1 e2, step e1 e2 -> step_or_value e1 e2.

Hint Constructors step_or_value : core.

Lemma step_consistent_preservation :
  forall e1 e2 e1' e2' A B,
    typing nil e1 A -> typing nil e2 B ->
    consistent e1 e2 ->
    step_or_value e1 e1' -> step_or_value e2 e2' ->
    consistent e1' e2'.
Proof.
  introv Ht1 Ht2 Hc Hs1 Hs2.
  gen A B e1' e2'.
  dependent induction Hc; intros; eauto with con.
  - dependent destruction Hs1; dependent destruction Hs2; eauto with value.
    dependent destruction H0. dependent destruction H1.
    admit.
  - dependent destruction Hs1; dependent destruction Hs2; eauto with value.
    + dependent destruction H1; eauto.
Abort.

Lemma step_consistent_preservation_l :
  forall e1 e2 e1' A B,
    typing nil e1 A -> typing nil e2 B ->
    consistent e1 e2 ->
    step e1 e1' ->
    consistent e1' e2.
Proof.
Admitted.

Lemma step_consistent_preservation_r :
  forall e1 e2 e2' A B,
    typing nil e1 A -> typing nil e2 B ->
    consistent e1 e2 ->
    step e2 e2' ->
    consistent e1 e2'.
Proof.
Admitted.

Lemma step_consistent_preservation :
  forall e1 e2 e1' e2' A B,
    typing nil e1 A -> typing nil e2 B ->
    consistent e1 e2 ->
    step e1 e1' -> step e2 e2' ->
    consistent e1' e2'.
Proof.
Admitted.
 
Lemma tred_lc_preservation :
  forall v v' A,
    lc v ->
    typedred v A v' ->
    lc v'.
Proof.
  introv Lc Htred.
  dependent induction Htred; eauto with lc.
Qed.

Hint Resolve tred_lc_preservation : lc.

Lemma papp_lc_preservation :
  forall e1 e2 e,
    lc e1 -> lc e2 -> papp e1 e2 e -> lc e.
Proof.
  introv Lc1 Lc2 Hp.
  dependent induction Hp; eauto 3 with lc.
  - eapply lc_anno. eapply open_abs; eauto with lc.
  - dependent destruction Lc1; eauto.
Qed.

Hint Resolve papp_lc_preservation : lc.                                       

Lemma step_lc_preservation :
  forall e e',
    lc e -> step e e' -> lc e'.
Proof.
  introv Hlc Hstep. gen e'.
  induction Hlc; intros;
    try solve [dependent destruction Hstep; eauto].
  - dependent destruction Hstep; eauto 3 with lc.
  - dependent destruction Hstep; eauto 3 with lc.
    + eapply lc_merge; eauto.
    + eapply lc_merge; eauto.
Qed.

Hint Resolve step_lc_preservation : lc.

Lemma step_uvalue_preservation :
  forall u u',
    uvalue u -> step u u' -> uvalue u'.
Proof.
  introv Hu Hstep. gen u'.
  induction Hu; intros.
  - dependent destruction H.
    + dependent destruction Hstep; eauto.
    + dependent destruction Hstep; eauto.
  - dependent destruction Hstep; eauto.
    + assert (value v') by eauto with value.
      eapply value_is_uvalue; assumption.
    + eapply uvalue_anno; eauto with lc.
  - dependent destruction Hstep; eauto with lc.
Qed.

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
    exists (typ_arrow A B). split; eauto 3.
  - dependent destruction Hred.
    + dependent destruction Htyp.
      exists (typ_and A1 A2).
      split; eauto.
      dependent induction H1.
      * eapply typing_merge_uvalue; eauto 3.
        eapply typing_anno; eauto.
        eapply sub_inversion_split_r in H0; eauto.
        destruct_conjs. assumption.
        eapply typing_anno; eauto.
        eapply sub_inversion_split_r in H0; eauto.
        destruct_conjs. assumption.
      * destruct (toplike_decidability B0).
        ** eapply split_toplike in H1; eauto.
           destruct H1.
           eapply typing_merge_uvalue; eauto 3.
           *** eapply typing_anno; eauto.
               assert (toplike (typ_arrow A C)) by eauto.
               now eapply sub_toplike.
           *** eapply typing_anno; eauto.
               assert (toplike (typ_arrow A D)) by eauto.
               now eapply sub_toplike.
        ** eauto with subtyping.
    + dependent destruction Htyp.
      exists (typ_and C1 C2).
      split; eauto.
      eapply sub_inversion_split_r in H1; eauto.
      destruct H1.
      eapply typing_merge_uvalue; eauto 3.
      eapply uvalue_anno.
      assert (typing nil (trm_abs e0 A0 B0) (typ_arrow A0 B0)); eauto.
      eapply uvalue_anno.
      assert (typing nil (trm_abs e0 A0 B0) (typ_arrow A0 B0)); eauto.
      eapply con_anno; eauto.
    + eapply tred_preservation; eauto.
    + eapply IHHtyp in Hred; eauto.
      destruct Hred.
      exists A. split; eauto 3.
      destruct_conjs.
      eapply iso_to_sub in H2.
      assert (sub x A) by (eapply sub_transitivity; eauto).
      eapply typing_anno with (C:=x); eauto.
  - dependent destruction Hred.
    + pose proof (papp_preservation e1 e2 e) as Hp.
      eapply Hp; eauto.
    + assert (exists B0, typing nil e1' B0 /\ isomorphic B0 B) by eauto.
      destruct H1.
      destruct H1.
      eapply appsub_iso2 in H; eauto.
      destruct H. destruct H.
      exists x0. split; eauto.
    + assert (exists B0, typing nil e2' B0 /\ isomorphic B0 A) by eauto.
      destruct H1. destruct H1.
      eapply appsub_iso1 in H; eauto.
      destruct H. destruct H.
      exists x0. split; eauto.
  - dependent destruction Hred.
    + assert (exists C, (typing nil e1' C) /\ (isomorphic C A)) by eauto.
      assert (exists C, (typing nil e2' C) /\ (isomorphic C B)) by eauto.
      destruct_conjs.
      exists (typ_and H0 H1).
      split.
      eapply typing_merge; eauto.
      eapply disjoint_iso_l; eauto.
      eauto.
    + assert (exists C, (typing nil e1' C) /\ (isomorphic C A)) by eauto.
      assert (exists C, (typing nil e2 C) /\ (isomorphic C B)) by eauto.
      destruct_conjs.
      exists (typ_and H1 H2).
      split.
      eapply typing_merge; eauto.
      eapply disjoint_iso_l; eauto.
      eauto.
    + assert (exists C, (typing nil e1 C) /\ (isomorphic C A)) by eauto.
      assert (exists C, (typing nil e2' C) /\ (isomorphic C B)) by eauto.
      destruct_conjs.
      exists (typ_and H1 H2).
      split.
      eapply typing_merge; eauto.
      eapply disjoint_iso_l; eauto.
      eauto.
  - dependent destruction Hred.
    + assert (exists C, (typing nil e1' C) /\ (isomorphic C A)) by eauto.
      assert (exists C, (typing nil e2' C) /\ (isomorphic C B)) by eauto.
      destruct_conjs.
      exists (typ_and H3 H4).
      pose proof (step_uvalue_preservation _ _ H0 Hred1).
      pose proof (step_uvalue_preservation _ _ H1 Hred2).
      split; eauto.
      eapply typing_merge_uvalue; eauto.
      pose proof (step_consistent_preservation u1 u2 e1' e2' A B Htyp1 Htyp2 H2 Hred1 Hred2).
      assumption.
    + assert (exists C, (typing nil e1' C) /\ (isomorphic C A)) by eauto.
      destruct_conjs.
      exists (typ_and H4 B).
      pose proof (step_uvalue_preservation _ _ H0 Hred).
      split; eauto.
      eapply typing_merge_uvalue; eauto.
      pose proof (step_consistent_preservation_l u1 u2 e1' A B Htyp1 Htyp2 H2 Hred).
      assumption.
    + assert (exists C, (typing nil e2' C) /\ (isomorphic C B)) by eauto.
      destruct_conjs.
      exists (typ_and A H4).
      pose proof (step_uvalue_preservation _ _ H1 Hred).
      split; eauto.
      eapply typing_merge_uvalue; eauto.
      pose proof (step_consistent_preservation_r u1 u2 e2' A B Htyp1 Htyp2 H2 Hred).
      assumption.
Qed.

Theorem progress :
  forall (e : trm) (A : typ),
    typing nil e A ->
    value e \/ exists e', step e e'.
Proof.
  introv Htyp.
  dependent induction Htyp; eauto.
  - destruct IHHtyp; eauto.
    + right.
      eapply tred_progress in Htyp; eauto.
      destruct Htyp.
      exists x. eapply step_anno_value; eauto.
    + destruct (pvalue_decidability e);
        destruct (split_or_ord A); eauto.
      * destruct H1.
        ** right. destruct_conjs.
           exists (trm_merge (trm_anno (trm_int n) H2) (trm_anno (trm_int n) H1)); eauto.
        ** right. destruct_conjs.
           exists (trm_merge (trm_anno (trm_abs e A0 B0) H2) (trm_anno (trm_abs e A0 B0) H3)); eauto.
      * destruct H0.
        right. exists (trm_anno x A); eauto.
      * destruct H0.
        right. exists (trm_anno x A); eauto.
  - right. destruct IHHtyp1; destruct IHHtyp2; eauto; try solve [destruct_conjs; eauto].
    + eapply papp_progress in Htyp1; eauto.
      destruct_conjs.
      exists Htyp1. eapply step_papp; eauto.
  - destruct IHHtyp1; destruct IHHtyp2; try solve [eauto | destruct_conjs; eauto].
  - destruct IHHtyp1; destruct IHHtyp2; try solve [eauto | destruct_conjs; eauto].
Qed.
