Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Strings.String.
Require Import Language LN LibTactics.
Require Import SubAndTopLike Appsub. (* Hint Base: subtyping *)
Require Import Ptype Disjoint Value. (* Hint Base: ptype, value, lc *)
Require Import Tred Consistent. (* Hint Base: tred, con *)
Require Import Papp.
Require Import Program.Tactics.
Require Import Psatz. (* lia *)

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
  - dependent destruction Hstep; eauto.
    + assert (value v') by eauto with value.
      eapply value_is_uvalue; assumption.
    + eapply uvalue_anno; eauto with lc.
  - dependent destruction Hstep; eauto with lc.
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

Lemma size_trm_lg_z :
  forall e, size_trm e > 0.
Proof.
  introv.
  dependent induction e; try solve [eauto | simpl; lia].
Qed.

Hint Resolve size_trm_lg_z : core.

Lemma step_consistent_preservation :
  forall e1 e2 e1' e2' A B,
    uvalue e1 -> uvalue e2 ->
    typing nil e1 A -> typing nil e2 B ->
    consistent e1 e2 ->
    step_or_value e1 e1' -> step_or_value e2 e2' ->
    (forall e e' A, size_trm e < (size_trm e1 + size_trm e2) ->
        typing nil e A -> step e e' -> (exists C, typing nil e' C /\ isomorphic C A)) ->
    consistent e1' e2'.
Proof.
  introv Hu1 Hu2 Htyp1 Htyp2 Hc Hs1 Hs2 IH.
  gen A B e1' e2'.
  dependent induction Hc; intros; eauto with con.
  - dependent destruction Hs1; dependent destruction Hs2; eauto with value.
    dependent destruction H0. dependent destruction H1; eauto.
  - dependent destruction Hs1; dependent destruction Hs2; eauto.
    + dependent destruction H1; eauto with value.
      assert (pvalue (trm_abs e A B2)) by eauto with lc. contradiction.
    + dependent destruction H0; eauto with value.
      assert (pvalue (trm_abs e A B1)) by eauto with lc. contradiction.
    + dependent destruction Htyp1. dependent destruction Htyp2.
      dependent destruction H2; eauto with value.
      * dependent destruction H3; eauto with value.
        ** eapply con_merge_l; eauto.
        ** assert (pvalue (trm_abs e A B2)) by eauto with lc. contradiction.
      * assert (pvalue (trm_abs e A B1)) by eauto with lc. contradiction.
  - dependent destruction Hs1; dependent destruction Hs2; eauto.
    + dependent destruction H0. dependent destruction H0.
      ** dependent destruction H2; eauto with con value.
         assert (pvalue (trm_int n)) by eauto. contradiction.
      ** dependent destruction H2; eauto with con value.
         assert (pvalue (trm_abs e A1 B1)) by eauto. contradiction.
    + dependent destruction H1. dependent destruction H1.
      ** dependent destruction H0; eauto with con value.
         assert (pvalue (trm_int n)) by eauto. contradiction.
      ** dependent destruction H0; eauto with con value.
         assert (pvalue (trm_abs e A1 B1)) by eauto. contradiction.
    + dependent destruction Htyp1. dependent destruction Htyp2.
      dependent destruction H2.
      * dependent destruction H3; eauto with con value.
        ** eapply con_merge_l; eauto.
        ** assert (pvalue (trm_int n)) by eauto. contradiction.
      * dependent destruction H3; eauto with con value.
        ** eapply con_merge_l; eauto.
        ** assert (pvalue (trm_abs e0 A0 B2)) by eauto. contradiction.
      * dependent destruction H4; eauto with con value.
        eapply tred_consistent_preservation; eauto.
      * dependent destruction H4; eauto with con value.
        ** assert (pvalue (trm_int n)) by eauto. contradiction.
        ** assert (pvalue (trm_abs e0 A0 B2)) by eauto. contradiction.
        ** assert (e' = e'0). eapply determinism; eauto. subst.
           eapply con_anno; eauto with lc.
  - Case "Disjoint".
    dependent destruction Hs1; dependent destruction Hs2; eauto.
    + SCase "Value, Step".
      assert (exists C, typing nil e2 C /\ (isomorphic C B0)).
      eapply IH; eauto 3. assert (size_trm v > 0) by eauto.
      lia. destruct H4. destruct H4.
      assert (uvalue e2). eapply step_uvalue_preservation; eauto.
      eapply typing_to_ptype_uvalue in H4; eauto.
      eapply typing_to_ptype_uvalue in Htyp2; eauto. simpl_deter.
      eapply con_disjoint; eauto. eapply disjoint_iso_l; eauto.
    + SCase "Step, Value".
      assert (exists C, typing nil e2 C /\ (isomorphic C A0)).
      eapply IH; eauto 3. assert (size_trm v > 0) by eauto.
      lia. destruct H4. destruct H4.
      assert (uvalue e2). eapply step_uvalue_preservation. eapply Hu1. assumption.
      eapply typing_to_ptype_uvalue in H4; eauto.
      eapply typing_to_ptype_uvalue in Htyp1; eauto. simpl_deter.
      eapply con_disjoint; eauto. eapply disjoint_iso_l; eauto.
    + SCase "Step, Step".
      assert (exists C, typing nil e2 C /\ (isomorphic C A0)).
      eapply IH; eauto 3. assert (size_trm e0 > 0) by eauto.
      lia. destruct H4. destruct H4.
      assert (exists C, typing nil e3 C /\ (isomorphic C B0)).
      eapply IH; eauto 3. assert (size_trm e1 > 0) by eauto.
      lia. destruct H6. destruct H6.
      pose proof (step_uvalue_preservation _ _ Hu1 H2).
      pose proof (step_uvalue_preservation _ _ Hu2 H3).
      pose proof (typing_to_ptype_uvalue _ _ Hu1 Htyp1).
      pose proof (typing_to_ptype_uvalue _ _ Hu2 Htyp2).
      simpl_deter.
      eapply con_disjoint; eauto.
      eapply disjoint_iso_l; eauto.
  - Case "Merge L".
    dependent destruction Hs1; eauto with con value.
    + dependent destruction Htyp1; eauto with con value.
      * dependent destruction H0.
        eapply con_merge_l.
        ** eapply IHHc1; eauto with value.
           intros. eapply IH; eauto. simpl. lia.
        ** eapply IHHc2; eauto with value.
           intros. eapply IH; eauto. simpl. lia.
      * dependent destruction H3.
        eapply con_merge_l.
        ** eapply IHHc1; eauto with value.
           intros. eapply IH; eauto. simpl. lia.
        ** eapply IHHc2; eauto with value.
           intros. eapply IH; eauto. simpl. lia.
    + dependent destruction Htyp1.
      * dependent destruction Hu1; try solve [inversion H].
        dependent destruction H0.
        ** eapply con_merge_l; eauto with value.
           *** eapply IHHc1; eauto. intros. eapply IH; eauto. simpl; lia.
           *** eapply IHHc2; eauto. intros. eapply IH; eauto. simpl; lia.
        ** eapply con_merge_l; eauto with value.
           *** eapply IHHc1; eauto. intros. eapply IH; eauto. simpl; lia.
           *** eapply IHHc2; eauto. intros. eapply IH; eauto. simpl; lia.
        ** eapply con_merge_l; eauto with value.
           *** eapply IHHc1; eauto. intros. eapply IH; eauto. simpl; lia.
           *** eapply IHHc2; eauto. intros. eapply IH; eauto. simpl; lia.
      * dependent destruction H3.
        ** eapply con_merge_l; eauto with value.
           *** eapply IHHc1; eauto. intros. eapply IH; eauto. simpl; lia.
           *** eapply IHHc2; eauto. intros. eapply IH; eauto. simpl; lia.
        ** eapply con_merge_l; eauto with value.
           *** eapply IHHc1; eauto. intros. eapply IH; eauto. simpl; lia.
           *** eapply IHHc2; eauto. intros. eapply IH; eauto. simpl; lia.
        ** eapply con_merge_l; eauto with value.
           *** eapply IHHc1; eauto. intros. eapply IH; eauto. simpl; lia.
           *** eapply IHHc2; eauto. intros. eapply IH; eauto. simpl; lia.
  - Case "Merge R".
    dependent destruction Hs2; eauto with con value.
    + dependent destruction Htyp2; eauto with con value.
      * dependent destruction H0.
        eapply con_merge_r.
        ** eapply IHHc1; eauto with value.
           intros. eapply IH; eauto. simpl. lia.
        ** eapply IHHc2; eauto with value.
           intros. eapply IH; eauto. simpl. lia.
      * dependent destruction H3.
        eapply con_merge_r.
        ** eapply IHHc1; eauto with value.
           intros. eapply IH; eauto. simpl. lia.
        ** eapply IHHc2; eauto with value.
           intros. eapply IH; eauto. simpl. lia.
    + dependent destruction Htyp2.
      * dependent destruction Hu2; try solve [inversion H].
        dependent destruction H0.
        ** eapply con_merge_r; eauto with value.
           *** eapply IHHc1; eauto. intros. eapply IH; eauto. simpl; lia.
           *** eapply IHHc2; eauto. intros. eapply IH; eauto. simpl; lia.
        ** eapply con_merge_r; eauto with value.
           *** eapply IHHc1; eauto. intros. eapply IH; eauto. simpl; lia.
           *** eapply IHHc2; eauto. intros. eapply IH; eauto. simpl; lia.
        ** eapply con_merge_r; eauto with value.
           *** eapply IHHc1; eauto. intros. eapply IH; eauto. simpl; lia.
           *** eapply IHHc2; eauto. intros. eapply IH; eauto. simpl; lia.
      * dependent destruction H3.
        ** eapply con_merge_r; eauto with value.
           *** eapply IHHc1; eauto. intros. eapply IH; eauto. simpl; lia.
           *** eapply IHHc2; eauto. intros. eapply IH; eauto. simpl; lia.
        ** eapply con_merge_r; eauto with value.
           *** eapply IHHc1; eauto. intros. eapply IH; eauto. simpl; lia.
           *** eapply IHHc2; eauto. intros. eapply IH; eauto. simpl; lia.
        ** eapply con_merge_r; eauto with value.
           *** eapply IHHc1; eauto. intros. eapply IH; eauto. simpl; lia.
           *** eapply IHHc2; eauto. intros. eapply IH; eauto. simpl; lia.
Qed.

Theorem preservation' :
  forall (e e' : trm) (A: typ),
    typing nil e A ->
    step e e' ->
    (exists B, typing nil e' B /\ isomorphic B A).
Proof.
  intros e e' A Htyp Hred.  
  gen e' A.
  indExpSize (size_trm e).
  dependent destruction Htyp.
  - dependent destruction Hred.
    exists typ_int. split; eauto.
  - dependent destruction Hred.
  - dependent destruction Hred.
    exists (typ_arrow A B). split; eauto 3.
  - dependent destruction Hred.
    + dependent destruction Htyp.
      exists (typ_and A1 A2).
      split; eauto.
      dependent induction H.
      * eapply typing_merge_uvalue; eauto 3.
        eapply typing_anno; eauto.
        eapply sub_inversion_split_r in H1; eauto.
        destruct_conjs. assumption.
        eapply typing_anno; eauto.
        eapply sub_inversion_split_r in H1; eauto.
        destruct_conjs. assumption.
      * destruct (toplike_decidability B).
        ** eapply split_toplike in H; eauto.
           destruct H.
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
      eapply sub_inversion_split_r in H; eauto.
      destruct H.
      eapply typing_merge_uvalue; eauto with lc.
    + eapply tred_preservation; eauto.
    + eapply IH in Hred; eauto.
      destruct Hred.
      exists A. split; eauto 3.
      destruct_conjs.
      eapply iso_to_sub in H2.
      assert (sub x A) by (eapply sub_transitivity; eauto).
      eapply typing_anno with (C:=x); eauto.
      simpl in SizeInd. lia.
  - dependent destruction Hred.
    + pose proof (papp_preservation e1 e2 e) as Hp.
      eapply Hp; eauto.
    + assert (exists B0, typing nil e1' B0 /\ isomorphic B0 B).
      eapply IH; eauto. simpl in SizeInd. lia.
      destruct H1.
      destruct H1.
      eapply appsub_iso in H0; eauto.
      destruct H0. destruct H0.
      exists x0. split; eauto.
    + assert (exists B0, typing nil e2' B0 /\ isomorphic B0 A).
      eapply IH; eauto. simpl in SizeInd. lia.
      destruct H1. destruct H1.
      eapply appsub_iso in H0; eauto.
      destruct H0. destruct H0.
      exists x0. split; eauto.
  - dependent destruction Hred.
    + assert (exists C, (typing nil e1' C) /\ (isomorphic C A)).
      eapply IH; eauto. simpl in SizeInd. lia.
      assert (exists C, (typing nil e2' C) /\ (isomorphic C B)).
      eapply IH; eauto. simpl in SizeInd. lia.
      destruct_conjs.
      exists (typ_and H0 H1).
      split.
      eapply typing_merge; eauto.
      eapply disjoint_iso_l; eauto.
      eauto.
    + assert (exists C, (typing nil e1' C) /\ (isomorphic C A)).
      eapply IH; eauto. simpl in SizeInd. lia.   
      assert (exists C, (typing nil e2 C) /\ (isomorphic C B)); eauto.
      destruct_conjs.
      exists (typ_and H1 H2).
      split.
      eapply typing_merge; eauto.
      eapply disjoint_iso_l; eauto.
      eauto.
    + assert (exists C, (typing nil e1 C) /\ (isomorphic C A)) by eauto.
      assert (exists C, (typing nil e2' C) /\ (isomorphic C B)).
      eapply IH; eauto. simpl in SizeInd. lia.
      destruct_conjs.
      exists (typ_and H1 H2).
      split.
      eapply typing_merge; eauto.
      eapply disjoint_iso_l; eauto.
      eauto.
  - dependent destruction Hred.
    + assert (exists C, (typing nil e1' C) /\ (isomorphic C A)).
      eapply IH; eauto. simpl in SizeInd. lia.
      assert (exists C, (typing nil e2' C) /\ (isomorphic C B)).
      eapply IH; eauto. simpl in SizeInd. lia.
      destruct_conjs.
      exists (typ_and H3 H4).
      pose proof (step_uvalue_preservation _ _ H0 Hred1).
      pose proof (step_uvalue_preservation _ _ H1 Hred2).
      split; eauto.
      eapply typing_merge_uvalue; eauto.
      pose proof (sov_s _ _ Hred1) as Sov1.
      pose proof (sov_s _ _ Hred2) as Sov2.
      pose proof (step_consistent_preservation u1 u2 e1' e2' A B H0 H1 Htyp1 Htyp2 H2 Sov1 Sov2).
      eapply H11. intros. eapply IH; eauto. simpl in *. lia.
    + assert (exists C, (typing nil e1' C) /\ (isomorphic C A)).
      eapply IH; eauto. simpl in SizeInd. lia.
      destruct_conjs.
      exists (typ_and H4 B).
      pose proof (step_uvalue_preservation _ _ H1 Hred).
      split; eauto.
      eapply typing_merge_uvalue; eauto.
      pose proof (sov_s _ _ Hred) as Sov1.
      pose proof (sov_v _ H) as Sov2.
      pose proof (step_consistent_preservation u1 u2 e1' u2 A B H1 H2 Htyp1 Htyp2 H3 Sov1 Sov2).
      eapply H8; eauto. intros. eapply IH; eauto. simpl in SizeInd. lia.
    + assert (exists C, (typing nil e2' C) /\ (isomorphic C B)).
      eapply IH; eauto. simpl in SizeInd. lia.
      destruct_conjs.
      exists (typ_and A H4).
      pose proof (step_uvalue_preservation _ _ H2 Hred).
      split; eauto.
      eapply typing_merge_uvalue; eauto.
      pose proof (sov_v _ H) as Sov1.
      pose proof (sov_s _ _ Hred) as Sov2.
      pose proof (step_consistent_preservation u1 u2 u1 e2' A B H1 H2 Htyp1 Htyp2 H3 Sov1 Sov2).
      eapply H8; eauto. intros. eapply IH; eauto. simpl in SizeInd. lia.
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
