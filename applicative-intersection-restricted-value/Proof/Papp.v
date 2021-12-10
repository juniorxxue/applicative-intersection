Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language LibTactics LN.
Require Import Coq.Program.Tactics.
Require Import SubAndTopLike Ptype Appsub Tred Consistent Disjoint Value.

Set Printing Parentheses.

Lemma typing_merge_distri_app_l :
  forall (A C D: typ) (v1 v2 vl : trm),
    value v1 -> value v2 -> value vl ->
    ptype v1 A -> ptype vl C ->
    typing nil (trm_app (trm_merge v1 v2) vl) D ->
    auxas (Some C) A ->
    exists E, typing nil (trm_app v1 vl) E.
Proof.
  introv Hv1 Hv2 Hvl Hp1 Hpl Htyp Has.
  dependent destruction Htyp.
  dependent destruction Htyp2.
  - dependent destruction H0; eauto.
    eapply typing_to_ptype in Htyp2_1; eauto.
    eapply typing_to_ptype in Htyp1; eauto.
    simpl_deter. contradiction.
  - dependent destruction H3; eauto.
    eapply typing_to_ptype in Htyp2_1; eauto.
    eapply typing_to_ptype in Htyp1; eauto.
    simpl_deter. contradiction.
Qed.

Lemma typing_merge_distri_app_r :
  forall (B C D: typ) (v1 v2 vl : trm),
    value v1 -> value v2 -> value vl ->
    ptype v2 B -> ptype vl C ->
    typing nil (trm_app (trm_merge v1 v2) vl) D ->
    auxas (Some C) B ->
    exists E, typing nil (trm_app v2 vl) E.
Proof.
  introv Hv1 Hv2 Hvl Hp2 Hpl Htyp Has.
  dependent destruction Htyp.
  dependent destruction Htyp2.
  - dependent destruction H0; eauto.
    eapply typing_to_ptype in Htyp2_2; eauto.
    eapply typing_to_ptype in Htyp1; eauto.
    simpl_deter. contradiction.
  - dependent destruction H3; eauto.
    eapply typing_to_ptype in Htyp2_2; eauto.
    eapply typing_to_ptype in Htyp1; eauto.
    simpl_deter. contradiction.
Qed.

(* typing is only accouting for checking merges *)
Lemma papp_to_auxas_l :
  forall v1 v2 vl e A B C D,
    value v1 -> value v2 -> value vl ->
    ptype v1 A ->
    ptype v2 B ->
    ptype vl C ->
    typing nil (trm_app (trm_merge v1 v2) vl) D ->
    papp v1 vl e ->
    not (auxas (Some C) B) ->
    auxas (Some C) A.
Proof.
  introv Val1 Val2 Val Ptyp1 Ptyp2 Ptyp Typ Papp nAux.
  dependent destruction Typ.
  dependent destruction Typ2.
  - pose proof (typing_to_ptype _ _ Val1 Typ2_1).
    pose proof (typing_to_ptype _ _ Val2 Typ2_2).
    pose proof (typing_to_ptype _ _ Val Typ1).
    simpl_deter.
    dependent destruction H0.
    + eapply appsub_to_auxas; eauto.
    + eapply appsub_to_auxas in H0; eauto. contradiction.
    + eapply appsub_to_auxas in H0_0; eauto. contradiction.
  - pose proof (typing_to_ptype _ _ Val1 Typ2_1).
    pose proof (typing_to_ptype _ _ Val2 Typ2_2).
    pose proof (typing_to_ptype _ _ Val Typ1).
    simpl_deter.
    dependent destruction H3.
    + eapply appsub_to_auxas; eauto.
    + eapply appsub_to_auxas in H3; eauto. contradiction.
    + eapply appsub_to_auxas in H3_0; eauto. contradiction.
Qed.

Lemma papp_to_auxas_r :
  forall v1 v2 vl e A B C D,
    value v1 -> value v2 -> value vl ->
    ptype v1 A ->
    ptype v2 B ->
    ptype vl C ->
    typing nil (trm_app (trm_merge v1 v2) vl) D ->
    papp v2 vl e ->
    not (auxas (Some C) A) ->
    auxas (Some C) B.
Proof.
  introv Val1 Val2 Val Ptyp1 Ptyp2 Ptyp Typ Papp nAux.
  dependent destruction Typ.
  dependent destruction Typ2.
  - pose proof (typing_to_ptype _ _ Val1 Typ2_1).
    pose proof (typing_to_ptype _ _ Val2 Typ2_2).
    pose proof (typing_to_ptype _ _ Val Typ1).
    simpl_deter.
    dependent destruction H0.
    + eapply appsub_to_auxas in H0; eauto. contradiction.
    + eapply appsub_to_auxas in H0; eauto.
    + eapply appsub_to_auxas in H0_0; eauto.
  - pose proof (typing_to_ptype _ _ Val1 Typ2_1).
    pose proof (typing_to_ptype _ _ Val2 Typ2_2).
    pose proof (typing_to_ptype _ _ Val Typ1).
    simpl_deter.
    dependent destruction H3.
    + eapply appsub_to_auxas in H3; eauto. contradiction.
    + eapply appsub_to_auxas in H3; eauto.
    + eapply appsub_to_auxas in H3_0; eauto.
Qed.

Theorem papp_determinism :
  forall (v vl e1 e2 : trm) (A : typ),
    value v -> value vl ->
    papp v vl e1 ->
    papp v vl e2 ->
    typing nil (trm_app v vl) A ->
    e1 = e2.
Proof.
  introv Hv Hvl Hp1 Hp2 Htyp.
  gen e2 A.
  dependent induction Hp1; intros.
  - dependent destruction Hp2; eauto.
  - dependent destruction Hp2; eauto.
    contradiction.
  - dependent destruction Hp2.
    + contradiction.
    + dependent destruction Htyp.
      assert (v' = v'0).
      eapply tred_determinism; eauto with con.
      congruence.
  - dependent destruction Hp2.
    + (* correct *)
      simpl_deter.
      dependent destruction Hv.
      pose proof Htyp as AS.
      eapply papp_to_auxas_l in AS; eauto.
      eapply typing_merge_distri_app_l in Htyp; eauto 3.
      destruct Htyp.
      eapply IHHp1; eauto 3.
    + simpl_deter.
      dependent destruction Hv.
      pose proof Htyp as AS.
      eapply papp_to_auxas_r in AS; eauto.
      contradiction.
    + simpl_deter.
      contradiction.
  - dependent destruction Hp2.
    + simpl_deter.
      dependent destruction Hv.
      pose proof Htyp as AS.
      eapply papp_to_auxas_l in AS; eauto.
      contradiction.
    + (* correct *)
      simpl_deter.
      dependent destruction Hv.
      pose proof Htyp as AS.
      eapply papp_to_auxas_r in AS; eauto.
      eapply typing_merge_distri_app_r in Htyp; eauto 3.
      destruct Htyp.
      eapply IHHp1; eauto 3.
    + simpl_deter. contradiction.
  - dependent destruction Hp2.
    + simpl_deter. contradiction.
    + simpl_deter. contradiction.
    + (* correct *)
      simpl_deter.
      dependent destruction Hv.
      assert (exists E, typing nil (trm_app v1 vl) E).
      eapply typing_merge_distri_app_l in Htyp; eauto.
      assert (exists E, typing nil (trm_app v2 vl) E).
      eapply typing_merge_distri_app_r in Htyp; eauto.
      destruct_conjs.
      assert (e1 = e0); eauto 3.
      assert (e2 = e3); eauto 3.
      congruence.
Qed.

Lemma papp_uvalue :
  forall (v vl e : trm) (A B: typ),
    value v -> value vl ->
    typing nil v A ->
    typing nil vl B ->
    papp v vl e ->
    uvalue e.
Proof.
  introv Hv1 Hv2 Htyp1 Htyp2 Hpapp.
  gen A B.
  induction Hpapp; intros; eauto.
  - dependent destruction Hv1.
    dependent destruction Htyp1; eauto.
    assert (value v') by eauto with value.
    eapply uvalue_anno.
    eapply open_abs; eauto with lc.
  - dependent destruction Hv1.
    dependent destruction Htyp1; eauto.
  - dependent destruction Hv1.
    dependent destruction Htyp1; eauto.
  - dependent destruction Hv1.
    dependent destruction Htyp1; eauto.
Qed.

Lemma uvalue_ptype :
  forall (u : trm),
    uvalue u ->
    (exists A, ptype u A).
Proof.
  introv Hu.
  dependent induction Hu; eauto.
  destruct_conjs; eauto.
Qed.

Lemma open_abs_auto :
  forall e v v' A B C,
    value v ->
    typedred v A v' ->
    lc (trm_abs e B C) ->
    lc (open e v').
Proof.
  introv Hv H LC.
  eapply tred_value_preservation in H.
  eapply open_abs; eauto.
  eapply value_lc. assumption. assumption.
Qed.

Hint Resolve open_abs_auto : lc.

Lemma papp_consistent :
  forall (v1 v2 vl e1 e2 : trm) (A B C : typ),
    value v1 -> value v2 -> value vl ->
    typing nil v1 A ->
    typing nil v2 B ->
    typing nil vl C ->
    papp v1 vl e1 ->
    papp v2 vl e2 ->
    consistent v1 v2 ->
    consistent e1 e2.
Proof.
  introv Hv1 Hv2 Hvl Htyp1 Htyp2 Htyp Hp1 Hp2 Hcons.
  gen A B C.
  dependent induction Hp1.
  - dependent induction Hp2; intros; eauto. (* all solved by consistent -> disjoint -> toplike *)
    + eapply con_disjoint; eauto with lc.
      eapply disjoint_toplike; eauto.
    + dependent destruction Hv2.
      dependent destruction Htyp2.
      * eapply IHHp2; eauto.
        eapply con_disjoint; eauto.
        eapply disjoint_toplike; eauto.
      * eapply IHHp2; eauto.
        eapply con_disjoint; eauto.
        eapply disjoint_toplike; eauto.
    + dependent destruction Hv2.
      dependent destruction Htyp2.
      * eapply IHHp2; eauto.
        eapply con_disjoint; eauto.
        eapply disjoint_toplike; eauto.
      * eapply IHHp2; eauto.
        eapply con_disjoint; eauto.
        eapply disjoint_toplike; eauto.
    + dependent destruction Hv2.
      eapply con_merge_r.
      * dependent destruction Htyp2.
        ** eapply IHHp2_1; eauto.
           eapply con_disjoint; eauto.
           eapply disjoint_toplike; eauto.
        ** eapply IHHp2_1; eauto.
           eapply con_disjoint; eauto.
           eapply disjoint_toplike; eauto.
      * dependent destruction Htyp2.
        ** eapply IHHp2_2; eauto.
           eapply con_disjoint; eauto.
           eapply disjoint_toplike; eauto.
        ** eapply IHHp2_2; eauto.
           eapply con_disjoint; eauto.
           eapply disjoint_toplike; eauto.
  - dependent induction Hp2; intros; eauto. (* all solved by consistent -> disjoint -> toplike *)
    + eapply con_disjoint.
      eapply ptype_anno. eapply lc_int.
      eapply ptype_anno. eapply open_abs; eauto.
      assert (value v'0) by eauto with value. eauto with lc.
      eapply disjoint_toplike; eauto.
    + dependent destruction Hv2.
      dependent destruction Htyp2.
      * eapply IHHp2; eauto.
        eapply con_disjoint; eauto.
        eapply disjoint_toplike; eauto.
      * eapply IHHp2; eauto.
        eapply con_disjoint; eauto.
        eapply disjoint_toplike; eauto.
    + dependent destruction Hv2.
      dependent destruction Htyp2.
      * eapply IHHp2; eauto.
        eapply con_disjoint; eauto.
        eapply disjoint_toplike; eauto.
      * eapply IHHp2; eauto.
        eapply con_disjoint; eauto.
        eapply disjoint_toplike; eauto.
    + dependent destruction Hv2.
      eapply con_merge_r.
      * dependent destruction Htyp2.
        ** eapply IHHp2_1; eauto.
           eapply con_disjoint; eauto.
           eapply disjoint_toplike; eauto.
        ** eapply IHHp2_1; eauto.
           eapply con_disjoint; eauto.
           eapply disjoint_toplike; eauto.
      * dependent destruction Htyp2.
        ** eapply IHHp2_2; eauto.
           eapply con_disjoint; eauto.
           eapply disjoint_toplike; eauto.
        ** eapply IHHp2_2; eauto.
           eapply con_disjoint; eauto.
           eapply disjoint_toplike; eauto.
  - dependent induction Hp2; intros; eauto.
    + eapply con_disjoint.
      eapply ptype_anno.
      eapply open_abs; eauto.
      assert (value v') by eauto with value. eauto with lc.
      eapply ptype_anno. eapply lc_int.
      eapply disjoint_symmetry; eauto.
      eapply disjoint_toplike; eauto.
    + eapply con_disjoint; eauto with lc.
      eapply disjoint_symmetry; eauto.
      eapply disjoint_toplike; eauto.
    + dependent destruction Hcons.
      * assert (v' = v'0). eapply tred_determinism; eauto with con.
        subst. eapply con_anno. eauto with lc.
      * (* same e *)
        assert (v' = v'0). eapply tred_determinism; eauto with con.
        subst. eapply con_anno. eauto with lc.
      * dependent destruction H5. dependent destruction H6.
        dependent destruction H7.
        eapply con_disjoint; eauto with lc.
    + dependent destruction Hv2.
      dependent destruction Htyp2.
      * eapply consistent_merge_r in Hcons.
        destruct Hcons.
        eapply IHHp2; eauto.
      * eapply consistent_merge_r in Hcons.
        destruct Hcons.
        eapply IHHp2; eauto.
    + dependent destruction Hv2.
      dependent destruction Htyp2.
      * eapply consistent_merge_r in Hcons.
        destruct Hcons.
        eapply IHHp2; eauto.
      * eapply consistent_merge_r in Hcons.
        destruct Hcons.
        eapply IHHp2; eauto.
    + dependent destruction Hv2.
      dependent destruction Htyp2.
      * eapply consistent_merge_r in Hcons.
        destruct Hcons.
        eapply con_merge_r.
        ** eapply IHHp2_1; eauto.
        ** eapply IHHp2_2; eauto.
      * eapply consistent_merge_r in Hcons.
        destruct Hcons.
        eapply con_merge_r.
        ** eapply IHHp2_1; eauto.
        ** eapply IHHp2_2; eauto.
  - dependent induction Hp2; intros; eauto.
    + (* find a ptype for e *)
      dependent destruction Hv1.
      dependent destruction Htyp1.
      * pose proof (papp_uvalue _ _ _ _ _ Hv1_1 Hvl Htyp1_1 Htyp Hp1) as Ptyp.
        eapply uvalue_ptype in Ptyp. destruct Ptyp.
        eapply con_disjoint; eauto.
        eapply disjoint_symmetry.
        eapply disjoint_toplike; eauto.
      * pose proof (papp_uvalue _ _ _ _ _ Hv1_1 Hvl Htyp1_1 Htyp Hp1) as Ptyp.
        eapply uvalue_ptype in Ptyp. destruct Ptyp.
        eapply con_disjoint; eauto.
        eapply disjoint_symmetry.
        eapply disjoint_toplike; eauto.
    + (* find a ptype for e *)
      dependent destruction Hv1.
      dependent destruction Htyp1.
      * pose proof (papp_uvalue _ _ _ _ _ Hv1_1 Hvl Htyp1_1 Htyp Hp1) as Ptyp.
        pose proof (uvalue_ptype e Ptyp). destruct_conjs.
        eapply con_disjoint; eauto.
        eapply disjoint_symmetry.
        eapply disjoint_toplike; eauto.
      * pose proof (papp_uvalue _ _ _ _ _ Hv1_1 Hvl Htyp1_1 Htyp Hp1) as Ptyp.
        pose proof (uvalue_ptype e Ptyp). destruct_conjs.
        eapply con_disjoint; eauto.
        eapply disjoint_symmetry.
        eapply disjoint_toplike; eauto.
    + (* abs *)
      dependent destruction Hv1.
      eapply consistent_merge_l in Hcons.
      destruct Hcons.
      dependent destruction Htyp1.
      * eapply IHHp1; eauto.
      * eapply IHHp1; eauto.
    + dependent destruction Hv1.
      eapply consistent_merge_l in Hcons.
      destruct Hcons.
      dependent destruction Htyp1; eauto 3.
    + dependent destruction Hv1.
      eapply consistent_merge_l in Hcons.
      destruct Hcons.
      dependent destruction Htyp1; eauto 3.
    + dependent destruction Hv1.
      eapply consistent_merge_l in Hcons.
      destruct Hcons.
      dependent destruction Htyp1; eauto 3.
  - dependent induction Hp2; intros; eauto.
    + (* find a ptype for e *)
      dependent destruction Hv1.
      dependent destruction Htyp1.
      * pose proof (papp_uvalue _ _ _ _ _ Hv1_2 Hvl Htyp1_2 Htyp Hp1) as Ptyp.
        eapply uvalue_ptype in Ptyp. destruct Ptyp.
        eapply con_disjoint; eauto.
        eapply disjoint_symmetry.
        eapply disjoint_toplike; eauto.
      * pose proof (papp_uvalue _ _ _ _ _ Hv1_2 Hvl Htyp1_2 Htyp Hp1) as Ptyp.
        eapply uvalue_ptype in Ptyp. destruct Ptyp.
        eapply con_disjoint; eauto.
        eapply disjoint_symmetry.
        eapply disjoint_toplike; eauto.
    + (* find a ptype for e *)
      dependent destruction Hv1.
      dependent destruction Htyp1.
      * pose proof (papp_uvalue _ _ _ _ _ Hv1_2 Hvl Htyp1_2 Htyp Hp1) as Ptyp.
        eapply uvalue_ptype in Ptyp. destruct Ptyp.
        eapply con_disjoint; eauto.
        eapply disjoint_symmetry.
        eapply disjoint_toplike; eauto.
      * pose proof (papp_uvalue _ _ _ _ _ Hv1_2 Hvl Htyp1_2 Htyp Hp1) as Ptyp.
        eapply uvalue_ptype in Ptyp. destruct Ptyp.
        eapply con_disjoint; eauto.
        eapply disjoint_symmetry.
        eapply disjoint_toplike; eauto.
    + (* abs *)
      dependent destruction Hv1.
      eapply consistent_merge_l in Hcons.
      destruct Hcons.
      dependent destruction Htyp1.
      * eapply IHHp1; eauto.
      * eapply IHHp1; eauto.
    + dependent destruction Hv1.
      eapply consistent_merge_l in Hcons.
      destruct Hcons.
      dependent destruction Htyp1; eauto 3.
    + dependent destruction Hv1.
      eapply consistent_merge_l in Hcons.
      destruct Hcons.
      dependent destruction Htyp1; eauto 3.
    +  dependent destruction Hv1.
      eapply consistent_merge_l in Hcons.
      destruct Hcons.
       dependent destruction Htyp1; eauto 3.
  - dependent induction Hp2; intros; eauto.
    + (* find a ptype for e *)
      dependent destruction Hv1.
      dependent destruction Htyp1.
      * eapply con_merge_l.
        ** pose proof (papp_uvalue _ _ _ _ _ Hv1_1 Hvl Htyp1_1 Htyp Hp1_1) as Ptyp.
           eapply uvalue_ptype in Ptyp. destruct Ptyp.
           eapply con_disjoint; eauto.
           eapply disjoint_symmetry.
           eapply disjoint_toplike; eauto.
        ** pose proof (papp_uvalue _ _ _ _ _ Hv1_2 Hvl Htyp1_2 Htyp Hp1_2) as Ptyp.
           eapply uvalue_ptype in Ptyp. destruct Ptyp.
           eapply con_disjoint; eauto.
           eapply disjoint_symmetry.
           eapply disjoint_toplike; eauto.
      * eapply con_merge_l.
        ** pose proof (papp_uvalue _ _ _ _ _ Hv1_1 Hvl Htyp1_1 Htyp Hp1_1) as Ptyp.
           eapply uvalue_ptype in Ptyp. destruct Ptyp.
           eapply con_disjoint; eauto.
           eapply disjoint_symmetry.
           eapply disjoint_toplike; eauto.
        ** pose proof (papp_uvalue _ _ _ _ _ Hv1_2 Hvl Htyp1_2 Htyp Hp1_2) as Ptyp.
           eapply uvalue_ptype in Ptyp. destruct Ptyp.
           eapply con_disjoint; eauto.
           eapply disjoint_symmetry.
           eapply disjoint_toplike; eauto.
    + (* find a ptype for e *)
      dependent destruction Hv1.
      dependent destruction Htyp1.
      * eapply con_merge_l.
        ** pose proof (papp_uvalue _ _ _ _ _ Hv1_1 Hvl Htyp1_1 Htyp Hp1_1) as Ptyp.
           eapply uvalue_ptype in Ptyp. destruct Ptyp.
           eapply con_disjoint; eauto.
           eapply disjoint_symmetry.
           eapply disjoint_toplike; eauto.
        ** pose proof (papp_uvalue _ _ _ _ _ Hv1_2 Hvl Htyp1_2 Htyp Hp1_2) as Ptyp.
           eapply uvalue_ptype in Ptyp. destruct Ptyp.
           eapply con_disjoint; eauto.
           eapply disjoint_symmetry.
           eapply disjoint_toplike; eauto.
      * eapply con_merge_l.
        ** pose proof (papp_uvalue _ _ _ _ _ Hv1_1 Hvl Htyp1_1 Htyp Hp1_1) as Ptyp.
           eapply uvalue_ptype in Ptyp. destruct Ptyp.
           eapply con_disjoint; eauto.
           eapply disjoint_symmetry.
           eapply disjoint_toplike; eauto.
        ** pose proof (papp_uvalue _ _ _ _ _ Hv1_2 Hvl Htyp1_2 Htyp Hp1_2) as Ptyp.
           eapply uvalue_ptype in Ptyp. destruct Ptyp.
           eapply con_disjoint; eauto.
           eapply disjoint_symmetry.
           eapply disjoint_toplike; eauto.
    + (* abs *)
      dependent destruction Hv1.
      eapply consistent_merge_l in Hcons.
      destruct Hcons.
      dependent destruction Htyp1.
      * eapply con_merge_l.
        eapply IHHp1_1; eauto.
        eapply IHHp1_2; eauto.
      * eapply con_merge_l.
        eapply IHHp1_1; eauto.
        eapply IHHp1_2; eauto.
    + dependent destruction Hv1.
      eapply consistent_merge_l in Hcons.
      destruct Hcons.
      assert (consistent e1 e); dependent destruction Htyp1; eauto.
    + dependent destruction Hv1.
      eapply consistent_merge_l in Hcons.
      destruct Hcons.
      assert (consistent e1 e); dependent destruction Htyp1; eauto.
    + dependent destruction Hv1.
      eapply consistent_merge_l in Hcons.
      destruct Hcons.
      assert (consistent e1 (trm_merge e2 e3)); dependent destruction Htyp1; eauto.
Qed.

Lemma typing_weakening_gen :
  forall G E F e A,
    typing (E ++ G) e A ->
    uniq (E ++ F ++ G) ->
    typing (E ++ F ++ G) e A.
Proof.
  introv Htyp.
  gen F.
  dependent induction Htyp; introv Henv; eauto.
  pick fresh x and apply typing_lam.
  rewrite_env (([(x,A)] ++ E) ++ F ++ G).
  apply H0; eauto.
  solve_uniq. assumption.
Qed.

Lemma typing_weakening :
  forall E F e A,
    typing E e A ->
    uniq (F ++ E) ->
    typing (F ++ E) e A.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  eapply typing_weakening_gen; eauto.
Qed.

Lemma typing_uniq :
  forall E e T,
    typing E e T -> uniq E.
Proof.
  introv H.
  induction H; eauto.
  - pick fresh x.
    assert (J: uniq ((x ~ A) ++ T)); eauto.
    dependent destruction J; eauto.
Qed.

Lemma typing_subst_var_case :
  forall E F u S T (z x : atom),
    binds x T (F ++ (z ~ S) ++ E) ->
    uniq (F ++ (z ~ S) ++ E) ->
    typing E u S ->
    typing (F ++ E) (subst_exp z u x) T.
Proof.
  introv H J K.
  simpl.
  destruct (x == z).
  - subst. assert (T = S).
    eapply binds_mid_eq; eauto. subst.
    eapply typing_weakening; eauto.
  - eapply typing_var; eauto.
Qed.

Lemma fv_open_lower :
  forall e1 e2 k,
    fv e1 [<=] fv (open_rec k e2 e1).
Proof with auto.
  intros.
  generalize dependent k.
  induction e1; intros; simpl; try fsetdec...
  - specialize (IHe1_1 k).
    specialize (IHe1_2 k).
    fsetdec...
  - specialize (IHe1_1 k).
    specialize (IHe1_2 k).
    fsetdec...
Qed.

Lemma add_notin_context :
  forall x T1 T2,
    T1 [<=] add x T2 ->
    x \notin T1 ->
    T1 [<=] T2.
Proof with auto.
  intros.
  fsetdec...
Qed.

Lemma fv_in_dom :
  forall T e A,
    typing T e A -> fv e [<=] dom T.
Proof.
  introv Htyp.
  dependent induction Htyp; simpl; try fsetdec; eauto.
  - apply binds_In in H0.
    fsetdec.
  - pick fresh x.
    assert ((fv (open e x)) [<=] (dom ([(x, A)] ++ T))); eauto.
    simpl in H2.
    assert (fv e [<=] fv (open e x)).
    eapply fv_open_lower.
    assert (fv e [<=] add x (dom T)).
    fsetdec.
    eapply add_notin_context; eauto.
Qed.
    

Lemma subst_value :
  forall e z u A ,
    typing nil e A -> subst_exp z u e = e.
Proof with auto.
  intros.
  apply fv_in_dom in H...
  simpl in H...
  eapply subst_fresh; eauto.
  fsetdec.
Qed.

Lemma typing_subst:
  forall E F e u S T (z : atom),
    typing (F ++ (z ~ S) ++ E) e T ->
    typing E u S ->
    typing (F ++ E) (subst_exp z u e) T.
Proof.
  introv He Hu.
  remember (F ++ (z ~ S) ++ E) as E'.
  gen F.
  induction He; intros.
  - subst. eapply typing_int; eauto.
  - subst. eapply typing_subst_var_case; eauto.
  - subst. simpl.
    pick fresh y and apply typing_lam; eauto.
    rewrite subst_open_var; eauto.
    rewrite_env (([(y, A)] ++ F) ++ E).
    eapply H0; eauto.
  - subst. simpl.
    eapply typing_anno; eauto.
  - subst. simpl.
    eapply typing_app; eauto.
  - subst. simpl.
    eapply typing_merge; eauto.
  - subst. simpl.
    pose proof (subst_value u1 z u _ He1).
    pose proof (subst_value u2 z u _ He2).
    rewrite H3. rewrite H4.
    eapply typing_merge_uvalue; eauto.
Qed.

Lemma typing_rename : forall (x y : atom) E e T1 T2,
  x `notin` fv e -> y `notin` (dom E `union` fv e) ->
  typing ((x ~ T1) ++ E) (open e x) T2 ->
  typing ((y ~ T1) ++ E) (open e y) T2.
Proof.
  introv Fr1 Fr2 Htyp.
  destruct (x == y).
  - subst. eauto.
  - assert (J : uniq ((x ~ T1) ++ E)).
    eapply typing_uniq; eauto.
    assert (J': uniq E).
    inversion J; eauto.
    rewrite (@subst_intro x); eauto.
    rewrite_env (nil ++ (y ~ T1) ++ E).
    eapply typing_subst with (S := T1).
    simpl_env.
    eapply typing_weakening_gen; eauto.
    eapply typing_var; eauto.
Qed.

(* we can't prove it without substitution lemma *)

Lemma substitution_preservation :
  forall F E x v e A B C,
    typing (F ++ [(x, A)] ++ E) e B ->
    typing nil v C -> isomorphic C A ->
    (exists D, typing (F ++ E) (subst_exp x v e) D /\ isomorphic D B).
Proof.
  introv Htyp Htypv Hiso.
  remember (F ++ [(x, A)] ++ E) as E'.
  gen F.
  induction Htyp; intros; simpl; subst; eauto.
  - destruct (x0 == x); eauto.
    subst. eapply binds_mid_eq in H0; eauto. subst.
    exists C. split; eauto.
    eapply typing_weakening; eauto.
    rewrite_env (E ++ nil).
    eapply typing_weakening; eauto.
    solve_uniq.
  - exists (typ_arrow A0 B).
    split; eauto.
    pick fresh y.
    assert (y `notin` L) by eauto.
    assert ((([(y, A0)] ++ (F ++ ([(x, A)] ++ E))) = (([(y, A0)] ++ F) ++ ([(x, A)] ++ E)))).
    rewrite_env (([(y, A0)] ++ F) ++ ([(x, A)] ++ E)). auto.
    pose proof (H0 y H2 ([(y, A0)] ++ F) H3).
    destruct H4. destruct H4.
    eapply (typing_lam  (union L
                  (union (singleton x)
                     (union (dom E)
                        (union (dom F)
                           (union (singleton x) (union (fv v) (fv e)))))))  (F ++ E) A0 B x0); eauto.
    intros.
    assert ((subst_exp x v (open e y)) = (open (subst_exp x v e) y)).
    symmetry.
    eapply subst_open_var; eauto.
    rewrite H7 in H4.    
    rewrite_env ([(y, A0)] ++ (F ++ E)) in H4.
    eapply (typing_rename y x1); eauto 3.
    eapply subst_notin_fv; eauto.
    eapply notin_union; eauto.
    eapply subst_notin_fv; eauto.
    eapply iso_to_sub in H5.
    eapply sub_transitivity; eauto.
  - exists A0. split; eauto 3.
    pose proof (IHHtyp F).
    assert ( ((F ++ ([(x, A)] ++ E)) = (F ++ ([(x, A)] ++ E)))).
    rewrite_env (F ++ ([(x, A)] ++ E)). reflexivity.
    pose proof (H0 H1). destruct H2. destruct H2.
    eapply typing_anno; eauto. eapply iso_to_sub in H3.
    eapply sub_transitivity; eauto.
  - assert (((F ++ ([(x, A)] ++ E)) = (F ++ ([(x, A)] ++ E)))) by reflexivity.
    pose proof (IHHtyp1 F H0).
    pose proof (IHHtyp2 F H0).
    destruct_conjs.
    eapply appsub_iso in H; eauto.
    destruct H. destruct H.
    exists x0. split; eauto.
  - assert ( ((F ++ ([(x, A)] ++ E)) = (F ++ ([(x, A)] ++ E)))) by reflexivity.
    pose proof (IHHtyp1 F H0).
    pose proof (IHHtyp2 F H0).
    destruct H1. destruct H2.
    destruct_conjs.
    exists (typ_and x0 x1). split; eauto.
    eapply typing_merge; eauto.
    eapply disjoint_iso_l; eauto.
  - assert ( ((F ++ ([(x, A)] ++ E)) = (F ++ ([(x, A)] ++ E)))) by reflexivity.
    exists (typ_and A0 B).
    split; eauto.
    pose proof (subst_value u1 x v _ Htyp1).
    pose proof (subst_value u2 x v _ Htyp2).    
    rewrite H4. rewrite H5.
    eapply typing_merge_uvalue; eauto.
Qed.

Theorem papp_preservation :
  forall (v1 v2 e : trm) (A B C : typ),
    value v1 -> value v2 ->
    typing nil v1 B ->
    typing nil v2 A ->
    appsub (Some A) B C ->
    papp v1 v2 e ->
    (exists D, typing nil e D /\ isomorphic D C).
Proof.
  introv Hv1 Hv2 Htyp1 Htyp2 Has Hp.
  gen A B C.
  dependent induction Hp; intros.
  - dependent destruction Htyp1.
    exists B. split.
    + eapply typing_anno; eauto.
      eapply sub_toplike; eauto.
    + dependent destruction Has; eauto.
  - dependent destruction Htyp1.
    exists D. split.
    + eapply typing_anno; eauto.
      eapply sub_toplike; eauto.
    + dependent destruction Has; eauto.
  - dependent destruction Htyp1.
    dependent destruction Has.
    dependent destruction Htyp1.
    dependent destruction H4; eauto with subtyping.
    + (* correct *)
      exists D. split; eauto 3.
      eapply tred_preservation in H0; eauto 3.
      destruct H0. destruct H0.
      pick fresh y.
      rewrite (subst_intro y); eauto 3.
      assert (Fr': y `notin` L) by eauto.
      pose proof (H2 y Fr').
      rewrite_env (nil ++ [(y, A)] ++ nil) in H7.
      pose proof (substitution_preservation nil nil y v' (open e y) A C0 x H7 H0 H6).
      destruct H8. destruct H8.
      eapply typing_anno; eauto.
      eapply iso_to_sub in H9.
      eapply sub_transitivity; eauto with subtyping.
      eapply sub_transitivity; eauto with subtyping.
    + dependent destruction Hv1.
      exfalso. eapply split_and_ord; eauto.
  - dependent destruction Hv1.
    dependent destruction Htyp1.
    + dependent destruction Has; eauto.
      * assert (ptype v1 A1); eauto.
        assert (ptype v2 B0); eauto.
        assert (ptype vl A0); eauto.
        simpl_deter. eapply appsub_to_auxas in Has.
        contradiction.
      * assert (ptype v1 A1); eauto.
        assert (ptype v2 B0); eauto.
        assert (ptype vl A0); eauto.
        simpl_deter.
        eapply appsub_to_auxas in Has2. contradiction.
    + dependent destruction Has; eauto.
      * assert (ptype v1 A1); eauto.
        assert (ptype v2 B0); eauto.
        assert (ptype vl A0); eauto.
        simpl_deter.
        eapply appsub_to_auxas in Has. contradiction.
      * assert (ptype v1 A1); eauto.
        assert (ptype v2 B0); eauto.
        assert (ptype vl A0); eauto.
        simpl_deter.
        eapply appsub_to_auxas in Has2. contradiction.
  - dependent destruction Hv1.
    dependent destruction Htyp1.
    + dependent destruction Has; eauto.
      * assert (ptype v1 A1); eauto.
        assert (ptype v2 B0); eauto.
        assert (ptype vl A0); eauto.
        simpl_deter.
        eapply appsub_to_auxas in Has. contradiction.
      * assert (ptype v1 A1); eauto.
        assert (ptype v2 B0); eauto.
        assert (ptype vl A0); eauto.
        simpl_deter.
        eapply appsub_to_auxas in Has1. contradiction.
    +  dependent destruction Has; eauto.
      * assert (ptype v1 A1); eauto.
        assert (ptype v2 B0); eauto.
        assert (ptype vl A0); eauto.
        simpl_deter. eapply appsub_to_auxas in Has.
        contradiction.
      * assert (ptype v1 A1); eauto.
        assert (ptype v2 B0); eauto.
        assert (ptype vl A0); eauto.
        simpl_deter.
        eapply appsub_to_auxas in Has1. contradiction.
  - dependent destruction Hv1.
    dependent destruction Htyp1.
    + dependent destruction Has; eauto.
      * assert (ptype v1 A1); eauto.
        assert (ptype v2 B0); eauto.
        assert (ptype vl A0); eauto.
        simpl_deter. contradiction.
      * assert (ptype v1 A1); eauto.
        assert (ptype v2 B0); eauto.
        assert (ptype vl A0); eauto.
        simpl_deter.
        eapply appsub_to_auxas in Has. contradiction.
      * assert (ptype v1 A1); eauto.
        assert (ptype v2 B0); eauto.
        assert (ptype vl A0); eauto.
        simpl_deter.
        pose proof (IHHp1 Hv1_1 Hv2 _ Htyp2 _ Htyp1_1 _ Has1).
        pose proof (IHHp2 Hv1_2 Hv2 _ Htyp2 _ Htyp1_2 _ Has2).
        destruct_conjs.
        exists (typ_and H H0).
        split; eauto.
        pose proof (papp_uvalue v1 vl e1 A C Hv1_1 Hv2 Htyp1_1 Htyp2 Hp1).
        pose proof (papp_uvalue v2 vl e2 B C Hv1_2 Hv2 Htyp1_2 Htyp2 Hp2).
        eapply typing_merge_uvalue; eauto.
        pose proof (papp_consistent v1 v2 vl e1 e2 A B C).
        eapply H13; eauto.
    + dependent destruction Has; eauto.
      * assert (ptype v1 A1); eauto.
        assert (ptype v2 B0); eauto.
        assert (ptype vl A0); eauto.
        simpl_deter. contradiction.
      * assert (ptype v1 A1); eauto.
        assert (ptype v2 B0); eauto.
        assert (ptype vl A0); eauto.
        simpl_deter.
        eapply appsub_to_auxas in Has. contradiction.
      * assert (ptype v1 A1); eauto.
        assert (ptype v2 B0); eauto.
        assert (ptype vl A0); eauto.
        simpl_deter.
        pose proof (IHHp1 Hv1_1 Hv2 _ Htyp2 _ Htyp1_1 _ Has1).
        pose proof (IHHp2 Hv1_2 Hv2 _ Htyp2 _ Htyp1_2 _ Has2).
        destruct_conjs.
        exists (typ_and H H0).
        split; eauto.
        pose proof (papp_uvalue v1 vl e1 A C Hv1_1 Hv2 Htyp1_1 Htyp2 Hp1).
        pose proof (papp_uvalue v2 vl e2 B C Hv1_2 Hv2 Htyp1_2 Htyp2 Hp2).
        eapply typing_merge_uvalue; eauto.
        pose proof (papp_consistent v1 v2 vl e1 e2 A B C).
        eapply H16; eauto.
Qed.

Lemma ord_sub_int :
  forall (A : typ),
    sub typ_int A ->
    ordinary A ->
    A = typ_int \/ toplike A.
Proof.
  introv Hsub Hord.
  induction Hord; eauto.
  dependent destruction Hsub; eauto.
  dependent destruction H.
  eapply split_and_ord in H; eauto.
  contradiction.
Qed.

Lemma ord_sub_arrow :
  forall (A B C : typ),
    sub (typ_arrow A B) C ->
    ordinary C ->
    (exists D E, C = typ_arrow D E /\ sub B E /\ sub D A /\ not (toplike E)) \/ toplike C.
Proof.
  introv Hsub Hord.  
  induction Hord; eauto.
  dependent destruction Hsub; eauto.
  - inversion H.
  - destruct (toplike_decidability B0); eauto.
    dependent destruction Hsub; eauto.
    + left. exists A0. exists B0.
      eauto.
    + assert (ordinary (typ_arrow A0 B0)) by eauto.
      eapply split_and_ord in H1; eauto.
      contradiction.
Qed.

Lemma appsub_ord_form :
  forall (A B C : typ),
    ordinary A ->
    appsub (Some B) A C ->
    (exists D E, A = (typ_arrow D E) /\ ordinary E).
Proof.
  introv Hord Has.
  eapply appsub_to_auxas in Has.
  destruct Hord.
  - inversion Has.
  - inversion Has.
  - eexists; eauto.
Qed.

Theorem papp_progress :
  forall (v1 v2 : trm) (A B C: typ),
    value v1 -> value v2 ->
    typing nil v1 A ->
    typing nil v2 B ->
    appsub (Some B) A C ->
    exists e, papp v1 v2 e.
Proof.
  introv Hv1 Hv2 Htyp1 Htyp2 Has.
  gen A B C v2.
  dependent induction Hv1; intros.
  - dependent destruction H.
    + dependent destruction Htyp1.
      dependent destruction Htyp1.
      eapply ord_sub_int in H1; eauto.
      destruct H1.
      * subst. inversion Has.
      * eapply appsub_ord_form in Has; eauto.
        destruct_conjs. subst.
        exists (trm_anno (trm_int 1) H2).
        eapply papp_int_toplike; eauto.
        dependent destruction H1; eauto.
    + dependent destruction Htyp1.
      dependent destruction Htyp1.
      pose proof (H0) as Hord.
      eapply ord_sub_arrow in H0; eauto.
      destruct H0.
      * destruct_conjs. subst.
        dependent destruction Has.
        assert (exists v2', typedred v2 A0 v2').
        eapply tred_progress; eauto.
        eapply sub_transitivity; eauto.
        destruct_conjs.
        eexists.
        eapply papp_abs_anno; eauto.
      * eapply appsub_ord_form in Has; eauto.
        destruct_conjs. subst.
        dependent destruction H0.
        eexists.
        eapply papp_abs_toplike; eauto.
  - dependent destruction Has.
    + inversion Htyp1.
    + dependent destruction Htyp1.
      * assert (exists e, papp v1 v0 e). (* from appsub *)
        eapply IHHv1_1. eapply Htyp1_1. eapply Has. eapply Hv2. eapply Htyp2.
        destruct H1. exists x. eapply papp_merge_l; eauto.
      * assert (exists e, papp v1 v0 e). (* from appsub *)
        eapply IHHv1_1. eapply Htyp1_1. eapply Has. eapply Hv2. eapply Htyp2.
        destruct H4. exists x. eapply papp_merge_l; eauto.
    + dependent destruction Htyp1.
      * assert (exists e, papp v2 v0 e). (* from appsub *)
        eapply IHHv1_2. eapply Htyp1_2. eapply Has. eapply Hv2. eapply Htyp2.
        destruct H1. exists x. eapply papp_merge_r; eauto.
      *  assert (exists e, papp v2 v0 e). (* from appsub *)
         eapply IHHv1_2. eapply Htyp1_2. eapply Has. eapply Hv2. eapply Htyp2.
         destruct H4. exists x. eapply papp_merge_r; eauto.
    + dependent destruction Htyp1.
      * assert (exists e, papp v1 v0 e). (* from appsub *)
        eapply IHHv1_1. eapply Htyp1_1. eapply Has1. eapply Hv2. eapply Htyp2.
        assert (exists e, papp v2 v0 e).
        eapply IHHv1_2. eapply Htyp1_2. eapply Has2. eapply Hv2. eapply Htyp2.
        destruct_conjs.
        exists (trm_merge H0 H1). eapply papp_merge_p; eauto.
        eapply appsub_to_auxas; eauto.
        eapply appsub_to_auxas; eauto.
      * assert (exists e, papp v1 v0 e). (* from appsub *)
        eapply IHHv1_1. eapply Htyp1_1. eapply Has1. eapply Hv2. eapply Htyp2.
        assert (exists e, papp v2 v0 e).
        eapply IHHv1_2. eapply Htyp1_2. eapply Has2. eapply Hv2. eapply Htyp2.
        destruct_conjs.
        eexists. eapply papp_merge_p; eauto.
        eapply appsub_to_auxas; eauto.
        eapply appsub_to_auxas; eauto.
Qed.
