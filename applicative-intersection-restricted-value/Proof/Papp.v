Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language LibTactics.
Require Import Coq.Program.Tactics.
Require Import SubAndTopLike Ptype Appsub Tred Consistent Disjoint.

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
  - dependent destruction H2; eauto.
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
  - dependent destruction H2; eauto.
    eapply typing_to_ptype in Htyp2_2; eauto.
    eapply typing_to_ptype in Htyp1; eauto.
    simpl_deter. contradiction.
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
      eapply tred_determinism; eauto 3.
      congruence.
  - dependent destruction Hp2.
    + (* correct *)
      simpl_deter.
      dependent destruction Hv.
      eapply typing_merge_distri_app_l in Htyp; eauto 3.
      destruct Htyp.
      eapply IHHp1; eauto 3.
    + simpl_deter. contradiction.
    + simpl_deter. contradiction.
  - dependent destruction Hp2.
    + simpl_deter. contradiction.
    + (* correct *)
      simpl_deter.
      dependent destruction Hv.
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
  - dependent destruction H; eauto.
  - destruct_conjs; eauto.
Qed.

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
    + eapply con_disjoint; eauto.
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
      + eapply con_disjoint; eauto.
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
    + eapply con_disjoint; eauto.
      eapply disjoint_symmetry; eauto.
      eapply disjoint_toplike; eauto.
    + eapply con_disjoint; eauto.
      eapply disjoint_symmetry; eauto.
      eapply disjoint_toplike; eauto.
    + dependent destruction Hcons.
      * (* same e *)
        assert (v' = v'0). eapply tred_determinism; eauto.
        rewrite H3. eauto.
      * dependent destruction H3. dependent destruction H4.
        dependent destruction H5.
        eapply con_disjoint; eauto.
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
      * pose proof (papp_uvalue _ _ _ _ _ Hv1_1 Hvl Htyp1_1 Htyp Hp1).
        eapply uvalue_ptype in H6. destruct H6.
        eapply con_disjoint; eauto.
        eapply disjoint_symmetry.
        eapply disjoint_toplike; eauto.
      * pose proof (papp_uvalue _ _ _ _ _ Hv1_1 Hvl Htyp1_1 Htyp Hp1).
        eapply uvalue_ptype in H8. destruct H8.
        eapply con_disjoint; eauto.
        eapply disjoint_symmetry.
        eapply disjoint_toplike; eauto.
    + (* find a ptype for e *)
      dependent destruction Hv1.
      dependent destruction Htyp1.
      * pose proof (papp_uvalue _ _ _ _ _ Hv1_1 Hvl Htyp1_1 Htyp Hp1).
        eapply uvalue_ptype in H6. destruct H6.
        eapply con_disjoint; eauto.
        eapply disjoint_symmetry.
        eapply disjoint_toplike; eauto.
      * pose proof (papp_uvalue _ _ _ _ _ Hv1_1 Hvl Htyp1_1 Htyp Hp1).
        eapply uvalue_ptype in H8. destruct H8.
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
      * pose proof (papp_uvalue _ _ _ _ _ Hv1_2 Hvl Htyp1_2 Htyp Hp1).
        eapply uvalue_ptype in H6. destruct H6.
        eapply con_disjoint; eauto.
        eapply disjoint_symmetry.
        eapply disjoint_toplike; eauto.
      * pose proof (papp_uvalue _ _ _ _ _ Hv1_2 Hvl Htyp1_2 Htyp Hp1).
        eapply uvalue_ptype in H8. destruct H8.
        eapply con_disjoint; eauto.
        eapply disjoint_symmetry.
        eapply disjoint_toplike; eauto.
    + (* find a ptype for e *)
      dependent destruction Hv1.
      dependent destruction Htyp1.
      * pose proof (papp_uvalue _ _ _ _ _ Hv1_2 Hvl Htyp1_2 Htyp Hp1).
        eapply uvalue_ptype in H6. destruct H6.
        eapply con_disjoint; eauto.
        eapply disjoint_symmetry.
        eapply disjoint_toplike; eauto.
      * pose proof (papp_uvalue _ _ _ _ _ Hv1_2 Hvl Htyp1_2 Htyp Hp1).
        eapply uvalue_ptype in H8. destruct H8.
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
        ** pose proof (papp_uvalue _ _ _ _ _ Hv1_1 Hvl Htyp1_1 Htyp Hp1_1).
           eapply uvalue_ptype in H6. destruct H6.
           eapply con_disjoint; eauto.
           eapply disjoint_symmetry.
           eapply disjoint_toplike; eauto.
        ** pose proof (papp_uvalue _ _ _ _ _ Hv1_2 Hvl Htyp1_2 Htyp Hp1_2).
           eapply uvalue_ptype in H6. destruct H6.
           eapply con_disjoint; eauto.
           eapply disjoint_symmetry.
           eapply disjoint_toplike; eauto.
      * eapply con_merge_l.
        ** pose proof (papp_uvalue _ _ _ _ _ Hv1_1 Hvl Htyp1_1 Htyp Hp1_1).
           eapply uvalue_ptype in H8. destruct H8.
           eapply con_disjoint; eauto.
           eapply disjoint_symmetry.
           eapply disjoint_toplike; eauto.
        ** pose proof (papp_uvalue _ _ _ _ _ Hv1_2 Hvl Htyp1_2 Htyp Hp1_2).
           eapply uvalue_ptype in H8. destruct H8.
           eapply con_disjoint; eauto.
           eapply disjoint_symmetry.
           eapply disjoint_toplike; eauto.
    + (* find a ptype for e *)
      dependent destruction Hv1.
      dependent destruction Htyp1.
      * eapply con_merge_l.
        ** pose proof (papp_uvalue _ _ _ _ _ Hv1_1 Hvl Htyp1_1 Htyp Hp1_1).
           eapply uvalue_ptype in H6. destruct H6.
           eapply con_disjoint; eauto.
           eapply disjoint_symmetry.
           eapply disjoint_toplike; eauto.
        ** pose proof (papp_uvalue _ _ _ _ _ Hv1_2 Hvl Htyp1_2 Htyp Hp1_2).
           eapply uvalue_ptype in H6. destruct H6.
           eapply con_disjoint; eauto.
           eapply disjoint_symmetry.
           eapply disjoint_toplike; eauto.
      * eapply con_merge_l.
        ** pose proof (papp_uvalue _ _ _ _ _ Hv1_1 Hvl Htyp1_1 Htyp Hp1_1).
           eapply uvalue_ptype in H8. destruct H8.
           eapply con_disjoint; eauto.
           eapply disjoint_symmetry.
           eapply disjoint_toplike; eauto.
        ** pose proof (papp_uvalue _ _ _ _ _ Hv1_2 Hvl Htyp1_2 Htyp Hp1_2).
           eapply uvalue_ptype in H8. destruct H8.
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

Lemma typing_rename : forall (x y : atom) E e T1 T2,
  x `notin` fv e -> y `notin` (dom E `union` fv e) ->
  typing ((x ~ T1) ++ E) (open e x) T2 ->
  typing ((y ~ T1) ++ E) (open e y) T2.
Proof.
Admitted.

Lemma subst_notin_fv : forall x y u e,
   x `notin` fv e -> x `notin` fv u ->
   x `notin` fv (subst_exp y u e).
Proof.
Admitted.

Lemma subst_open_var_c : forall (x y : atom) u e,
    open (subst_exp x u e) y = subst_exp x u (open e y).
Proof.
  Admitted.

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
    eapply subst_open_var_c.
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
  - exists C0. split; eauto.
    assert (((F ++ ([(x, A)] ++ E)) = (F ++ ([(x, A)] ++ E)))) by reflexivity.
    pose proof (IHHtyp1 F H0).
    pose proof (IHHtyp2 F H0).
    destruct_conjs.
    eapply typing_app; eauto.
    admit.
  - assert ( ((F ++ ([(x, A)] ++ E)) = (F ++ ([(x, A)] ++ E)))) by reflexivity.
    pose proof (IHHtyp1 F H0).
    pose proof (IHHtyp2 F H0).
    destruct H1. destruct H2.
    destruct_conjs.
    exists (typ_and x0 x1). split; eauto.
    eapply typing_merge; eauto.
    eapply disjoint_iso_r.
    
    

Admitted.

Lemma substitution_preservation' :
  forall F E x v e A B C,
    typing (F ++ [(x, A)] ++ E) e B ->
    typing nil v C -> sub C A ->
    (exists D, typing (F ++ E) (subst_exp x v e) D /\ sub D B).
Proof.
  introv Htyp Htypv Hsub.
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
    split.
Admitted.

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
    dependent destruction H3.
    + dependent destruction H4. contradiction.
    + (* correct *)
      exists D. split; eauto 3.
      eapply tred_preservation in H; eauto 3.
      destruct H. destruct H.
      pick fresh y.
      rewrite (subst_intro y); eauto 3.
      assert (Fr': y `notin` L) by eauto.
      pose proof (H1 y Fr').
      rewrite_env (nil ++ [(y, A)] ++ nil) in H6.
      eapply typing_anno; eauto.
      admit.
    + dependent destruction Hv1.
      exfalso. eapply split_and_ord; eauto.
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
        eapply appsub_to_auxas in Has2. contradiction.
    + dependent destruction Has; eauto.
      * assert (ptype v1 A1); eauto.
        assert (ptype v2 B0); eauto.
        assert (ptype vl A0); eauto.
        simpl_deter. contradiction.
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
        simpl_deter. contradiction.
      * assert (ptype v1 A1); eauto.
        assert (ptype v2 B0); eauto.
        assert (ptype vl A0); eauto.
        simpl_deter.
        eapply appsub_to_auxas in Has1. contradiction.
    +  dependent destruction Has; eauto.
      * assert (ptype v1 A1); eauto.
        assert (ptype v2 B0); eauto.
        assert (ptype vl A0); eauto.
        simpl_deter. contradiction.
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
        eapply H15; eauto.
Admitted.

Inductive applicable : typ -> Prop :=
| applicable_arrow : forall (A B : typ),
    applicable (typ_arrow A B)
| applicable_merge_l : forall (A B : typ),
    applicable A -> applicable (typ_and A B)
| applicable_merge_r : forall (A B : typ),
    applicable B -> applicable (typ_and A B).

Hint Constructors applicable : core.

Lemma split_and_applicable :
  forall (A B C: typ),
    applicable A -> splitable A B C ->
    applicable B \/ applicable C.
Proof.
  introv Happ Hspl.
  dependent induction Hspl; eauto.
  - dependent destruction Happ; eauto.
Qed.

Lemma appsub_is_applicable :
  forall (A B : typ),
    auxas (Some B) A -> applicable A.
Proof.
  intros.
  dependent induction H; eauto.
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
  - destruct (toplike_or_not_toplike B0); eauto.
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
        exists (trm_anno (open e H8) H3).
        eapply papp_abs_anno; eauto.
      * eapply appsub_ord_form in Has; eauto.
        destruct_conjs. subst.
        exists (trm_anno (trm_int 1) H3).
        dependent destruction H0.
        eapply papp_abs_toplike; eauto.
  - dependent destruction Has.
    + inversion Htyp1.
    + dependent destruction Htyp1.
      * assert (exists e, papp v1 v0 e). (* from appsub *)
        eapply IHHv1_1. eapply Htyp1_1. eapply Has. eapply Hv2. eapply Htyp2.
        destruct H1. exists x. eapply papp_merge_l; eauto.
        eapply appsub_to_auxas; eauto.
      * assert (exists e, papp v1 v0 e). (* from appsub *)
        eapply IHHv1_1. eapply Htyp1_1. eapply Has. eapply Hv2. eapply Htyp2.
        destruct H3. exists x. eapply papp_merge_l; eauto.
        eapply appsub_to_auxas; eauto.
    + dependent destruction Htyp1.
      * assert (exists e, papp v2 v0 e). (* from appsub *)
        eapply IHHv1_2. eapply Htyp1_2. eapply Has. eapply Hv2. eapply Htyp2.
        destruct H1. exists x. eapply papp_merge_r; eauto.
        eapply appsub_to_auxas; eauto. 
      *  assert (exists e, papp v2 v0 e). (* from appsub *)
         eapply IHHv1_2. eapply Htyp1_2. eapply Has. eapply Hv2. eapply Htyp2.
         destruct H3. exists x. eapply papp_merge_r; eauto.
         eapply appsub_to_auxas; eauto.
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
        exists (trm_merge H2 H3). eapply papp_merge_p; eauto.
        eapply appsub_to_auxas; eauto.
        eapply appsub_to_auxas; eauto.
Qed.
