Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language LibTactics.
Require Import Coq.Program.Tactics.
Require Import SubAndTopLike Ptype Appsub Tred Consistent.

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
  - dependent destruction Hp2.
    + simpl_deter.
      reflexivity.
    + dependent destruction H. dependent destruction H0. contradiction.
    + dependent destruction H.
      simpl_deter.
      contradiction.
    + dependent destruction H.
      simpl_deter.
      contradiction.
    + dependent destruction H.
      simpl_deter.
      contradiction.
  - dependent destruction Hp2.
    + dependent destruction H1. dependent destruction H2.
      contradiction.
    + dependent destruction Htyp.
      assert (v' = v'0).
      eapply tred_determinism; eauto 3.
      congruence.
  - dependent destruction Hp2.
    + dependent destruction H5.
      simpl_deter. contradiction.
    + (* correct *)
      simpl_deter.
      dependent destruction Hv.
      eapply typing_merge_distri_app_l in Htyp; eauto 3.
      destruct Htyp.
      eapply IHHp1; eauto 3.
    + simpl_deter. contradiction.
    + simpl_deter. contradiction.
  - dependent destruction Hp2.
    + dependent destruction H5.
      simpl_deter. contradiction.
    + simpl_deter. contradiction.
    + (* correct *)
      simpl_deter.
      dependent destruction Hv.
      eapply typing_merge_distri_app_r in Htyp; eauto 3.
      destruct Htyp.
      eapply IHHp1; eauto 3.
    + simpl_deter. contradiction.
  - dependent destruction Hp2.
    + dependent destruction H5.
      simpl_deter. contradiction.
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

Theorem papp_preservation :
  forall (v1 v2 e : trm) (A B C : typ),
    value v1 -> value v2 ->
    typing nil v1 A ->
    typing nil v2 B ->
    appsub (Some B) A C ->
    papp v1 v2 e ->
    (exists D, typing nil e D /\ isomorphic D C).
Proof.
  introv Hv1 Hv2 Htyp1 Htyp2 Has Hp.
  gen A B C.
  dependent induction Hp; intros.
  - dependent destruction Htyp1.
Abort.

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
      * exists (trm_anno (trm_int 1) A).
        eapply papp_toplike; eauto.
    + dependent destruction Htyp1.
      dependent destruction Htyp1.
      eapply ord_sub_arrow in H0; eauto.
      destruct H0.
      * destruct_conjs. subst.
        dependent destruction Has.
        assert (exists v2', typedred v2 A0 v2').
        eapply tred_progress; eauto.
        eapply sub_transitivity; eauto.
        destruct_conjs.
        exists (trm_anno (open e H7) H2).
        eapply papp_abs_anno; eauto.
      * exists (trm_anno (trm_int 1) A).
        eapply papp_toplike; eauto.
  - dependent destruction Has.
    + inversion Htyp1.
    + destruct (toplike_or_not_toplike (typ_and A B0)).
      * exists (trm_anno (trm_int 1) (typ_and A B0)).
        eapply papp_toplike; eauto.
      * dependent destruction Htyp1.
        ** assert (exists e, papp v1 v0 e). (* from appsub *)
           eapply IHHv1_1. eapply Htyp1_1. eapply Has. eapply Hv2. eapply Htyp2.
           destruct H2. exists x. eapply papp_merge_l; eauto.
           eapply appsub_to_auxas; eauto. 
        ** assert (exists e, papp v1 v0 e). (* from appsub *)
           eapply IHHv1_1. eapply Htyp1_1. eapply Has. eapply Hv2. eapply Htyp2.
           destruct H4. exists x. eapply papp_merge_l; eauto.
           eapply appsub_to_auxas; eauto.
    + destruct (toplike_or_not_toplike (typ_and A B0)).
      * exists (trm_anno (trm_int 1) (typ_and A B0)).
        eapply papp_toplike; eauto.
      * dependent destruction Htyp1.
        ** assert (exists e, papp v2 v0 e). (* from appsub *)
           eapply IHHv1_2. eapply Htyp1_2. eapply Has. eapply Hv2. eapply Htyp2.
           destruct H2. exists x. eapply papp_merge_r; eauto.
           eapply appsub_to_auxas; eauto. 
        ** assert (exists e, papp v2 v0 e). (* from appsub *)
           eapply IHHv1_2. eapply Htyp1_2. eapply Has. eapply Hv2. eapply Htyp2.
           destruct H4. exists x. eapply papp_merge_r; eauto.
           eapply appsub_to_auxas; eauto.
    + destruct (toplike_or_not_toplike (typ_and A B0)).
      * exists (trm_anno (trm_int 1) (typ_and A B0)).
        eapply papp_toplike; eauto.
      * dependent destruction Htyp1.
        ** assert (exists e, papp v1 v0 e). (* from appsub *)
           eapply IHHv1_1. eapply Htyp1_1. eapply Has1. eapply Hv2. eapply Htyp2.
           assert (exists e, papp v2 v0 e).
           eapply IHHv1_2. eapply Htyp1_2. eapply Has2. eapply Hv2. eapply Htyp2.
           destruct_conjs.
           exists (trm_merge H1 H2). eapply papp_merge_p; eauto.
           eapply appsub_to_auxas; eauto.
           eapply appsub_to_auxas; eauto.
        ** assert (exists e, papp v1 v0 e). (* from appsub *)
           eapply IHHv1_1. eapply Htyp1_1. eapply Has1. eapply Hv2. eapply Htyp2.
           assert (exists e, papp v2 v0 e).
           eapply IHHv1_2. eapply Htyp1_2. eapply Has2. eapply Hv2. eapply Htyp2.
           destruct_conjs.
           exists (trm_merge H3 H4). eapply papp_merge_p; eauto.
           eapply appsub_to_auxas; eauto.
           eapply appsub_to_auxas; eauto.
Qed.
