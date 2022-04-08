Require Import Metalib.Metatheory.
Require Import Metalib.LibTactics.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Strings.String.
Require Import Lia.

Require Import Language.
Require Import Tactical.
Require Import Subtyping.Subtyping.
Require Import Subtyping.Splitable.
Require Import Subtyping.Toplike.
Require Import Appsub.

Require Import Value.
Require Import Disjoint.
Require Import PrincipalTyping.
Require Import Consistent.
Require Import Typing.
Require Import Casting.
Require Import LocallyNameless.

(** * Definition *)

Inductive papp : term -> term -> term -> Prop :=
| Pa_Lit_Tl : forall (A B : type) (v vl : term) (n : nat),
    toplike B ->
    papp (Ann (Lit n) (Arr A B)) vl (Ann (Lit 1) B)
| Pa_Lam_Tl : forall (A B C D : type) (e vl: term),
    lc (Lam A e B) ->
    toplike D ->
    papp (Ann (Lam A e B) (Arr C D)) vl
         (Ann (Lit 1) D)
| Pa_Lam : forall (A B C D : type) (e vl vl' : term),
    lc (Lam A e B) ->
    casting vl A vl' ->
    not (toplike D) ->
    papp (Ann (Lam A e B) (Arr C D)) vl
         (Ann (open e vl') D)
| Pa_Mrg_L : forall (A B C : type) (v1 v2 vl e: term),
    ptype v1 A -> ptype v2 B -> ptype vl C ->
    not (auxas (Some C) B) ->
    papp v1 vl e ->
    papp (Mrg v1 v2) vl e
| Pa_Mrg_R : forall (A B C : type) (v1 v2 vl e : term),
    ptype v1 A -> ptype v2 B -> ptype vl C ->
    not (auxas (Some C) A) ->
    papp v2 vl e ->
    papp (Mrg v1 v2) vl e
| Pa_Mrg_P : forall (A B C : type) (v1 v2 vl e1 e2 : term),
    ptype v1 A -> ptype v2 B -> ptype vl C ->
    auxas (Some C) A ->
    auxas (Some C) B ->
    papp v1 vl e1 ->
    papp v2 vl e2 ->
    papp (Mrg v1 v2) vl (Mrg e1 e2).

Hint Constructors papp : core.

Notation "v · vl ⟹ e" := (papp v vl e) (at level 69).

(** * Determinism *)

(** Well-typed application term doesn't ensure that all subterms of function can accept its argument,
    but ensures part of its functions can accept *)

(** Notation: automation heavily relies on [contra_appsub] *)

Section papp_determinism.

Lemma papp_determinism :
  forall v vl e1 e2 A,
    value v -> value vl ->
    papp v vl e1 ->
    papp v vl e2 ->
    typing nil (App v vl) Inf A ->
    e1 = e2.
Proof.
  Ltac solver1 := repeat match goal with
                         | [Typ: typing nil ?v Inf ?A, Val: value ?v, Pt: ptype ?v _ |- _] =>
                             (pose proof (typing_to_ptype _ _ (value_is_uvalue _ Val) Typ); subst_ptype; clear Pt)
                         end;
                  match goal with
                  | [H: appsub _ _ _ |- _] => (dependent destruction H; eauto)
                  end.  
  introv Val Vall P1 P2 Typ. gen e2 A.
  induction P1; intros.
  - Case "Lit Toplike".
    dependent destruction P2; eauto.
  - Case "Lam Toplike".
    dependent destruction P2; eauto.
  - Case "Lam".
    dependent destruction P2; eauto.
    dependent destruction Typ.
    repeat (f_equal). eapply casting_determinism; eauto.
  - Case "Merge L".
    dependent destruction P2; eauto;
      repeat subst_ptype; dependent destruction Val;
      dependent destruction Typ; dependent destruction Typ1; eauto; solver1.
  - Case "Merge R".
    dependent destruction P2; eauto;
      repeat subst_ptype; dependent destruction Val;
      dependent destruction Typ; dependent destruction Typ1; eauto; solver1.
  - Case "Merge P".
    dependent destruction P2; eauto;
      repeat subst_ptype; dependent destruction Val;
      dependent destruction Typ; dependent destruction Typ1; eauto.
    + f_equal; solver1.
    + f_equal; solver1.
Qed.
      
End papp_determinism.

(** * App & Value *)

Lemma papp_lc :
  forall v vl e,
    lc v -> lc vl ->
    papp v vl e ->
    lc e.
Proof.
  introv Lc Lcl Pa.
  dependent induction Pa; try solve [econstructor; eauto 3].
  - eapply Lc_Ann. eapply open_abs; eauto.
    pose proof (casting_lc vl vl' A). eauto 3.
  - dependent destruction Lc; eauto 3.
  - dependent destruction Lc; eauto 3.
Qed.

(** * App & Consistent *)

(** Automating this lemma is tricky for it has "four" irrelevant cases *)

Section papp_consistent.

Lemma papp_consistent :
  forall v1 v2 vl e1 e2 A B C,
    value v1 -> value v2 -> value vl ->
    typing nil v1 Inf A ->
    typing nil v2 Inf B ->
    typing nil vl Inf C ->
    papp v1 vl e1 ->
    papp v2 vl e2 ->
    consistent v1 v2 ->
    consistent e1 e2.
Proof.
  Ltac solver1 := try solve [eapply Con_Dj; eauto; eapply disjoint_toplike; eauto 3].
  Ltac solver2 := try solve [eapply Con_Dj; eauto; eapply disjoint_symmetry; eapply disjoint_toplike; eauto 3].
  Ltac solver3 :=  try solve [match goal with
                              | [Val: value (Mrg ?v1 ?v2),
                                 Con: consistent _ (Mrg ?v1 ?v2),
                                 Typ: typing nil (Mrg ?v1 ?v2) Inf _ |- _] =>
      (dependent destruction Val; eapply consistent_inv_merge_r in Con; destruct Con; dependent destruction Typ; eauto 4)
                              end].
  Ltac solver4 :=  try solve [match goal with
                              | [Val: value (Mrg ?v1 ?v2),
                                 Con: consistent (Mrg ?v1 ?v2) _,
                                 Typ: typing nil (Mrg ?v1 ?v2) Inf _ |- _] =>
      (dependent destruction Val; eapply consistent_inv_merge_l in Con; destruct Con; dependent destruction Typ; eauto 4)
                              end].
  introv Val1 Val2 Vall Typ1 Typ2 Typl P1 P2 Con. gen A B C.
  dependent induction P1.  
  - Case "Lit-Toplike".
    dependent induction P2; intros; solver1; solver3.
  - Case "Lam-Toplike".
    dependent induction P2; intros; solver1; solver3.
  - Case "Lam".
    dependent induction P2; intros; solver2; solver3.
    dependent destruction Con; eauto.
    + assert (vl' = vl'0). eapply casting_determinism; eauto. subst. eapply Con_Ann; eauto 4.
    + assert (vl' = vl'0). eapply casting_determinism; eauto. subst. eapply Con_Ann; eauto 4.
    + repeat (dependent destruction Typ1; dependent destruction Typ2).
      repeat match goal with
               [H: ptype _ _ |- _] => (dependent destruction H)
             end.
      eapply Con_Dj; eauto. admit.
  - Case "Merge L".
    dependent induction P2; intros; solver4.
  - Case "Merge R".
    dependent induction P2; intros; solver4.
  - Case "Merge P".
    dependent induction P2; intros; eapply Con_Mrg_L; solver4.
Admitted.

End papp_consistent.

(** * Weakening Lemma *)

Lemma typing_weakening_gen :
  forall G E F e A dir,
    typing (E ++ G) e dir A ->
    uniq (E ++ F ++ G) ->
    typing (E ++ F ++ G) e dir A.
Proof.
  introv Typ. gen F.
  dependent induction Typ; introv Env; eauto.
  pick fresh x and apply Ty_Lam.
  rewrite_env (([(x,A)] ++ E) ++ F ++ G).
  apply H0; eauto.
  solve_uniq.
Qed.

Lemma typing_weakening :
  forall E F e A dir,
    typing E e dir A ->
    uniq (F ++ E) ->
    typing (F ++ E) e dir A.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  eapply typing_weakening_gen; eauto.
Qed.

(** * Subsitution Lemma *)

Lemma typing_uniq :
  forall E e T,
    typing E e Inf T -> uniq E.
Proof.
  introv Typ.
  induction Typ; eauto.
  - pick fresh x.
    assert (J: uniq ((one (x,A)) ++ T)); eauto.
    dependent destruction J; eauto.
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

Lemma fv_in_dom :
  forall T e A dir,
    typing T e dir A -> fv e [<=] dom T.
Proof.
  introv Typ.
  dependent induction Typ; simpl; try fsetdec; eauto.
  - apply binds_In in H0.
    fsetdec.
  - pick fresh x. 
    assert ((fv (open e x)) [<=] (dom ((one (x, A)) ++ T))) by eauto.
    simpl in *.
    assert (fv e [<=] fv (open e x)).
    eapply fv_open_lower.
    assert (fv e [<=] add x (dom T)).
    fsetdec.
    eapply add_notin_context; eauto.
Qed.    

Lemma subst_value :
  forall e z u A ,
    typing nil e Inf A -> substitution z u e = e.
Proof with auto.
  intros.
  apply fv_in_dom in H...
  simpl in H...
  eapply subst_fresh; eauto.
  fsetdec.
Qed.

(** substitution lemma, 
stating that substituting a (closed, well-typed) term s for a variable x in a term t preserves the type of t *)

Lemma substitution_lemma :
   forall F E x v e A B C dir,
    typing (F ++ [(x, A)] ++ E) e dir B ->
    typing nil v Inf C ->
    isosub C A ->
    (exists D, typing (F ++ E) (substitution x v e) dir D /\ isosub D B).
Proof.
  introv Typ Typv Isub. remember (F ++ [(x, A)] ++ E) as E'. gen F.
  induction Typ; intros; simpl; subst; eauto.
  - Case "Var".
    destruct (x0 == x); eauto. subst.
    eapply binds_mid_eq in H0; eauto. subst.
    exists C. split; eauto.
    eapply typing_weakening; eauto.
    rewrite_env (E ++ nil).
    eapply typing_weakening; eauto.
    solve_uniq.
  - Case "Lam".
    exists (Arr A0 B). split; eauto.
    eapply (Ty_Lam (union L (singleton x))); eauto. intros.
    pose proof (H0 x0) as IH.
    exploit IH; eauto. intros IH'. destruct_conjs.
    rewrite_env (([(x0, A0)] ++ F) ++ E).
    rewrite subst_open_var; eauto 3.
    eapply isosub_to_sub1 in H3.
    eapply typing_chk_sub; eauto.    
  - Case "Ann".
    exists A0. split; eauto.
    pose proof (IHTyp F) as IH. destruct IH; eauto. destruct_conjs.
    eapply Ty_Ann; eauto. eapply isosub_to_sub1 in H0.
    eapply typing_chk_sub; eauto.
  - Case "App".
    pose proof (IHTyp1 F) as IH1. pose proof (IHTyp2 F) as IH2.
    destruct IH1; destruct IH2; eauto. destruct_conjs.
    eapply appsub_iso in H; eauto. destruct H. destruct H.
    exists x2. split; eauto.
  - Case "Merge".
    pose proof (IHTyp1 F) as IH1. pose proof (IHTyp2 F) as IH2.
    destruct IH1; destruct IH2; eauto. destruct_conjs.
    exists (And x0 x1). split; eauto.
    eapply Ty_Mrg; eauto. eapply disjoint_iso_l; eauto.
  - Case "Merge V".
    exists (And A0 B). split; eauto.
    pose proof (subst_value u1 x v _ Typ1) as Rw1.
    pose proof (subst_value u2 x v _ Typ2) as Rw2.
    rewrite Rw1. rewrite Rw2.
    eapply Ty_Mrg_Uv; eauto.
  - Case "Sub".
    pose proof (IHTyp F). destruct H0; eauto. destruct H0.
    exists B. split; eauto. eapply isosub_to_sub1 in H1.
    eapply Ty_Sub; eauto. eapply sub_transitivity; eauto.
Qed.

(** * Preservation *)

Section papp_preservation.

Lemma papp_uvalue :
  forall v vl e A B,
    value v -> value vl ->
    typing nil v Inf A -> typing nil vl Inf B ->
    papp v vl e ->
    uvalue e.
Proof.
  introv Val Vall Typ Typl Pa. gen A B.
  induction Pa; intros; eauto 5;
    try solve [dependent destruction Val; dependent destruction Typ; eauto].
Qed.  

Lemma papp_preservation :
  forall v vl e A B C,
    value v -> value vl ->
    typing nil v Inf A ->
    typing nil vl Inf B ->
    appsub (Some B) A C ->
    papp v vl e ->
    (exists D, typing nil e Inf D /\ isosub D C).
Proof.
  Ltac solver1 := repeat match goal with
                         | [Typ: typing nil ?v Inf ?A, Val: value ?v, Pt: ptype ?v _ |- _] =>
                             (pose proof (typing_to_ptype _ _ (value_is_uvalue _ Val) Typ); subst_ptype; clear Pt)
                         end.
  introv Val Vall Typ Typl As Pa. gen A B C.
  induction Pa; intros.
  - Case "Lit Toplike".
    dependent destruction Typ. exists B. split.
    + eapply Ty_Ann; eauto. eapply typing_chk_sub; eauto.
      eapply sub_toplike_super; eauto.
    + dependent destruction As; eauto.
  - Case "Lam Toplike".
    dependent destruction Typ. exists D. split.
    + eapply Ty_Ann; eauto. eapply typing_chk_sub; eauto.
      eapply sub_toplike_super; eauto.
    + dependent destruction As; eauto.
  - Case "Lam".
    repeat dependent destruction Typ. dependent destruction As.
    dependent destruction Val.
    match goal with
    | [H: sub (Arr _ _) (Arr _ _) |- _] => (dependent destruction H; eauto)
    end.
    exists D. split; eauto.
    match goal with
    | [H: casting _ _ _ |- _] => (eapply casting_preservation in H; eauto; destruct H; destruct H)
    end.
    pick fresh y. rewrite (subst_intro y); eauto.
    assert (Fr': y `notin` L) by eauto.
    pose proof (H4 y Fr').
    rewrite_env (nil ++ [(y, A)] ++ nil) in H8.
    pose proof (substitution_lemma nil nil y vl' (open e y) A B x Chk) as Sl.
    destruct Sl as [x' Sl']; eauto. destruct Sl'.
    eapply Ty_Ann; eauto.
    eapply isosub_to_sub1 in H10; eauto.
    eapply typing_chk_sub; eauto.
    eapply sub_transitivity; eauto 3.
  - Case "Merge L".
    dependent destruction Val. dependent destruction Typ;
      dependent destruction As; eauto 3; solver1; eauto.
  - Case "Merge R".
    dependent destruction Val. dependent destruction Typ;
      dependent destruction As; eauto 3; solver1; eauto.
  - Case "Merge P".
    dependent destruction Val. dependent destruction Typ.
    + solver1.
      dependent destruction As; eauto.
      pose proof (IHPa1 Val1 Vall _ Typ1 _ Typl _ As1).
      pose proof (IHPa2 Val2 Vall _ Typ2 _ Typl _ As2).
      destruct_conjs. exists (And H H0). split; eauto.
      eapply Ty_Mrg; eauto.
      assert (disjoint D1 D2). eapply disjoint_appsub; eauto.
      eapply disjoint_iso_l; eauto.
    + solver1.
      dependent destruction As; eauto.
      pose proof (IHPa1 Val1 Vall _ Typ1 _ Typl _ As1).
      pose proof (IHPa2 Val2 Vall _ Typ2 _ Typl _ As2).
      destruct_conjs. exists (And H H0). split; eauto.
      pose proof (papp_uvalue _ _ _ _ _ Val1 Vall Typ1 Typl Pa1).
      pose proof (papp_uvalue _ _ _ _ _ Val2 Vall Typ2 Typl Pa2).
      eapply Ty_Mrg_Uv; eauto 3.
      pose proof (papp_consistent v1 v2 vl e1 e2 A0 B0 B1) as Pc.
      eapply Pc; eauto.    
Qed.

End papp_preservation.
    
(** * Progress *)

Lemma papp_progress :
  forall v vl A B C,
    value v -> value vl ->
    typing nil v Inf A -> typing nil vl Inf B ->
    appsub (Some B) A C ->
    exists e, papp v vl e.
Proof.
  introv Val Vall Typ Typl As. gen A B C vl.
  induction Val; intros.
  - Case "Anno".
    destruct H.
    + SCase "Lit".
      repeat dependent destruction Typ.
      dependent destruction H1; eauto. dependent destruction As; eauto.
    + SCase "Lam".
      repeat dependent destruction Typ.
      dependent destruction H2; eauto.
      * dependent destruction As; eauto.
      * destruct (toplike_decidable D); eauto.
        dependent destruction As; eauto.
        assert (Sub: sub B1 A1) by (eapply sub_transitivity; eauto).
        pose proof (casting_progress' _ _ _ Vall Typl Sub) as Ct. destruct Ct.
        eexists. eapply Pa_Lam; eauto.
  - Case "Merge".
    dependent destruction As.
    + inversion Typ.
    + dependent destruction Typ.
      * pose proof (IHVal1 _ Typ1 _ _ As _ Vall Typl) as IH. destruct IH.
        eexists. eapply Pa_Mrg_L; eauto.
      * pose proof (IHVal1 _ Typ1 _ _ As _ Vall Typl) as IH. destruct IH.
        eexists. eapply Pa_Mrg_L; eauto.
    + dependent destruction Typ.
      * pose proof (IHVal2 _ Typ2 _ _ As _ Vall Typl) as IH. destruct IH.
        eexists. eapply Pa_Mrg_R; eauto.
      * pose proof (IHVal2 _ Typ2 _ _ As _ Vall Typl) as IH. destruct IH.
        eexists. eapply Pa_Mrg_R; eauto.
    + dependent destruction Typ.
      * pose proof (IHVal1 _ Typ1 _ _ As1 _ Vall Typl) as IH1. destruct IH1.
        pose proof (IHVal2 _ Typ2 _ _ As2 _ Vall Typl) as IH2. destruct IH2.
        eexists. eapply Pa_Mrg_P; eauto.
      * pose proof (IHVal1 _ Typ1 _ _ As1 _ Vall Typl) as IH1. destruct IH1.
        pose proof (IHVal2 _ Typ2 _ _ As2 _ Vall Typl) as IH2. destruct IH2.
        eexists. eapply Pa_Mrg_P; eauto.
Qed.
