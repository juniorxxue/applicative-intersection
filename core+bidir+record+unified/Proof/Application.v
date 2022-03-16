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
Require Import Subtyping.Unisub.
Require Import Appsub.

Require Import Value.
Require Import Disjoint.
Require Import PrincipalTyping.
Require Import Consistent.
Require Import Typing.
Require Import Casting.
Require Import LocallyNameless.

(** * Definition *)

(** instead of using principal typing to get the type, we can define a function 
    atype : vl -> arg
    atype v = Some A
    atype l = Some l
 *)

(** value and label *)

Inductive vl : Set :=
| Av : term -> vl
| Al : label -> vl.

Hint Constructors vl : core.

(** I'm confused a little bit and try to think why not let merge to be general one (work both on type and label),
    Since we can't allow label to be merged, so merge case only account for types 
*)

Inductive atype : vl -> arg -> Prop :=
| At_Ann : forall e A,
    atype (Av (Ann e A)) (Avt A)
| At_Rcd : forall e l A,
    atype (Av e) (Avt A) ->
    atype (Av (Fld l e)) (Avt (Rcd l A))
| At_Mrg : forall e1 e2 A1 A2,
    atype (Av e1) (Avt A1) ->
    atype (Av e2) (Avt A2) ->
    atype (Av (Mrg e1 e2)) (Avt (And A1 A2))
| At_Lbl : forall l,
    atype (Al l) (Alt l).

Hint Constructors atype : core.

Inductive papp : term -> vl -> term -> Prop :=
| Pa_Lit_Tl : forall A B v n,
    toplike B ->
    papp (Ann (Lit n) (Arr A B)) (Av v)
         (Ann (Lit 1) B)
| Pa_Lit_Tl_R : forall A n l,
    toplike A ->
    papp (Ann (Lit n) (Rcd l A)) (Al l)
         (Ann (Lit 1) A)
| Pa_Lam_Tl : forall A B C D e v,
    lc (Lam A e B) ->
    toplike D ->
    papp (Ann (Lam A e B) (Arr C D)) (Av v)
         (Ann (Lit 1) D)
| Pa_Lam_Tl_R : forall A B C l e,
    lc (Lam A e B) ->
    toplike C ->
    papp (Ann (Lam A e B) (Rcd l C)) (Al l)
         (Ann (Lit 1) C)
| Pa_Lam : forall A B C D v v' e,
    lc (Lam A e B) ->
    casting v A v' ->
    not (toplike D) ->
    papp (Ann (Lam A e B) (Arr C D)) (Av v)
         (Ann (open e v') D)
| Pa_Rcd : forall v l,
    papp (Fld l v) (Al l) v
| Pa_Mrg_L : forall v1 v2 A B vl TA e,
    ptype v1 A -> ptype v2 B ->
    atype vl TA ->
    not (auxas (Some TA) B) ->
    papp v1 vl e ->
    papp (Mrg v1 v2) vl e
| Pa_Mrg_R : forall v1 v2 A B vl TA e,
    ptype v1 A -> ptype v2 B ->
    atype vl TA ->
    not (auxas (Some TA) A) ->
    papp v2 vl e ->
    papp (Mrg v1 v2) vl e
| Pa_Mrg_P : forall v1 v2 A B vl TA e1 e2,
    ptype v1 A -> ptype v2 B ->
    atype vl TA ->
    auxas (Some TA) A ->
    auxas (Some TA) B ->
    papp v1 vl e1 ->
    papp v2 vl e2 ->
    papp (Mrg v1 v2) vl (Mrg e1 e2).

Hint Constructors papp : core.

Notation "v · vl ⟹ e" := (papp v vl e) (at level 69).

(** * Determinism *)

Lemma atype_determinism :
  forall vl TA1 TA2,
    atype vl TA1 ->
    atype vl TA2 ->
    TA1 = TA2.
Proof.
  introv At1 At2. gen TA2.
  dependent induction At1; intros.
  - dependent destruction At2; eauto.
  - dependent destruction At2; eauto.
    pose proof (IHAt1 _ At2) as IH.
    dependent destruction IH; eauto.
  - dependent destruction At2.
    pose proof (IHAt1_1 _ At2_1) as IH1.
    pose proof (IHAt1_2 _ At2_2) as IH2.
    dependent destruction IH1. dependent induction IH2.
    auto.
  - dependent destruction At2; eauto.
Qed.

Ltac subst_atype :=
  match goal with
  | [H1: atype ?vl ?TA1, H2: atype ?vl ?TA2 |- _] =>
      (pose proof (atype_determinism _ _ _ H1 H2) as Eqs; subst; clear H2)
  end.

Lemma typing_to_atype :
  forall v A,
    value v ->
    typing nil v Inf A ->
    atype (Av v) (Avt A).
Proof.
  introv Val Typ. gen A.
  induction Val; intros.
  - dependent destruction Typ; eauto.
  - dependent destruction Typ; eauto.
  - dependent destruction Typ; eauto.
Qed.

Hint Resolve typing_to_atype : core.

(** Well-typed application term doesn't ensure that all subterms of function can accept its argument,
    but ensures part of its functions can accept *)

(** Notation: automation heavily relies on [contra_appsub] *)

Section papp_determinism.

Ltac solver1 := repeat match goal with
                       | Typ: typing nil ?v Inf ?A, Val: value ?v, Pt: ptype ?v _ |- _ =>
                           pose proof (typing_to_ptype _ _ (value_is_uvalue _ Val) Typ);
                           subst_ptype; clear Pt
                       | Typ: typing nil ?v Inf ?A, Val: value ?v, At: atype (Av ?v) _ |- _ =>
                           pose proof (typing_to_atype _ _ Val Typ);
                           subst_atype; clear At
                       end;
                match goal with
                | As: appsub _ _ _ |- _ => (dependent destruction As; eauto)
                end.

Lemma papp_determinism_v :
  forall f v e1 e2 A B C,
    value f -> value v ->
    typing nil f Inf A -> typing nil v Inf B ->
    appsub (Some (Avt B)) A C ->
    papp f (Av v) e1 ->
    papp f (Av v) e2 ->
    e1 = e2.
Proof.
  introv Valf Val Typ1 Typ2 As P1 P2. gen e2 A B C.
  dependent induction P1; intros.
  - Case "Lit Toplike".
    dependent destruction P2; eauto.
  - Case "Lam Toplike".
    dependent destruction P2; eauto.
  - Case "Lam".
    dependent destruction P2; eauto.
    repeat (f_equal). eapply casting_determinism; eauto.
  - Case "Merge L".
    dependent destruction P2;
      repeat subst_ptype; subst_atype;
      dependent destruction Valf; dependent destruction Typ1; solver1.
  - Case "Merge R".
    dependent destruction P2; eauto;
      repeat subst_ptype; subst_atype;
      dependent destruction Valf; dependent destruction Typ1; solver1.
  - Case "Merge P".
    dependent destruction P2; eauto;
      repeat subst_ptype; subst_atype;
      dependent destruction Valf; dependent destruction Typ1; solver1.
    + f_equal; solver1.
    + f_equal; solver1.
Qed.

Lemma papp_determinism_l :
  forall v l e1 e2 A B,
    value v ->
    typing nil v Inf A ->
    appsub (Some (Alt l)) A B ->
    papp v (Al l) e1 ->
    papp v (Al l) e2 ->
    e1 = e2.
Proof.
  introv Val Typ As P1 P2. gen e2 A B.
  dependent induction P1; intros.
  - Case "Lit Toplike".
    dependent destruction P2; eauto.
  - Case "Lam Toplike".
    dependent destruction P2; eauto.
  - Case "Prj".
    dependent destruction P2; eauto.
  - Case "Mrg L".
    dependent destruction P2;
      repeat subst_ptype; subst_atype;
      match goal with
      | At: atype (Al _) _ |- _ => dependent destruction At
      end; eauto;
      dependent destruction Val; dependent destruction Typ; solver1.
  - Case "Mrg R".
    dependent destruction P2;
      repeat subst_ptype; subst_atype;
      match goal with
      | At: atype (Al _) _ |- _ => dependent destruction At
      end; eauto;
      dependent destruction Val; dependent destruction Typ; solver1.
  - Case "Mrg P".
    dependent destruction P2;
      repeat subst_ptype; subst_atype;
      match goal with
      | At: atype (Al _) _ |- _ => dependent destruction At
      end; eauto;
      dependent destruction Val; dependent destruction Typ; solver1.
    + f_equal; eauto.
    + f_equal; eauto.
Qed.
      
End papp_determinism.

(** * App & Value *)

Lemma papp_lc_v :
  forall v vl e,
    lc v -> lc vl ->
    papp v (Av vl) e ->
    lc e.
Proof.
  introv Lc Lcl Pa.
  dependent induction Pa; try solve [econstructor; eauto 3].
  - econstructor. eapply open_abs; eauto 3.
    eapply casting_lc; eauto.
  - dependent destruction Lc; eauto 3.
  - dependent destruction Lc; eauto 3.
Qed.

Lemma papp_lc_l :
  forall v vl e,
    lc v ->
    papp v (Al vl) e ->
    lc e.
Proof.
  introv Lc Pa.
  dependent induction Pa; try solve [econstructor; eauto 3].
  - dependent destruction Lc. assumption.
  - dependent destruction Lc; eauto 3.
  - dependent destruction Lc; eauto 3.
Qed.

(** * App & Consistent *)

(** Automating this lemma is tricky for it has "four" irrelevant cases *)

Section papp_consistent.

Ltac solver1 := try solve [eapply Con_Dj; eauto; eapply disjoint_toplike; eauto 3].
Ltac solver2 := try solve [eapply Con_Dj; eauto; eapply disjoint_symmetry; eapply disjoint_toplike; eauto 3].
Ltac solver3 := try solve [match goal with
                           | [Val: value (Mrg ?v1 ?v2),
                              Con: consistent _ (Mrg ?v1 ?v2),
                              Typ: typing nil (Mrg ?v1 ?v2) Inf _ |- _] =>
      (dependent destruction Val; eapply consistent_inv_merge_r in Con; destruct Con; dependent destruction Typ; eauto 4)
                              end].
Ltac solver4 := try solve [match goal with
                           | [Val: value (Mrg ?v1 ?v2),
                              Con: consistent (Mrg ?v1 ?v2) _,
                              Typ: typing nil (Mrg ?v1 ?v2) Inf _ |- _] =>
      (dependent destruction Val; eapply consistent_inv_merge_l in Con; destruct Con; dependent destruction Typ; eauto 4)
                            end].
Ltac solver5 := try solve [match goal with
                           | Typ: typing nil (Fld ?l ?v) Inf _,
                              Val: value (Fld ?l ?v) |- _=> pose proof (typing_to_ptype _ _ (value_is_uvalue _ Val) Typ) as TEMPPT;
                                                          dependent destruction TEMPPT; solver1
                           end].
Ltac solver6 := try solve [match goal with
                           | Typ: typing nil (Fld ?l ?v) Inf _,
                              Val: value (Fld ?l ?v) |- _=> pose proof (typing_to_ptype _ _ (value_is_uvalue _ Val) Typ) as TEMPPT;
                                                          dependent destruction TEMPPT; solver2
                           end].
                                    

Lemma papp_consistent_v :
  forall v1 v2 vl e1 e2 A B C,
    value v1 -> value v2 -> value vl ->
    typing nil v1 Inf A ->
    typing nil v2 Inf B ->
    typing nil vl Inf C ->
    papp v1 (Av vl) e1 ->
    papp v2 (Av vl) e2 ->
    consistent v1 v2 ->
    consistent e1 e2.
Proof.
  introv Val1 Val2 Vall Typ1 Typ2 Typl P1 P2 Con. gen A B C.
  dependent induction P1.  
  - Case "Lit-Toplike".
    dependent induction P2; intros; solver1; solver3.
  - Case "Lam-Toplike".
    dependent induction P2; intros; solver1; solver3.
  - Case "Lam".
    dependent induction P2; intros; solver2; solver3.
    dependent destruction Con; eauto.
    + assert (v' = v'0). eapply casting_determinism; eauto. subst. eapply Con_Ann; eauto 4.
    + assert (v' = v'0). eapply casting_determinism; eauto. subst. eapply Con_Ann; eauto 4.
    + repeat (dependent destruction Typ1; dependent destruction Typ2).
      repeat match goal with
               [H: ptype _ _ |- _] => (dependent destruction H)
             end.
      eapply Con_Dj; eauto.
  - Case "Merge L".
    dependent induction P2; intros; solver4.
  - Case "Merge R".
    dependent induction P2; intros; solver4.
  - Case "Merge P".
    dependent induction P2; intros; eapply Con_Mrg_L; solver4.
Qed.

Lemma papp_consistent_l :
  forall v1 v2 e1 e2 A B l,
    value v1 -> value v2 ->
    typing nil v1 Inf A ->
    typing nil v2 Inf B ->
    papp v1 (Al l) e1 ->
    papp v2 (Al l) e2 ->
    consistent v1 v2 ->
    consistent e1 e2.
Proof.
  introv Val1 Val2 Typ1 Typ2 P1 P2 Con. gen A B.
  dependent induction P1.
  - Case "Lit-Toplike".
    dependent induction P2; intros; solver1; solver3; solver5.
  - Case "Lam-Toplike".
    dependent induction P2; intros; solver1; solver3; solver5.
  - Case "Rcd".
    dependent induction P2; intros; solver3; solver6.
    dependent destruction Con; eauto.
    dependent destruction H. dependent destruction H0.
    eapply Con_Dj; eauto. dependent destruction H1; eauto.
    contradiction.
  - Case "Merge L".
    dependent induction P2; intros; solver4.
  - Case "Merge R".
    dependent induction P2; intros; solver4.
  - Case "Merge P".
    dependent induction P2; intros; eapply Con_Mrg_L; solver4.
Qed.

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
  - Case "Rcd".
    pose proof (IHTyp F) as IH. exploit IH; eauto. intros IH'.
    destruct IH'. destruct H. exists (Rcd l x0). split; eauto.
  - Case "Ann".
    exists A0. split; eauto.
    pose proof (IHTyp F) as IH. destruct IH; eauto. destruct_conjs.
    eapply Ty_Ann; eauto. eapply isosub_to_sub1 in H0.
    eapply typing_chk_sub; eauto.
  - Case "App".
    pose proof (IHTyp1 F) as IH1. pose proof (IHTyp2 F) as IH2.
    destruct IH1; destruct IH2; eauto. destruct_conjs.
    eapply unisub_sound_appsub in H.
    eapply appsub_iso_v in H; eauto. destruct H. destruct H.
    exists x2. split; eauto. eapply Ty_App; eauto.
    eapply unisub_complete_appsub; eauto.
  - Case "Prj".
    pose proof (IHTyp F) as IH. exploit IH; eauto. intros IH'.
    destruct IH'. destruct H0.
    eapply unisub_sound_appsub in H.
    eapply appsub_iso_l in H; eauto. destruct H. destruct H.
    exists x1. split; eauto. eapply Ty_Prj; eauto.
    eapply unisub_complete_appsub; eauto.
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

Lemma papp_uvalue_v :
  forall v vl e A B,
    value v -> value vl ->
    typing nil v Inf A -> typing nil vl Inf B ->
    papp v (Av vl) e ->
    uvalue e.
Proof.
  introv Val Vall Typ Typl Pa. gen A B.
  dependent induction Pa; intros; eauto 3.
  - dependent destruction Val. dependent destruction Typ; eauto.
  - dependent destruction Val. dependent destruction Typ; eauto 3.
  - dependent destruction Val. dependent destruction Typ; eauto 3.
  - eapply Uv_Mrg;
    dependent destruction Val; dependent destruction Typ; eauto 3.
Qed.

Lemma papp_uvalue_l :
  forall v l e A,
    value v ->
    typing nil v Inf A ->
    papp v (Al l) e ->
    uvalue e.
Proof.
  introv Val Typ Pa. gen A.
  dependent induction Pa; intros; eauto 3.
  - dependent destruction Val. dependent destruction Typ; eauto.
  - dependent destruction Val. dependent destruction Typ; eauto 3.
  - dependent destruction Val. dependent destruction Typ; eauto 3.
  - eapply Uv_Mrg;
    dependent destruction Val; dependent destruction Typ; eauto 3.
Qed.


Ltac solver1 := repeat match goal with
                       | [Typ: typing nil ?v Inf ?A, Val: value ?v, Pt: ptype ?v _ |- _] =>
                           (pose proof (typing_to_ptype _ _ (value_is_uvalue _ Val) Typ); subst_ptype; clear Pt)
                       | Typ: typing nil ?v Inf ?A, Val: value ?v, At: atype (Av ?v) _ |- _ =>
                           pose proof (typing_to_atype _ _ Val Typ);
                           subst_atype; clear At
                       end.

Lemma papp_preservation_v :
  forall v vl e A B C,
    value v -> value vl ->
    typing nil v Inf A ->
    typing nil vl Inf B ->
    appsub (Some (Avt B)) A C ->
    papp v (Av vl) e ->
    (exists D, typing nil e Inf D /\ isosub D C).
Proof.
  introv Val Vall Typ Typl As Pa. gen A B C.
  dependent induction Pa; intros.
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
    pose proof (substitution_lemma nil nil y v' (open e y) A B x Chk) as Sl.
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
      exploit (IHPa1 Val1 _ Vall); eauto.
      exploit (IHPa2 Val2 _ Vall); eauto.
      intros IH2 IH1.
      destruct_conjs. exists (And IH1 IH2). split; eauto.
      eapply Ty_Mrg; eauto.
      assert (disjoint C1 C2). eapply disjoint_appsub; eauto.
      eapply disjoint_iso_l; eauto.
    + solver1.
      dependent destruction As; eauto.
      exploit (IHPa1 Val1 _ Vall); eauto.
      exploit (IHPa2 Val2 _ Vall); eauto.
      intros IH2 IH1.
      destruct_conjs. exists (And IH1 IH2). split; eauto.
      pose proof (papp_uvalue_v _ _ _ _ _ Val1 Vall Typ1 Typl Pa1).
      pose proof (papp_uvalue_v _ _ _ _ _ Val2 Vall Typ2 Typl Pa2).
      eapply Ty_Mrg_Uv; eauto 3.
      pose proof (papp_consistent_v v1 v2 vl0 e1 e2 A0 B0 B1) as Pc.
      eapply Pc; eauto.    
Qed.


Ltac solver2 := repeat match goal with
                       | [Typ: typing nil ?v Inf ?A, Val: value ?v, Pt: ptype ?v _ |- _] =>
                           (pose proof (typing_to_ptype _ _ (value_is_uvalue _ Val) Typ); subst_ptype; clear Pt)
                       | At: atype (Al _) _ |- _ =>
                           dependent destruction At
                       end.

Lemma papp_preservation_l :
  forall v l e A B,
    value v ->
    typing nil v Inf A ->
    appsub (Some (Alt l)) A B ->
    papp v (Al l) e ->
    (exists C, typing nil e Inf C /\ isosub C B).
Proof.
  introv Val Typ As Pa. gen A B.
  dependent induction Pa; intros.
  - Case "Lit Toplike".
    dependent destruction Typ. dependent destruction As. exists A. split; eauto.
    eapply Ty_Ann; eauto. eapply typing_chk_sub; eauto.
    eapply sub_toplike_super; eauto.
  - Case "Lam Toplike".
    dependent destruction Typ. dependent destruction As. exists C. split; eauto.
    eapply Ty_Ann; eauto. eapply typing_chk_sub; eauto.
    eapply sub_toplike_super; eauto.
  - Case "Prj".
    dependent destruction Typ. dependent destruction As.
    exists A. split; eauto.
  - Case "Merge L".
    dependent destruction Val. dependent destruction Typ;
      dependent destruction As; eauto 3; solver2; eauto.
  - Case "Merge R".
    dependent destruction Val. dependent destruction Typ;
      dependent destruction As; eauto 3; solver2; eauto.
  - Case "Merge P".
    dependent destruction Val. dependent destruction Typ.
    + solver2.
      dependent destruction As; eauto.
      exploit (IHPa1 l Val1); eauto.
      exploit (IHPa2 l Val2); eauto.
      intros IH2 IH1.
      destruct_conjs. exists (And IH1 IH2). split; eauto.
      eapply Ty_Mrg; eauto.
      assert (disjoint C1 C2). eapply disjoint_appsub; eauto.
      eapply disjoint_iso_l; eauto.
    + solver2.
      dependent destruction As; eauto.
      exploit (IHPa1 l Val1); eauto.
      exploit (IHPa2 l Val2); eauto.
      intros IH2 IH1.
      destruct_conjs. exists (And IH1 IH2). split; eauto.
      pose proof (papp_uvalue_l v1 l e1).
      pose proof (papp_uvalue_l v2 l e2).
      eapply Ty_Mrg_Uv; eauto 3.
      pose proof (papp_consistent_l _ _ _ _ _ _ _ Val1 Val2 Typ1 Typ2 Pa1 Pa2) as Pc.
      eapply Pc; eauto.
Qed.

End papp_preservation.

(** * Progress *)

Lemma papp_progress_v :
  forall f v A B C,
    value f -> value v ->
    typing nil f Inf A -> typing nil v Inf B ->
    appsub (Some (Avt B)) A C ->
    exists e, papp f (Av v) e.
Proof.
  introv Vf Vv Tf Tv As. gen A B C v.
  induction Vf; intros.
  - Case "Anno".
    destruct H.
    + SCase "Lit".
      repeat dependent destruction Tf.
      dependent destruction H1; eauto. dependent destruction As; eauto.
    + SCase "Lam".
      repeat dependent destruction Tf.
      dependent destruction H2; eauto.
      * dependent destruction As; eauto.
      * destruct (toplike_decidable D); eauto.
        dependent destruction As; eauto.
        assert (Sub: sub B1 A1) by (eapply sub_transitivity; eauto).
        pose proof (casting_progress' _ _ _ Vv Tv Sub) as Ct. destruct Ct.
        eexists. eapply Pa_Lam; eauto.
  - Case "Rcd".
    dependent destruction Tf; eauto.
  - Case "Merge".
    dependent destruction As.
    + inversion Tf.
    + dependent destruction Tf.
      * pose proof (IHVf1 _ Tf1 _ _ As _ Vv Tv) as IH. destruct IH.
        eexists. eapply Pa_Mrg_L; eauto.
      * pose proof (IHVf1 _ Tf1 _ _ As _ Vv Tv) as IH. destruct IH.
        eexists. eapply Pa_Mrg_L; eauto.
    + dependent destruction Tf.
      * pose proof (IHVf2 _ Tf2 _ _ As _ Vv Tv) as IH. destruct IH.
        eexists. eapply Pa_Mrg_R; eauto.
      * pose proof (IHVf2 _ Tf2 _ _ As _ Vv Tv) as IH. destruct IH.
        eexists. eapply Pa_Mrg_R; eauto.
    + dependent destruction Tf.
      * pose proof (IHVf1 _ Tf1 _ _ As1 _ Vv Tv) as IH1. destruct IH1.
        pose proof (IHVf2 _ Tf2 _ _ As2 _ Vv Tv) as IH2. destruct IH2.
        eexists. eapply Pa_Mrg_P; eauto.
      * pose proof (IHVf1 _ Tf1 _ _ As1 _ Vv Tv) as IH1. destruct IH1.
        pose proof (IHVf2 _ Tf2 _ _ As2 _ Vv Tv) as IH2. destruct IH2.
        eexists. eapply Pa_Mrg_P; eauto.
Qed.

Lemma papp_progress_l :
  forall v A B l,
    value v ->
    typing nil v Inf A ->
    appsub (Some (Alt l)) A B ->
    exists e, papp v (Al l) e.
Proof.
  introv Val Typ As. gen A B l.
  induction Val; intros.
  - Case "Ann". destruct H.
    + SCase "Lit".
      repeat dependent destruction Typ.
      dependent destruction H1; eauto. dependent destruction As; eauto.
    + SCase "Lam".
      repeat dependent destruction Typ.
      dependent destruction H2; eauto. dependent destruction As; eauto.
  - Case "Rcd".
    dependent destruction Typ; eauto.
    dependent destruction As. eauto.
  - Case "Merge".
    dependent destruction As.
    + inversion Typ.
    + dependent destruction Typ.
      * pose proof (IHVal1 _ Typ1 _ _ As) as IH. destruct IH.
        eexists. eapply Pa_Mrg_L; eauto.
      * pose proof (IHVal1 _ Typ1 _ _ As) as IH. destruct IH.
        eexists. eapply Pa_Mrg_L; eauto.
    + dependent destruction Typ.
      * pose proof (IHVal2 _ Typ2 _ _ As) as IH. destruct IH.
        eexists. eapply Pa_Mrg_R; eauto.
      * pose proof (IHVal2 _ Typ2 _ _ As) as IH. destruct IH.
        eexists. eapply Pa_Mrg_R; eauto.
    + dependent destruction Typ.
      * pose proof (IHVal1 _ Typ1 _ _ As1) as IH1. destruct IH1.
        pose proof (IHVal2 _ Typ2 _ _ As2) as IH2. destruct IH2.
        eexists. eapply Pa_Mrg_P; eauto.
      * pose proof (IHVal1 _ Typ1 _ _ As1) as IH1. destruct IH1.
        pose proof (IHVal2 _ Typ2 _ _ As2) as IH2. destruct IH2.
        eexists. eapply Pa_Mrg_P; eauto.
Qed.
