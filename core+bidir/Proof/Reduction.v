Require Import Metalib.Metatheory.
Require Import Metalib.LibTactics.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Strings.String.
Require Import Psatz.

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
Require Import Application.

(** * Definition *)

Inductive step : term -> term -> Prop :=
| St_Lit : forall n,
    step (Lit n) (Ann (Lit n) Int)
| St_Lam : forall e A B,
    step (Lam A e B) (Ann (Lam A e B) (Arr A B))
| St_Spl : forall p A A1 A2,
    pvalue p ->
    splitable A A1 A2 ->
    step (Ann p A) (Mrg (Ann p A1) (Ann p A2))
| St_App : forall v vl e,
    value v -> value vl ->
    papp v vl e ->
    step (App v vl) e
| St_Val : forall v v' A,
    value v ->
    casting v A v' ->
    step (Ann v A) v'
| St_Ann : forall e e' A,
    not (pvalue e) ->
    step e e' ->
    step (Ann e A) (Ann e' A)
| St_App_L : forall e1 e1' e2,
    lc e2 ->
    step e1 e1' ->
    step (App e1 e2) (App e1' e2)
| St_App_R : forall v e2 e2',
    value v ->
    step e2 e2' ->
    step (App v e2) (App v e2')
| St_Mrg : forall e1 e1' e2 e2',
    step e1 e1' ->
    step e2 e2' ->
    step (Mrg e1 e2) (Mrg e1' e2')         
| St_Mrg_L : forall e1 v e1',
    value v ->
    step e1 e1' ->
    step (Mrg e1 v) (Mrg e1' v)
| St_Mrg_R : forall v e2 e2',
    value v ->
    step e2 e2' ->
    step (Mrg v e2) (Mrg v e2').

Hint Constructors step : core.

Notation "e ⟾ e'" := (step e e') (at level 68).

(** * Value *)

Lemma value_no_step :
  forall v,
    value v -> forall e, ~ step v e.
Proof.
  introv Val.
  induction v; intros; eauto.
  - intros St.
    dependent destruction Val. dependent destruction St; eauto.
    + eapply IHv1; eauto.
    + eapply IHv1; eauto.
    + eapply IHv2; eauto.
  - dependent destruction Val.
    destruct H.
    + intros St. dependent destruction St; eauto.
    + intros St. dependent destruction St; eauto.
Qed.

Lemma step_lc :
  forall e e',
    lc e -> step e e' -> lc e'.
Proof.
  introv Lc St. gen e'.
  induction Lc; intros;
    try solve [dependent destruction St; eauto 3].
  - dependent destruction St. eapply Lc_Ann. eapply Lc_Lam; eauto.
  - dependent destruction St; try solve [econstructor; eauto].
    pose proof (papp_lc e1 e2 e). eauto 3.
  - dependent destruction St; econstructor; eauto.
  - dependent destruction St.
    + econstructor; eapply Lc_Ann; eapply lc_pvalue; eauto.
    + eapply casting_lc; eauto.
    + econstructor. eauto.
Qed. 

Lemma step_uvalue :
  forall u u',
    uvalue u -> step u u' -> uvalue u'.
Proof.
  introv Uv St. gen u'.
  induction Uv; intros.
  - dependent destruction St; eauto.
    eapply Uv_Ann. eapply step_lc; eauto.
  - dependent destruction St; eauto.
Qed.

Hint Resolve step_uvalue : core.

(** * Determinism *)

Section determinism.

Ltac solver1 := try solve [match goal with
                           | [Val: value ?v, St: step ?v _ |- _] =>
                               (pose proof (value_no_step _ Val _ St); contradiction)
                           end].

Theorem determinism:
  forall e e1 e2 A,
    typing nil e A ->
    step e e1 -> step e e2 -> e1 = e2.
Proof.
  introv Typ St1 St2. gen e2 A.
  dependent induction St1; intros.
  - dependent destruction St2; eauto.
  - dependent destruction St2; eauto.
  - dependent destruction St2; eauto.
    subst_splitable. reflexivity.
  - dependent destruction St2; solver1.
    pose proof (papp_determinism v vl e). eauto.
  - dependent destruction St2; eauto; solver1.
    dependent destruction Typ.
    eapply casting_determinism; eauto.
  - dependent destruction St2; eauto; solver1.
    f_equal. dependent destruction Typ; eauto.
  - dependent destruction St2; solver1.
    f_equal. dependent destruction Typ; eauto.
  - dependent destruction St2; solver1.
    f_equal. dependent destruction Typ; eauto.
  - dependent destruction St2; solver1.
    dependent destruction Typ;
      f_equal; eauto.
  - dependent destruction St2; solver1.
    dependent destruction Typ;
      f_equal; eauto.
  - dependent destruction St2; solver1.
    dependent destruction Typ;
      f_equal; eauto.
Qed.

End determinism.

(** * Consistent *)

Inductive step_or_value : term -> term -> Prop :=
| Sv_V : forall v, value v -> step_or_value v v
| Sv_S : forall e1 e2, step e1 e2 -> step_or_value e1 e2.

Hint Constructors step_or_value : core.

Lemma size_term_lg_z :
  forall e, size_term e > 0.
Proof.
  introv.
  dependent induction e; try solve [eauto | simpl; lia].
Qed.

Hint Resolve size_term_lg_z : core.

Lemma size_term_lg_z_any1 :
  forall e1 e2,
    size_term e1 < (size_term e2 + size_term e1).
Proof.
  introv.
  assert (size_term e2 > 0). eapply size_term_lg_z.
  lia.
Qed.

Lemma size_term_lg_z_any2 :
  forall e1 e2,
    size_term e1 < (size_term e1 + size_term e2).
Proof.
  introv.
  assert (size_term e2 > 0). eapply size_term_lg_z.
  lia.
Qed.

Hint Resolve size_term_lg_z_any1 : core.
Hint Resolve size_term_lg_z_any2 : core.

Section step_consistent.

Ltac solver1 := match goal with
                | [St: step (Ann (Lam _ _ _) _) _ |- _] => (dependent destruction St; eauto)
                end.

Ltac solver2 := match goal with
                | [St: step (Ann _ _) _ |- _] => (dependent destruction St; eauto)
                end.

Ltac solver3 := match goal with
                | [Val: value ?v, St: step ?v _ |- _] =>
                    (pose proof (value_no_step _ Val _ St); contradiction)
                end.

Ltac solver4 IHC IH :=
  eapply IHC; eauto; intros; match goal with
                             | St: step ?e ?e' |- _ => eapply (IH e e'); eauto; simpl; lia
                             end.

Lemma step_consistent :
  forall e1 e2 e1' e2' A B,
    uvalue e1 -> uvalue e2 ->
    typing nil e1 A -> typing nil e2 B ->
    consistent e1 e2 ->
    step_or_value e1 e1' -> step_or_value e2 e2' ->
    (forall e e' A, size_term e < (size_term e1 + size_term e2) ->
        typing nil e A -> step e e' -> (exists C, typing nil e' C /\ isosub C A)) ->
    consistent e1' e2'.
Proof.
  introv Uv1 Uv2 Typ1 Typ2 Con Sv1 Sv2 IH. gen A B e1' e2'.
  dependent induction Con; intros; eauto.
  - Case "Lam Lam".
    dependent destruction Sv1; dependent destruction Sv2; eauto; try solve [solver1].
    dependent destruction Typ1. dependent destruction Typ2.
    solver1. solver1. eapply Con_Mrg_L; eauto.
  - Case "Anno Anno".
    dependent destruction Sv1; dependent destruction Sv2; eauto; try solve [solver2].
    dependent destruction Typ1. dependent destruction Typ2.
    solver2.
    * solver2. eapply Con_Mrg_L; eauto.
    * solver2; try solve [solver3].
      pose proof (casting_preservation e v' A C) as Cp1.
      pose proof (casting_preservation e v'0 B C0) as Cp2.
      destruct Cp1; destruct Cp2; eauto. destruct_conjs.
      eapply casting_consistent; eauto.      
    * solver2; try solve [solver3].
      assert (e' = e'0). eapply determinism; eauto. subst. econstructor; eauto.
      eapply step_lc; eauto.
  - Case "Disjoint".    
    dependent destruction Sv1; dependent destruction Sv2; eauto.
    + pose proof (step_uvalue _ _ Uv2 H3).
      eapply IH in H3; eauto; try lia.
      destruct H3 as [x Typ]; destruct Typ as [Typ Isub].
      eapply typing_to_ptype in Typ; eauto.
      eapply typing_to_ptype in Typ2; eauto. subst_ptype.
      eapply Con_Dj; eauto. eapply disjoint_iso_l; eauto.
    + pose proof (step_uvalue _ _ Uv1 H2).
      eapply IH in H2; eauto; try lia.
      destruct H2 as [x Typ]; destruct Typ as [Typ Isub].
      eapply typing_to_ptype in Typ; eauto.
      eapply typing_to_ptype in Typ1; eauto. subst_ptype.
      eapply Con_Dj; eauto. eapply disjoint_iso_l; eauto.
    + pose proof (step_uvalue _ _ Uv1 H2).
      pose proof (step_uvalue _ _ Uv2 H3).
      eapply IH in H2; eauto; try lia.
      eapply IH in H3; eauto; try lia.
      destruct_conjs.
      eapply typing_to_ptype in Typ1; eauto.
      eapply typing_to_ptype in Typ2; eauto. repeat subst_ptype.
      eapply Con_Dj; eauto. eapply disjoint_iso_l; eauto.
  - Case "Merge L".
    dependent destruction Sv1; eauto 3.
    + dependent destruction Typ1;
        eapply Con_Mrg_L; try solve [solver4 IHCon1 IH | solver4 IHCon2 IH].
    + dependent destruction Typ1;
        match goal with
        | St: step (Mrg _ _) _ |- _ => dependent destruction St
        end; eapply Con_Mrg_L; try solve [solver4 IHCon1 IH | solver4 IHCon2 IH].
  - Case "Merge R".
    dependent destruction Sv2; eauto 3.
    + dependent destruction Typ2;
        eapply Con_Mrg_R; try solve [solver4 IHCon1 IH | solver4 IHCon2 IH].
    + dependent destruction Typ2;
        match goal with
        | St: step (Mrg _ _) _ |- _ => dependent destruction St
        end; eapply Con_Mrg_R; try solve [solver4 IHCon1 IH | solver4 IHCon2 IH].
Qed.
    
End step_consistent.

(** * Preservation *)

Ltac ind_term_size s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : term |- _ ] => (gen h) end;
  induction i as [|i IH]; [
      intros; match goal with | [ H : _ < 0 |- _ ] => (dependent destruction H) end
    | intros ].

Theorem preservation :
  forall e e' A,
    typing nil e A ->
    step e e' ->
    (exists B, typing nil e' B /\ isosub B A).
Proof.
  introv Typ St. gen e' A.
  ind_term_size (size_term e).
  dependent destruction Typ; simpl in SizeInd.
  - Case "Lit".
    dependent destruction St; eauto.
  - Case "Var".
    dependent destruction St.
  - Case "Lam".
    dependent destruction St; eauto.
  - Case "Ann".
    dependent destruction St.
    + SCase "Split".
      exists (And A1 A2). split; eauto.
      pose proof (sub_inv_splitable_r C A A1 A2) as Sub. destruct Sub; eauto.
      eapply Ty_Mrg_Uv; eauto.
    + SCase "Value".
      eapply casting_preservation; eauto.
    + SCase "Ann".
      eapply IH in St; eauto; try lia.
      destruct St as [B Typ']. destruct Typ' as [Typ'1 Typ'2].
      pose proof (isosub_to_sub1 _ _ Typ'2).
      exists A. split; eauto. eapply Ty_Ann; eauto; try solve [eapply sub_transitivity; eauto].
  - Case "App".
    dependent destruction St.
    + pose proof (papp_preservation e1 e2 e) as P.
      eapply P; eauto.
    + eapply IH in St; eauto; try lia. destruct_conjs.
      eapply appsub_iso in H0; eauto. destruct_conjs.
      eexists; eauto.
    + eapply IH in St; eauto; try lia. destruct_conjs.
      eapply appsub_iso in H0; eauto. destruct_conjs.
      eexists; eauto.
  - Case "Merge".
    dependent destruction St.
    + eapply IH in St1; eauto; try lia.
      eapply IH in St2; eauto; try lia. destruct_conjs.      
      eapply disjoint_iso_l in H; eauto.
    + eapply IH in St; eauto; try lia. destruct_conjs.
      eapply disjoint_iso_l in H0; eauto.
    + eapply IH in St; eauto; try lia. destruct_conjs.
      eapply disjoint_iso_l in H0; eauto.
  - Case "Merge U".
    dependent destruction St.    
    + (* TODO: Automation *)
      assert (exists C, (typing nil e1' C) /\ (isosub C A)) by (eapply IH; eauto; lia).
      assert (exists C, (typing nil e2' C) /\ (isosub C B)) by (eapply IH; eauto; lia).
      destruct_conjs. exists (And H3 H4).
      pose proof (step_uvalue _ _ H0 St1).
      pose proof (step_uvalue _ _ H1 St2).
      split; eauto. eapply Ty_Mrg_Uv; eauto.
      pose proof (Sv_S _ _ St1) as Sov1.
      pose proof (Sv_S _ _ St2) as Sov2.
      pose proof (step_consistent u1 u2 e1' e2' A B H0 H1 Typ1 Typ2 H2 Sov1 Sov2) as Sc.
      eapply Sc. intros. eapply IH; eauto. lia.
    + assert (exists C, (typing nil e1' C) /\ (isosub C A)) by (eapply IH; eauto; lia).
      destruct_conjs. exists (And H4 B).
      pose proof (step_uvalue _ _ H1 St).
      split; eauto. eapply Ty_Mrg_Uv; eauto.
      pose proof (Sv_S _ _ St) as Sov1.
      pose proof (Sv_V _ H) as Sov2.
      pose proof (step_consistent u1 u2 e1' u2 A B H1 H2 Typ1 Typ2 H3 Sov1 Sov2) as Sc.
      eapply Sc; eauto. intros. eapply IH; eauto. lia.
    + assert (exists C, (typing nil e2' C) /\ (isosub C B)) by (eapply IH; eauto; lia).
      destruct_conjs. exists (And A H4).
      pose proof (step_uvalue _ _ H2 St).
      split; eauto. eapply Ty_Mrg_Uv; eauto.
      pose proof (Sv_V _ H) as Sov1.
      pose proof (Sv_S _ _ St) as Sov2.
      pose proof (step_consistent u1 u2 u1 e2' A B H1 H2 Typ1 Typ2 H3 Sov1 Sov2) as Sc.
      eapply Sc; eauto. intros. eapply IH; eauto. lia.
      Unshelve. eauto.
Qed.

(** * Progress *)

Theorem progress :
  forall e A,
    typing nil e A ->
    value e \/ exists e', step e e'.
Proof.
  introv Typ.
  dependent induction Typ; eauto 3.
  - Case "Anno".
    destruct IHTyp as [Val | St] ; eauto.
    + right. eapply casting_progress in Typ; eauto. destruct Typ.
      exists x. eapply St_Val; eauto.
    + destruct (pvalue_decidable e) as [Pv | nPv];
        destruct (splitable_or_ordinary A) as [Spl | Ord]; eauto.
      * destruct Pv; right; destruct_conjs; eexists; eauto.
      * destruct St. right. eexists; eauto.
      * destruct St. right. eexists; eauto.
  - Case "App".
    right. destruct IHTyp1; destruct IHTyp2; eauto 3; try solve [destruct_conjs; eauto].
    pose proof (papp_progress e1 e2 A B C) as P. destruct P; eauto.
  - Case "Merge".
    destruct IHTyp1; destruct IHTyp2; eauto 3; try solve [destruct_conjs; eauto].
  - Case "Merge V".
    destruct IHTyp1; destruct IHTyp2; eauto 3; try solve [destruct_conjs; eauto].
Qed.
