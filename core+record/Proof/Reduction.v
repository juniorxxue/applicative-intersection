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
Require Import Subtyping.Unisub.
Require Import Appsub.

Require Import Value.
Require Import PrincipalTyping.
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
| St_App : forall f v e,
    value f -> value v ->
    papp f (Av v) e ->
    step (App f v) e
| St_Prj : forall l v e,
    value v ->
    papp v (Al l) e ->
    step (Prj v l) e    
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
| St_Rcd : forall l e e',
    step e e' ->
    step (Fld l e) (Fld l e')
| St_Prj_L : forall e e' l,
    step e e' ->
    step (Prj e l) (Prj e' l)     
| St_Mrg_L : forall e1 e1' e2,
    step e1 e1' ->
    step (Mrg e1 e2) (Mrg e1' e2)
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
    + eapply IHv2; eauto.
  - dependent destruction Val.
    destruct H.
    + intros St. dependent destruction St; eauto.
    + intros St. dependent destruction St; eauto.
  - intros St.
    dependent destruction St.
    dependent destruction Val.
    pose proof (IHv Val e'). contradiction.
Qed.

Lemma step_lc :
  forall e e',
    lc e -> step e e' -> lc e'.
Proof.
  introv Lc St. gen e'.
  induction Lc; intros;
    try solve [dependent destruction St; eauto 3].
  - dependent destruction St. eapply Lc_Ann. eapply Lc_Lam; eauto.
  - Case "App".
    dependent destruction St; try solve [econstructor; eauto].
    pose proof (papp_lc_v e1 e2 e). eauto 3.
  - dependent destruction St; econstructor; eauto.
  - dependent destruction St.
    + econstructor; eapply Lc_Ann; eapply lc_pvalue; eauto.
    + eapply casting_lc; eauto.
    + econstructor. eauto.
  - dependent destruction St. econstructor. eauto.
  - Case "Prj".
    dependent destruction St; try solve [econstructor; eauto].
    pose proof (papp_lc_l e l e0). eauto 3.
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
  - dependent destruction St; eauto.
Qed.

Hint Resolve step_uvalue : core.

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
    typing nil e Inf A ->
    step e e' ->
    (exists B, typing nil e' Inf B /\ isosub B A).
Proof.
  introv Typ St. gen e' A.
  ind_term_size (size_term e). (* shelved item *)
  dependent destruction Typ; simpl in SizeInd.
  - Case "Lit".
    dependent destruction St; eauto.
    exists Int; eauto.
  - Case "Var".
    dependent destruction St.
  - Case "Lam".
    dependent destruction St; eauto.
    exists (Arr A B). split; eauto.
  - Case "Rcd".
    dependent destruction St; eauto.
    exploit (IH e); eauto; try lia. intros IH'. destruct_conjs.
    eexists. split; eauto.
  - Case "Ann".
    dependent destruction St.
    + SCase "Split".
      dependent destruction Typ.
      exists (And A1 A2). split; eauto.
      pose proof (sub_inv_splitable_r A B A1 A2) as Sub. destruct Sub; eauto.
      eapply Ty_Mrg; eauto.
    + SCase "Value".
      dependent destruction Typ.
      eapply casting_preservation; eauto.
    + SCase "Ann".
      dependent destruction Typ.
      eapply IH in St; eauto; try lia.
      destruct St as [C Typ']. destruct Typ' as [Typ'1 Typ'2].
      pose proof (isosub_to_sub1 _ _ Typ'2).
      exists B. split; eauto. eapply Ty_Ann; eauto; try solve [eapply sub_transitivity; eauto].
      eapply Ty_Sub; eauto. eapply sub_transitivity; eauto.     
  - Case "App".
    dependent destruction St.
    + pose proof (papp_preservation_v e1 e2 e) as P.
      eapply P; eauto. now eapply uunisub_sound_appsub.
    + eapply IH in St; eauto; try lia. destruct_conjs.
      eapply uunisub_sound_appsub in H0.
      eapply appsub_iso_v in H0; eauto. destruct_conjs.
      eapply uunisub_complete_appsub in H3.
      eexists; eauto.
    + eapply IH in St; eauto; try lia. destruct_conjs.
      eapply uunisub_sound_appsub in H0.
      eapply appsub_iso_v in H0; eauto. destruct_conjs.
      eapply uunisub_complete_appsub in H3.
      eexists; eauto.
  - Case "Prj".
    dependent destruction St.
    + eapply uunisub_sound_appsub in H1.
      pose proof (papp_preservation_l e l e0) as P.
      eapply P; eauto.
    + eapply uunisub_sound_appsub in H.
      eapply IH in St; eauto; try lia. destruct_conjs.
      eapply appsub_iso_l in H; eauto. destruct_conjs.
      eapply uunisub_complete_appsub in H2.
      eexists; eauto.
  - Case "Merge".
    dependent destruction St.
    + eapply IH in St; eauto; try lia. destruct_conjs. eauto.
    + eapply IH in St; eauto; try lia. destruct_conjs. eauto.
Qed.

Theorem preservation_chk :
  forall e e' A,
    typing nil e Chk A ->
    step e e' ->
    typing nil e' Chk A.
Proof.
  introv Typ St.
  dependent destruction Typ.
  pose proof (preservation _ _ _ Typ St). destruct_conjs.
  eapply Ty_Sub; eauto. eapply isosub_to_sub1 in H2. eapply sub_transitivity; eauto.
Qed.

Theorem preservation_gen :
  forall e e' A dir,
    typing nil e dir A ->
    step e e' ->
    typing nil e' Chk A.
Proof.
  introv Typ St.
  destruct dir.
  - pose proof (preservation _ _ _ Typ St). destruct_conjs.
    eapply Ty_Sub; eauto. eapply isosub_to_sub1 in H1. auto.
  - eapply preservation_chk; eauto.
Qed.

(** * Progress *)

Theorem progress :
  forall e A dir,
    typing nil e dir A ->
    value e \/ exists e', step e e'.
Proof.
  introv Typ.
  dependent induction Typ; eauto 3.
  - Case "Rcd".
    destruct IHTyp as [Val | St] ; eauto.
    right. destruct St. exists (Fld l x); eauto.    
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
    eapply uunisub_sound_appsub in H.
    right. destruct IHTyp1; destruct IHTyp2; eauto 3; try solve [destruct_conjs; eauto].
    pose proof (papp_progress_v e1 e2 A B C) as Pa. destruct Pa; eauto.
  - Case "Prj".
    eapply uunisub_sound_appsub in H.
    right. destruct IHTyp; eauto 3; try solve [destruct_conjs; eauto].
    pose proof (papp_progress_l e A B l) as Pa. destruct Pa; eauto.
  - Case "Merge".
    destruct IHTyp1; destruct IHTyp2; eauto 3; try solve [destruct_conjs; eauto].
Qed.

(** * Soundness *)

Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
| multi_refl : forall (x : X), multi R x x
| multi_step : forall (x y z : X), R x y -> multi R y z -> multi R x z.

Notation multistep := (multi step).

Definition normal_form {X : Type} (R : relation X) (e : X) : Prop :=
  not (exists e', R e e').

Definition stuck (e : term) : Prop :=
  (normal_form step) e /\ ~ value e.

Corollary soundness :
  forall e e' A dir,
    typing nil e dir A ->
    multistep e e' ->
    ~ (stuck e').
Proof.
  introv Typ Mult. unfold stuck.
  intros [Nf Nval]. unfold normal_form in Nf. gen A dir.
  dependent induction Mult; intros.
  - pose proof (progress _ _ _ Typ). destruct H; eauto.
  - destruct dir.
    + pose proof (preservation _ _ _ Typ H) as Prv.
      destruct Prv. destruct H0.
      eapply IHMult; eauto.
    + pose proof (preservation_chk _ _ _ Typ H) as Prv.
      dependent destruction Prv.
      eapply IHMult; eauto.      
Qed.
