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
  ind_term_size (size_term e).
  dependent destruction Typ; simpl in SizeInd.
  - Case "Lit".
    dependent destruction St; eauto.
    exists Int; eauto.
  - Case "Var".
    dependent destruction St.
  - Case "Lam".
    dependent destruction St; eauto.
    exists (Arr A B). split; eauto.
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
      eapply IH in St2; eauto; try lia. destruct_conjs. eauto.
    + eapply IH in St; eauto; try lia. destruct_conjs. eauto.
    + eapply IH in St; eauto; try lia. destruct_conjs. eauto.
Qed.

(** * Progress *)

Theorem progress :
  forall e A dir,
    typing nil e dir A ->
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
Qed.
