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
Require Import PrincipalTyping.
Require Import Typing.

(** * Definition *)

Inductive casting : term -> type -> term -> Prop :=
| Ct_Lit : forall n A,
    sub A Int ->
    casting (Ann (Lit n) A) Int (Ann (Lit n) Int)
| Ct_Top : forall A v,
    lc v ->
    toplike A ->
    ordinary A ->
    casting v A (Ann (Lit 1) A)
| Ct_Lam : forall A B C D E e,
    lc (Lam A e B) ->
    not (toplike D) ->
    sub E (Arr C D) ->
    ordinary D ->
    casting (Ann (Lam A e B) E)
            (Arr C D)
            (Ann (Lam A e D) (Arr C D))
| Ct_Mrg_L : forall v1 v2 v A,
    casting v1 A v ->
    ordinary A ->
    casting (Mrg v1 v2) A v
| Ct_Mrg_R : forall v1 v2 v A,
    casting v2 A v ->
    ordinary A ->
    casting (Mrg v1 v2) A v
| Ct_And : forall v1 v2 v A A1 A2,
    splitable A A1 A2 ->
    casting v A1 v1 ->
    casting v A2 v2 ->
    casting v A (Mrg v1 v2).

Hint Constructors casting : core.

Notation "e ⇝ [ A ] e'" := (casting e A e') (at level 68).

(** * Casting & LC & Value *)

Lemma casting_lc :
  forall v v' A,
    lc v ->
    casting v A v' ->
    lc v'.
Proof.
  introv Lc Ct.
  dependent induction Ct; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Lemma casting_value :
  forall v v' A,
    value v ->
    casting v A v' ->
    value v'.
Proof.
  introv Val Ct.
  induction Ct; eauto.
Qed.

Hint Resolve casting_value : core.

(** * Transitivity *)

Lemma casting_transitivity :
  forall v v1 v2 A B,
    value v ->
    casting v A v1 ->
    casting v1 B v2 ->
    casting v B v2.
Proof.
  introv Val Ct1 Ct2. gen B v2.
  induction Ct1; intros; try solve [dependent induction Ct2; eauto].
  - dependent induction Ct2; eauto.
    eapply Ct_Lam; eauto. eapply sub_transitivity; eauto.
  - dependent destruction Val.
    dependent induction Ct2; eauto.
  - dependent destruction Val.
    dependent induction Ct2; eauto.
Qed.

(** * Progress *)

Lemma casting_progress' :
  forall v A B,
    value v ->
    typing nil v Inf A ->
    sub A B ->
    exists v', casting v B v'.
Proof.
  introv Val Typ Sub. gen v.
  induction Sub; intros.
  - Case "Sub-Int".
    dependent destruction Typ; eauto.
    dependent destruction Val. dependent destruction H.
    + SCase "Lit".
      dependent destruction Typ; eauto.
    + SCase "Lam".
      dependent destruction Typ; eauto.
      dependent destruction Typ; eauto.
  - Case "Sub-Top".
    dependent destruction Typ; eauto.
  - Case "Sub-Arr".
    dependent destruction Typ; eauto.
    destruct (toplike_decidable D).
    + SCase "Toplike".
      eexists; eauto.
    + SCase "Not Toplike".
      dependent destruction Val. dependent destruction H0; eauto.
      dependent destruction Typ. dependent destruction Typ.
      dependent destruction H2; eauto. dependent destruction H3.
      assert (toplike D) by (eapply sub_toplike; eauto).
      contradiction.
  - Case "Sub-And".
    pose proof (IHSub1 _ Val Typ). pose proof (IHSub2 _ Val Typ).
    destruct_conjs; eauto.
  - Case "Sub-And-L".
    dependent destruction Typ; eauto.
    dependent destruction Val.
    pose proof (IHSub _ Val1 Typ1). destruct_conjs; eauto.
  - Case "Sub-And-R".
    dependent destruction Typ; eauto.
    dependent destruction Val.
    pose proof (IHSub _ Val2 Typ2). destruct_conjs; eauto.
Qed.

Lemma casting_progress :
  forall v A ,
    value v ->
    typing nil v Chk A ->
    exists v', casting v A v'.
Proof.
  introv Val Typ.
  dependent destruction Typ.
  eapply casting_progress'; eauto.
Qed.

Print Assumptions casting_progress.

 (** * Preservation *)

Lemma casting_preservation :
  forall v v' A B,
    value v ->
    typing nil v Inf B ->
    casting v A v' ->
    exists C, typing nil v' Inf C /\ isosub C A.
Proof.
  introv Val Typ Ct. gen B.
  induction Ct; intros; try solve [eexists; eauto].
  - Case "Lit".
    exists A. split; eauto.
  - Case "Lam".
    exists (Arr C D). split; eauto 3.
    repeat (dependent destruction Typ).
    dependent destruction Val.
    assert (Sub1: sub (Arr A B) (Arr C D)) by (eapply sub_transitivity; eauto).
    dependent destruction Sub1; eauto 3.
    assert (Sub2: sub (Arr A D) (Arr C D)) by eauto.
    eapply Ty_Ann; eauto. eapply Ty_Sub; eauto.
    eapply Ty_Lam; eauto. intros. eapply typing_chk_sub; eauto.
  - Case "Merge L".
    dependent destruction Val. dependent destruction Typ; eauto.
  - Case "Merge R".
    dependent destruction Val. dependent destruction Typ; eauto.
  - pose proof (IHCt1 Val B Typ) as IH1. destruct IH1 as [x1 IH1].
    pose proof (IHCt2 Val B Typ) as IH2. destruct IH2 as [x2 IH2].
    destruct_conjs.
    exists (And x1 x2). split; eauto.
Qed.
