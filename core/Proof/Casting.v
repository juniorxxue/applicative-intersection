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

Require Import Value.
Require Import PrincipalTyping.
Require Import Typing.

(** * Definition *)

Inductive casting : term -> type -> term -> Prop :=
| Ct_Lit : forall n A,
    casting (Ann (Lit n) A) Int (Ann (Lit n) Int)
| Ct_Top : forall v,
    lc v ->
    casting v Top (Ann (Lit 1) Top)
| Ct_Lam : forall A B C D E e,
    lc (Lam A e B) ->
    sub E (Arr C D) ->
    ordinary D ->
    casting (Ann (Lam A e B) E)
            (Arr C D)
            (Ann (Lam A e D) (Arr C D))
| Ct_Rcd : forall v v' A l,
    ordinary A ->
    casting v A v' ->
    casting (Fld l v) (Rcd l A) (Fld l v')
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

(** * Casting & Value *)

(** Value property is preserved by casting *)

Lemma casting_lc :
  forall v v' A,
    lc v ->
    casting v A v' ->
    lc v'.
Proof.
  introv Lc Ct.
  dependent induction Ct; eauto 3; econstructor; eauto.
Qed.

Lemma casting_value :
  forall v v' A,
    value v ->
    casting v A v' ->
    value v'.
Proof.
  introv Val Ct.
  induction Ct; eauto.
  inversion Val; eauto.
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
    dependent destruction Val. dependent destruction H0; eauto.
    dependent destruction Typ. dependent destruction Typ.
    dependent destruction H2; eauto.
  - Case "Sub-Rcd".
    dependent destruction Typ; eauto.
    + dependent destruction Val. destruct (IHSub e); eauto.
    + dependent destruction Val.
      destruct H0.
      repeat (dependent destruction Typ). dependent destruction H2; eauto.
      repeat (dependent destruction Typ). dependent destruction H3; eauto.
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
  - Case "Lam".
    exists (Arr C D). split; eauto 3.
    repeat (dependent destruction Typ).
    dependent destruction Val.
    assert (Sub1: sub (Arr A B) (Arr C D)) by (eapply sub_transitivity; eauto).
    dependent destruction Sub1; eauto 3.
    assert (Sub2: sub (Arr A D) (Arr C D)) by eauto.
    eapply Ty_Ann; eauto. eapply Ty_Sub; eauto.
    eapply Ty_Lam; eauto. intros. eapply typing_chk_sub; eauto.
  - Case "Rcd".
    dependent destruction Val. dependent destruction Typ; eauto.
    pose proof (IHCt Val _ Typ). destruct H0. destruct H0.
    exists (Rcd l x). split; eauto.
  - Case "Merge L".
    dependent destruction Val. dependent destruction Typ; eauto.
  - Case "Merge R".
    dependent destruction Val. dependent destruction Typ; eauto.
  - Case "Merge".
    pose proof (IHCt1 Val B Typ) as IH1. destruct IH1 as [x1 IH1].
    pose proof (IHCt2 Val B Typ) as IH2. destruct IH2 as [x2 IH2].
    destruct_conjs.
    exists (And x1 x2). split; eauto.
Qed.
