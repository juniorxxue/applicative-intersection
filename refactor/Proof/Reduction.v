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
| St_Lit : forall (n : nat),
    step (Lit n) (Ann (Lit n) Int)
| St_Lam : forall (e : term) (A B : type),
    step (Lam A e B) (Ann (Lam A e B) (Arr A B))
| St_Spl : forall (A A1 A2 : type) (p : term),
    pvalue p ->
    splitable A A1 A2 ->
    step (Ann p A) (Mrg (Ann p A1) (Ann p A2))
| St_App : forall (v vl e : term) (A : type),
    value v -> value vl ->
    papp v vl e ->
    step (App v vl) e
| St_Val : forall (v v' : term) (A : type),
    value v ->
    casting v A v' ->
    step (Ann v A) v'
| St_Ann : forall (e e' : term) (A : type),
    not (pvalue e) ->
    step e e' ->
    step (Ann e A) (Ann e' A)
| St_App_L : forall (e1 e2 e1' : term),
    lc e2 ->
    step e1 e1' ->
    step (App e1 e2) (App e1' e2)
| St_App_R : forall (v e2 e2' : term),
    value v ->
    step e2 e2' ->
    step (App v e2) (App v e2')
| St_Mrg : forall (e1 e1' e2 e2' : term),
    step e1 e1' ->
    step e2 e2' ->
    step (Mrg e1 e2) (Mrg e1' e2')         
| St_Mrg_L : forall (e1 v e1' : term),
    value v ->
    step e1 e1' ->
    step (Mrg e1 v) (Mrg e1' v)
| St_Mrg_R : forall (v e2 e2' : term),
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

(** * Preservation *)

Lemma step_uvalue :
  forall u u',
    uvalue u -> step u u' -> uvalue u'.
Proof.
Admitted.

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
