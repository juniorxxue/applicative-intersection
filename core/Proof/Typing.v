Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Import Strings.String.
Require Import Language.
Require Import Tactical.
Require Import Subtyping.Subtyping.
Require Import Appsub.
Require Import Disjoint.
Require Import Value.
Require Import PrincipalTyping.
Require Import Consistent.


Import ListNotations.

(** * Definition *)

Inductive typing : ctx -> term -> type -> Prop :=
| Ty_Int : forall T n,
    uniq T ->
    typing T (Lit n) Int
| Ty_Var : forall T x A,
    uniq T -> binds x A T ->
    typing T (Fvar x) A
| Ty_Lam : forall L T A B C e,
    (forall x, x \notin L ->
          typing ((one (x, A)) ++ T) (open e (Fvar x)) C) ->
    sub C B ->
    typing T (Lam A e B) (Arr A B)
| Ty_Ann : forall T A C e,
    typing T e C ->
    sub C A ->
    typing T (Ann e A) A
| Ty_App : forall T A B C e1 e2,
    typing T e1 A ->
    typing T e2 B ->
    appsub (Some B) A C ->
    typing T (App e1 e2) C
| Ty_Mrg : forall T A B e1 e2,
    disjoint A B ->
    typing T e1 A ->
    typing T e2 B ->
    typing T (Mrg e1 e2) (And A B)
| Ty_Mrg_Uv : forall T A B u1 u2,
    uniq T ->
    uvalue u1 -> uvalue u2 ->
    consistent u1 u2 ->
    typing nil u1 A ->
    typing nil u2 B ->
    typing T (Mrg u1 u2) (And A B).

Hint Constructors typing : core.

Notation "T ⊢ e ⦂ A" := (typing T e A) (at level 50).

(** * Typing & PrincipalTyping *)

Lemma typing_to_ptype :
  forall u A,
    uvalue u ->
    typing nil u A ->
    ptype u A.
Proof.
  introv Uval Typ. gen A.
  induction Uval; intros.
  - dependent destruction Typ; eauto.
  - dependent destruction Typ; eauto.
Qed.

Hint Resolve typing_to_ptype : core.

(** * Typing & Consistent *)

(** ** Reflexivity *)

(** Well-typed values are consistent with themselves *)

Lemma consistent_reflexivity :
  forall v A,
    typing nil v A ->
    value v ->
    consistent v v.
Proof.
  introv Typ Val. gen A.
  induction Val; eauto; intros.
  Case "Merge".  
  dependent destruction Typ.
  - SCase "Disjoint".
    assert (consistent v1 v2) by (eapply Con_Dj; eauto).
    eapply Con_Mrg_L; eauto.
    eapply Con_Mrg_R; eauto.
    now apply consistent_symmetry.
  - SCase "Consistent".
    eapply Con_Mrg_L; eauto.
    eapply Con_Mrg_R; eauto.
    now apply consistent_symmetry.
Qed.

Hint Resolve consistent_reflexivity : core.

(** * Typing & LC *)

Lemma typing_to_lc :
  forall T e A,
    typing T e A -> lc e.
Proof.
  introv Typ.
  induction Typ; try solve [econstructor; eauto].
Qed.

Hint Resolve typing_to_lc : core.
