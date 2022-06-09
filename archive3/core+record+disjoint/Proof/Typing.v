Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Import Strings.String.
Require Import Language.
Require Import Tactical.
Require Import Subtyping.Subtyping.
Require Import Appsub.
Require Import Subtyping.Unisub.
Require Import Disjoint.
Require Import Value.
Require Import PrincipalTyping.
Require Import Consistent.


Import ListNotations.

(** * Definition *)

Inductive mode : Set :=
| Inf
| Chk.

Inductive typing : ctx -> term -> mode -> type -> Prop :=
| Ty_Int : forall T n,
    uniq T ->
    typing T (Lit n) Inf Int
| Ty_Var : forall T x A,
    uniq T -> binds x A T ->
    typing T (Fvar x) Inf A
| Ty_Lam : forall L T A B e,
    (forall x, x \notin L ->
          typing ((one (x, A)) ++ T) (open e (Fvar x)) Chk B) ->
    typing T (Lam A e B) Inf (Arr A B)
| Ty_Rcd : forall T e l A,
    typing T e Inf A ->
    typing T (Fld l e) Inf (Rcd l A)
| Ty_Ann : forall T A e,
    typing T e Chk A ->
    typing T (Ann e A) Inf A
| Ty_App : forall T A B C e1 e2,
    typing T e1 Inf A ->
    typing T e2 Inf B ->
    uunisub A (uP (Avt B)) (Some C) ->
    typing T (App e1 e2) Inf C
| Ty_Prj : forall T e l A B,
    typing T e Inf A ->
    uunisub A (uP (Alt l)) (Some B) ->
    typing T (Prj e l) Inf B
| Ty_Mrg : forall T A B e1 e2,
    disjoint A B ->
    typing T e1 Inf A ->
    typing T e2 Inf B ->
    typing T (Mrg e1 e2) Inf (And A B)
| Ty_Mrg_Uv : forall T A B u1 u2,
    uniq T ->
    uvalue u1 -> uvalue u2 ->
    consistent u1 u2 ->
    typing nil u1 Inf A ->
    typing nil u2 Inf B ->
    typing T (Mrg u1 u2) Inf (And A B)
| Ty_Sub : forall T e A B,
    typing T e Inf A ->
    sub A B ->
    typing T e Chk B.    

Hint Constructors typing : core.

Notation "T ⊢ e ⇒ A" := (typing T e Inf A) (at level 50).
Notation "T ⊢ e ⇐ A" := (typing T e Chk A) (at level 50).

(** * Typing & PrincipalTyping *)

Lemma typing_to_ptype :
  forall u A,
    uvalue u ->
    typing nil u Inf A ->
    ptype u A.
Proof.
  introv Uval Typ. gen A.
  induction Uval; intros;
    dependent destruction Typ; eauto.
Qed.

Hint Resolve typing_to_ptype : core.

(** * Typing & Consistent *)

(** ** Reflexivity *)

(** Well-typed values are consistent with themselves *)

Lemma consistent_reflexivity :
  forall v A,
    typing nil v Inf A ->
    value v ->
    consistent v v.
Proof.
  introv Typ Val. gen A.
  induction Val; eauto; intros.
  dependent destruction Typ; eauto.
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
    typing T e Inf A -> lc e.
Proof.
  introv Typ.
  induction Typ; eauto 3; try solve [econstructor; eauto].
Qed.

Hint Resolve typing_to_lc : core.

(** * Check Subsumption *)

Lemma typing_chk_sub :
  forall A B e T,
    typing T e Chk A ->
    sub A B ->
    typing T e Chk B.
Proof.
  introv Typ Sub.
  dependent destruction Typ.
  eapply Ty_Sub; eauto.
  eapply sub_transitivity; eauto.
Qed.
