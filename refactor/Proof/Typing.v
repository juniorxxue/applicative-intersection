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

(*

---------------- T-Int
T |- n => Int


x : A \in T
----------------- T-Var
T |- x => A


T, x : A |- e => C    C <: B
-------------------------------- T-Lam
T |- \x. e : A -> B => A -> B


T |- e => C      C <: A
--------------------------------------------- T-Ann
T |- e : A => A


T |- e2 => A      T |- e1 => B    A |- B <: C
---------------------------------------------------- T-App
T |- e1 e2 => C


disjoint A B        T |- e1 => A   T |- e2 => B
------------------------------------------------------ T-Merge
T |- e1,,e2 => A & B


consistent u1 u2      . |- u1 => A     . |- u2 => B
------------------------------------------------------ T-Merge-uValue
T |- u1,,u2 => A & B

*)

Inductive typing : ctx -> term -> type -> Prop :=
| Ty_Int : forall (T : ctx) (n : nat),
    uniq T ->
    typing T (Lit n) Int
| Ty_Var : forall (T : ctx) (x : var) (A : type),
    uniq T -> binds x A T ->
    typing T (Fvar x) A
| Ty_Lam : forall (L : vars) (T : ctx) (A B C : type) (e : term),
    (forall x, x \notin L -> typing (cons (x , A) T) (open e (Fvar x)) C) ->
    sub C B ->
    typing T (Lam A e B) (Arr A B)
| Ty_Ann : forall (T : ctx) (A B C : type) (e : term),
    typing T e C ->
    sub C A ->
    typing T (Ann e A) A
| Ty_App : forall (T : ctx) (A B C : type) (e1 e2 : term),
    typing T e1 A ->
    typing T e2 B ->
    appsub (Some B) A C ->
    typing T (App e1 e2) C
| Ty_Mrg : forall (T : ctx) (A B : type) (e1 e2 : term),
    disjoint A B ->
    typing T e1 A ->
    typing T e2 B ->
    typing T (Mrg e1 e2) (And A B)
| Ty_Mrg_Uv : forall (T : ctx) (A B : type) (u1 u2 : term),
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
