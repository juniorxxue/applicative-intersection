Require Import Metalib.Metatheory.
Require Import Language.
Require Import Subtyping.Subtyping.
Require Import Appsub.
Require Import Disjoint.
Require Import Value.

Import ListNotations.

(** * Definition *)

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
    (* consistent u1 u2 -> *)
    typing nil u1 A ->
    typing nil u2 B ->
    typing T (Mrg u1 u2) (And A B).

Hint Constructors typing : core.

Notation "T ⊢ e ⦂ A" := (typing T e A) (at level 50).
