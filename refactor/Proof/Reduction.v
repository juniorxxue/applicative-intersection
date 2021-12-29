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

Notation "e ~-> e'" := (step e e') (at level 68).
