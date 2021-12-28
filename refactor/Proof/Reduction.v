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

(** * Definitions *)

Inductive papp : term -> term -> term -> Prop :=
| Pa_Lit_Tl : forall (A B : type) (v vl : term) (n : nat),
    toplike B ->
    papp (Ann (Lit n) (Arr A B)) vl (Ann (Lit 1) B)
| Pa_Lam_Tl : forall (A B C D : type) (e vl: term),
    lc (Lam A e B) ->
    toplike D ->
    papp (Ann (Lam A e B) (Arr C D)) vl
         (Ann (Lit 1) D)
| Pa_Lam : forall (A B C D : type) (e vl vl' : term),
    lc (Lam A e B) ->
    casting vl A vl' ->
    not (toplike D) ->
    papp (Ann (Lam A e B) (Arr C D)) vl'
         (Ann (open e vl') D)
| Pa_Mrg_L : forall (A B C : type) (v1 v2 vl e: term),
    ptype v1 A -> ptype v2 B -> ptype vl C ->
    not (auxas (Some C) B) ->
    papp v1 vl e ->
    papp (Mrg v1 v2) vl e
| Pa_Mrg_R : forall (A B C : type) (v1 v2 vl e : term),
    ptype v1 A -> ptype v2 B -> ptype vl C ->
    not (auxas (Some C) A) ->
    papp v2 vl e ->
    papp (Mrg v1 v2) vl e
| Pa_Mrg_P : forall (A B C : type) (v1 v2 vl e1 e2 : term),
    ptype v1 A -> ptype v2 B -> ptype vl C ->
    auxas (Some C) A ->
    auxas (Some C) B ->
    papp v1 vl e1 ->
    papp v2 vl e2 ->
    papp (Mrg v1 v2) vl (Mrg e1 e2).

Hint Constructors papp : core.

Notation "v ◐ vl ~-> e" := (papp v vl e) (at level 69).

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

(** * Parallell Application & Consistent *)

(** Automating this lemma is tricky for it has "four" irrelevant cases *)

Section papp_consistent.

Lemma papp_consistent :
  forall v1 v2 vl e1 e2 A B C,
    value v1 -> value v2 -> value vl ->
    typing nil v1 A ->
    typing nil v2 B ->
    typing nil vl C ->
    papp v1 vl e1 ->
    papp v2 vl e2 ->
    consistent v1 v2 ->
    consistent e1 e2.
Proof.
  Ltac solver1 := try solve [eapply Con_Dj; eauto; eapply disjoint_toplike; eauto 3].
  Ltac solver2 := try solve [eapply Con_Dj; eauto; eapply disjoint_symmetry; eapply disjoint_toplike; eauto 3].
  Ltac solver3 :=  try solve [match goal with
                              | [Val: value (Mrg ?v1 ?v2),
                                 Con: consistent _ (Mrg ?v1 ?v2),
                                 Typ: typing nil (Mrg ?v1 ?v2) _ |- _] =>
      (dependent destruction Val; eapply consistent_inv_merge_r in Con; destruct Con; dependent destruction Typ; eauto 4)
                              end].
  Ltac solver4 :=  try solve [match goal with
                              | [Val: value (Mrg ?v1 ?v2),
                                 Con: consistent (Mrg ?v1 ?v2) _,
                                 Typ: typing nil (Mrg ?v1 ?v2) _ |- _] =>
      (dependent destruction Val; eapply consistent_inv_merge_l in Con; destruct Con; dependent destruction Typ; eauto 4)
                              end].
  introv Val1 Val2 Vall Typ1 Typ2 Typl P1 P2 Con. gen A B C.
  dependent induction P1.
  - Case "Lit-Toplike".
    dependent induction P2; intros; solver1; solver3.
  - Case "Lam-Toplike".
    dependent induction P2; intros; solver1; solver3.
  - Case "Lam".
    dependent induction P2; intros; solver2; solver3.
    dependent destruction Con; eauto.
    repeat (dependent destruction Typ1; dependent destruction Typ2).
    repeat match goal with
             [H: ptype _ _ |- _] => (dependent destruction H)
           end.
    eapply Con_Dj; eauto.
  - Case "Merge L".
    dependent induction P2; intros; solver4.
  - Case "Merge R".
    dependent induction P2; intros; solver4.
  - Case "Merge P".
    dependent induction P2; intros; eapply Con_Mrg_L; solver4.
Qed.

End papp_consistent.