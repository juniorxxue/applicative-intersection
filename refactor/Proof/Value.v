Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Language Tactical.
Require Import Strings.String.
Require Import Subtyping.Splitable.

(** * Definitions *)

(** ** Locally Closed *)

Inductive lc : term -> Prop :=
| Lc_Lit : forall (n : nat),
    lc (Lit n)
| Lc_Var : forall (x : atom),
    lc (Fvar x)
| Lc_Lam : forall (e : term) (A B : type) (L : atoms),
    (forall x : atom, x `notin` L -> lc (open e x)) ->
    lc (Lam A e B)
| Lc_App : forall (e1 e2 : term),
    lc e1 -> lc e2 ->
    lc (App e1 e2)
| Lc_Mrg : forall (e1 e2 : term),
    lc e1 -> lc e2 ->
    lc (Mrg e1 e2)
| Lc_Ann : forall (e : term) (A : type),
    lc e ->
    lc (Ann e A).

(** ** Partial Value *)

Inductive pvalue : term -> Prop :=
| Pv_Lit : forall (n : nat),
    pvalue (Lit n)
| Pv_Lam : forall (e : term) (A B : type),
    lc (Lam A e B) ->
    pvalue (Lam A e B).

Hint Constructors pvalue : core.

(** ** Universal Value *)

Inductive uvalue : term -> Prop :=
| Uv_Ann : forall (e : term) (A : type),
    lc e ->
    uvalue (Ann e A)
| Uv_Mrg : forall (u1 u2 : term),
    uvalue u1 -> uvalue u2 ->
    uvalue (Mrg u1 u2).

Hint Constructors uvalue : core.

(** ** Value *)

Inductive value : term -> Prop :=
| V_Ann : forall (A : type) (e : term),
    pvalue e -> ordinary A ->
    value (Ann e A)
| V_Mrg : forall (v1 v2 : term),
    value v1 -> value v2 ->
    value (Mrg v1 v2).

Hint Constructors value : core.

(** * Automations *)

(** ** Solve LC *)

Lemma lc_pvalue :
  forall p,
    pvalue p -> lc p.
Proof.
  introv H.
  induction p; try solve [eauto | inversion H; eauto].
  econstructor.
Qed.

Hint Resolve lc_pvalue : core.

Lemma lc_value :
  forall v,
    value v -> lc v.
Proof.
  introv Hv.
  induction Hv; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Hint Resolve lc_value : core.

Lemma lc_inv_anno:
  forall e A,
    lc (Ann e A) -> lc e.
Proof.
  intros.
  now dependent destruction H.
Qed.

Hint Resolve lc_inv_anno : core.


Lemma lc_inv_merge_l:
  forall e1 e2,
    lc (Mrg e1 e2) -> lc e1.
Proof.
  intros.
  now dependent destruction H.
Qed.

Hint Resolve lc_inv_merge_l : core.

Lemma lc_inv_merge_r:
  forall e1 e2,
    lc (Mrg e1 e2) -> lc e2.
Proof.
  intros.
  now dependent destruction H.
Qed.

Hint Resolve lc_inv_merge_r : core.

Lemma lc_inv_lam:
  forall e A B1 B2,
    lc (Lam A e B1) ->
    lc (Lam A e B2).
Proof.
  inversion 1; eauto.
  econstructor; eauto.
Qed.

Hint Resolve lc_inv_lam : core.

(** ** Structural Inversion *)

Ltac solve_value :=
  match goal with
  | [H: value (Lit _) |- _] => (inversion H)
  | [H: value (Fvar _) |- _] => (inversion H)
  | [H: value (Bvar _) |- _] => (inversion H)
  | [H: value (Lam _ _ _) |- _] => (inversion H)
  | [H: value (App _ _) |- _] => (inversion H)
  | [H: binds _ _ nil |- _] => (inversion H)
  end.

Hint Extern 5 => solve_value : core.

(** ** Contradictions *)

(** value is not pvalue *)

Lemma pvalue_and_value:
  forall (e : term),
    pvalue e -> value e -> False.
Proof.
  intros e Hp Hv.
  dependent destruction Hp; try solve [inversion Hv].
Qed.

Ltac solve_pvalue_and_value :=
  match goal with
  | [H1: value ?v, H2: pvalue ?v |- _] =>
      (pose proof (pvalue_and_value _ H2 H1) as Contra; inversion Contra)
  | [H1: pvalue ?p, H2: ~ pvalue ?p |- _] =>
      (contradiction)
  | [H: lc (Lam ?A ?e ?B1), Contra: ~ pvalue (Lam ?A ?e ?B2) |- _] =>
      (pose proof (Pv_Lam _ _ _ (lc_inv_lam e A B1 B2 H)); contradiction)
  | [H1: value (Ann ?e _), H2: ~ pvalue ?e |- _] =>
      (dependent destruction H1; contradiction)
  end.

Hint Extern 5 => solve_pvalue_and_value : core.

(** value is not value with anno *)

Lemma value_and_value_anno:
  forall v A,
    value v -> value (Ann v A) -> False.
Proof.
  introv Hv Hvn.
  dependent destruction Hvn.
  eapply pvalue_and_value.
  eapply H. eapply Hv.
Qed.

Ltac solve_value_and_value_anno :=
  match goal with
  | [H1: value ?v, H2: value (Ann ?v ?A) |- _] =>
      (pose proof (value_and_value_anno _ _ H1 H2) as Contra; inversion Contra)
  end.

Hint Extern 5 => solve_value_and_value_anno : core.

(** annotations in value is ordinary *)

Lemma value_anno_ordinary :
  forall e A B,
    value (Ann e (And A B)) -> False.
Proof.
  introv Hv.
  dependent destruction Hv.
  inversion H0.
Qed.

Ltac solve_value_anno_ordinary :=
  match goal with
  | [H: value (Ann _ (And _ _)) |- _] =>
      (pose proof (value_anno_ordinary _ _ _ H) as Contra; inversion Contra)
  end.

Hint Extern 5 => solve_value_anno_ordinary : core.

(** ** Solve Value *)

Lemma value_merge_inversion_l :
  forall (v1 v2 : term),
    value (Mrg v1 v2) -> value v1.
Proof.
  inversion 1; eauto.
Qed.

Hint Resolve value_merge_inversion_l : core.

Lemma value_merge_inversion_r :
  forall (v1 v2 : term),
    value (Mrg v1 v2) -> value v2.
Proof.
  inversion 1; eauto.
Qed.

Hint Resolve value_merge_inversion_r : core.

Lemma value_is_uvalue :
  forall v,
    value v -> uvalue v.
Proof.
  introv Hv.
  induction Hv; eauto.
Qed.

Hint Resolve value_is_uvalue : core.

(** * Properties *)

(** ** Decidability *)

Lemma pvalue_decidable :
  forall (e : term),
    lc e ->
    pvalue e \/ ~ pvalue e.
Proof.
  intros e LC.
  dependent induction e; eauto; try solve [right; intro H; inversion H].
Qed.

Lemma value_decidable :
  forall (e : term),
    lc e ->
    value e \/ ~ value e.
Proof.
  intros e LC.
  dependent induction e; eauto; try solve [right; unfold not; intros; inversion H].
  - destruct IHe1; destruct IHe2; eauto;
      try solve [right; unfold not; intros; dependent destruction H1; contradiction].
  - destruct IHe; eauto.
    destruct (pvalue_decidable e);
      destruct (ordinary_decidable t); eauto;
      try solve [right; intros Hcontra; inversion Hcontra; contradiction].
Qed.
