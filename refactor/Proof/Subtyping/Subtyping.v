Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Strings.String.
Require Import Program.Tactics.
Require Import Psatz. (* lia *)
Require Import Language Tactical.
Require Import Subtyping.Toplike.
Require Import Subtyping.Splitable.

Set Printing Parentheses.

(** * Definition *)

Inductive sub : type -> type -> Prop :=
| Sub_Int :
    sub Int Int
| Sub_Top : forall (A B : type),
    ordinary B -> toplike B ->
    sub A B
| Sub_Arrow : forall (A B C D : type),
    sub C A -> sub B D ->
    ordinary D ->
    sub (Arr A B) (Arr C D)
| Sub_And : forall (A B B1 B2 : type),
    splitable B B1 B2 ->
    sub A B1 -> sub A B2 ->
    sub A B
| Sub_And_L : forall (A B C : type),
    sub A C -> ordinary C ->
    sub (And A B) C
| Sub_And_R : forall (A B C : type),
    sub B C -> ordinary C ->
    sub (And A B) C.

Hint Constructors sub : core.

Notation "A <: B" := (sub A B) (at level 40).

(** * Generlization *)

(** generlization of [Sub_Arrow] *)

Lemma sub_arrow :
  forall A B C D,
    sub B D ->
    sub C A ->
    sub (Arr A B) (Arr C D).
Proof.
  introv H. dependent induction H; eauto.
Qed.

(** generlization of [Sub_And_L] *)

Lemma sub_and_l :
  forall A B C,
    sub A C -> sub (And A B) C.
Proof.
  introv H.
  dependent induction H; eauto.
Qed.

(** generlization of [Sub_And_R] *)

Lemma sub_and_r :
  forall A B C,
    sub B C -> sub (And A B) C.
Proof.
  introv H.
  dependent induction H; eauto.
Qed.

(** add it to local and global hint base **)

Hint Resolve sub_arrow : subtyping core.
Hint Resolve sub_and_l : subtyping core.
Hint Resolve sub_and_r : subtyping core.

(** * Reflexivity *)

Lemma sub_reflexivity:
  forall A,
    sub A A.
Proof.
  induction A; eauto with subtyping.
Qed.

Hint Resolve sub_reflexivity : subtyping.
Hint Resolve sub_reflexivity : core.

(** * Subtyping & Splitable *)

Lemma sub_splitable_l :
  forall A A1 A2,
    splitable A A1 A2 -> sub A A1.
Proof.
  introv H. dependent induction H; eauto with subtyping.
Qed.

Lemma sub_splitable_r :
  forall A A1 A2,
    splitable A A1 A2 -> sub A A2.
Proof.
  introv H. dependent induction H; eauto with subtyping.
Qed.

Hint Resolve sub_splitable_l : subtyping.
Hint Resolve sub_splitable_r : subtyping.

Lemma sub_splitable:
  forall A A1 A2,
    splitable A A1 A2 -> sub A (And A1 A2) /\ sub (And A1 A2) A.
Proof.
  introv H. split.
  - eapply Sub_And; eauto with subtyping.
  - dependent induction H; eauto with subtyping.
Qed.

Hint Resolve sub_splitable : subtyping.

(** * Splitable & Toplike *)

Lemma splitable_toplike1:
  forall A A1 A2,
    splitable A A1 A2 -> toplike A1 -> toplike A2 -> toplike A.
Proof.
  introv Spl Tl1 Tl2.
  dependent induction Spl; eauto.
  dependent destruction Tl1.
  dependent destruction Tl2.
  eapply Tl_Arr; eauto.
Qed.

Lemma splitable_toplike2 :
  forall A A1 A2,
    splitable A A1 A2 -> toplike A -> toplike A1 /\ toplike A2.
Proof.
  introv Spl Tl.
  induction Spl.
  - dependent destruction Tl; eauto.
  - dependent destruction Tl.
    pose proof (IHSpl Tl).
    destruct_conjs; eauto.
Qed.

Lemma splitable_not_toplike :
  forall A A1 A2,
    ~ toplike A -> splitable A A1 A2 ->
    ~ toplike A1 \/ ~ toplike A2.
Proof.
  introv nTl Spl. gen A1 A2.
  induction A; intros; eauto.
  - dependent destruction Spl.
    destruct (toplike_decidable A2); eauto.
    pose proof (IHA2 H _ _ Spl) as Ntls.
    destruct Ntls.
    + left. intros Contra. contra_toplike.
    + right. intros Contra. contra_toplike.
  - dependent destruction Spl.
    destruct (toplike_decidable A1); eauto.
Qed.

(** * Subtyping & Toplike (1) *)

Lemma sub_toplike:
  forall A B,
    toplike A -> sub A B -> toplike B.
Proof.
  introv Tl Sub.
  induction Sub; eauto with subtyping.
  - dependent destruction Tl; eauto.
  - eapply splitable_toplike1; eauto.
  - dependent destruction Tl; eauto.
  - dependent destruction Tl; eauto.
Qed.

Hint Resolve sub_toplike : subtyping.
Hint Resolve sub_toplike : core.

Lemma sub_not_toplike :
  forall A B,
    ~ toplike B -> sub A B -> ~ toplike A.
Proof.
  introv Ntl Sub.
  intros Contra.
  pose proof (sub_toplike _ _ Contra Sub).
  contradiction.
Qed.

(** * Inversion Lemmas *)

Lemma sub_inv_splitable_l :
  forall A B A1 A2,
    sub A B -> splitable A A1 A2 -> ordinary B -> sub A1 B \/ sub A2 B.
Proof.
  introv Sub Spl Ord. gen A1 A2.
  induction Sub; eauto; intros.
  - dependent destruction Spl.
    dependent destruction Ord.
    pose proof (IHSub2 H _ _ Spl) as IH.
    destruct IH; eauto with subtyping.
  - dependent destruction Spl.
    left. assumption.
  - dependent destruction Spl.
    right. assumption.
Qed.

Lemma sub_inv_splitable_r :
  forall A B B1 B2,
    sub A B -> splitable B B1 B2 -> sub A B1 /\ sub A B2.
Proof.
  introv Sub Spl.
  dependent destruction Sub; eauto with subtyping.
  subst_splitable; intuition.
Qed.

(** * Proper Types *)

(** ** Definition *)

Inductive proper : type -> Prop :=
| Pr_Int : proper Int
| Pr_Top : proper Top
| Pr_Arr : forall (A B : type),
    ordinary B ->
    proper A -> proper B ->
    proper (Arr A B)
| Pr_Spl : forall (A A1 A2 : type),
    splitable A A1 A2 ->
    proper A1 -> proper A2 ->
    proper A.

Hint Constructors proper : core.

(** ** Completeness *)

Lemma proper_arrow :
  forall A B,
    proper A -> proper B ->
    proper (Arr A B).
Proof.
  introv Pr_A Pr_B.
  gen A.
  induction Pr_B; eauto.
Qed.

Lemma proper_complete:
  forall (A : type), proper A.
Proof.
  induction A; eauto.
  eapply proper_arrow; eauto.
Qed.

(** We build a new induction principle for [type] *)

(** ** Proper Induction Principle *)

Ltac proper_ind A := assert (Pr: proper A)
    by apply (proper_complete A); induction Pr.

(** * Transitivity *)

Lemma sub_transitivity:
  forall A B C,
    sub A B -> sub B C -> sub A C.
Proof.
  introv Sub1 Sub2.
  gen A C.
  proper_ind B; intros.
  - dependent induction Sub2; eauto.
  - dependent induction Sub2; eauto.
  - dependent induction Sub2; eauto.
    clear IHSub2_1 IHSub2_2.
    dependent induction Sub1; eauto with subtyping.
  - gen A A1.
    proper_ind C; introv Sub1 Sub2 Spl Pr IH; eauto with subtyping.
    + eapply sub_inv_splitable_r in Sub1; eauto. destruct Sub1.
      eapply sub_inv_splitable_l in Sub2; eauto. intuition.
    + eapply sub_inv_splitable_r in Sub1; eauto. destruct Sub1.
      eapply sub_inv_splitable_l in Sub2; eauto. intuition.
    + eapply sub_inv_splitable_r in Sub2; eauto.
      destruct Sub2; eauto.
Qed.

(** * Subtyping & Toplike (2) *)

Lemma sub_toplike_super :
  forall A,
    toplike A -> forall B, sub B A.
Proof.
  introv Tl.
  proper_ind A; eauto.
  pose proof (splitable_toplike2 _ _ _ H Tl) as Spl_Tl.
  destruct Spl_Tl; eauto.
Qed.

(** * Isomorphic Subtyping *)

(** ** Definition *)

Inductive isosub : type -> type -> Prop :=
| Isub_Refl : forall (A : type),
    isosub A A
| Isub_And : forall (A1 A2 B B1 B2 : type),
    splitable B B1 B2 ->
    isosub A1 B1 ->
    isosub A2 B2 ->
    isosub (And A1 A2) B.

Hint Constructors isosub : core.

Notation "A ≋ B" := (isosub A B) (at level 40).

(** ** Transitivity *)

Lemma isosub_transitivity :
  forall A B C,
    isosub A B -> isosub B C ->
    isosub A C.
Proof.
  introv Isub1 Isub2. gen A.
  dependent induction Isub2; intros; eauto.
  dependent destruction Isub1; eauto.
  dependent destruction H0; eauto.
Qed.

(** ** Specficiation *)

Definition isomorphic_spec A B :=
  sub A B /\ sub B A.

Lemma isosub_sound :
  forall A B,
    isosub A B -> isomorphic_spec A B.
Proof.
  introv Isub. unfold isomorphic_spec.
  split.
  - Case "sub A B".
    induction Isub; eauto with subtyping.
  - Case "sub B A".
    induction Isub; eauto with subtyping.
    eapply Sub_And; eauto.
    + eapply sub_splitable in H. destruct H.
      pose proof (sub_and_l B1 B2 A1 IHIsub1).
      eapply sub_transitivity; eauto.
    + eapply sub_splitable in H. destruct H.
      pose proof (sub_and_r B1 B2 A2 IHIsub2).
      eapply sub_transitivity; eauto.
Qed.

(** * Subtyping & Isomorphic Subtyping *)

Lemma isosub_to_sub1 :
  forall A B,
    isosub A B -> sub A B.
Proof.
  introv Isub.
  pose proof (isosub_sound _ _ Isub).
  unfold isomorphic_spec in H.
  destruct H; assumption.
Qed.

Lemma isosub_to_sub2 :
  forall A B,
    isosub A B -> sub B A.
Proof.
  introv Isub.
  pose proof (isosub_sound _ _ Isub).
  unfold isomorphic_spec in H.
  destruct H; assumption.
Qed.
