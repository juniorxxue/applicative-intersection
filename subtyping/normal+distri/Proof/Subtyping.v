Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Strings.String.
Require Import Program.Tactics.
Require Import Lia.
Require Import Language Tactical.
Require Import Splitable.

Set Printing Parentheses.

(** * Definition *)

Inductive sub : type -> type -> Prop :=
| Sub_Int :
    sub Int Int
| Sub_Top : forall A,
    sub A Top
| Sub_Arr : forall A B C D,
    sub C A -> sub B D ->
    ordinary D ->
    sub (Arr A B) (Arr C D)
| Sub_Rcd : forall A B l,
    ordinary B ->
    sub A B ->
    sub (Rcd l A) (Rcd l B)
| Sub_And : forall A B B1 B2,
    splitable B B1 B2 ->
    sub A B1 -> sub A B2 ->
    sub A B
| Sub_And_L : forall A B C,
    sub A C -> ordinary C ->
    sub (And A B) C
| Sub_And_R : forall A B C,
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

(** generlization of [Sub_Rcd] *)

Lemma sub_record :
  forall l A B,
    sub A B ->
    sub (Rcd l A) (Rcd l B).
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

Hint Resolve sub_arrow : core.
Hint Resolve sub_record : core.
Hint Resolve sub_and_l : core.
Hint Resolve sub_and_r : core.

(** * Reflexivity *)

Lemma sub_reflexivity:
  forall A,
    sub A A.
Proof.
  dependent induction A; eauto.
Qed.

Hint Resolve sub_reflexivity : core.


(** * Subtyping & Splitable *)

Lemma sub_splitable_l :
  forall A A1 A2,
    splitable A A1 A2 -> sub A A1.
Proof.
  introv H. dependent induction H; eauto.
Qed.

Lemma sub_splitable_r :
  forall A A1 A2,
    splitable A A1 A2 -> sub A A2.
Proof.
  introv H. dependent induction H; eauto.
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
    dependent destruction Ord.
    pose proof (IHSub Ord _ _ Spl) as IH.
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
| Pr_Arr : forall A B,
    ordinary B ->
    proper A -> proper B ->
    proper (Arr A B)
| Pr_Rcd : forall l A,
    ordinary A ->
    proper A ->
    proper (Rcd l A)
| Pr_Spl : forall A A1 A2,
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

Lemma proper_record :
  forall l A,
    proper A ->
    proper (Rcd l A).
Proof.
  introv Pr_A.
  induction Pr_A; eauto.
Qed.

Lemma proper_complete:
  forall (A : type), proper A.
Proof.
  induction A; eauto.
  eapply proper_arrow; eauto.
  eapply proper_record; eauto.
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
  - dependent induction Sub2; eauto.
    clear IHSub2.
    dependent induction Sub1; eauto with subtyping.
  - gen A A1.
    proper_ind C; introv Sub1 Sub2 Spl IPr IH; eauto with subtyping.
    + eapply sub_inv_splitable_r in Sub1; eauto. destruct Sub1.
      eapply sub_inv_splitable_l in Sub2; eauto. intuition.
    + eapply sub_inv_splitable_r in Sub1; eauto. destruct Sub1.
      eapply sub_inv_splitable_l in Sub2; eauto. intuition.
    + eapply sub_inv_splitable_r in Sub1; eauto. destruct Sub1.
      eapply sub_inv_splitable_l in Sub2; eauto. intuition.
    + eapply sub_inv_splitable_r in Sub2; eauto.
      destruct Sub2; eauto.
Qed.

(** * Decidablility *)

(** subtyping is decidable, refer https://github.com/andongfan/CP-Foundations/blob/main/fiplus/coq/Subtyping.v#L1214 *)
Axiom dec_sub : forall A B, sumbool (sub A B) (not (sub A B)).
