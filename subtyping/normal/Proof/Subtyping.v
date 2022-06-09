Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Strings.String.
Require Import Program.Tactics.
Require Import Lia.
Require Import Language Tactical.

Set Printing Parentheses.

(** * Definition *)

Inductive sub : type -> type -> Prop :=
| Sub_Int :
    sub Int Int
| Sub_Top : forall A,
    sub A Top
| Sub_Arr : forall A B C D,
    sub C A -> sub B D ->
    sub (Arr A B) (Arr C D)
| Sub_And : forall A B1 B2,
    sub A B1 -> sub A B2 ->
    sub A (And B1 B2)
| Sub_And_L : forall A B C,
    sub A C ->
    sub (And A B) C
| Sub_And_R : forall A B C,
    sub B C ->
    sub (And A B) C.

Hint Constructors sub : core.

Notation "A <: B" := (sub A B) (at level 40).

(** * Reflexivity *)

Lemma sub_reflexivity:
  forall A,
    sub A A.
Proof.
  dependent induction A; eauto.
Qed.

Hint Resolve sub_reflexivity : core.

(** * Transitivity *)

Lemma sub_and_inversion1:
  forall A B C, sub A (And B C) -> sub A B /\ sub A C.
Proof.
  introv Sub.
  dependent induction Sub; eauto.
  destruct (IHSub B C); eauto.
  destruct (IHSub B C); eauto.
Qed.

Lemma sub_transitivity:
  forall B A C,
    sub A B -> sub B C -> sub A C.
Proof.
  dependent induction B; intros; eauto.
  - dependent induction H; eauto.
  - dependent induction H; eauto.
    dependent induction H0; eauto.
  - dependent induction H0; eauto.
    clear IHsub1 IHsub2.
    dependent induction H; eauto.
  - eapply sub_and_inversion1 in H. destruct H.
    dependent induction H0; eauto.
Qed.

(** * Decidablility *)

(** subtyping is decidable, refer https://github.com/andongfan/CP-Foundations/blob/main/fiplus/coq/Subtyping.v#L1214 *)
Axiom dec_sub : forall A B, sumbool (sub A B) (not (sub A B)).
