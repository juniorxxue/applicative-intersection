Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language LibTactics.
Require Import Strings.String.

Set Printing Parentheses.

Lemma sub_reflexivity:
  forall (A : typ), sub A A.
Proof.
  induction A; eauto.
Qed.

Hint Resolve sub_reflexivity : core.

Lemma sub_and_inversion1:
  forall (A B C : typ), sub A (typ_and B C) -> sub A B /\ sub A C.
Proof.
  introv Sub.
  dependent induction Sub; eauto.
  destruct (IHSub B C); eauto.
  destruct (IHSub B C); eauto.
Qed.

Lemma sub_and_inversion2:
  forall (A B C : typ), sub (typ_and A B) C -> sub A C \/ sub B C \/ exists C1 C2, C = typ_and C1 C2.
Proof.
  introv Hsub.
  dependent induction Hsub; eauto.
Qed.

Lemma sub_transitivity:
  forall (B A C : typ),
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

Lemma sub_toplike1:
  forall (A B : typ),
    toplike A -> sub B A.
Proof.
  intros.
  generalize dependent B.
  dependent induction H; eauto.
Qed.

Lemma sub_toplike2:
  forall (A : typ),
    sub typ_top A -> toplike A.
Proof.
  intros.
  dependent induction H; eauto.
Qed.

Hint Resolve sub_toplike1 : core.
Hint Resolve sub_toplike2 : core.
