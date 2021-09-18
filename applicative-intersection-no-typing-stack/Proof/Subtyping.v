Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language LibTactics.
Require Import Strings.String.
Require Import Program.Tactics.

Set Printing Parentheses.

Inductive proper_typ : typ -> Prop :=
| pt_int : proper_typ typ_int
| pt_top : proper_typ typ_top
| pt_ord_fun : forall (A B : typ),
    ordinary B -> proper_typ A -> proper_typ B ->
    proper_typ (typ_arrow A B)
| pt_split : forall (A B C : typ),
    splitable A B C -> proper_typ B -> proper_typ C ->
    proper_typ A.

Hint Constructors proper_typ : core.

Lemma proper_typ_arrow :
  forall (A B : typ),
    proper_typ A -> proper_typ B ->
    proper_typ (typ_arrow A B).
Proof.
  intros * H1 H2.
  gen A.
  induction H2; eauto.
Qed.

Hint Resolve proper_typ_arrow : core.

Lemma proper_typ_complete :
  forall (A : typ), proper_typ A.
Proof.
  induction A; eauto.
Qed.

Ltac proper_ind A := assert (r: proper_typ A)
    by apply (proper_typ_complete A); induction r.

Lemma split_and_ord :
  forall (A A1 A2 : typ),
    splitable A A1 A2 -> ordinary A -> False.
Proof.
  introv Hsp Hord. gen A1 A2.
  dependent induction Hord; intros; try solve [inversion Hsp; eauto]; eauto.
Qed.

Hint Resolve split_and_ord : core.

Lemma split_or_ord :
  forall (A : typ),
    ordinary A \/ exists B C, splitable A B C.
Proof.
  introv. dependent induction A; eauto.
  destruct IHA1; destruct IHA2; eauto.
  - right. destruct_conjs; eauto.
  - right. destruct_conjs; eauto.
Qed.

Lemma sub_arrow_gen :
  forall (A B C D : typ),
    sub B D -> sub C A -> sub (typ_arrow A B) (typ_arrow C D).
Proof.
  introv H. dependent induction H; eauto.
Qed.

Hint Resolve sub_arrow_gen : core.

Lemma sub_and_l_gen :
  forall (A B C : typ),
    sub A C -> sub (typ_and A B) C.
Proof.
  introv H.
  dependent induction H; eauto.
Qed.

Lemma sub_and_r_gen :
  forall (A B C : typ),
    sub B C -> sub (typ_and A B) C.
Proof.
  introv H.
  dependent induction H; eauto.
Qed.

Hint Resolve sub_and_l_gen : core.
Hint Resolve sub_and_r_gen : core.

Lemma sub_reflexivity:
  forall (A : typ), sub A A.
Proof.
  induction A; eauto.
Qed.

Hint Resolve sub_reflexivity : core.

Lemma splitable_sub_l :
  forall (A B C : typ),
    splitable A B C -> sub A B.
Proof.
  introv H. dependent induction H; eauto.
Qed.

Lemma splitable_sub_r :
  forall (A B C : typ),
    splitable A B C -> sub A C.
Proof.
  introv H. dependent induction H; eauto.
Qed.

Hint Resolve splitable_sub_l : core.
Hint Resolve splitable_sub_r : core.

Lemma splitable_iso :
  forall (A B C : typ),
    splitable A B C -> sub A (typ_and B C) /\ sub (typ_and B C) A.
Proof.
  introv H.
  split.
  - eapply sub_and; eauto.
  - dependent induction H; eauto.
Qed.

Hint Resolve splitable_iso : core.

Lemma split_determinism :
  forall (T A1 A2 B1 B2 : typ),
    splitable T A1 B1 -> splitable T A2 B2 ->
    A1 = A2 /\ B1 = B2.
Proof.
  introv Hsp1 Hsp2.
  gen A2 B2.
  dependent induction Hsp1; eauto; intros.
  - dependent destruction Hsp2.
    split; eauto.
  - dependent destruction Hsp2.
    pose proof IHHsp1; eauto.
    assert (C = C0 /\ D = D0); eauto.
    destruct_conjs. split; congruence.
Qed.

Lemma sub_inversion_split_l :
  forall (A B A1 A2 : typ),
    sub A B -> splitable A A1 A2 -> ordinary B -> sub A1 B \/ sub A2 B.
Proof.
  intros. gen A1 A2.
  set (Case := A <: B).
  induction H; eauto; intros.
  - inversion H0.
  - dependent destruction H3.
    eapply IHsub2 in H2; eauto.
    destruct H2; eauto.
  - eapply split_and_ord in H1; eauto. inversion H1.
  - dependent destruction H2.
    left. assumption.
  - dependent destruction H2.
    right. assumption.
Qed.

Print HintDb core.

Lemma sub_inversion_split_r :
  forall (A B B1 B2 : typ),
    sub A B -> splitable B B1 B2 -> sub A B1 /\ sub A B2.
Proof.
  intros * Hsub Hspl.
  dependent destruction Hsub; try solve [eauto | exfalso; eauto].
  eapply split_determinism in H; eauto.
  intuition; subst; eauto.
Qed.

Lemma toplike_spl_combine :
  forall (A B C : typ),
    splitable A B C -> toplike B -> toplike C -> toplike A.
Proof.
  introv Hspl Htl1 Htl2.
  dependent induction Hspl; eauto.
  dependent destruction Htl1.
  dependent destruction Htl2.
  eapply tl_arrow. eapply IHHspl; eauto.
Qed.

Lemma sub_toplike_preservation :
  forall (A B : typ),
    ordinary A -> ordinary B ->
    toplike A -> sub A B -> toplike B.
Proof.
  introv Hord1 Hord2 Htl Hsub.
  dependent induction Hsub; try solve [eauto | exfalso; eauto].
  eapply tl_arrow; eauto.
  dependent destruction Htl; eauto.
  dependent destruction Hord1; eauto.
Qed.

Lemma sub_transitivity:
  forall (B A C : typ),
    sub A B -> sub B C -> sub A C.
Proof.
  intros * Hs1 Hs2.
  gen A C.
  proper_ind B; intros.
  - dependent induction Hs2; eauto.
  - dependent induction Hs2; eauto.
  - dependent induction Hs2; eauto.
    clear IHHs2_1 IHHs2_2.
    dependent induction Hs1; try solve [eauto | exfalso; eauto].
    + dependent destruction H1; eauto.
      assert (toplike D); eauto.
      eapply sub_toplike_preservation; eauto.
  - gen A B.
    proper_ind C0; introv Hs1 Hs2 Hspl Hrb IH; eauto.
    + eapply sub_inversion_split_r in Hs1; eauto.
      destruct Hs1.
      eapply sub_inversion_split_l in Hs2; eauto.
      destruct Hs2; eauto.
    + eapply sub_inversion_split_r in Hs1; eauto.
      destruct Hs1.
      eapply sub_inversion_split_l in Hs2; eauto.
      destruct Hs2; eauto.
    + eapply sub_inversion_split_r in Hs2; eauto.
      destruct Hs2; eauto.
Qed.
