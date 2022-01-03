Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Strings.String.
Require Import Program.Tactics.
Require Import Language LibTactics.

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

Hint Resolve proper_typ_arrow : proper.

Lemma proper_typ_complete :
  forall (A : typ), proper_typ A.
Proof.
  induction A; eauto with proper.
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

Ltac solve_split_and_ord :=
  match goal with
  | [H1: splitable ?A ?A1 ?A2, H2: ordinary ?A |- _] =>
      (eapply split_and_ord in H1; eauto; inversion H1)
  | [H1: splitable (typ_arrow ?A ?B) ?B1 ?B2, H2: ordinary ?B |- _] =>
      (dependent destruction H1; eapply split_and_ord in H1; eauto; inversion H1)
  end.

Hint Extern 5 => solve_split_and_ord : subtyping.

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

Hint Resolve sub_arrow_gen : subtyping.

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

Hint Resolve sub_and_l_gen : subtyping.
Hint Resolve sub_and_r_gen : subtyping.

Lemma sub_reflexivity:
  forall (A : typ), sub A A.
Proof.
  induction A; eauto with subtyping.
Qed.

Hint Resolve sub_reflexivity : subtyping core.

Lemma splitable_sub_l :
  forall (A B C : typ),
    splitable A B C -> sub A B.
Proof.
  introv H. dependent induction H; eauto with subtyping.
Qed.

Lemma splitable_sub_r :
  forall (A B C : typ),
    splitable A B C -> sub A C.
Proof.
  introv H. dependent induction H; eauto with subtyping.
Qed.

Hint Resolve splitable_sub_l : subtyping.
Hint Resolve splitable_sub_r : subtyping.

Lemma splitable_iso :
  forall (A B C : typ),
    splitable A B C -> sub A (typ_and B C) /\ sub (typ_and B C) A.
Proof.
  introv H.
  split.
  - eapply sub_and; eauto with subtyping.
  - dependent induction H; eauto with subtyping.
Qed.

Hint Resolve splitable_iso : subtyping.

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
    eapply IHsub2 in H2; eauto with subtyping.
    destruct H2; eauto with subtyping.
  - eapply split_and_ord in H1; eauto. inversion H1.
  - dependent destruction H2.
    left. assumption.
  - dependent destruction H2.
    right. assumption.
Qed.

Lemma sub_inversion_split_r :
  forall (A B B1 B2 : typ),
    sub A B -> splitable B B1 B2 -> sub A B1 /\ sub A B2.
Proof.
  intros * Hsub Hspl.
  dependent destruction Hsub; try solve [eauto with subtyping].
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

Lemma split_toplike :
  forall (A B C : typ),
    splitable A B C -> toplike A -> toplike B /\ toplike C.
Proof.
  introv Hspl Htl.
  induction Hspl.
  - dependent destruction Htl; eauto.
  - dependent destruction Htl.
    pose proof (IHHspl Htl).
    destruct_conjs.
    auto.
Qed.

Lemma sub_toplike_preservation :
  forall (A B : typ),
    toplike A -> sub A B -> toplike B.
Proof.
  introv Htl Hsub.
  dependent induction Hsub; try solve [inversion Htl]; eauto.
  - dependent destruction Htl; eauto.
  - eapply toplike_spl_combine; eauto.
  - dependent destruction Htl; eauto.
  - dependent destruction Htl; eauto.
Qed.

Hint Resolve sub_toplike_preservation : subtyping.

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
    dependent induction Hs1; eauto with subtyping.
  - gen A B.
    proper_ind C0; introv Hs1 Hs2 Hspl Hrb IH; eauto with subtyping.
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

Ltac solve_toplike :=
  match goal with
  | [H: toplike typ_int |- _] => (inversion H)
  | [H1: toplike (typ_arrow _ ?B), H2: not (toplike ?B) |- _] =>
    (dependent destruction H1; contradiction)
  end.

Hint Extern 5 => solve_toplike : subtyping.

Ltac solve_splitable :=
  match goal with
  | [H: splitable typ_int _ _ |- _] => (inversion H)
  end.

Hint Extern 5 => solve_splitable : subtyping.

Lemma ordinary_decidability :
  forall (A : typ),
    ordinary A \/ not (ordinary A).
Proof.
  introv.
  induction A; eauto.
  - destruct IHA1; destruct IHA2; eauto.
    + right. intros Hcontra. dependent destruction Hcontra. contradiction.
    + right. intros Hcontra. dependent destruction Hcontra. contradiction.
  - right. intros Hcontra. inversion Hcontra.
Qed.

Hint Resolve ordinary_decidability : subtyping.

Lemma toplike_decidability:
  forall (A : typ),
    toplike A \/ not (toplike A).
Proof.
  intros A.
  induction A;
    try solve [left; eauto | right; intros Hcontra; inversion Hcontra].
  - destruct IHA1; destruct IHA2; eauto.
    + right; intros H1; dependent destruction H1; contradiction.
    + right; intros H1; dependent destruction H1; contradiction.
  - destruct IHA1; destruct IHA2; eauto.
    + right; intros H1; dependent destruction H1; contradiction.
    + right; intros H1; dependent destruction H1; contradiction.
    + right; intros H1; dependent destruction H1; contradiction.
Qed.

Hint Resolve toplike_decidability : subtyping.

Lemma split_and_not_toplike :
  forall (A B C : typ),
    not (toplike A) -> splitable A B C ->
    not (toplike B) \/ not (toplike C).
Proof.
  introv Hntl Hspl.
  gen B C.
  induction A; intros.
  - inversion Hspl.
  - inversion Hspl.
  - dependent destruction Hspl.
    assert (not (toplike C) \/ not (toplike D)); eauto.
    destruct H.
    + left. intros Hcontra. dependent destruction Hcontra. contradiction.
    + right. intros Hcontra. dependent destruction Hcontra. contradiction.
  - dependent destruction Hspl.
    destruct (toplike_decidability A1);
    destruct (toplike_decidability A2); eauto.
Qed.

Lemma sub_int_form :
  forall (A : typ),
    sub typ_int A -> not (toplike A) -> ordinary A -> A = typ_int.
Proof.
  introv Hsub Htl Hord.
  dependent induction Hord; eauto.
  - destruct Htl; eauto.
  - dependent destruction Hsub.
    + contradiction.
    + dependent destruction H.
      eauto with subtyping.
Qed.

Lemma sub_int_arrow :
  forall (A B : typ),
    not (toplike B) ->
    sub typ_int (typ_arrow A B) ->
    False.
Proof.
  introv Htl Hsub.
  dependent induction Hsub; eauto.
  - dependent destruction H0. contradiction.
  - dependent destruction H.
    destruct (toplike_decidability C); eauto.
    destruct (toplike_decidability D); eauto.
    eapply split_and_not_toplike in H; eauto.
    intuition.
Qed.

Lemma sub_arrow_int :
  forall (A B : typ),
    sub (typ_arrow A B) typ_int -> False.
Proof.
  introv H.
  dependent destruction H; eauto with subtyping.
Qed.

Lemma sub_toplike_int :
  forall (A : typ),
    toplike A -> sub A typ_int -> False.
Proof.
  introv Htl Hsub.
  induction Htl;
    dependent destruction Hsub; eauto with subtyping.
Qed.

Ltac solve_subtype :=
  match goal with
  | [H: sub (typ_arrow _ _) typ_int |- _] =>
    (eapply sub_arrow_int in H; inversion H)
  | [H1: not (toplike ?B), H2: sub typ_int (typ_arrow _ ?B) |- _] =>
    (eapply sub_int_arrow in H1; eauto; inversion H1)
  | [H1: toplike ?A, H2: sub ?A typ_int |- _] =>
    (eapply sub_toplike_int in H1; eauto; inversion H1)
  end.

Hint Extern 5 => solve_subtype : subtyping.

Lemma sub_toplike :
  forall (A B : typ),
    toplike A -> sub B A.
Proof.
  introv Htl.
  proper_ind A; eauto.
  pose proof (split_toplike A B0 C H Htl).
  destruct_conjs.
  eapply sub_and; eauto.
Qed.

Lemma iso_to_sub :
  forall (A B : typ),
    isomorphic A B -> sub A B.
Proof.
  introv Hiso.
  induction Hiso; eauto with subtyping.
Qed.

Lemma iso_to_sub' :
  forall (A B : typ),
    isomorphic A B -> sub B A.
Proof.
  introv Hiso.
  induction Hiso; eauto with subtyping.
  eapply sub_and; eauto.
  - assert (sub (typ_and B1 B2) A1) by eauto with subtyping.
    eapply splitable_iso in H. destruct H.
    eapply sub_transitivity; eauto.
  - assert (sub (typ_and B1 B2) A2) by eauto with subtyping.
    eapply splitable_iso in H. destruct H.
    eapply sub_transitivity; eauto.
Qed.

Hint Resolve iso_to_sub : subtyping.

Lemma sub_not_toplike :
  forall A B,
    not (toplike B) ->
    sub A B ->
    not (toplike A).
Proof.
  introv Hntl Hsub.
  intros Hcontra.
  assert (toplike B) by eauto with subtyping.
  contradiction.
Qed.

Hint Resolve sub_not_toplike : subtyping.

Lemma sub_arrow_form :
  forall (A B C : typ),
    not (toplike C) -> ordinary C ->
    sub (typ_arrow A B) C ->
    (exists D E, C = (typ_arrow D E)).
Proof.
  introv nHtl Hord Hsub.
  induction Hord; eauto.
  - destruct nHtl; eauto.
  - dependent destruction Hsub.
    + inversion H0.
    + inversion H.
Qed.

Hint Resolve sub_arrow_form : subtyping.
