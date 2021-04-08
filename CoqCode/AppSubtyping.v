Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language Subtyping Notations.

Set Printing Parentheses.

Lemma appsub_coincides_with_sub :
  forall (S : arg) (A B : typ),
    appsub S A B ->
    exists (B' : typ), B = (typ_stack S B').
Proof.
  intros.
  induction H; eauto.
  - exists A. unfold typ_stack. auto.
  - exists typ_top. auto.
  - destruct IHappsub. rewrite H1.
    simpl. exists x. reflexivity.
Qed.

Lemma appsub_reflexivity :
  forall (S : arg) (A : typ),
    appsub S (typ_stack S A) (typ_stack S A).
Proof.
  induction S; intros.
  - constructor.
  - simpl. apply as_fun.
    + apply sub_reflexivity.
    + apply IHS.
Qed.

Lemma stack_commutativity :
  forall (S1 S2 : arg) (A : typ),
    (typ_stack (S1 ++ S2) A) = (typ_stack S1 (typ_stack S2 A)).
Proof.
  intros S1 S2 A.
  induction S1.
  - simpl. reflexivity.
  - simpl. rewrite IHS1. reflexivity.
Qed.

Lemma stack_sub_top :
  forall (S : arg) (A : typ),
    sub (typ_stack S A) (typ_stack S typ_top).
Proof.
  intros S A.
  induction S.
  - simpl. apply sub_top.
  - simpl. apply sub_arrow.
    + apply sub_reflexivity.
    + apply IHS.
Qed.

Lemma appsub_transitivity :
  forall (S1 S2 : arg) (A B C: typ),
    appsub S1 A (typ_stack S1 B) ->
    appsub S2 B C ->
    appsub (S1 ++ S2) A (typ_stack S1 C).
Proof.
  intros S1 S2 A B C H1 H2.
  dependent induction H1; subst.
  - simpl in *.
    assumption.
  - simpl in *; subst.
    inversion H2; subst.
    constructor. constructor.
  - simpl in *.
    constructor.
    + assumption.
    + apply IHappsub with B.
      reflexivity. assumption.
  - apply as_and_l.
    + apply IHappsub with B.
      reflexivity. assumption.
    + unfold not. intros.
      rewrite stack_commutativity in H0.
      assert (Hsub: sub B0 (typ_stack S typ_top)).
      eapply sub_transitivity. apply H0.
      eapply stack_sub_top.
      unfold not in H.
      apply H in Hsub. assumption.
  - apply as_and_r.
    + apply IHappsub with B.
      reflexivity. assumption.
    + unfold not. intros.
      rewrite stack_commutativity in H0.
      assert (Hsub: sub A (typ_stack S typ_top)).
      eapply sub_transitivity. apply H0.
      eapply stack_sub_top.
      unfold not in H.
      apply H in Hsub. assumption.
Qed.

Lemma appsub_to_sub :
  forall (S : arg) (A B : typ),
  appsub S A B -> sub A B.
Proof.
  intros S A B H.
  induction H; eauto.
  apply sub_reflexivity.
Qed.


(*aux lemma for sub_to_app *)
Lemma stack_is_top :
  forall (S : arg) (A : typ),
    typ_stack S A = typ_top -> S = nil /\ A = typ_top.
Proof.
  induction S.
  - simpl. split.
    + reflexivity.
    + assumption.
  - simpl. intros. split.
    + inversion H.
    + inversion H.
Qed.

(* aux lemma for stack_toplike *)
Lemma typ_arrow_toplike :
  forall (A B : typ),
    toplike (typ_arrow A B) -> toplike B.
Proof.
  intros A B Htl.
  inversion Htl.
  assumption.
Qed.

(* aux lemma for sub_to_appsub *)
Lemma stack_toplike :
  forall (S : arg) (A : typ),
    toplike (typ_stack S A) -> toplike A.
Proof.
  intros S A Htl.
  induction S.
  - simpl in *. assumption.
  - simpl in *. apply IHS.
    apply typ_arrow_toplike in Htl. assumption.
Qed.

Lemma sub_to_appsub :
  forall (S : arg) (A B1 : typ),
    sub A (typ_stack S B1) -> not (toplike B1) ->
    exists B2 : typ, (appsub S A (typ_stack S B2) /\ (sub B2 B1)).
Proof.
  intros S A B1 H1 H2.
  dependent induction H1.
  - destruct S.
    + simpl. exists typ_int. split.
      * constructor.
      * simpl in x. rewrite <- x. constructor.
    + inversion x.
  - destruct S; simpl in *; subst.
    + exists A. split.
      * constructor.
      * constructor.
    + inversion x.
  - destruct S; simpl in *; subst.
    + exists A. split.
      * constructor.
      * assert (H2': toplike (typ_arrow B0 B2)).
        constructor.
        apply toplike_sub_top. assumption.
        contradiction.
    + inversion x; subst; simpl in *.
      assert (H2': toplike (typ_stack S B1)).
      apply toplike_sub_top. assumption.
      apply stack_toplike in H2'.
      contradiction.
  - destruct S; simpl in *; subst.
    + exists (typ_arrow A B). split.
      * constructor.
      * apply sub_arrow. assumption. assumption.
    + inversion x; subst.
      pose proof (IHsub2 S B1) as IHsub2'.
      assert (IHsub2_help: typ_stack S B1 = typ_stack S B1).
      reflexivity.
      apply IHsub2' in IHsub2_help.
      destruct IHsub2_help.
      exists x0. split.
      * constructor. assumption.
        destruct H as [H11 H12].
        assumption.
      * destruct H as [H11 H12].
        assumption.
      * assumption.
  - destruct S; simpl in *; subst.
    exists A. split. constructor. constructor. assumption. assumption.
    inversion x.
  - destruct S; simpl in *; subst.
    + exists (typ_and A B). split.
      * constructor.
      * apply sub_and_l. assumption.
    + pose proof (IHsub (cons t S) B1) as IHsub'.
      assert(IHsub_help: typ_arrow t (typ_stack S B1) = typ_stack (t :: S) B1).
      simpl. reflexivity.
      apply IHsub' in IHsub_help.
      destruct IHsub_help.
      destruct H as [H01 H02].
      exists x. split.
      * apply as_and_l. assumption.
Admitted.
