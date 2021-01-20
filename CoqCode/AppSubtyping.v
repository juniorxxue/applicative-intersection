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
Admitted.

Lemma appsub_to_sub :
  forall (S : arg) (A B : typ),
  appsub S A B -> sub A B.
Proof.
  intros S A B H.
  induction H; eauto.
  apply sub_reflexivity.
Qed.


Lemma sub_to_appsub :
  forall (S : arg) (A B1 : typ),
    sub A (typ_stack S B1) -> not (toplike B1) ->
    exists B2 : typ, (appsub S A (typ_stack S B2) /\ (sub B2 B1)).
Proof.
  intros S A B1 H1 H2.
  dependent induction H1.
  - destruct S.
    simpl. exists typ_int. split.
    constructor. simpl in x. rewrite <- x.
    constructor.
    inversion x.
  - destruct S; simpl in *; subst.
    exists A. split. constructor. constructor.
    inversion x.
Admitted.
