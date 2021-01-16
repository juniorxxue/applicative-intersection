Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language Subtyping.

Lemma appsub_coincides_with_sub :
  forall (S : arg) (A B : typ),
    appsub S A B ->
    exists (B' : typ), B = (typ_stack S B').
Proof.
  intros.
  induction H; eauto.
  - exists A. unfold typ_stack. auto.
  - exists typ_top. auto.
  - destruct IHappsub. rewrite H0.
    simpl. exists x. reflexivity.
Qed.

Lemma appsub_reflexivity :
  forall (S : arg) (A : typ),
    appsub S (typ_stack S A) (typ_stack S A).
Proof.
  induction S; intros.
  - constructor.
  - simpl. apply as_fun.
    apply IHS.
Qed.

(*
S1 |- A <: S1 -> B
S2 |- B <: C
S1, S2 |- A <: S1 -> C
*)

Lemma appsub_transitivity_simpl :
  forall (S1 S2 : arg) (A B C : typ),
    appsub S1 A B ->
    appsub S2 B C ->
    appsub (S1 ++ S2) A C.
Proof.
  intros S1 S2 A B C H1 H2.
  dependent induction H1; subst.
  - simpl in *. assumption.
  - simpl in *. inversion H2; subst; clear H2.
    + constructor.
    + constructor.
  - simpl in *.
    Admitted.

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
    apply IHappsub with B.
    reflexivity. assumption.
  - apply as_and_l.
    + apply IHappsub with B.
      reflexivity. assumption.
Admitted.
(*     + *)
(*   - apply as_and_r. *)
(*     apply IHappsub with B. *)
(*     reflexivity. *)
(*     assumption. *)
(* Qed. *)

Lemma appsub_to_sub :
  forall (S : arg) (A B : typ),
  appsub S A B -> sub A B.
Proof.
  intros S A B H.
  induction H; eauto; subst.
  - apply sub_reflexivity.
  - apply sub_top_arr.
Admitted.


Lemma sub_to_appsub :
  forall (S : arg) (A B1 : typ),
    sub A (typ_stack S B1) ->
    exists B2 : typ,
      appsub S A (typ_stack S B2) /\ (sub B2 B1).
Proof.
  intros S A B1 H.
  dependent induction H.
  - destruct S.
    simpl. exists typ_int. split.
    constructor. simpl in x. rewrite <- x.
    constructor.
    inversion x.
  - destruct S; simpl in *; subst.
    exists A. split. constructor. constructor.
    inversion x.
  - destruct S; simpl in *; subst.
    exists typ_top. split.
    constructor. constructor. assumption.
    inversion x; subst.
    pose proof (IHsub S B1) as IHsub'.
    assert (IHsub_help: typ_stack S B1 = typ_stack S B1).
    reflexivity.
Admitted.
    (* (inversion x; subst. *) *) *)
(*     pose proof (IHsub2 S B1) as IHsub2'. *)
(*     assert (IHsub2_help: typ_stack S B1 = typ_stack S B1). *)
(*     reflexivity. *)
(*     apply IHsub2' in IHsub2_help. *)
(*     destruct IHsub2_help. *)
(*     exists x0. split. *)
(*     constructor. assumption. *)
(*     destruct H1 as [H11 H12]. *)
(*     assumption. *)
(*     destruct H1 as [H11 H12]. *)
(*     assumption. *)
(*   - destruct S; simpl in *; subst. *)
(*     exists A. split. constructor. constructor. assumption. assumption. *)
(*     inversion x. *)
(*   - destruct S; simpl in *; subst. *)
(*     exists (typ_and A B). split. constructor. apply sub_AndL. assumption. *)
(*     pose proof (IHsub (cons t S) B1) as IHsub'. *)
(*     assert(IHsub_help: typ_arrow t (typ_stack S B1) = typ_stack (t :: S) B1). *)
(*     simpl. reflexivity. *)
(*     apply IHsub' in IHsub_help. *)
(*     destruct IHsub_help. *)
(*     destruct H0 as [H01 H02]. *)
(*     exists x. split. apply as_AndL. *)
(*     simpl in H01. assumption. assumption. *)
(*   - destruct S; simpl in *; subst. *)
(*     exists (typ_and A B). split. constructor. apply sub_AndR. assumption. *)
(*     pose proof (IHsub (cons t S) B1) as IHsub'. *)
(*     assert(IHsub_help: typ_arrow t (typ_stack S B1) = typ_stack (t :: S) B1). *)
(*     simpl. reflexivity. *)
(*     apply IHsub' in IHsub_help. *)
(*     destruct  IHsub_help. *)
(*     destruct  H0 as [H01 H02]. *)
(*     exists x. split. apply as_AndR. *)
(*     simpl in H01. assumption. assumption. *)
(* Qed. *)
