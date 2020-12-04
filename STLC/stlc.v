Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.

Definition tvar : Set := var. (*r term variable *)
Definition Tvar : Set := var. (*r term variable *)

Inductive type : Set :=  (*r type *)
 | type_int(*r int *)
 | type_top(*r top *)
 | type_arrow (A:type) (B:type) (*r function *)
 | type_and (A:type) (B:type). (*r intersection type *)

Inductive sub : type -> type -> Prop :=    (* defn sub *)
 | sub_Int :
     sub type_int type_int
 | sub_Top : forall (A:type),
     sub A type_top
 | sub_Arrow : forall (A B C D:type),
     sub C A ->
     sub B D ->
     sub (type_arrow A B) (type_arrow C D)
 | sub_And : forall (A B C:type),
     sub A B ->
     sub A C ->
     sub A (type_and B C)
 | sub_AndL : forall (A B C:type),
     sub A C ->
     sub (type_and A B) C
 | sub_AndR : forall (A B C:type),
     sub B C ->
     sub (type_and A B) C.

Hint Constructors sub : core.

Theorem sub_reflexivity :
  forall t, sub t t.
Proof.
  induction t.
  - apply sub_Int.
  - apply sub_Top.
  - apply sub_Arrow.
    + apply IHt1.
    + apply IHt2.
  - apply sub_And.
    + apply sub_AndL. apply IHt1.
    + apply sub_AndR. apply IHt2.
Qed.

Lemma lemma_sub_and:
  forall t1 t2 t3, sub t1 (type_and t2 t3) -> sub t1 t2 /\ sub t1 t3.
Proof.
  intros t1 t2 t3 H.
  dependent induction H; eauto.
  destruct (IHsub t2 t3); split; constructor; eauto.
  destruct (IHsub t2 t3); split.
  apply sub_AndR. assumption.
  apply sub_AndR. assumption.
Qed.

Theorem sub_transitivity :
  forall t2 t1 t3, sub t1 t2 -> sub t2 t3 -> sub t1 t3.
Proof.
  induction t2; intros; eauto.
  - induction t1; eauto.
    + inversion H.
    + inversion H.
    + inversion H; eauto.
  - induction t3; eauto.
    + induction t1; eauto.
      inversion H0.
    + inversion H0.
    + inversion H0.
      constructor.
      apply IHt3_1.
      assumption.
      apply IHt3_2.
      assumption.
  - dependent induction H; eauto.
    clear IHsub1 IHsub2.
    dependent induction H1; eauto.
  - apply lemma_sub_and in H.
    destruct H.
    dependent induction H0; eauto.
Qed.

(* ----------------------------- *)
(*   Applicative Subtyping *)
(* ----------------------------- *)

Definition arg := list type.

(* S |- A <: B *)
Inductive appsub : arg -> type -> type -> Prop :=
| as_Refl : forall (A : type), appsub nil A A
| as_Fun : forall (C A B D : type) (S : arg),
    sub C A ->
    appsub S B D ->
    appsub (cons C S) (type_arrow A B) (type_arrow C D)
| as_AndL : forall (A B D : type) (S : arg),
    appsub S A D ->
    appsub S (type_and A B) D
| as_AndR : forall (A B D : type) (S : arg),
    appsub S B D ->
    appsub S (type_and A B) D.

Fixpoint type_stack (S : arg) (A : type) : type :=
  match S with
  | nil => A
  | cons A' S' => type_arrow A' (type_stack S' A)
  end.

Compute (type_stack (cons type_int (cons type_int nil)) type_top).

Lemma appsub_coincides_with_sub :
  forall (S : arg) (A B : type),
    appsub S A B ->
    exists (B' : type), B = (type_stack S B').
Proof.
  intros.
  induction H; eauto.
  - exists A. unfold type_stack. auto.
  - destruct IHappsub. rewrite H1.
    simpl. exists x.
Admitted.

Lemma appsub_reflexivity :
  forall (S : arg) (A : type),
    appsub S (type_stack S A) (type_stack S A).
Proof.
  induction S; intros.
  - constructor.
  - simpl. apply as_Fun.
    apply sub_reflexivity.
    apply IHS.
Qed.

(* Lemma appsub_transitivity : *)
(*   forall (S1 S2 : arg) (A B C : type), *)
(*     appsub S1 A (type_stack S1 B) -> *)
(*     appsub S2 B (type_stack S2 C) -> *)
(*     appsub (cons S2 S1) A (type_stack S1 (type_stack S2 C)). *)
(* Proof. *)
(* Admitted. *)

Lemma appsub_to_sub :
  forall (S : arg) (A B : type),
  appsub S A B ->
  sub A B.
Proof.
  intros S A B H.
  induction H; eauto; subst.
  apply sub_reflexivity.
Qed.

Lemma sub_to_appsub :
  forall (S : arg) (A B1 : type),
    sub A (type_stack S B1) ->
    exists B2 : type,
      appsub S A (type_stack S B2) /\ (sub B2 B1).
Proof.
  Admitted.




