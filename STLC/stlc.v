Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.

Definition tvar : Set := var. (*r term variable *)
Definition Tvar : Set := var. (*r term variable *)

Inductive type : Set :=  (*r type *)
 | type_int(*r int *)
 | type_top(*r top *)
 | type_arrow (A:type) (B:type) (*r function *)
 | type_intersection (A:type) (B:type). (*r intersection type *)

Check type_int.

Inductive sub : type -> type -> Prop :=    (* defn sub *)
 | sub_S_Int :
     sub type_int type_int
 | sub_S_Top : forall (A:type),
     sub A type_top
 | sub_S_Arrow : forall (A B C D:type),
     sub C A ->
     sub B D ->
     sub (type_arrow A B) (type_arrow C D)
 | sub_S_And : forall (A B C:type),
     sub A B ->
     sub A C ->
     sub A (type_intersection B C)
 | sub_S_AndL : forall (A B C:type),
     sub A C ->
     sub (type_intersection A B) C
 | sub_S_AndR : forall (A B C:type),
     sub B C ->
     sub (type_intersection A B) C.

Hint Constructors sub : core.

Theorem sub_reflexivity :
  forall t, sub t t.
Proof.
  induction t.
  - apply sub_S_Int.
  - apply sub_S_Top.
  - apply sub_S_Arrow.
    + apply IHt1.
    + apply IHt2.
  - apply sub_S_And.
    + apply sub_S_AndL. apply IHt1.
    + apply sub_S_AndR. apply IHt2.
Qed.

Lemma sub_and:
  forall t1 t2 t3, sub t1 (type_intersection t2 t3) -> sub t1 t2 /\ sub t1 t3.
Proof.
  intros t1 t2 t3 H.
  dependent induction H; eauto.
  destruct (IHsub t2 t3); split; constructor; eauto.
  destruct (IHsub t2 t3); split.
  apply sub_S_AndR. assumption.
  apply sub_S_AndR. assumption.
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
  - apply sub_and in H.
    destruct H.
    dependent induction H0; eauto.
Qed.
