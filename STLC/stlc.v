Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.

Definition tvar : Set := var. (*r term variable *)
Definition Tvar : Set := var. (*r type variable *)

Inductive type : Set :=  (*r type *)
| type_int(*r int *)
| type_top(*r top *)
| type_arrow (A:type) (B:type) (*r function *)
| type_and (A:type) (B:type). (*r intersection type *)

Inductive typep : type -> Prop :=
| typep_int : typep type_int
| typep_top : typep type_top
| typep_arrow : forall (A B : type),
    typep A -> typep B -> typep (type_arrow A B)
| typep_and : forall (A B : type),
    typep A -> typep B -> typep (type_and A B).

Inductive term : Set :=
| term_nat : nat -> term
| term_bvar : nat -> term
| term_fvar : var -> term
| term_abs : term -> term
| term_app : term -> term -> term
| term_merge : term -> term -> term
| term_anno : term -> type -> term.

Inductive termp : term -> Prop :=
| termp_nat : forall (n : nat), termp (term_nat n)
| termp_bvar : forall (n : nat), termp (term_bvar n)
| termp_fvar : forall (x : var), termp (term_fvar x)
| termp_abs : forall (e : term), termp (term_abs e)
| termp_app : forall (e1 e2 : term), termp (term_app e1 e2)
| termp_merge : forall (e1 e2 : term), termp (term_merge e1 e2)
| termp_anno : forall (e : term) (A : type), termp (term_anno e A).

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
    simpl. exists x. reflexivity.
Qed.

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

Lemma appsub_transitivity :
  forall (S1 S2 : arg) (A B C: type),
    appsub S1 A (type_stack S1 B) ->
    appsub S2 B C ->
    appsub (S1 ++ S2) A (type_stack S1 C).
Proof.
  intros S1 S2 A B C H1 H2.
  dependent induction H1; subst.
  - simpl in *.
    assumption.
  - simpl in *.
    constructor. assumption.
    apply IHappsub with B.
    reflexivity. assumption.
  - apply as_AndL.
    apply IHappsub with B.
    reflexivity.
    assumption.
  - apply as_AndR.
    apply IHappsub with B.
    reflexivity.
    assumption.
Qed.

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
  intros S A B1 H.
  dependent induction H.
  - destruct S.
    simpl. exists type_int. split.
    constructor. simpl in x. rewrite <- x.
    constructor.
    inversion x.
  - destruct S; simpl in *; subst.
    exists A. split. constructor. constructor.
    inversion x.
  - destruct S; simpl in *; subst.
    exists (type_arrow A B). split.
    constructor.
    constructor. assumption. assumption.
    inversion x; subst.
    pose proof (IHsub2 S B1) as IHsub2'.
    assert (IHsub2_help: type_stack S B1 = type_stack S B1).
    reflexivity.
    apply IHsub2' in IHsub2_help.
    destruct IHsub2_help.
    exists x0. split.
    constructor. assumption.
    destruct H1 as [H11 H12].
    assumption.
    destruct H1 as [H11 H12].
    assumption.
  - destruct S; simpl in *; subst.
    exists A. split. constructor. constructor. assumption. assumption.
    inversion x.
  - destruct S; simpl in *; subst.
    exists (type_and A B). split. constructor. apply sub_AndL. assumption.
    pose proof (IHsub (cons t S) B1) as IHsub'.
    assert(IHsub_help: type_arrow t (type_stack S B1) = type_stack (t :: S) B1).
    simpl. reflexivity.
    apply IHsub' in IHsub_help.
    destruct IHsub_help.
    destruct H0 as [H01 H02].
    exists x. split. apply as_AndL.
    simpl in H01. assumption. assumption.
  - destruct S; simpl in *; subst.
    exists (type_and A B). split. constructor. apply sub_AndR. assumption.
    pose proof (IHsub (cons t S) B1) as IHsub'.
    assert(IHsub_help: type_arrow t (type_stack S B1) = type_stack (t :: S) B1).
    simpl. reflexivity.
    apply IHsub' in IHsub_help.
    destruct  IHsub_help.
    destruct  H0 as [H01 H02].
    exists x. split. apply as_AndR.
    simpl in H01. assumption. assumption.
Qed.

(* ----------------------------- *)
(*   Typing Relation *)
(* ----------------------------- *)

Definition ctx : Set := list (atom * type).

Inductive ctxp : ctx -> Prop :=
| ctxp_empty : ctxp nil
| ctxp_cons : forall (T : ctx) (x : var) (A : type),
    ctxp T -> typep A -> ctxp ((x ~ A) ++ T).

Inductive mode := check_mode | infer_mode.

Fixpoint open_rec (k : nat) (u : term) (t : term) {struct t} : term :=
  match t with
  | term_nat n => term_nat n
  | term_bvar i => if k == i then u else (term_bvar i)
  | term_fvar x => term_fvar x
  | term_abs t1 => term_abs (open_rec (S k) u t1)
  | term_app t1 t2 => term_app (open_rec k u t1) (open_rec k u t2)
  | term_merge t1 t2 => term_merge (open_rec k u t1) (open_rec k u t2)
  | term_anno t1 A => term_anno (open_rec k u t1) A
  end.

Definition open t u := open_rec 0 u t.

Inductive typing : ctx -> arg -> mode -> term -> type -> Prop :=
| typing_int : forall (T: ctx) (n : nat),
    uniq T ->
    (typing T nil infer_mode (term_nat n) type_int)
| typing_var : forall (T : ctx) (x : var) (A : type),
    uniq T ->
    binds x A T ->
    typing T nil infer_mode (term_fvar x) A
| typing_abs1 : forall (L : vars) (T : ctx) (e : term) (A B : type),
    (forall x, x \notin L ->
          (typing ((x ~ A) ++ T)) nil check_mode (open e (term_fvar x)) B) ->
    typing T nil check_mode (term_abs e) (type_arrow A B)
| typing_abs2 : forall (L: vars) (T : ctx) (S : arg) (A B : type) (e : term),
    (forall x, x \notin L ->
          (typing ((x ~ A) ++ T)) S infer_mode (open e (term_fvar x)) B) ->
    typing T (cons A S) infer_mode (term_abs e) (type_arrow A B)
| typing_anno : forall (T : ctx) (S : arg) (A B : type) (e : term),
    appsub S A B ->
    typing T nil check_mode e A ->
    typing T S infer_mode (term_anno e A) B
| typing_app1 : forall (T : ctx) (S : arg) (A B : type) (e1 e2 : term),
    typing T nil infer_mode e2 A ->
    typing T nil check_mode e1 (type_arrow A B) ->
    typing T S infer_mode (term_app e1 e2) B
| typing_app2 : forall (T : ctx) (A B : type) (e1 e2 : term),
    typing T nil infer_mode e2 A ->
    typing T nil check_mode e1 (type_arrow A B) ->
    typing T nil check_mode (term_app e1 e2) B
| typing_sub : forall (T : ctx) (A B : type) (e : term),
    typing T nil infer_mode e B ->
    (sub B A) ->
    typing T nil check_mode e A
| typing_merge : forall (T : ctx) (A B : type) (e1 e2 : term),
    typing T nil infer_mode e1 A ->
    typing T nil infer_mode e2 B ->
    typing T nil infer_mode (term_merge e1 e2) (type_and A B).


Lemma typing_regularity :
  forall (T : ctx) (e : term) (A : type),
    typing T nil infer_mode e A -> typep A /\ ctxp T.
Proof.
Admitted.

Lemma typing_weaken :
  forall (T1 T2 : ctx) (e : term) (A : type) (x : var),
    typing (T1 ++ T2) nil infer_mode e A ->
    typing (T1 ++ (x ~ A) ++ T2) nil infer_mode e A.
Proof.
Admitted.
