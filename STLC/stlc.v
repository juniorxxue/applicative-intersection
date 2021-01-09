Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.

Inductive typ : Set :=  (*r typ *)
| typ_int(*r int *)
| typ_top(*r top *)
| typ_arrow (A:typ) (B:typ) (*r function *)
| typ_and (A:typ) (B:typ). (*r intersection typ *)

Inductive type : typ -> Prop :=
| type_int : type typ_int
| type_top : type typ_top
| type_arrow : forall (A B : typ),
    type A -> type B -> type (typ_arrow A B)
| type_and : forall (A B : typ),
    type A -> type B -> type (typ_and A B).

Hint Constructors typ : core.
Hint Constructors type : core.

Inductive trm : Set :=
| trm_top : trm
| trm_nat : nat -> trm
| trm_bvar : nat -> trm
| trm_fvar : var -> trm
| trm_abs : trm -> trm
| trm_app : trm -> trm -> trm
| trm_merge : trm -> trm -> trm
| trm_anno : trm -> typ -> trm.

(* term is locally closed *)

Definition ctx : Set := list (var * typ).

Inductive mode := check_mode | infer_mode.

Fixpoint open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_top => trm_top
  | trm_nat n => trm_nat n
  | trm_bvar i => if k == i then u else (trm_bvar i)
  | trm_fvar x => trm_fvar x
  | trm_abs t1 => trm_abs (open_rec (S k) u t1)
  | trm_app t1 t2 => trm_app (open_rec k u t1) (open_rec k u t2)
  | trm_merge t1 t2 => trm_merge (open_rec k u t1) (open_rec k u t2)
  | trm_anno t1 A => trm_anno (open_rec k u t1) A
  end.

Definition open t u := open_rec 0 u t.

Inductive term : trm -> Prop :=
| term_top : term trm_top
| term_nat : forall (n : nat), term (trm_nat n)
| term_bvar : forall (n : nat), term (trm_bvar n)
| term_fvar : forall (x : var), term (trm_fvar x)
| term_abs : forall (e : trm) (L : vars),
    (forall x, x \notin L -> term (open e (trm_fvar x))) ->
    term (trm_abs e)
| term_app : forall (e1 e2 : trm), term (trm_app e1 e2)
| term_merge : forall (e1 e2 : trm), term (trm_merge e1 e2)
| term_anno : forall (e : trm) (A : typ), term (trm_anno e A).

Hint Constructors trm : core.
Hint Constructors term : core.

(* value *)
Inductive value : trm -> Prop :=
| value_top : value trm_top
| value_nat : forall (n : nat), value (trm_nat n)
| value_abs : forall (e : trm),
    term (trm_abs e) -> value (trm_abs e)
| value_merge : forall (e1 e2 : trm),
    value e1 -> value e2 -> value (trm_merge e1 e2).

Hint Constructors value : core.

Inductive toplike : typ -> Prop :=
| tl_top : toplike typ_top
| tl_and : forall (A B : typ), toplike A -> toplike B -> toplike (typ_and A B)
| tl_arrow : forall (A B : typ), toplike B -> toplike (typ_arrow A B).

Hint Constructors toplike : core.

(* ordinary types are those types aren't intersection *)
Inductive ordinary : typ -> Prop :=
| ord_top : ordinary typ_top
| ord_int : ordinary typ_int
| ord_arrow : forall (A B : typ), ordinary (typ_arrow A B).

Hint Constructors ordinary : core.

(* ----------------------------- *)
(* Subtyping *)
(* ----------------------------- *)

Inductive sub : typ -> typ -> Prop :=    (* defn sub *)
| sub_Int :
    sub typ_int typ_int
| sub_Top : forall (A:typ),
    sub A typ_top
| sub_TopArr : forall (A B1 B2 : typ),
    sub typ_top B2 -> sub A (typ_arrow B1 B2)
| sub_Arrow : forall (A B C D:typ),
    sub C A ->
    sub B D ->
    sub (typ_arrow A B) (typ_arrow C D)
| sub_And : forall (A B C:typ),
    sub A B ->
    sub A C ->
    sub A (typ_and B C)
| sub_AndL : forall (A B C:typ),
    sub A C ->
    sub (typ_and A B) C
| sub_AndR : forall (A B C:typ),
    sub B C ->
    sub (typ_and A B) C.

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
  forall t1 t2 t3, sub t1 (typ_and t2 t3) -> sub t1 t2 /\ sub t1 t3.
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
    + inversion H0; subst. constructor. assumption.
    + inversion H0.
      constructor.
      apply IHt3_1.
      assumption.
      apply IHt3_2.
      assumption.
  - dependent induction H0; eauto.
    clear IHsub1 IHsub2.
    dependent induction H; eauto.
  - apply lemma_sub_and in H.
    destruct H.
    dependent induction H0; eauto.
Qed.

(* ----------------------------- *)
(*   Applicative Subtyping *)
(* ----------------------------- *)

Definition arg := list typ.

(* S |- A <: B *)
Inductive appsub : arg -> typ -> typ -> Prop :=
| as_Refl : forall (A : typ), appsub nil A A
| as_Top : forall (A : typ), appsub nil A typ_top
| as_Fun : forall (C A B D : typ) (S : arg),
    sub C A -> appsub S B D -> appsub (cons C S) (typ_arrow A B) (typ_arrow C D)
| as_AndL : forall (A B D : typ) (S : arg),
    appsub S A D  -> appsub S (typ_and A B) D
| as_AndR : forall (A B D: typ) (S : arg),
    appsub S B D -> appsub S (typ_and A B) D.

Fixpoint typ_stack (S : arg) (A : typ) : typ :=
  match S with
  | nil => A
  | cons A' S' => typ_arrow A' (typ_stack S' A)
  end.

(* Compute (typ_stack (cons type_int (cons type_int nil)) type_top). *)

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
  - simpl. apply as_Fun.
    apply sub_reflexivity.
    apply IHS.
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
  forall (S : arg) (A B : typ),
  appsub S A B ->
  sub A B.
Proof.
  intros S A B H.
  induction H; eauto; subst.
  apply sub_reflexivity.
Qed.

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
    apply IHsub' in IHsub_help.
    destruct IHsub_help. destruct H0.
    exists x0. split.
    Admitted.
(*   - destruct S; simpl in *; subst. *)
(*     exists (typ_arrow A B). split. *)
(*     constructor. *)
(*     constructor. assumption. assumption. *)
(*     inversion x; subst. *)
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

(* ----------------------------- *)
(*   Typing Relation *)
(* ----------------------------- *)

Inductive typing : ctx -> arg -> mode -> trm -> typ -> Prop :=
| typing_int : forall (T: ctx) (n : nat),
    uniq T ->
    (typing T nil infer_mode (trm_nat n) typ_int)
| typing_var : forall (T : ctx) (x : var) (A : typ),
    uniq T -> type A ->
    binds x A T ->
    typing T nil infer_mode (trm_fvar x) A
| typing_abs1 : forall (L : vars) (T : ctx) (e : trm) (A B : typ),
    type A ->
    (forall x, x \notin L ->
          (typing ((x ~ A) ++ T)) nil check_mode (open e (trm_fvar x)) B) ->
    typing T nil check_mode (trm_abs e) (typ_arrow A B)
| typing_abs2 : forall (L: vars) (T : ctx) (S : arg) (A B : typ) (e : trm),
    type A ->
    (forall x, x \notin L ->
          (typing ((x ~ A) ++ T)) S infer_mode (open e (trm_fvar x)) B) ->
    typing T (cons A S) infer_mode (trm_abs e) (typ_arrow A B)
| typing_anno : forall (T : ctx) (S : arg) (A B : typ) (e : trm),
    type A -> type B ->
    appsub S A B ->
    typing T nil check_mode e A ->
    typing T S infer_mode (trm_anno e A) B
| typing_app1 : forall (T : ctx) (S : arg) (A B : typ) (e1 e2 : trm),
    typing T nil infer_mode e2 A ->
    typing T nil check_mode e1 (typ_arrow A B) ->
    typing T S infer_mode (trm_app e1 e2) B
| typing_app2 : forall (T : ctx) (A B : typ) (e1 e2 : trm),
    typing T nil infer_mode e2 A ->
    typing T nil check_mode e1 (typ_arrow A B) ->
    typing T nil check_mode (trm_app e1 e2) B
| typing_sub : forall (T : ctx) (A B : typ) (e : trm),
    typing T nil infer_mode e B ->
    type B -> type A -> (sub B A) ->
    typing T nil check_mode e A
| typing_merge : forall (T : ctx) (A B : typ) (e1 e2 : trm),
    typing T nil infer_mode e1 A ->
    typing T nil infer_mode e2 B ->
    typing T nil infer_mode (trm_merge e1 e2) (typ_and A B).

Hint Constructors typing : core.

Search uniq.

Lemma typing_regular :
  forall (T : ctx) (e : trm) (A : typ),
    typing T nil infer_mode e A -> type A /\ uniq T.
Proof.
  split; induction H; eauto.
  - pick fresh y. pose proof (H1 y) as H1b. apply H1b in Fr.
    constructor. assumption. assumption.
  - pick fresh y. pose proof (H1 y) as H1b. apply H1b in Fr.
    constructor. assumption. assumption.
  - inversion IHtyping2; subst. assumption.
  - inversion IHtyping2. subst. assumption.
  - pick fresh y. pose proof (H1 y) as H1b. apply H1b in Fr.
    simpl in Fr. apply uniq_cons_1 in Fr. assumption.
  - pick fresh y. pose proof (H1 y) as H1b. apply H1b in Fr.
    simpl in Fr. apply uniq_cons_1 in Fr. assumption.
Qed.

Lemma typing_weaken :
  forall (T1 T2 T3: ctx) (e : trm) (A : typ),
    typing (T1 ++ T2) nil infer_mode e A ->
    uniq (T1 ++ T3 ++ T2) ->
    typing (T1 ++ T3 ++ T2) nil infer_mode e A.
Proof.
  intros.
  remember (T1 ++ T2) as T12.
  generalize dependent T1.
  induction H; intros; subst; eauto.
  - apply typing_abs1 with (L := dom (T1 ++ T3 ++ T2) \u L).
    assumption. intros x Frx.
    rewrite_env (([(x, A)] ++ T1) ++ T3 ++ T2).
    apply H1. auto. simpl_env. reflexivity.
    simpl_env. apply uniq_push. assumption. auto.
  - apply typing_abs2 with (L := dom (T1 ++ T3 ++ T2) \u L).
    assumption. intros x Frx.
    rewrite_env (([(x, A)] ++ T1) ++ T3 ++ T2).
    apply H1. auto. simpl_env. reflexivity.
    simpl_env. apply uniq_push. assumption. auto.
Qed.

(* ----------------------------- *)
(*   Typed Reduction *)
(* ----------------------------- *)
Inductive typedred : trm -> typ -> trm -> Prop :=
| tred_int : forall (n : nat),
    typedred (trm_nat n) typ_int (trm_nat n)
| tred_top : forall (A : typ) (e : trm),
    term e -> toplike A -> ordinary A -> typedred e A trm_top
| tred_arrow_anno : forall (A B C D : typ) (e : trm), (* A -> B <: C -> D *)
    term (trm_abs e) -> not (toplike D) -> sub C A -> sub B D ->
    typedred (trm_anno (trm_abs e) (typ_arrow A B))
             (typ_arrow C D)
             (trm_anno (trm_abs e) (typ_arrow A D))
| tred_merge_l : forall (e1 e1' e2 : trm) (A : typ),
    typedred e1 A e1' -> ordinary A -> typedred (trm_merge e1 e2) A e1'
| tred_merge_r : forall (e1 e2 e2' : trm) (A : typ),
    typedred e2 A e2' -> ordinary A -> typedred (trm_merge e1 e2) A e2'
| tred_and : forall (e1 e2 e3 : trm) (A B: typ),
    typedred e1 A e2 -> typedred e1 B e3 -> typedred e1 (typ_and A B) (trm_merge e2 e3).


(* auxiliary lemma *)
Lemma tred_ord_toplike_normal : forall (e e' : trm) (A : typ),
    ordinary A -> toplike A -> typedred e A e' -> e' = trm_top.
Proof.
  intros e e' A H_ord H_top H_tred.
  dependent induction H_tred; subst; eauto.
  - inversion H_top.
  - destruct H0. inversion H_top; subst.
    assumption.
  - inversion H_ord.
Qed.

Lemma tred_toplike :
  forall (A : typ),
    toplike A -> forall e1 e2 e1' e2' : trm, typedred e1 A e1' -> typedred e2 A e2' -> e1' = e2'.
Proof.
  intros A Htop.
  dependent induction Htop; intros e1 e2 e1' e2' H_tred1 H_tred2.
  - apply tred_ord_toplike_normal with (A:=typ_top) in H_tred1; auto; subst.
    apply tred_ord_toplike_normal with (A:=typ_top) in H_tred2; auto; subst.
  - inversion H_tred1; subst; eauto.
    + inversion H1.
    + inversion H_tred2; subst; eauto; inversion H0. (* ordinary (typ_and A B) is wrong*)
    + inversion H0.
    + inversion H_tred2; subst; eauto; try (inversion H0); try (inversion H1).
      assert (Heq1: e3 = e5).
      pose proof (IHHtop1 e1 e2 e3 e5) as IHHtop1'.
      apply IHHtop1'. assumption. assumption.
      assert (Heq2: e4 = e6).
      pose proof (IHHtop2 e1 e2 e4 e6) as IHHtop2'.
      apply IHHtop2'. assumption. assumption.
      rewrite Heq1. rewrite Heq2. reflexivity.
  - assert (HAB: toplike (typ_arrow A B)).
    constructor. assumption.
    apply tred_ord_toplike_normal with (A:=(typ_arrow A B)) in H_tred2.
    apply tred_ord_toplike_normal with (A:=(typ_arrow A B)) in H_tred1.
    rewrite H_tred1. rewrite H_tred2. reflexivity.
    constructor. assumption. constructor. assumption.
Qed.

Lemma toplike_sub_top : forall (A : typ),
    toplike A <-> sub typ_top A.
Proof.
  intro A. split.
  - intro H. induction H.
    + constructor.
    + constructor. assumption. assumption.
    + constructor. assumption.
  - intro H. induction A; eauto.
    + inversion H; subst; eauto.
    + inversion H; subst. constructor.
      apply IHA2. assumption.
    + constructor; inversion H; subst.
      apply IHA1. assumption.
      apply IHA2. assumption.
Qed.

Lemma tred_to_sub: forall (e e' : trm) (A B : typ),
    value e -> typedred e A e' -> typing nil nil infer_mode e B -> sub B A.
Proof.
  intros.
  induction H0; eauto.
  - inversion H1. constructor.
  - apply toplike_sub_top in H2.
    pose proof (sub_transitivity typ_top B A) as sub_trans'.
    assert (H_sub1: sub B typ_top).
    constructor. apply sub_trans' in H_sub1. assumption. assumption.
  - inversion H.
  - inversion H; subst; clear H.
    apply IHtypedred in H5. assumption.
Admitted.

Lemma tred_transitivity : forall (e1 e2 e3: trm) (A B : typ),
    value e1 -> typedred e1 A e2 -> typedred e2 B e3 -> typedred e1 B e3.
Proof.
  intros e1 e2 e3 A B Hval Hred1 Hred2.
  dependent induction Hred1; eauto.
  - dependent induction Hred2; eauto.
    + constructor. assumption. assumption. assumption.
    + assert (Htop : trm_top = trm_top).
      reflexivity. constructor.
      * apply IHHred2_1 in Htop. assumption.
      * apply IHHred2_2 in Htop. assumption.
  - dependent induction Hred2; eauto.
    + constructor. constructor. assumption. assumption.
    + constructor. assumption. assumption. assumption.
      pose proof (sub_transitivity D B0 D0) as Hsub.
      apply Hsub in H2. assumption. assumption.
    + constructor.
      * pose proof (IHHred2_1 D) as IHHred2_1'.
        apply IHHred2_1'. assumption. assumption. assumption. assumption. assumption.
        reflexivity.
      * pose proof (IHHred2_2 D) as IHHred2_2'.
        apply IHHred2_2'. assumption. assumption. assumption. assumption. assumption.
        reflexivity.
  - inversion Hval; subst; clear Hval. constructor. apply IHHred1. assumption. assumption.
    dependent induction Hred2; eauto.
Admitted.

Inductive step : trm -> trm -> Prop :=
| step_anno : forall (e e' : trm) (A : typ),
    step e e' -> step (trm_anno e A) (trm_anno e' A)
| step_app_l : forall (e1 e2 e1' : trm),
    term e2 -> step e1 e1' -> step (trm_app e1 e2) (trm_app e1' e2)
| step_app_r : forall (e1 e2 e2' : trm),
    value e1 -> step e2 e2' -> step (trm_app e1 e2) (trm_app e1 e2')
| step_merge_l : forall (e1 e2 e1' : trm),
    term e2 -> step e1 e1' -> step (trm_merge e1 e2) (trm_app e1' e2)
| step_merge_r : forall (e1 e2 e2' : trm),
    value e2 -> step e2 e2' -> step (trm_app e1 e2) (trm_app e1 e2')
| step_beta : forall (e1 e2 e2' : trm) (A B : typ),
    term (trm_abs e1) -> value e2 -> typedred e2 A e2' ->
    step (trm_app (trm_abs e1) e2) (trm_anno (open e1 e2') B)
| step_anno_typed : forall (e e' : trm) (A : typ),
    typedred e A e' -> step (trm_anno e A) e'.
