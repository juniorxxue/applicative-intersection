Require Import Metalib.Metatheory.
Require Import Metalib.LibTactics.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Strings.String.
Require Import Psatz.

Require Import Language.
Require Import Tactical.
Require Import Subtyping.Subtyping.
Require Import Subtyping.Splitable.
Require Import Subtyping.Toplike.

Require Import Value.
Require Import Disjoint.
Require Import PrincipalTyping.
Require Import Consistent.
Require Import Typing.

(** * Definition *)

(*

A <: Int  (required for toplike)
---------------------- Cast-Int-Anno
n : A -->Int n : Int


Ordinary A
TopLike A
------------------- Cast-Top
v -->A (1 : A)


not (TopLike D)
E <: C -> D
Ordinary D
---------------------------------------------------------- Cast-Arrow-Anno
(\x. e : A -> B) : E  -->(C -> D)  (\x. e : A -> D) : C -> D


v1 -->A v1'
Ordinary A
---------------------------- Cast-Merge-L
v1,,v2 -->A v1'


v2 -->A v2'
Ordinary A
---------------------------- Cast-Merge-R
v1,,v2 -->A v2'


B <| A |> C
v -->B v1
v -->C v2
--------------------------------- Cast-And
v --> A v1,,v2

*)

Inductive casting : term -> type -> term -> Prop :=
| Ct_Lit : forall (n : nat) (A : type),
    sub A Int ->
    casting (Ann (Lit n) A) Int (Ann (Lit n) Int)
| Ct_Top : forall (A : type) (v : term),
    lc v ->
    toplike A ->
    ordinary A ->
    casting v A (Ann (Lit 1) A)
| Ct_Lam : forall (A B C D E : type) (e : term),
    lc (Lam A e B) ->
    not (toplike D) ->
    sub E (Arr C D) ->
    ordinary D ->
    casting (Ann (Lam A e B) E)
            (Arr C D)
            (Ann (Lam A e D) (Arr C D))
| Ct_Mrg_L : forall (v1 v2 v: term) (A : type),
    casting v1 A v ->
    ordinary A ->
    casting (Mrg v1 v2) A v
| Ct_Mrg_R : forall (v1 v2 v : term) (A : type),
    casting v2 A v ->
    ordinary A ->
    casting (Mrg v1 v2) A v
| Ct_And : forall (v1 v2 v : term) (A A1 A2 : type),
    splitable A A1 A2 ->
    casting v A1 v1 ->
    casting v A2 v2 ->
    casting v A (Mrg v1 v2).

Hint Constructors casting : core.

Notation "e ~~> [ A ] e'" := (casting e A e') (at level 68).

(** * Determinism *)

(** Under toplike and ordinary type A, value v is always casted to a constant *)

Lemma casting_ordinary_toplike :
  forall v v' A,
    ordinary A ->
    toplike A ->
    casting v A v' ->
    v' = (Ann (Lit 1) A).
Proof.
  introv Ord Tl Ct.
  induction Ct; eauto.
Qed.

(** Value v can only be casted by its super type *)

Lemma casting_super :
  forall A B v v',
    value v ->
    typing nil v B ->
    casting v A v' ->
    sub B A.
Proof.
  introv Val Typ Ct. gen B.
  induction Ct; eauto; intros.
  - Case "Lit".
    repeat (dependent destruction Typ).
    assumption.
  - Case "Lam".
    dependent destruction Typ.
    assumption.
  - Case "Merge L".
    dependent destruction Val.
    dependent destruction Typ;
      eapply sub_and_l; eauto.
  - Case "Merge R".
    dependent destruction Val.
    dependent destruction Typ;
      eapply sub_and_r; eauto.
Qed.

(** We first prove the general version of determinism (generlized on consistent) *)

Lemma casting_determinism_gen :
  forall v1 v2 v1' v2' A B C,
    value v1 -> value v2 ->
    typing nil v1 A -> typing nil v2 B ->
    consistent v1 v2 ->
    casting v1 C v1' ->
    casting v2 C v2' ->
    v1' = v2'.
Proof.
  introv Val1 Val2 Typ1 Typ2 Con Ct1 Ct2.
  gen A B v1 v2 v1' v2'.
  ind_type_size (size_type C).
  destruct (splitable_or_ordinary C).
  - Case "Ord".
    gen A B. induction Con; eauto; intros.
    + SCase "Arr".
      dependent destruction Val1. dependent destruction Val2.
      dependent destruction Ct1; dependent destruction Ct2; eauto.
    + SCase "Anno".
      dependent destruction Val1. dependent destruction Val2.
      destruct H; dependent destruction Ct1; dependent destruction Ct2; eauto.
    + SCase "Disjoint".
      pose proof (typing_to_ptype _ _ (value_is_uvalue _ Val1) Typ1).
      pose proof (typing_to_ptype _ _ (value_is_uvalue _ Val2) Typ2).
      repeat (subst_ptype).
      pose proof (disjoint_complete _ _ H2).
      pose proof (casting_super _ _ _ _ Val1 Typ1 Ct1).
      pose proof (casting_super _ _ _ _ Val2 Typ2 Ct2).
      assert (Tl: toplike C) by eauto.
      pose proof (casting_ordinary_toplike _ _ _ H Tl Ct1).
      pose proof (casting_ordinary_toplike _ _ _ H Tl Ct2).
      now subst.
    + SCase "Merge L".
      dependent destruction Ct1; eauto.
      * symmetry. eapply casting_ordinary_toplike; eauto.
      * dependent destruction Typ1; eauto.
      * dependent destruction Typ1; eauto.
    + SCase "Merge R".
      dependent destruction Ct2; eauto.
      * eapply casting_ordinary_toplike; eauto.
      * dependent destruction Typ2; eauto.
      * dependent destruction Typ2; eauto.
  - Case "Spl".
    destruct H as [C1 H]. destruct H as [C2 H].
    dependent destruction Ct1; dependent destruction Ct2; eauto.
    repeat (subst_splitable).
    pose proof (splitable_decrease_size _ _ _ H1) as SplSize. destruct SplSize.
    assert (size_type C1 < i) by lia. assert (size_type C2 < i) by lia.
    f_equal; eauto 3.
Qed.

(** Then prove its determinism by directly applying [casting_determinism_gen] *)

Lemma casting_determinism :
  forall v v1 v2 A B,
    value v ->
    typing nil v A ->
    casting v B v1 ->
    casting v B v2 ->
    v1 = v2.
Proof.
  introv Val Typ Ct1 Ct2.
  eapply casting_determinism_gen; eauto.
Qed.

(** * Casting & Value *)

(** Value property is preserved by casting *)

Lemma casting_value :
  forall v v' A,
    value v ->
    casting v A v' ->
    value v'.
Proof.
  introv Val Ct.
  induction Ct; eauto.
Qed.

Hint Resolve casting_value : core.

(** * Transitivity *)

Lemma casting_transitivity :
  forall v v1 v2 A B,
    value v ->
    casting v A v1 ->
    casting v1 B v2 ->
    casting v B v2.
Proof.
  introv Val Ct1 Ct2. gen B v2.
  induction Ct1; intros; try solve [dependent induction Ct2; eauto].
  - dependent induction Ct2; eauto.
    eapply Ct_Lam; eauto. eapply sub_transitivity; eauto.
  - dependent destruction Val.
    dependent induction Ct2; eauto.
  - dependent destruction Val.
    dependent induction Ct2; eauto.
Qed.

(** * Progress *)

Lemma casting_progress :
  forall v A B,
    value v ->
    typing nil v A ->
    sub A B ->
    exists v', casting v B v'.
Proof.
  introv Val Typ Sub. gen v.
  induction Sub; intros.
  - Case "Sub-Int".
    dependent destruction Typ; eauto.
    dependent destruction Val. dependent destruction H.
    dependent destruction Typ; eauto.
    dependent destruction Typ; eauto.
  - Case "Sub-Top".
    dependent destruction Typ; eauto.
  - Case "Sub-Arr".
    dependent destruction Typ; eauto.
    destruct (toplike_decidable D).
    + SCase "Toplike".
      eexists; eauto.
    + SCase "Not Toplike".
      dependent destruction Val. dependent destruction H0; eauto.
      dependent destruction Typ. dependent destruction H1.
      assert (toplike B) by (eapply sub_inv_int_arrow; eauto).
      assert (toplike D) by (eapply sub_toplike; eauto).
      contradiction.
  - Case "Sub-And".
    pose proof (IHSub1 _ Val Typ). pose proof (IHSub2 _ Val Typ).
    destruct_conjs; eauto.
  - Case "Sub-And-L".
    dependent destruction Typ; eauto.
    + dependent destruction Val.
      pose proof (IHSub _ Val1 Typ1). destruct_conjs; eauto.
    + dependent destruction Val.
      pose proof (IHSub _ Val1 Typ1). destruct_conjs; eauto.
  - Case "Sub-And-R".
    dependent destruction Typ; eauto.
    + dependent destruction Val.
      pose proof (IHSub _ Val2 Typ2). destruct_conjs; eauto.
    + dependent destruction Val.
      pose proof (IHSub _ Val2 Typ2). destruct_conjs; eauto.
Qed.

(** * Casting & Consistent *)

(** ** Specification *)

Definition consistent_spec v1 v2 :=
  forall A v1' v2',
    ordinary A ->
    casting v1 A v1' ->
    casting v2 A v2' ->
    v1' = v2'.

(** ** Soundness *)

Lemma consistent_sound :
  forall v1 v2 A B,
    value v1 -> value v2 ->
    typing nil v1 A ->
    typing nil v2 B ->
    consistent v1 v2 ->
    consistent_spec v1 v2.
Proof.
  introv Val1 Val2 Typ1 Typ2 Con.
  unfold consistent_spec. intros C v1' v2' Ord Ct1 Ct2.
  now pose proof (casting_determinism_gen _ _ _ _ _ _ _ Val1 Val2 Typ1 Typ2 Con Ct1 Ct2).
Qed.

(** ** Completeness *)

(** We need two "inversion lemmas" on specification *)

Lemma consistent_spec_inv_merge_l :
  forall v v1 v2,
    consistent_spec (Mrg v1 v2) v ->
    consistent_spec v1 v /\ consistent_spec v2 v.
Proof.
  introv Cons. split; unfold consistent_spec in *; intros; eauto.
Qed.

Lemma consistent_spec_inv_merge_r :
  forall v v1 v2,
    consistent_spec v (Mrg v1 v2) ->
    consistent_spec v v1 /\ consistent_spec v v2.
Proof.
  introv Cons. split; unfold consistent_spec in *; intros; eauto.
Qed.

Ltac ind_term_size s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : term |- _ ] => (gen h) end;
  induction i as [|i IH]; [
      intros; match goal with | [ H : _ < 0 |- _ ] => (dependent destruction H; eauto) end
    | intros ].

Lemma consistent_complete :
  forall v1 v2 A B,
    value v1 -> value v2 ->
    typing nil v1 A ->
    typing nil v2 B ->
    consistent_spec v1 v2 ->
    consistent v1 v2.
Proof.
  introv Val1 Val2 Typ1 Typ2 Cons. gen A B.
  ind_term_size (size_term v1 + size_term v2).
  dependent destruction Val1; dependent destruction Val2; simpl in SizeInd.
  - Case "Anno~Anno".
    dependent destruction Typ1. dependent destruction Typ2.
    destruct (toplike_decidable A); destruct (toplike_decidable A0).
    + eapply Con_Dj; eauto; eapply disjoint_toplike; eauto.
    + eapply Con_Dj; eauto; eapply disjoint_toplike; eauto.
    + eapply consistent_symmetry; eauto. eapply Con_Dj; eauto; eapply disjoint_toplike; eauto.
    + destruct H; destruct H1.
      * SCase "Lit Lit".
        dependent destruction Typ1. dependent destruction Typ2.
        (* derive equality from Cons *)
        unfold consistent_spec in Cons.
        repeat match goal with
               | [H: sub Int ?A |- _] => (dependent destruction H; eauto)
               end.
        assert (Ct1: casting (Ann (Lit n) Int) Int (Ann (Lit n) Int)) by eauto.
        assert (Ct2: casting (Ann (Lit n0) Int) Int (Ann (Lit n0) Int)) by eauto.
        pose proof (Cons _ _ _ H0 Ct1 Ct2) as Eq.
        dependent destruction Eq. eauto.
      * SCase "Lit Lam".
        dependent destruction Typ1. dependent destruction Typ2.
        repeat match goal with
               | [H: sub Int ?A |- _] => (dependent destruction H; eauto)
               | [H: sub (Arr _ _) _ |- _] => (dependent destruction H; eauto)
               end.
      * SCase "Lam Lit". 
        dependent destruction Typ1. dependent destruction Typ2.
        repeat match goal with
               | [H: sub Int ?A |- _] => (dependent destruction H; eauto)
               | [H: sub (Arr _ _) _ |- _] => (dependent destruction H; eauto)
               end.
      * SCase "Lam Lam".
        inversion Typ1; subst. inversion Typ2; subst.
        repeat match goal with
               | [H: sub (Arr _ _) _ |- _] => (dependent destruction H; eauto)
               end.
        destruct (disjoint_spec_decidable D0 D); eauto.
        unfold consistent_spec in Cons.
        destruct_conjs.
        match goal with
        | [H1: sub ?D1 ?DD, H2: sub ?D2 ?DD
           |- consistent (Ann (Lam ?A1 ?e1 ?B1) (Arr ?C1 ?D1)) (Ann (Lam ?A2 ?e2 ?B2) (Arr ?C2 ?D2))] =>
            (pose proof (casting_progress (Ann (Lam A1 e1 B1) (Arr C1 D1)) (Arr C1 D1) (Arr (And C1 C2) DD)) as Ct1;
             pose proof (casting_progress (Ann (Lam A2 e2 B2) (Arr C2 D2)) (Arr C2 D2) (Arr (And C1 C2) DD)) as Ct2;
             assert (Ord: ordinary (Arr (And C1 C2) DD)) by eauto)
        end.
        destruct Ct1 as [x1 Ct1]; eauto. destruct Ct2 as [x2 Ct2]; eauto.
        pose proof (Cons _ _ _ Ord Ct1 Ct2). subst.
        dependent destruction Ct1; dependent destruction Ct2; eauto.
  - eapply consistent_spec_inv_merge_r in Cons. destruct_conjs.
    dependent destruction Typ2;
      eapply Con_Mrg_R; eapply IH; eauto; simpl in *; lia.
  - eapply consistent_spec_inv_merge_l in Cons. destruct_conjs.
    dependent destruction Typ1;
      eapply Con_Mrg_L; eapply IH; eauto; simpl in *; lia.
  - eapply consistent_spec_inv_merge_l in Cons. destruct_conjs.
    dependent destruction Typ1;
      eapply Con_Mrg_L; eapply IH; eauto; simpl in *; lia.
Qed.

(** ** Preservation *)

Lemma casting_consistent :
  forall v v1 v2 A A1 A2 B C,
    value v ->
    typing nil v A ->
    typing nil v1 A1 ->
    typing nil v2 A2 ->
    casting v B v1 ->
    casting v C v2 ->
    consistent v1 v2.
Proof.
  introv Val Typ Typ1 Typ2 Ct1 Ct2.
  eapply consistent_complete; eauto.
  unfold consistent_spec. intros E v1' v2' Ord Ct1' Ct2'.
  pose proof (casting_transitivity v v1 v1' B E Val Ct1 Ct1').
  pose proof (casting_transitivity v v2 v2' C E Val Ct2 Ct2').
  eapply casting_determinism_gen; eauto.
Qed.

(** * Preservation *)

Lemma casting_preservation :
  forall v v' A B,
    value v ->
    typing nil v B ->
    casting v A v' ->
    exists C, typing nil v' C /\ isosub C A.
Proof.
  introv Val Typ Ct. gen B.
  induction Ct; intros; try solve [eexists; eauto].
  - Case "Lam".
    exists (Arr C D). split; eauto 3.
    repeat (dependent destruction Typ).
    dependent destruction Val.
    assert (Sub1: sub (Arr A B) (Arr C D)) by (eapply sub_transitivity; eauto).
    dependent destruction Sub1; eauto 3.
    assert (Sub2: sub (Arr A D) (Arr C D)) by eauto.
    eapply Ty_Ann; eauto. eapply Ty_Lam; eauto. eapply sub_transitivity; eauto.
  - Case "Merge L".
    dependent destruction Val. dependent destruction Typ; eauto.
  - Case "Merge R".
    dependent destruction Val. dependent destruction Typ; eauto.
  - pose proof (IHCt1 Val B Typ) as IH1. destruct IH1 as [x1 IH1].
    pose proof (IHCt2 Val B Typ) as IH2. destruct IH2 as [x2 IH2].
    destruct_conjs.
    exists (And x1 x2). split; eauto. eapply Ty_Mrg_Uv; eauto.
    eapply casting_consistent; eauto.
Qed.
