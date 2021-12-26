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

(**

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
    casting v B v2 ->
    casting v B v2.
Proof.
  induction 2; eauto.
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
     
      
    
    
