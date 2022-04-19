Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Strings.String.
Require Import Program.Tactics.
Require Import Lia.
Require Import Language Tactical.
Require Import Subtyping.Toplike.
Require Import Subtyping.Splitable.
Require Import Subtyping.Subtyping.
Require Import Appsub.

Set Printing Parentheses.

(** * Specification *)

(* this specification doesn't exclude cases when A is not a arrow-like type *)

Definition disjoint_spec_forall A B :=
  forall C, ~ (ordinary C -> (auxas (Some C) A /\ auxas (Some C) B)).

(* if A and B are disjoint, A and B should be arrow-like types,
   then for any ordinary types, if one branch can accpet it,  another branch should reject it *)

Definition disjoint_spec_exist A B :=
  ~ (exists C, ordinary C -> auxas (Some C) A /\ auxas (Some C) B).

Definition disjoint_spec := disjoint_spec_forall.

Lemma disjoint_spec_equal :
  forall A B,
    disjoint_spec_forall A B <-> disjoint_spec_exist A B.
Proof.
  introv.
  split.
  - intros. unfold disjoint_spec_exist. unfold disjoint_spec_forall in H.
    intros Contra. destruct Contra. pose proof (H x). contradiction.
  - intros. unfold disjoint_spec_exist in H. unfold disjoint_spec_forall.
    introv Contra. apply H. exists C. auto.
Qed.

Definition cost_spec A B :=
  exists C, ordinary C -> sub C A /\ sub C B.

(**
Definition cost_spec A B :=
  forall C, ordinary C -> sub C A -> sub C B.
**)

(** * Definition *)

Inductive cost : type -> type -> Prop :=
| Cst_Top :
  cost Top Top
| Cst_Ord_L : forall A B,
    ordinary A ->
    toplike B ->
    cost A B
| Cst_Ord_R : forall A B,
    ordinary B ->
    toplike A ->
    cost A B
| Cst_Int :
  cost Int Int
| Cst_Arr : forall A1 A2 B1 B2,
    cost B1 B2 ->
    cost (Arr A1 B1) (Arr A2 B2)
| Cst_And_L : forall A A1 A2 B,
    splitable A A1 A2 ->
    cost A1 B ->
    cost A2 B ->
    cost A B
| Cst_And_R : forall A B B1 B2,
    splitable B B1 B2 ->
    cost A B1 ->
    cost A B2 ->
    cost A B.

Hint Constructors cost : core.

Inductive overloadable : type -> type -> Prop :=
| Ol_Arr : forall A1 A2 B1 B2,
    ~ cost A1 A2 ->
    overloadable (Arr A1 B1) (Arr A2 B2)
| Ol_And_L : forall A1 A2 B,
    overloadable A1 B ->
    overloadable A2 B ->
    overloadable (And A1 A2) B
| Ol_And_R : forall A B1 B2,
    overloadable A B1 ->
    overloadable A B2 ->
    overloadable A (And B1 B2).

Hint Constructors overloadable : core.

Definition disjoint := overloadable.

(** * Properties *)

(** induction on size *)

Ltac ind_type_size s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with
         | [ h : type |- _ ] => (gen h)
         end;
  induction i as [|i IH]; [
      intros; match goal with
              | [ H : _ < 0 |- _ ] => (dependent destruction H)
              end
    | intros ].

(** ** Completeness and Soundness *)

Lemma cost_complete :
  forall A B, cost A B -> cost_spec A B.
Proof.
  introv Cst. unfold cost_spec.
  dependent induction Cst; eauto.
  Unshelve. all: auto.
Qed.

Lemma cost_sound_alternative :
  forall A, ordinary A -> forall B, sub A B -> forall C, sub A C -> cost B C.
Proof.
  introv Ord Sub1.
  dependent induction Sub1; introv Sub2.
  - dependent induction Sub2; eauto.
  - dependent induction Sub2; eauto.
  - dependent induction Sub2; eauto.
    dependent destruction Ord.
    eapply Cst_Arr; eauto.
  - dependent destruction H; eauto.
  - inversion Ord.
  - inversion Ord.
Qed.

Lemma disjoint_sound :
  forall A B, disjoint_spec A B -> disjoint A B.
Proof.
  introv Dj. unfold disjoint_spec in Dj. unfold disjoint_spec_forall in Dj.
  gen B. induction A; intros.
  - 
Admitted.

Lemma disjoint_complete :
  forall A B, disjoint A B -> disjoint_spec A B.
Proof.
  introv Dj. unfold disjoint_spec. introv Contra. gen C.
  dependent induction Dj; intros.
  -   
Admitted.

(** ** Symmetry *)

Lemma cost_symmetry :
  forall A B,
    cost A B -> cost B A.
Proof.
  introv Cst. induction Cst; eauto.
Qed.

Lemma disjoint_symmetry:
  forall A B,
    disjoint A B -> disjoint B A.
Proof.
  introv H.
  induction H; eauto.
  - eapply Ol_Arr. intro Cst. eapply cost_symmetry in Cst. contradiction.
  - eapply Ol_And_R; eauto.
  - eapply Ol_And_L; eauto.
Qed.

(** ** Soundness *)

Lemma disjoint_soundness :
  forall A B,
    disjoint_spec A B -> disjoint A B.
Proof.
  introv. unfold disjoint_spec.
  intros Spec.
  gen B. induction A; intros.
  - induction B; eauto.
    + 
Admitted.

(** ** Decidablility *)

Lemma disjoint_spec_decidable :
  forall A B,
    disjoint A B \/ (exists C, ~ toplike C /\ ordinary C /\ sub A C /\ sub B C).
Proof.
  introv. gen B. induction A; eauto; intros.
  - Case "Int".
Abort.

(** * Disjoint & Toplike *)

Lemma disjoint_spec_toplike :
  forall A B,
    toplike A -> disjoint_spec A B.
Proof.
  introv Tl.
  unfold disjoint_spec.
Abort.


(** * Disjoint & Splitable *)

Lemma disjoint_splitable :
  forall A A1 A2 B,
    splitable A A1 A2 ->
    disjoint A1 B -> disjoint A2 B ->
    disjoint A B.
Proof.
  introv Spl Dj1 Dj2. gen B.
  dependent induction Spl; intros.
  - eapply Ol_And_L; eauto.
  - dependent induction Dj1.
    + eapply Ol_Arr; eauto.
    + dependent destruction Dj2.
      eapply Ol_And_R.
      * eapply IHDj1_1; eauto.
      * eapply IHDj1_2; eauto.
Qed.

Lemma disjoint_splitable_l :
  forall A A1 A2 B,
    splitable A A1 A2 ->
    disjoint A B ->
    disjoint A1 B /\ disjoint A2 B.
Proof.
  introv Spl Dj. gen A1 A2.
  dependent induction Dj; intros; eauto.
  - dependent destruction Spl.
    split; eauto.
    + eapply Ol_Arr; eauto.
    + eapply Ol_Arr; eauto.
  - dependent destruction Spl.
    split; eauto.
  - pose proof (IHDj1 _ _ Spl).
    pose proof (IHDj2 _ _ Spl).
    destruct_conjs.
    split.
    + eapply Ol_And_R; eauto.
    + eapply Ol_And_R; eauto.
Qed.

Lemma disjoint_splitable_r :
  forall A A1 A2 B,
    splitable A A1 A2 ->
    disjoint B A ->
    disjoint B A1 /\ disjoint B A2.
Proof.
  introv Spl Dj. gen A1 A2.
  dependent induction Dj; intros; eauto.
  - dependent destruction Spl.
    split; eapply Ol_Arr; eauto.
  - pose proof (IHDj1 _ _ Spl).
    pose proof (IHDj2 _ _ Spl).
    destruct_conjs.
    split.
    + eapply Ol_And_L; eauto.
    + eapply Ol_And_L; eauto.
  - dependent destruction Spl.
    split; eauto.
Qed.

(** * Disjoint & Subtyping *)

Lemma disjoint_sub :
  forall A B C,
    disjoint A B -> sub A C -> disjoint C B.
Proof.
  introv Dj Sub. gen C.
  dependent induction Dj; intros.
  - dependent induction Sub.
Abort.


(** * Disjoint & Isomorphic Subtyping *)

Lemma disjoint_isosub :
  forall A B C,
    disjoint A B -> isosub A C -> disjoint C B.
Proof.
  introv Dj Isub.
  dependent induction Isub; eauto.
  dependent induction Dj; eauto.
  - pose proof (IHIsub1 Dj1).
    pose proof (IHIsub2 Dj2).
    eapply disjoint_splitable; eauto.
  - eapply disjoint_splitable_l in Dj1; eauto.
    eapply disjoint_splitable_l in Dj2; eauto.
    destruct_conjs.
    eapply disjoint_splitable; eauto.
    eapply IHIsub1. eapply Ol_And_R; eauto.
    eapply IHIsub2. eapply Ol_And_R; eauto.
Qed.

Lemma disjoint_iso_l1 :
  forall A C1 C2,
    disjoint C1 C2 ->
    isosub A C1 ->
    disjoint A C2.
Proof.
  introv Hdisj Hiso.
  gen C2. dependent induction Hiso; intros; eauto.
  eapply disjoint_splitable_l in Hdisj; eauto.
  destruct Hdisj; eauto.
  eapply Ol_And_L; eauto.
  - eapply IHHiso1; eauto.
  - eapply IHHiso2; eauto.
Qed.

Lemma disjoint_iso_l2 :
  forall B C1 C2,
    disjoint C1 C2 ->
    isosub B C2 ->
    disjoint C1 B.
Proof.
  introv Hdisj Hiso.
  gen C1. dependent induction Hiso; intros; eauto.
  eapply disjoint_splitable_r in Hdisj; eauto.
  destruct Hdisj; eauto.
  eapply Ol_And_R.
  - eapply IHHiso1; eauto.
  - eapply IHHiso2; eauto.
Qed.

Lemma disjoint_iso_l :
  forall A B C1 C2,
    disjoint C1 C2 ->
    isosub A C1 ->
    isosub B C2 ->
    disjoint A B.
Proof.
  introv Hdisj Hiso1 Hiso2.
  assert (disjoint A C2).
  - eapply disjoint_iso_l1; eauto.
  - eapply disjoint_iso_l2; eauto.
Qed.

Lemma disjoint_iso_r :
  forall A B C1 C2,
    disjoint A B ->
    isosub A C1 ->
    isosub B C2 ->
    disjoint C1 C2.
Proof.
  introv Hdisj Hiso1 Hiso2.
  assert (disjoint C1 B).
  eapply disjoint_isosub; eauto.
  eapply disjoint_symmetry.
  eapply disjoint_symmetry in H.
  eapply disjoint_isosub; eauto.
Qed.

(** * Disjoint & Applicative Subtyping *)

Lemma disjoint_appsub :
  forall A B C D1 D2,
    disjoint A B ->
    appsub (Some C) A D1 ->
    appsub (Some C) B D2 ->
    disjoint D1 D2.
Proof.
  introv Dj As1 As2. gen C D1 D2.
  eapply disjoint_complete in Dj.
  unfold disjoint_spec in Dj.
  unfold disjoint_spec_forall in Dj. intros.
  pose proof (Dj C).
  destruct H. intros.
  split; eauto.
Qed.
