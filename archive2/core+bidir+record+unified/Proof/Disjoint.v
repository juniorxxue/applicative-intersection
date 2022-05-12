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

Definition disjoint_spec A B :=
  forall (C : type), sub A C -> sub B C -> toplike C.

(** * Definition *)

Inductive disjoint : type -> type -> Prop :=
| Dj_Top_L : forall A,
    disjoint Top A
| Dj_Top_R : forall A,
    disjoint A Top
| Dj_And_L : forall A1 A2 B,
    disjoint A1 B -> disjoint A2 B ->
    disjoint (And A1 A2) B
| Dj_And_R : forall A B1 B2,
    disjoint A B1 -> disjoint A B2 ->
    disjoint A (And B1 B2)
| Dj_Int_Arr : forall A1 A2,
    disjoint Int (Arr A1 A2)
| Dj_Arr_Int : forall A1 A2,
    disjoint (Arr A1 A2) Int
| Dj_Arr_Arr : forall A1 A2 B1 B2,
    disjoint B1 B2 ->
    disjoint (Arr A1 B1) (Arr A2 B2)
| Dj_Rcd_Eq : forall l A B,
    disjoint A B ->
    disjoint (Rcd l A) (Rcd l B)
| Dj_Rcd_Neq : forall l1 l2 A B,
    l1 <> l2 ->
    disjoint (Rcd l1 A) (Rcd l2 B)
| Dj_Int_Rcd : forall l A,
    disjoint Int (Rcd l A)
| Dj_Rcd_Int : forall l A,
    disjoint (Rcd l A) Int
| Dj_Arr_Rcd : forall A B C l,
    disjoint (Arr A B) (Rcd l C)
| Dj_Rcd_Arr : forall A B C l,
    disjoint (Rcd l A) (Arr B C).

Hint Constructors disjoint : core.

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

(** ** Completeness *)

Theorem disjoint_complete :
  forall A B, disjoint A B -> disjoint_spec A B.
Proof.
  intros A B Dj C Sub1 Sub2.
  ind_type_size (size_type A + size_type B + size_type C).
  destruct (splitable_or_ordinary C).
  - Case "Ord".
    dependent destruction Dj.
    + SCase "Top_L".
      eapply sub_toplike; eauto.
    + SCase "Top_R".
      eapply sub_toplike; eauto.
    + SCase "And_L".
      dependent destruction Sub1.
      * eapply sub_toplike; eauto.
      * eapply sub_toplike; eauto.
      * simpl in SizeInd.
        assert ((size_type A1 + size_type B + size_type C) < i) by lia.
        now pose proof (IH _ _ Dj1 _ Sub1 Sub2 H1).
      * simpl in SizeInd.
        assert ((size_type A2 + size_type B + size_type C) < i) by lia.
        now pose proof (IH _ _ Dj2 _ Sub1 Sub2 H1).
    + SCase "And_R".
      dependent destruction Sub2.
      * eapply sub_toplike; eauto.
      * eapply sub_toplike; eauto.
      * simpl in SizeInd.
        assert ((size_type A + size_type B1 + size_type C) < i) by lia.
        now pose proof (IH _ _ Dj1 _ Sub1 Sub2 H1).
      * simpl in SizeInd.
        assert ((size_type A + size_type B2 + size_type C) < i) by lia.
        now pose proof (IH _ _ Dj2 _ Sub1 Sub2 H1).
    + SCase "Int_Arr".
      dependent destruction Sub1; dependent destruction Sub2; eauto 1.
    + SCase "Arr_Int".
      dependent destruction Sub1; dependent destruction Sub2; eauto 1.
    + SCase "Arr_Arr".
      dependent destruction Sub1; dependent destruction Sub2; eauto 1.
      constructor. eapply IH; eauto.
      simpl in SizeInd. lia.
    + SCase "Rcd Eq".
      dependent destruction Sub1; dependent destruction Sub2; eauto 1.
      constructor. eapply IH; eauto.
      simpl in SizeInd. lia.
    + SCase "Rcd Neq".
      dependent destruction Sub1; dependent destruction Sub2; eauto 1.
      destruct H; eauto.      
    + SCase "Int Rcd".
      dependent destruction Sub1; dependent destruction Sub2; eauto 1.
    + SCase "Rcd Int".
      dependent destruction Sub1; dependent destruction Sub2; eauto 1.
    + SCase "Arr Rcd".
      dependent destruction Sub1; dependent destruction Sub2; eauto 1.
    + SCase "Rcd Arr".
      dependent destruction Sub1; dependent destruction Sub2; eauto 1.
  - Case "Split".
    destruct_conjs.
    dependent destruction Sub1; dependent destruction Sub2; eauto 1.
    simpl in SizeInd. subst_splitable. subst_splitable.
    pose proof (splitable_decrease_size _ _ _ H3). destruct_conjs.
    eapply splitable_toplike1; eauto 3.
    + eapply IH; eauto 3. lia.
    + eapply IH; eauto 3. lia.
Qed.

(** ** Symmetry *)

Lemma disjoint_symmetry:
  forall A B,
    disjoint A B -> disjoint B A.
Proof.
  introv H.
  induction H; eauto.
Qed.

(** ** Soundness *)

Lemma disjoint_soundness :
  forall A B,
    disjoint_spec A B -> disjoint A B.
Proof.
  introv. unfold disjoint_spec.
  gen B. induction A; introv H; induction B; eauto;
    try solve [eapply Dj_And_R; eauto | eapply Dj_And_L; eauto].
  - Case "Int Int".
    pose proof (H Int Sub_Int Sub_Int); eauto.
  - Case "Arr Arr".
    eapply Dj_Arr_Arr. eapply IHA2. intros.
    assert (Tl: toplike (Arr (And A1 B1) C)) by (eapply H; eauto).
    now dependent destruction Tl.
  - SCase "Rcd Rcd".
    destruct (l == l0); eauto. subst.
    eapply Dj_Rcd_Eq. eapply IHA. introv Sub1 Sub2.
    assert (Tl: toplike (Rcd l0 C)) by (eapply H; eauto).
    now dependent destruction Tl.
Qed.

(** ** Decidablility *)

Lemma disjoint_spec_decidable :
  forall A B,
    disjoint A B \/ (exists C, ~ toplike C /\ ordinary C /\ sub A C /\ sub B C).
Proof.
  introv. gen B. induction A; eauto; intros.
  - Case "Int".
    induction B; eauto.
    + SCase "Int".
      right. exists Int. split; eauto.
    + SCase "And".
      destruct IHB1; destruct IHB2; eauto;
        try solve [right; destruct_conjs; eexists; eauto].
  - Case "Arrow". clear IHA1.
    induction B; eauto.
    + SCase "Arrow".
      pose proof (IHA2 B2) as IH. destruct IH; eauto.
      destruct_conjs. right. exists (Arr (And A1 B1) H).
      repeat (split; eauto).
    + SCase "And".
      destruct IHB1; destruct IHB2;
        try solve [right; destruct_conjs; eexists; eauto | eauto].
  - Case "And".
    pose proof (IHA1 B) as IH1.
    pose proof (IHA2 B) as IH2.
    destruct IH1; destruct IH2;
      try solve [right; destruct_conjs; eexists; eauto | eauto].
  - Case "Rcd".
    induction B; eauto.
    + SCase "And".
      destruct IHB1; destruct IHB2; eauto.
      * right. destruct H0. exists x. destruct_conjs. repeat (split; eauto).
      * right. destruct H. exists x. destruct_conjs. repeat (split; eauto).
      * destruct H. right. exists x. destruct_conjs. repeat (split; eauto).
    + SCase "Rcd".
      destruct (l == l0); eauto. subst.
      destruct (IHA B); eauto. destruct H.
      right. exists (Rcd l0 x). destruct_conjs; repeat (split; eauto).
Qed.

(** * Disjoint & Toplike *)

Lemma disjoint_spec_toplike :
  forall A B,
    toplike A -> disjoint_spec A B.
Proof.
  introv Tl.
  unfold disjoint_spec.
  introv Sub1 Sub2.
  eapply sub_toplike; eauto.
Qed.

Lemma disjoint_toplike :
  forall A B,
    toplike A -> disjoint A B.
Proof.
  introv Tl.
  assert (disjoint_spec A B) by (eapply disjoint_spec_toplike; eauto).
  now eapply disjoint_soundness in H.
Qed.

(** * Disjoint & Splitable *)

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
  - pose proof (IHDj1 _ _ Spl).
    pose proof (IHDj2 _ _ Spl).
    destruct_conjs. eauto.
  - dependent destruction Spl; eauto.
  - dependent destruction Spl; eauto.
    pose proof (IHDj _ _ Spl).
    destruct H; eauto.
  - dependent destruction Spl; eauto.
    destruct (IHDj _ _ Spl); eauto.
  - dependent destruction Spl; eauto.
  - dependent destruction Spl; eauto.
  - dependent destruction Spl; eauto.
  - dependent destruction Spl; eauto.
Qed.

Lemma disjoint_splitable_r :
  forall A A1 A2 B,
    splitable A A1 A2 ->
    disjoint B A ->
    disjoint B A1 /\ disjoint B A2.
Proof.
Proof.
  introv Spl Dj. gen A1 A2.
  dependent induction Dj; intros; eauto.
  - pose proof (IHDj1 _ _ Spl).
    pose proof (IHDj2 _ _ Spl).
    destruct_conjs. eauto.
  - dependent destruction Spl; eauto.
  - dependent destruction Spl; eauto.
  - dependent destruction Spl; eauto.
    pose proof (IHDj _ _ Spl).
    destruct H; eauto.
  - dependent destruction Spl; eauto.
    destruct (IHDj _ _ Spl); eauto.
  - dependent destruction Spl; eauto.
  - dependent destruction Spl; eauto.
  - dependent destruction Spl; eauto.
  - dependent destruction Spl; eauto.
Qed.  

(** * Disjoint & Subtyping *)

Lemma disjoint_sub :
  forall A B C,
    disjoint A B -> sub A C -> disjoint C B.
Proof.
  introv Dj Sub.
  eapply disjoint_complete in Dj.
  eapply disjoint_soundness.
  unfold disjoint_spec in *. intros.
  eapply Dj; eauto.
  eapply sub_transitivity; eauto.
Qed.

(** * Disjoint & Isomorphic Subtyping *)

Lemma disjoint_isosub :
  forall A B C,
    disjoint A B -> isosub A C -> disjoint C B.
Proof.
  introv Dj Isub.
  eapply isosub_to_sub1 in Isub.
  eapply disjoint_sub; eauto.
Qed.

Lemma disjoint_iso_l1 :
  forall A C1 C2,
    disjoint C1 C2 ->
    isosub A C1 ->
    disjoint A C2.
Proof.
  introv Dj Isub.
  gen C2. dependent induction Isub; intros; eauto.
  - dependent induction Dj; eauto.
  - eapply disjoint_splitable_l in Dj; eauto.
    intuition.
Qed.

Lemma disjoint_iso_l2 :
  forall B C1 C2,
    disjoint C1 C2 ->
    isosub B C2 ->
    disjoint C1 B.
Proof.
  introv Dj Isub.
  gen C1. dependent induction Isub; intros; eauto.
  - dependent induction Dj; eauto.
  - eapply disjoint_splitable_r in Dj; eauto.
    intuition.
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
  eapply disjoint_iso_l1; eauto.
  eapply disjoint_iso_l2; eauto.
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
  induction Dj; intros; eauto.
  - dependent destruction As1; eauto.
  - dependent destruction As2; eauto.
  - dependent destruction As1. dependent destruction As2. eauto.
  - dependent destruction As1; dependent destruction As2; eauto. 
  - dependent destruction As1; dependent destruction As2; eauto.
    now destruct H.
  - dependent destruction As1; dependent destruction As2; eauto.
  - dependent destruction As1; dependent destruction As2; eauto.
Qed.

(** * Automations *)

Ltac solve_disjoint :=
  match goal with
  | [H: disjoint (Arr _ ?A) (Arr _ ?B) |- disjoint ?A ?B] => (dependent destruction H; assumption)
  end.

Hint Extern 5 => solve_disjoint : core.
