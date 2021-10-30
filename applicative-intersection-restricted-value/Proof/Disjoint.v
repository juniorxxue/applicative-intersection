Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language LibTactics.
Require Import Strings.String.
Require Import Program.Tactics.
Require Import SubAndTopLike Appsub.
Require Import Psatz. (* lia *)

Ltac ind_typ_size s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with
         | [ h : typ |- _ ] => (gen h)
         end;
  induction i as [|i IH]; [
      intros; match goal with
              | [ H : _ < 0 |- _ ] => (dependent destruction H)
              end
    | intros ].

Lemma split_decrease_size:
  forall A B C,
    splitable A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof.
  introv H. dependent induction H; simpl; lia.
Qed.

Theorem disjoint_complete :
  forall A B, disjoint A B -> disjoint_spec A B.
Proof.
  intros A B Hdisj C Hsub1 Hsub2.
  ind_typ_size (size_typ A + size_typ B + size_typ C).
  destruct (split_or_ord C).
  - dependent destruction Hdisj; try solve [eapply sub_toplike_preservation; eauto 3].
    + dependent destruction Hsub1.
      * eapply sub_toplike_preservation; eauto.
      * exfalso. eapply split_and_ord; eauto.
      * simpl in SizeInd.
        assert ((size_typ A1 + size_typ B + size_typ C) < i) by lia.
        now pose proof (IH _ _ Hdisj1 _ Hsub1 Hsub2 H1).
      * simpl in SizeInd.
        assert ((size_typ A2 + size_typ B + size_typ C) < i) by lia.
        now pose proof (IH _ _ Hdisj2 _ Hsub1 Hsub2 H1).
    + dependent destruction Hsub2.
      * eapply sub_toplike_preservation; eauto.
      * exfalso. eapply split_and_ord; eauto.
      * simpl in SizeInd.
        assert ((size_typ A + size_typ B1 + size_typ C) < i) by lia.
        now pose proof (IH _ _ Hdisj1 _ Hsub1 Hsub2 H1).
      * simpl in SizeInd.
        assert ((size_typ A + size_typ B2 + size_typ C) < i) by lia.
        now pose proof (IH _ _ Hdisj2 _ Hsub1 Hsub2 H1).
    + dependent destruction Hsub1; dependent destruction Hsub2; eauto 3.
      * inversion H.
      * dependent destruction H.
        exfalso. eapply split_and_ord; eauto.
      * exfalso. eapply split_and_ord; eauto.
    + dependent destruction Hsub1; dependent destruction Hsub2; eauto 3.
      * exfalso. eapply split_and_ord; eauto.
      * inversion H.
      * exfalso. eapply split_and_ord; eauto.
    + dependent destruction Hsub1; dependent destruction Hsub2; eauto 3.
      * constructor. eapply IH.
        eapply Hdisj. eapply Hsub1_2. eapply Hsub2_2.
        simpl in SizeInd. lia.
      * exfalso. eapply split_and_ord; eauto.
      * exfalso. eapply split_and_ord; eauto.
      * exfalso. eapply split_and_ord; eauto.
  - destruct_conjs.
    dependent destruction Hsub1; dependent destruction Hsub2;
      try solve [exfalso; eapply split_and_ord; eauto].
    eapply split_determinism in H0; eauto 3. destruct_conjs. subst.
    eapply split_determinism in H; eauto 3. destruct_conjs. subst.
    pose proof (split_decrease_size _ _ _ H3).
    destruct_conjs.
    eapply toplike_spl_combine; eauto 3.
    + eapply IH; eauto 3. lia.
    + eapply IH; eauto 3. lia.
Qed.

Lemma disjoint_symmetry:
  forall (A B : typ),
    disjoint A B -> disjoint B A.
Proof.
  introv H.
  dependent induction H; eauto.
Qed.

Lemma disjoint_soundness :
  forall (A B : typ),
    disjoint_spec A B -> disjoint A B.
Proof.
  introv. unfold disjoint_spec.
  gen B. induction A; introv H; induction B; eauto.
  - assert (sub typ_int typ_int) by eauto.
    pose proof (H typ_int H0 H0).
    inversion H1.
  - eapply disjoint_and_r; eauto.
  - eapply disjoint_arr_arr.
    eapply IHA2. intros.
    assert (toplike (typ_arrow (typ_and A1 B1) C)) by (eapply H; eauto).
    now dependent destruction H2.
  - eapply disjoint_and_r; eauto.
  - eapply disjoint_and_l; eauto.
  - eapply disjoint_and_l; eauto.
  - eapply disjoint_and_l; eauto.
Qed.

Lemma disjoint_sub :
  forall (A B C : typ),
    disjoint A B -> sub A C -> disjoint C B.
Proof.
  introv Hdisj Hsub.
  eapply disjoint_complete in Hdisj.
  eapply disjoint_soundness.
  unfold disjoint_spec in *. intros.
  eapply Hdisj; eauto.
  eapply sub_transitivity; eauto.
Qed.


Lemma iso_to_sub :
  forall (A B : typ),
    isomorphic A B -> sub A B.
Proof.
  introv Hiso.
  induction Hiso; eauto.  
Qed.

Lemma disjoint_iso_transitivity :
  forall (A B C : typ),
    disjoint A B -> isomorphic A C -> disjoint C B.
Proof.
  introv Hdisj Hiso.
  eapply iso_to_sub in Hiso.
  eapply disjoint_sub; eauto.
Qed.

Lemma disjoint_appsub :
  forall (A B C D1 D2 : typ),
    disjoint A B ->
    appsub (Some C) A D1 ->
    appsub (Some C) B D2 ->
    disjoint D1 D2.
Proof.
  introv Hdisj Has1 Has2.
  gen C D1 D2.
  induction Hdisj; intros.
  - inversion Has1.
  - inversion Has2.
  - dependent destruction Has1; eauto.
  - dependent destruction Has2; eauto.
  - inversion Has1.
  - inversion Has2.
  - dependent destruction Has1. dependent destruction Has2.
    eauto.
Qed.

Lemma disjoint_iso_l :
  forall (A B C1 C2 : typ),
    disjoint C1 C2 ->
    isomorphic A C1 ->
    isomorphic B C2 ->
    disjoint A B.
Proof.
  introv Hdisj Hiso1 Hiso2.
  eapply disjoint_complete in Hdisj.
  eapply disjoint_soundness.
  unfold disjoint_spec in *.
  introv Hsub1 Hsub2.
Abort.

Lemma disjoint_iso_r :
  forall (A B C1 C2 : typ),
    disjoint A B ->
    isomorphic A C1 ->
    isomorphic B C2 ->
    disjoint C1 C2.
Proof.
  introv Hdisj Hiso1 Hiso2.
  assert (disjoint C1 B).
  eapply disjoint_iso_transitivity; eauto.
  eapply disjoint_symmetry.
  eapply disjoint_symmetry in H.
  eapply disjoint_iso_transitivity; eauto.
Qed.

Lemma disjoint_spec_toplike :
  forall (A B : typ),
    toplike A -> disjoint_spec A B.
Proof.
  introv Htl.
  unfold disjoint_spec.
  introv Hsub1 Hsub2.
  eapply sub_toplike_preservation; eauto.
Qed.

Lemma disjoint_toplike :
  forall (A B : typ),
    toplike A -> disjoint A B.
Proof.
  introv Htl.
  assert (disjoint_spec A B) by (eapply disjoint_spec_toplike; eauto).
  now eapply disjoint_soundness in H.
Qed.
