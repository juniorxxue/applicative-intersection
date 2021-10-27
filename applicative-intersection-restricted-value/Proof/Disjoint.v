Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language LibTactics.
Require Import Strings.String.
Require Import Program.Tactics.
Require Import SubAndTopLike.
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

Lemma iso_disjoint :
  forall (A1 A2 B : typ),
    isomorphic A1 A2 ->
    (disjoint A1 B <-> disjoint A2 B).
Proof.
  introv Hiso.
  gen B.
  dependent induction Hiso; intros; try solve [split; eauto].
  - gen B. induction H; try solve [split; eauto].
    + split; eauto.
      intros.
      eapply disjoint_and_l.
      eapply IHtoplike1. assumption.
      eapply IHtoplike2. assumption.
    + split; eauto.
      intros.
Abort.
      

Lemma disjoint_iso_l :
  forall (A B C : typ),
    disjoint A B -> isomorphic C A -> disjoint C B.
Proof.
  introv Hdisj Hiso.
  gen C.
  induction Hdisj; eauto; intros.
  - dependent destruction Hiso; eauto.
    inversion H.
  - dependent destruction Hiso; eauto.
    dependent destruction H; eauto.
  - dependent destruction Hiso; eauto.
    inversion H.
  - dependent destruction Hiso; eauto.
    dependent destruction H.
Abort.
    
  
