Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language Automations Subtyping LibTactics.
Require Import Strings.String.

(* aux lemma for tred_determinism *)
Lemma tred_ord_toplike :
  forall (v v' : trm) (A : typ),
    ordinary A -> toplike A -> typedred v A v' ->
    v' = (trm_anno (trm_int 1) A).
Proof.
  induction 3; eauto; try solve [inversion_toplike | inversion_ordinary].
Qed.

Hint Resolve tred_ord_toplike : core.

(* aux lemma for disjoint_value_consistent *)
Lemma tred_sub :
  forall (A : typ) (v v' : trm),
    value v -> typedred v A v' -> forall (B : typ),
    typing nil nil v B ->
    sub B A.
Proof.
  introv Hv Hred.
  dependent induction Hred; eauto; introv Htyp.
  - dependent destruction Htyp.
    dependent destruction Htyp; eauto.
    simpl_as; eauto.
  - dependent destruction Htyp; eauto.
    simpl_as; eauto.
  - dependent destruction Hv.
    dependent destruction Htyp;
    eapply sub_and_l; eapply IHHred; eauto.
  - dependent destruction Hv.
    dependent destruction Htyp;
    eapply sub_and_r; eapply IHHred; eauto.
Qed.

(* aux lemma for disjoint_value_consistent *)
Lemma tred_determinism_toplike :
  forall (A : typ),
    toplike A ->
    forall (e1 e2 e1' e2' : trm), typedred e1 A e1' -> typedred e2 A e2' -> e1' = e2'.
Proof.
  intros A Htop.
  dependent induction Htop; introv Hred1 Hred2.
  - eapply tred_ord_toplike in Hred1; eauto.
    eapply tred_ord_toplike in Hred2; eauto.
    congruence.
  - dependent destruction Hred1; eauto; try solve [inversion_ordinary].
    dependent destruction Hred2; try solve [inversion_ordinary].
    assert (v1 = v0). eapply IHHtop1; eauto 3.
    assert (v2 = v3). eapply IHHtop2; eauto 3.
    congruence.
  - assert (toplike (typ_arrow A B)); eauto.
    eapply tred_ord_toplike in Hred1; eauto.
    eapply tred_ord_toplike in Hred2; eauto.
    congruence.
Qed.

(* aux lemma for tred_determinism *)
Lemma disjoint_value_consistent :
  forall (A B : typ) (v1 v2 : trm),
    disjoint_spec A B -> value v1 -> value v2 ->
    typing nil nil v1 A -> typing nil nil v2 B ->
    consistency_spec v1 v2.
Proof.
  intros. unfold consistency_spec. intros.
  unfold disjoint_spec in *.
  assert (sub A A0). eapply tred_sub with (v:=v1); eauto.
  assert (sub B A0). eapply tred_sub with (v:=v2); eauto.
  assert (toplike A0); eauto.
  eapply tred_determinism_toplike; eauto.
Qed.

Hint Resolve disjoint_value_consistent : core.

Theorem tred_determinism :
  forall (v v1 v2 : trm) (A : typ),
    value v -> (exists B, typing nil nil v B) ->
    typedred v A v1 -> typedred v A v2 -> v1 = v2.
Proof.
  introv Hv Htyp Hred1.
  generalize dependent v2.
  dependent induction Hred1; eauto; introv Hred2.
  - dependent induction Hred2; try solve [inversion_toplike]; eauto.
  - dependent destruction Hred2; try solve [inversion_toplike | inversion_ordinary]; eauto.
    + symmetry. eapply tred_ord_toplike; eauto.
    + symmetry. eapply tred_ord_toplike; eauto.
  - dependent destruction Hred2; try solve [inversion_toplike]; eauto.
  - dependent destruction Hv.
    dependent destruction Htyp.
    dependent destruction Hred2; try solve [inversion_ordinary]; eauto.
    + dependent destruction H; eauto.
    + dependent destruction H; eauto.
      assert (consistency_spec v1 v2).
      eapply disjoint_value_consistent; eauto 3. eauto.
  - dependent destruction Hv.
    dependent destruction Htyp.
    dependent destruction Hred2; try solve [inversion_ordinary]; eauto.
    + dependent destruction H; eauto.
      * assert (consistency_spec v1 v2); eauto.
        symmetry. eauto.
      * symmetry. eauto.
    + dependent destruction H; eauto.
  - dependent destruction Hred2; try solve [inversion_ordinary]; eauto.
    assert (v1 = v0); eauto.
    assert (v2 = v3); eauto.
    congruence.
Qed.

Lemma tred_value :
  forall (v v' : trm) (A : typ),
    value v -> typedred v A v' -> value v'.
Proof.
  intros.
  dependent induction H0; try solve [eauto | dependent destruction H; eauto].
Qed.

Hint Resolve tred_value : core.

Lemma tred_transitivity :
  forall (v1 v2 v3 : trm) (A B : typ),
    value v1 ->
    typedred v1 A v2 ->
    typedred v2 B v3 ->
    typedred v1 B v3.
Proof.
  intros.
  generalize dependent v3.
  generalize dependent B.
  dependent induction H0; eauto; introv Hred2.
  - dependent induction Hred2; eauto.
  - dependent induction Hred2; try solve [inversion_toplike_sub]; eauto.
  - dependent induction Hred2; eauto 4.
    eapply tred_arrow_anno; eauto;
    eapply sub_transitivity; eauto.
  - dependent destruction H.
    dependent induction Hred2; eauto.
  - dependent destruction H.
    dependent induction Hred2; eauto.
  - generalize dependent v3.
    induction B0; intros v0 Hred2; try solve [eauto | dependent destruction Hred2; eauto].
Qed.

Lemma tred_consistency :
  forall (v v1 v2 : trm) (A B C : typ),
    value v -> typing nil nil v C ->
    typedred v A v1 ->
    typedred v B v2 ->
    consistency_spec v1 v2.
Proof.
  intros.
  unfold consistency_spec; intros.
  assert (typedred v A0 e1').
  eapply tred_transitivity with (v1:=v) (v2:=v1) (v3:=e1'); eauto.
  assert (typedred v A0 e2').
  eapply tred_transitivity with (v1:=v) (v2:=v2) (v3:=e2'); eauto.
  eapply tred_determinism; eauto.
Qed.

Theorem tred_preservation:
  forall (v v': trm) (A B: typ),
    value v ->
    typing nil nil v B ->
    typedred v A v' ->
    typing nil nil v' A.
Proof.
  intros v v' A B Hv Htyp Hred.
  assert (Hsub: sub B A). eapply tred_sub; eauto.
  generalize dependent B.
  dependent induction Hred; eauto 3; intros.
  - eapply typing_anno; eauto.
  - dependent destruction Htyp.
    dependent destruction Htyp.
    eapply typing_anno; eauto.
    eapply sub_transitivity; eauto.
  - dependent destruction Hv.
    dependent destruction Htyp; eapply IHHred; eauto.
    + eapply tred_sub. apply Hv1. apply Hred. apply Htyp1.
    + eapply tred_sub. apply Hv1. apply Hred. apply Htyp1.
  - dependent destruction Hv.
    dependent destruction Htyp; eapply IHHred; eauto.
    + eapply tred_sub. apply Hv2. apply Hred. apply Htyp2.
    + eapply tred_sub. apply Hv2. apply Hred. apply Htyp2.
  - eapply typing_merge_value; eauto.
    + eapply tred_consistency; eauto.
    + eapply IHHred1; eauto.
      eapply tred_sub. apply Hv. apply Hred1. apply Htyp.
    + eapply IHHred2; eauto.
      eapply tred_sub. apply Hv. apply Hred2. apply Htyp.
Qed.

Theorem tred_progress :
  forall (v : trm) (A B : typ),
    value v -> typing nil nil v A ->
    sub A B ->
    exists v', typedred v B v'.
Proof.
  introv Hv Htyp Hsub.
  generalize dependent A.
  induction B; introv Htyp Hsub; eauto.
  - dependent induction Htyp; try solve [inversion Hv].
    + simpl_as. dependent destruction Hv.
      dependent destruction H.
      * clear IHHtyp. dependent destruction Htyp.
        exists (trm_anno (trm_int n) typ_int); eauto.
      * clear IHHtyp.
        dependent destruction Htyp.
        assert (sub (typ_arrow A0 B) typ_int). eapply sub_transitivity; eauto.
        inversion H1.
    + dependent destruction Hv.
      dependent destruction Hsub.
      * assert (exists v', typedred e1 typ_int v'); eauto.
        destruct H0; eauto.
      * assert (exists v', typedred e2 typ_int v'); eauto.
        destruct H0; eauto.
    + dependent destruction Hv.
      dependent destruction Hsub.
      * assert (exists v', typedred v1 typ_int v'); eauto.
        destruct H2; eauto.
      * assert (exists v', typedred v2 typ_int v'); eauto.
        destruct H2; eauto.
  - destruct (toplike_or_not_toplike B2).
    + exists (trm_anno (trm_int 1) (typ_arrow B1 B2)).
      eapply tred_top; eauto.
    + clear IHB1 IHB2.
      dependent induction Htyp; try solve [inversion Hv].
      * simpl_as.
        dependent destruction Hv.
        dependent induction H.
        (* case 1 *)
        dependent destruction Htyp.
        assert (sub typ_int (typ_arrow B1 B2)).
        eapply sub_transitivity; eauto.
        dependent destruction H2.
        assert (toplike B2); eauto.
        (* case 2 *)
        dependent destruction Htyp.
        exists (trm_anno (trm_abs e A0 B) (typ_arrow B1 B2)); eauto.
      * dependent destruction Hv.
        eapply sub_and_inversion2 in Hsub.
        destruct Hsub.
        (* case 1 *)
        assert (exists v', typedred e1 (typ_arrow B1 B2) v'); eauto.
        destruct H2. exists x; eauto.
        destruct H1.
        (* case 2 *)
        assert (exists v', typedred e2 (typ_arrow B1 B2) v'); eauto.
        destruct H2. exists x; eauto.
        (* case 3 *)
        destruct H1. destruct H1. inversion H1.
      * dependent destruction Hv.
        eapply sub_and_inversion2 in Hsub.
        destruct Hsub.
        (* case 1 *)
        assert (exists v', typedred v1 (typ_arrow B1 B2) v'); eauto.
        destruct H4. exists x; eauto.
        destruct H3.
        (* case 2 *)
        assert (exists v', typedred v2 (typ_arrow B1 B2) v'); eauto.
        destruct H4. exists x; eauto.
        (* case 3 *)
        destruct H3. destruct H3. inversion H3.
  - eapply sub_and_inversion1 in Hsub.
    destruct Hsub.
    assert (exists v', typedred v B1 v'); eauto.
    assert (exists v', typedred v B2 v'); eauto.
    destruct H1. destruct H2.
    exists (trm_merge x x0); eauto.
Qed.
