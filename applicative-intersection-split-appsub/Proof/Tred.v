Require Import Metalib.Metatheory.
Require Import Metalib.LibTactics.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Language LN LibTactics.
Require Import Strings.String.
Require Import SubAndTopLike Value Disjoint Ptype.
Require Import Psatz. (* lia *)

Lemma tred_ord_toplike :
  forall (v v' : trm) (A : typ),
    ordinary A -> toplike A -> typedred v A v' ->
    v' = (trm_anno (trm_int 1) A).
Proof.
  induction 3; eauto.
  - inversion H0.
  - dependent destruction H0. contradiction.
  - exfalso. eapply split_and_ord; eauto.
Qed.

Hint Resolve tred_ord_toplike : tred.

Lemma tred_sub :
  forall (A : typ) (v v' : trm),
    value v -> typedred v A v' -> forall (B : typ),
    typing nil v B ->
    sub B A.
Proof.
  introv Hv Hred.
  dependent induction Hred; eauto; introv Htyp.
  - dependent destruction Htyp.
    dependent destruction Htyp; eauto.
  - dependent destruction Htyp; eauto.
  - dependent destruction Hv.
    dependent destruction Htyp;
      eapply sub_and_l; eauto.
  - dependent destruction Hv.
    dependent destruction Htyp;
    eapply sub_and_r; eauto.
Qed.

Hint Resolve tred_sub : tred.

Theorem tred_determinism :
  forall (v1 v2 v1' v2' : trm) (A B C : typ),
    value v1 -> value v2 ->
    typing nil v1 A -> typing nil v2 B ->
    typedred v1 C v1' -> typedred v2 C v2' ->
    consistent v1 v2 -> v1' = v2'.
Proof.
  introv Hv1 Hv2 Htyp1 Htyp2 Hr1 Hr2 Hcons.
  gen A B v1 v2 v1' v2'.
  ind_typ_size (size_typ C).
  destruct (split_or_ord C).
  - gen A B. induction Hcons; eauto with value; intros.
    + Case "anno".
      dependent destruction Hv1. dependent destruction Hv2.
      destruct H; destruct H1;
        try solve [dependent destruction Hr1; dependent destruction Hr2; eauto with subtyping].
    + Case "disjoint".
      assert (A0 = A) by eauto with ptype. subst.
      assert (B0 = B) by eauto with ptype. subst.
      eapply disjoint_complete in H2.
      assert (sub A C) by eauto with tred.
      assert (sub B C) by eauto with tred.
      assert (toplike C) by eauto.
      eapply tred_ord_toplike in Hr1; eauto.
      eapply tred_ord_toplike in Hr2; eauto.
      now subst.
    + Case "merge".
      dependent destruction Hr1; eauto with subtyping.
      * symmetry. eapply tred_ord_toplike; eauto.
      * dependent destruction Htyp1; eapply IHHcons1; eauto with value.
      * dependent destruction Htyp1; eapply IHHcons2; eauto with value.
    + Case "merge".
      dependent destruction Hr2; eauto with subtyping.
      * eapply tred_ord_toplike; eauto.
      * dependent destruction Htyp2; eapply IHHcons1; eauto with value.
      * dependent destruction Htyp2; eapply IHHcons2; eauto with value.
  - destruct_conjs.
    dependent destruction Hr1; dependent destruction Hr2; eauto with subtyping.
    eapply split_determinism in H0; eauto.
    destruct_conjs. subst.
    eapply split_determinism in H; eauto.
    destruct_conjs. subst.
    assert (forall A B C, splitable A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A).
    eapply split_decrease_size.
    pose proof (H A0 B0 C H3).
    destruct_conjs.
    assert (size_typ B0 < i) by lia.
    assert (size_typ C < i) by lia.
    assert (v1 = v2); eauto 3.
    assert (v0 = v3); eauto 3.
    congruence.
Qed.

Lemma tred_value_preservation :
  forall (v v' : trm) (A : typ),
    value v -> typedred v A v' -> value v'.
Proof.
  introv Hv Htred.
  dependent induction Htred; eauto with value.
Qed.

Hint Resolve tred_value_preservation : value.

Lemma tred_transitivity :
  forall (v v1 v2 : trm) (A B : typ),
    value v ->
    typedred v A v1 ->
    typedred v1 B v2 ->
    typedred v B v2.
Proof.
  introv Hv Hred1 Hred2.
  gen B v2.
  induction Hred1; intros;
    try solve [dependent induction Hred2; eauto; eauto with lc; eauto with subtyping].
  - dependent induction Hred2; eauto.
    eapply tred_arrow_anno; eauto.
    eapply sub_transitivity; eauto.
  - dependent destruction Hv.
    dependent induction Hred2; eauto.
  - dependent destruction Hv.
    dependent induction Hred2; eauto.
Qed.

Theorem tred_progress :
  forall (v : trm) (A B : typ),
    value v -> typing nil v A ->
    sub A B ->
    exists v', typedred v B v'.
Proof.
  introv Hv Htyp Hsub.
  gen v.
  dependent induction Hsub; intros; eauto.
  - dependent destruction Htyp; eauto with value.
    dependent destruction Hv.
    dependent induction H; eauto.
    dependent destruction Htyp.
    eauto with subtyping.
  - dependent destruction Htyp; eauto with value.
    destruct (toplike_decidability D); try solve [eexists; eauto].
    + Case "top".
      exists (trm_anno (trm_int 1) (typ_arrow B D)).
      eapply tred_top; eauto.
    + Case "arrow".
      dependent destruction Hv.
      dependent destruction H0; eauto.      
      dependent destruction Htyp.
      assert (not (toplike C)) by eauto with subtyping.
      eauto with subtyping.
  - assert (exists v', typedred v B v'); eauto.
    assert (exists v', typedred v C v'); eauto.
    destruct_conjs; eauto.
  - dependent destruction Htyp; eauto; eauto with value.
    + dependent destruction Hv.
      assert (exists v', typedred e1 C v'); eauto.
      destruct_conjs; eauto.
    + dependent destruction Hv.
      assert (exists v', typedred u1 C v'); eauto.
      destruct_conjs; eauto.
  - dependent destruction Htyp; eauto with value.
    + dependent destruction Hv.
      assert (exists v', typedred e2 C v'); eauto.
      destruct_conjs; eauto.
    + dependent destruction Hv.
      assert (exists v', typedred u2 C v'); eauto.
      destruct_conjs; eauto.
Qed.

Hint Resolve tred_progress : tred.
