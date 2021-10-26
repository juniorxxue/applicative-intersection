Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Language LibTactics.
Require Import Strings.String.
Require Import SubAndTopLike Value Disjoint Ptype.
Require Import Psatz. (* lia *)

(* aux lemma for tred_determinism *)
Lemma tred_ord_toplike :
  forall (v v' : trm) (A : typ),
    ordinary A -> toplike A -> typedred v A v' ->
    v' = (trm_anno (trm_int 1) A).
Proof.
  induction 3; eauto.
  - inversion H0.
  - dependent destruction H0. contradiction.
  - exfalso; eauto.
Qed.

Hint Resolve tred_ord_toplike : core.

(* aux lemma for disjoint_value_consistent *)
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
  - gen A B. induction Hcons; try solve [inversion Hv1 | inversion Hv2]; intros.
    (* con anno *)
    + dependent destruction Hv1. dependent destruction Hv2.
      destruct H; destruct H1.
      * dependent destruction Hr1; dependent destruction Hr2;
          try solve [exfalso; eapply split_and_ord; eauto | reflexivity].
        ** inversion H1.
        ** inversion H.
      * dependent destruction Hr1; dependent destruction Hr2;
          try solve [exfalso; eapply split_and_ord; eauto | reflexivity].
        ** dependent destruction H. contradiction.
        ** dependent destruction H4. contradiction.
      * dependent destruction Hr1; dependent destruction Hr2;
          try solve [exfalso; eapply split_and_ord; eauto | reflexivity].
        ** inversion H1.
        ** inversion H.
      * dependent destruction Hr1; dependent destruction Hr2;
          try solve [exfalso; eapply split_and_ord; eauto | reflexivity].
        ** dependent destruction H. contradiction.
        ** dependent destruction H4. contradiction.
    (* con disjoint *)
    + assert (ptype u1 A0) by (now eapply typing_to_ptype in Htyp1).
      eapply ptype_determinism in H0; eauto. subst.
      assert (ptype u2 B0) by (now eapply typing_to_ptype in Htyp2).
      eapply ptype_determinism in H1; eauto. subst.
      eapply disjoint_complete in H2.
      assert (sub A C) by (eapply tred_sub in Hr1; eauto).
      assert (sub B C) by (eapply tred_sub in Hr2; eauto).
      assert (toplike C) by (now eapply H2).
      eapply tred_ord_toplike in Hr1; eauto.
      eapply tred_ord_toplike in Hr2; eauto.
      now subst.
    + dependent destruction Hv1.
      dependent destruction Hr1.
      * symmetry. eapply tred_ord_toplike; eauto.
      * dependent destruction Htyp1; eapply IHHcons1; eauto.
      * dependent destruction Htyp1; eapply IHHcons2; eauto.
      * exfalso; eauto.
    + dependent destruction Hv2.
      dependent destruction Hr2.
      * eapply tred_ord_toplike; eauto.
      * dependent destruction Htyp2; eapply IHHcons1; eauto.
      * dependent destruction Htyp2; eapply IHHcons2; eauto.
      * exfalso; eauto.
  - destruct_conjs.
    dependent destruction Hr1; try solve [exfalso; eauto 3].
    dependent destruction Hr2; try solve [exfalso; eauto 3].
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
  intros.
  dependent induction H0;
    try solve [eauto | dependent destruction H; eauto].
Qed.

Hint Resolve tred_value_preservation : core.

Lemma tred_transitivity :
  forall (v1 v2 v3 : trm) (A B : typ),
    value v1 ->
    typedred v1 A v2 ->
    typedred v2 B v3 ->
    typedred v1 B v3.
Proof.
Abort.

Theorem tred_preservation:
  forall (v v': trm) (A B: typ),
    value v ->
    typing nil v B ->
    typedred v A v' ->
    (exists C, typing nil v' C /\ isomorphic C A).
Proof.
  introv Hv Htyp Hred.
  gen B.
  induction Hred.
Abort.

Theorem tred_progress :
  forall (v : trm) (A B : typ),
    value v -> typing nil v A ->
    sub A B ->
    exists v', typedred v B v'.
Proof.
  introv Hv Htyp Hsub.
  gen v.
  dependent induction Hsub; intros; eauto.
  - dependent destruction Htyp;
      try solve [exfalso; eauto].
    + dependent destruction Hv.
      dependent induction H; eauto.
      dependent destruction Htyp.
      exfalso; eauto.
    + inversion Hv.
  - dependent destruction Htyp.
    + inversion H1.
    + inversion Hv.
    + assert (toplike D \/ not (toplike D)).
      eapply toplike_or_not_toplike.
      destruct H1.
      (* case top *)
      exists (trm_anno (trm_int 1) (typ_arrow B D)); eauto.
      (* case not top *)
      dependent destruction Hv.
      dependent destruction H0.
      (* case int *)
      dependent destruction Htyp.
      eapply sub_int_arrow_false in H2; eauto. contradiction.
      intro Hcontra. eapply sub_toplike_preservation in Hsub2; eauto.
      (* case arrow *)
      dependent destruction Htyp.
      exists (trm_anno (trm_abs e A0 B0) (typ_arrow B D)); eauto.
    + inversion Hv.
  - assert (exists v', typedred v B v'); eauto.
    assert (exists v', typedred v C v'); eauto.
    destruct_conjs; eauto.
  - dependent destruction Htyp; eauto; try solve [inversion Hv].
    + dependent destruction Hv.
      inversion H1.
    + dependent destruction Hv.
      assert (exists v', typedred e1 C v'); eauto.
      destruct_conjs; eauto.
    + dependent destruction Hv.
      assert (exists v', typedred u1 C v'); eauto.
      destruct_conjs; eauto.
  - dependent destruction Htyp; eauto; try solve [inversion Hv].
    + dependent destruction Hv.
      inversion H1.
    + dependent destruction Hv.
      assert (exists v', typedred e2 C v'); eauto.
      destruct_conjs; eauto.
    + dependent destruction Hv.
      assert (exists v', typedred u2 C v'); eauto.
      destruct_conjs; eauto.
Qed.
