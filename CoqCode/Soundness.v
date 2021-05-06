Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language Subtyping Auxiliaries Notations Deterministic.

Lemma sub_ord_disjoint :
  forall (A B C : typ),
    ordinary C -> disjoint_spec A B -> sub (typ_and A B) C ->
    sub A C /\ sub B C.
Proof.
  intros A B C Hord Hdisj Hsub.
  dependent destruction Hsub; try solve [inversion Hord].
  - split; eauto.
  - assert (Htl: toplike (typ_arrow B1 B2)).
    constructor. eapply toplike_sub_top; eauto.
    split; eauto.
Admitted.

Theorem tred_preservation :
  forall (v v' : trm) (A: typ),
    value v ->
    typing nil nil check_mode v A ->
    typedred v A v' ->
    typing nil nil infer_mode v' A.
Proof.
  intros v v' A Hv Htyp Hred.
  dependent induction Hred.
  - eapply typing_anno; eauto.
  - eapply typing_anno; eauto.
    admit. (* appsub and toplike *)
  - apply typing_anno; eauto.
    dependent destruction Htyp.
    dependent destruction Htyp.
    eapply typing_sub_check; eauto.
  - dependent destruction Hv.
    dependent destruction Htyp.
    dependent destruction Htyp.
    + apply IHHred; eauto.
      eapply typing_sub.
      apply Htyp1. (* Tred-Merge-L *)
      admit.
    + apply IHHred; eauto.
      eapply typing_sub.
      eapply Htyp1.
      admit.
  - dependent destruction Hv.
    dependent destruction Htyp.
    dependent destruction Htyp.
    + apply IHHred; eauto.
      eapply typing_sub.
      apply Htyp2.
      admit.
    + apply IHHred; eauto.
      eapply typing_sub.
      apply Htyp2.
      admit.
  - eapply typing_merge_value.
    + eapply tred_value; eauto.
    + eapply tred_value; eauto.
    + eapply IHHred1. assumption.
      admit.
    + eapply IHHred2. assumption.
      admit.
    + eapply tred_consistency; eauto.
Admitted.

Lemma papp_preservation :
  forall (r v e : trm) (A B : typ) (S : arg),
    rvalue r -> value v ->
    papp r v e ->
    typing nil nil infer_mode v A ->
    typing nil (cons A S) infer_mode r (typ_arrow A B) ->
    typing nil S infer_mode e B.
Proof.
  intros r v e A B Hr Hv Hp Htyp1 Htyp2.
  generalize dependent A.
  generalize dependent B.
  dependent induction Hp; intros.
Admitted.

Lemma papp_preservation_check :
  forall (r v e : trm) (A B : typ),
    rvalue r -> value v ->
    papp r v e ->
    typing nil nil infer_mode v A ->
    typing nil nil check_mode r (typ_arrow A B) ->
    typing nil nil check_mode e B.
Proof.
Admitted.

Theorem preservation :
  forall (e e' : trm) (A : typ) (dir : mode) (S : arg),
    typing nil S dir e A ->
    step e e' ->
    typing nil S dir e' A.
Proof.
  intros e e' A dir S Htyp Hred.
  generalize dependent e'.
  dependent induction Htyp; intros.
  - dependent destruction Hred.
    eapply typing_anno; eauto.
  - dependent destruction Hred.
  - dependent destruction Hred.
  - dependent destruction Hred.
  - dependent destruction Hred.
  - dependent destruction Hred.
  - dependent destruction Hred.
    + assert (Htyp2: typing nil nil infer_mode v' A).
      eapply tred_preservation; eauto.
      admit.
    + eapply typing_anno. assumption.
      eapply IHHtyp; eauto.
  - dependent destruction Hred.
    + eapply papp_preservation; eauto.
    + eapply typing_app1; eauto.
    + eapply typing_app1; eauto.
  - dependent destruction Hred.
    + eapply papp_preservation_check; eauto.
    + eapply typing_app2; eauto.
    + eapply typing_app2; eauto.
  - assert (Htyp2: typing nil nil infer_mode e' B).
    eapply IHHtyp; eauto.
    eapply typing_sub; eauto.
  - dependent destruction Hred.
    + eapply typing_merge; eauto.
    + eapply typing_merge; eauto.
  - assert (Hval: value (trm_merge v1 v2)).
    constructor; eauto.
    apply value_cannot_step_further with (e:=e') in Hval.
    destruct Hval. assumption.
  - assert (Htyp2: typing nil S infer_mode e' B).
    eapply IHHtyp; eauto.
    dependent destruction Hred.
    (*
      The problem is
      reduction of merge picking appears at papp
      typing of merge picking appears at merge
     *)
Admitted.
