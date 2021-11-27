Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Language LibTactics.
Require Import Strings.String.
Require Import SubAndTopLike.

Ltac solve_value :=
  match goal with
  | [H: value (trm_int _) |- _] => (inversion H)
  | [H: value (trm_abs _ _ _) |- _] => (inversion H)
  | [H: value (trm_app _ _) |- _] => (inversion H)
  end.

Hint Extern 5 => solve_value : value.

Lemma pvalue_lc :
  forall p,
    pvalue p -> lc p.
Proof.
  introv H.
  induction p; try solve [eauto | inversion H; eauto].
Qed.

Hint Resolve pvalue_lc : lc.

Lemma value_lc :
  forall v,
    value v -> lc v.
Proof.
  introv Hv.
  induction Hv; eauto with lc.
Qed.

Hint Resolve value_lc : lc.

Lemma pvalue_and_value:
  forall (e : trm),
    pvalue e -> value e -> False.
Proof.
  intros e Hp Hv.
  dependent destruction Hp; try solve [inversion Hv].
Qed.

Ltac solve_pvalue_and_value :=
  match goal with
  | [H1: value ?v, H2: pvalue ?v |- _] =>
      (eapply pvalue_and_value in H1; eauto; inversion H1)
  end.

Hint Extern 5 => solve_pvalue_and_value : value.

Lemma value_and_value_anno:
  forall v A,
    value v -> value (trm_anno v A) -> False.
Proof.
  introv Hv Hvn.
  dependent destruction Hvn.
  eapply pvalue_and_value; eauto.
Qed.

Ltac solve_value_and_value_anno :=
  match goal with
  | [H1: value ?v, H2: value (trm_anno ?v ?A) |- _] =>
      (eapply value_and_value_anno in H1; eauto; inversion H1)
  end.

Hint Extern 5 => solve_value_and_value_anno : value.

Lemma pvalue_decidability :
  forall (e : trm),
    lc e ->
    pvalue e \/ not (pvalue e).
Proof.
  intros e LC.
  dependent induction e; eauto; try solve [right; intro H; inversion H].
Qed.

Hint Resolve pvalue_decidability : value.

Lemma lc_anno_inversion :
  forall e A,
    lc (trm_anno e A) -> lc e.
Proof.
  intros.
  now dependent destruction H.
Qed.

Hint Resolve lc_anno_inversion : lc.

Lemma lc_merge_inversion_l :
  forall e1 e2,
    lc (trm_merge e1 e2) -> lc e1.
Proof.
  intros.
  now dependent destruction H.
Qed.

Hint Resolve lc_merge_inversion_l : lc.

Lemma lc_merge_inversion_r :
  forall e1 e2,
    lc (trm_merge e1 e2) -> lc e2.
Proof.
  intros.
  now dependent destruction H.
Qed.

Hint Resolve lc_merge_inversion_r : lc.

Lemma value_decidability :
  forall (e : trm),
    lc e ->
    value e \/ not (value e).
Proof.
  intros e LC.
  dependent induction e; eauto; try solve [right; unfold not; intros; inversion H].
  - destruct IHe1; destruct IHe2; eauto with lc;
      try solve [right; unfold not; intros; dependent destruction H1; contradiction].
  - destruct IHe; eauto with lc.
    + right. intros Hvn.
      eauto with value.
    + destruct (pvalue_decidability e);
        destruct (ordinary_decidability t); eauto; eauto with lc;
        try solve [right; intros Hcontra; inversion Hcontra; contradiction].
Qed.

Lemma value_cannot_step_further:
  forall (v : trm),
    value v -> forall (e : trm), not (step v e).
Proof.
  intros v Hv.
  dependent induction v; intros; try solve [inversion Hv]; eauto.
  - dependent destruction Hv. intros Hm.
    dependent destruction Hm.
    + eapply IHv1; eauto.
    + eapply IHv1; eauto.
    + eapply IHv2; eauto.
  - dependent destruction Hv.
    induction H; eauto.
    + intros Hs. dependent destruction Hs; eauto with subtyping; eauto with value.
    + intros Hs. dependent destruction Hs; eauto with subtyping; eauto with value.
Qed.

Ltac solve_value_cannot_step_further :=
  match goal with
  | [H1: value ?v, H2: step ?v ?e |- _] =>
      (eapply value_cannot_step_further in H2; eauto; contradiction)
  end.

Hint Extern 5 => solve_value_cannot_step_further : value.

Lemma value_merge_inversion_l :
  forall (v1 v2 : trm),
    value (trm_merge v1 v2) -> value v1.
Proof.
  inversion 1; eauto.
Qed.

Hint Resolve value_merge_inversion_l : value.

Lemma value_merge_inversion_r :
  forall (v1 v2 : trm),
    value (trm_merge v1 v2) -> value v2.
Proof.
  inversion 1; eauto.
Qed.

Hint Resolve value_merge_inversion_r : value.

Lemma value_anno_ordinary :
  forall e A B,
    value (trm_anno e (typ_and A B)) -> False.
Proof.
  introv Hv.
  dependent destruction Hv.
  inversion H0.
Qed.

Ltac solve_value_anno_ordinary :=
  match goal with
  | [H: value (trm_anno _ (typ_and _ _)) |- _] =>
    (eapply value_anno_ordinary in H; eauto; inversion H)
  end.

Hint Extern 5 => solve_value_anno_ordinary : value.

Lemma consistent_lam :
  forall e A B1 B2,
    lc (trm_abs e A B1) ->
    lc (trm_abs e A B2).
Proof.
  inversion 1; eauto.
Qed.

Hint Resolve consistent_lam : lc.

Lemma value_is_uvalue :
  forall (v : trm),
    value v -> uvalue v.
Proof.
  introv Hv.
  induction Hv; eauto with lc.
Qed.

Hint Resolve value_is_uvalue : value.

