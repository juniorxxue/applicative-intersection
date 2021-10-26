Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Language LibTactics.
Require Import Strings.String.
Require Import SubAndTopLike.

Lemma pvalue_cannot_be_value :
  forall (e : trm),
    pvalue e -> value e -> False.
Proof.
  intros e Hp Hv.
  dependent destruction Hp; try solve [inversion Hv].
Qed.

Lemma pvalue_or_not_pvalue :
  forall (e : trm),
    pvalue e \/ not (pvalue e).
Proof.
  intros e.
  dependent induction e; eauto; try solve [right; intro H; inversion H].
Qed.

Lemma ordinary_decidable :
  forall (A : typ),
    ordinary A \/ not (ordinary A).
Proof.
  introv.
  induction A; eauto.
  - destruct IHA1; destruct IHA2; eauto.
    + right. intros Hcontra. dependent destruction Hcontra. contradiction.
    + right. intros Hcontra. dependent destruction Hcontra. contradiction.
Qed.

Lemma value_or_not_value :
  forall (e : trm),
    value e \/ not (value e).
Proof.
  intros e.
  dependent induction e; eauto; try solve [right; unfold not; intros; inversion H].
  - destruct IHe1; destruct IHe2; eauto;
      try solve [right; unfold not; intros; dependent destruction H1; contradiction].
  - destruct IHe.
    + right. unfold not. intros. dependent destruction H0.
      eapply pvalue_cannot_be_value; eauto.
    + destruct (pvalue_or_not_pvalue e);
        destruct (ordinary_decidable t); eauto.
      * right. intros Hcontra. dependent destruction Hcontra. contradiction.
      * right. intros Hcontra. dependent destruction Hcontra. contradiction.
      * right. intros Hcontra. dependent destruction Hcontra. contradiction.
Qed.

Hint Resolve value_or_not_value : core.

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
    + intros Hs.
      dependent destruction Hs; eauto.
      inversion H.
    + intros Hs.
      dependent destruction Hs; eauto.
      inversion H.
Qed.

Ltac solve_value_cannot :=
  match goal with
  | [H1: value ?v, H2: step ?v ?e |- _] =>
      (eapply value_cannot_step_further in H2; eauto; contradiction)
  end.

Hint Extern 5 => solve_value_cannot : determinism.

Lemma value_int_n_false :
  forall (n : nat), value (trm_int n) -> False.
Proof.
  intros. inversion H.
Qed.

Hint Resolve value_int_n_false : core.
