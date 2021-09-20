Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language LibTactics.
Require Import Strings.String.
Require Import Program.Tactics.

Lemma ptype_determinism :
  forall (e : trm) (A B : typ),
    ptype e A -> ptype e B -> A = B.
Proof.
  intros. generalize dependent B.
  dependent induction H; eauto; intros * Hptyp.
  - dependent destruction Hptyp; eauto.
  - dependent destruction Hptyp; eauto.
    assert (A = A0); eauto.
    assert (B = B0); eauto.
    congruence.
Qed.

Hint Resolve ptype_determinism : core.

Ltac simpl_deter :=
  repeat
    match goal with
    | [H1: ptype ?v ?A1, H2: ptype ?v ?A2 |- _] => (eapply ptype_determinism in H1; eauto; subst)
    end.

Lemma typing_to_ptype :
  forall (A : typ) (v : trm),
    value v ->
    typing nil v A ->
    ptype v A.
Proof.
  introv Hv Htyp.
  generalize dependent A.
  dependent induction Hv; eauto; introv Htyp.
  - dependent destruction Htyp; eauto.
  - dependent destruction Htyp; eauto.
Qed.

Hint Resolve typing_to_ptype : core.
