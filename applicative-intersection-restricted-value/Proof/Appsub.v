Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Strings.String.
Require Import Program.Tactics.
Require Import Language LibTactics.

Lemma appsub_to_auxas :
  forall (A B : typ) (S : arg),
    appsub S A B ->
    auxas S A.
Proof.
  intros.
  dependent induction H; eauto.
Qed.

Lemma auxas_false :
  forall (A B : typ) (S : arg),
    not (auxas S A) ->
    appsub S A B ->
    False.
Proof.
  intros.
  eapply appsub_to_auxas in H0.
  contradiction.
Qed.

Hint Resolve auxas_false : obvious.

Lemma appsub_determinism :
  forall (A : typ) (B1 B2 : typ) (S : arg),
    appsub S A B1 ->
    appsub S A B2 ->
    B1 = B2.
Proof.
  intros A B1 B2 C Has1 Has2.
  generalize dependent B2.
  dependent induction Has1; intros;
    dependent destruction Has2; try solve [eauto | exfalso; eauto with obvious].
  assert (D1 = D0); eauto.
  assert (D2 = D3); eauto.
  congruence.
Qed.



