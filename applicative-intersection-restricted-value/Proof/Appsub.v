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

Ltac solve_appsub :=
  match goal with
  | [H1: not (auxas ?S ?A), H2: appsub ?S ?A _ |- _] => (eapply auxas_false in H1; eauto; inversion H1)
  end.

Hint Extern 5 => solve_appsub : subtyping.

Lemma appsub_determinism :
  forall (A : typ) (B1 B2 : typ) (S : arg),
    appsub S A B1 ->
    appsub S A B2 ->
    B1 = B2.
Proof.
  intros A B1 B2 C Has1 Has2.
  generalize dependent B2.
  dependent induction Has1; intros;
    dependent destruction Has2; eauto with subtyping.
  assert (D1 = D0); eauto.
  assert (D2 = D3); eauto.
  congruence.
Qed.

Lemma appsub_iso1 :
  forall A B C H,
    appsub (Some A) B C ->
    isomorphic H A ->
    appsub (Some H) B C.
Proof.
  introv Has Hiso.
  gen H.
Admitted.
    
Lemma appsub_iso2 :
  forall A B C H,
    appsub (Some A) B C ->
    isomorphic H B ->
    appsub (Some A) H C.
Proof.
Admitted.

Lemma appsub_iso :
  forall A B C H1 H2,
    appsub (Some A) B C ->
    isomorphic H1 A ->
    isomorphic H2 B ->
    appsub (Some H1) H2 C.
Proof.
  introv Has Hiso1 Hiso2.
  pose proof (appsub_iso1 A B C H1 Has Hiso1).
  eapply appsub_iso2; eauto.
Qed.




  



