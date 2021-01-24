Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language Notations.

Lemma value_cannot_step :
  forall (e : trm),
    value e -> forall (e' : trm), not (step e e').
Proof.
  intros e.
  induction e; intros Hval e'; inversion Hval; subst; unfold not; intros.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H; subst.
    + assert (H6': not (step e1 e1')).
      eapply IHe1. assumption. contradiction.
    + assert (H6': not (step e2 e2')).
      eapply IHe2. assumption. contradiction.
Qed.

Lemma step_determinism :
  forall (e e1 e2 : trm) (A : typ),
    typing nil nil check_mode e A ->
    step e e1 -> step e e2 -> e1 = e2.
Proof.
  intros e e1 e2 A Htyp Hred1.
  generalize dependent e2.
  generalize dependent A.
  induction Hred1.
  - intros A Htyp e2 Hred2.
    inversion Hred2; subst; clear Hred2; eauto.
    + inversion H4.
    + assert (H4' : not (step e e2')). eapply value_cannot_step. assumption.
      contradiction.
  - intros A0 Htyp e0 Hred2.
    inversion Hred2; subst; clear Hred2.
    + inversion Htyp; subst; clear Htyp.
Admitted.
  (* - intros A0 Htyp e2 Hred2. *)
  (*   inversion Hred2; subst; clear Hred2. *)
  (*   + f_equal. eapply IHHred1. *)
  (*     inversion Htyp; subst. *)
  (*     inversion H; subst. apply H7. assumption. *)
  (*   + inversion Htyp; subst. *)
  (*     assert (Hred1' : not (step e e')). *)
  (*     eapply value_cannot_step. assumption. *)
  (*     contradiction. *)
  (* - intros A Htyp e0 Hred2. *)
  (*   inversion Hred2; subst; clear Hred2. *)
  (*   + assert (Hred1' : not (step trm_top e1')). *)
  (*     eapply value_cannot_step. constructor. contradiction. *)
