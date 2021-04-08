Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language Subtyping Notations.

Inductive runsub : typ -> typ -> Prop :=
| rsub_refl : forall (A : typ),
    runsub A A
| rsub_arrow : forall (A1 A2 B1 B2 : typ),
    sub B1 A1 -> runsub A2 B2 ->
    runsub (typ_arrow A1 A2) (typ_arrow B1 B2)
| rsub_and : forall (A1 A2 B1 B2 : typ),
    runsub A1 B1 -> runsub A2 B2 ->
    runsub (typ_and A1 A2) (typ_and B1 B2)
| rsub_top : forall (A : typ),
    toplike A -> runsub typ_top A.


Theorem tred_preservation :
  forall (v v' : trm) (A: typ),
    value v -> typing nil nil check_mode v A ->
    typedred v A v' ->
    exists (B : typ), typing nil nil infer_mode v' B /\ runsub B A.
Proof.
  intros v v' A B.
  intros Htyp Hred.
  dependent induction Hred.
  - exists typ_int. split.
    + apply typing_anno.
      apply as_refl.
      apply typing_sub with (B:=typ_int).
      apply typing_int. constructor. apply sub_reflexivity.
    + apply rsub_refl.
  - exists typ_top. split.
    + apply typing_anno.
      apply as_refl.
      apply typing_sub with (B:=typ_top).
      apply typing_top. apply sub_reflexivity.
    + apply rsub_top. assumption.
  - exists (typ_arrow A D). split.
    Focus 2.
    + apply rsub_arrow. assumption. apply rsub_refl.
    + apply typing_anno.
      apply as_refl.
      inversion Htyp; subst; clear Htyp.
      inversion H2; subst; clear H2.
      inversion H8; subst; clear H8.
      inversion H3; subst.
      Focus 2.
      eapply typing_abs1.
      intros.
      (* inversion Htyp; subst. inversion H3; subst. *)
      (* inversion H10; subst. *)
      (* specialize (H11 x). *)
Admitted.

Theorem preservation :
  forall (e e' : trm) (A : typ),
    typing nil nil infer_mode e A ->
    step e e' ->
    typing nil nil check_mode e' A.
Proof.
  intros e e' A Htyp Hred.
  induction Htyp.
  - inversion Hred; subst.
    apply typing_sub with (B:=typ_int).
    apply typing_anno. constructor.
    apply typing_sub with (B:=typ_int).
    apply typing_int. assumption. apply sub_reflexivity. apply sub_reflexivity.
  - inversion Hred.
  - inversion Hred.
  - inversion Hred.
  - inversion Hred.
  - inversion Hred; subst.
    + induction A; eauto.
      * inversion H; subst; clear H.
Admitted.
