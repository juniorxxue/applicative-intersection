Require Import Metalib.Metatheory.
Require Import Language.
Require Import Coq.Program.Equality.

Lemma anno_equal_split :
  forall (e1 e2 : trm) (A B : typ),
    (trm_anno e1 A) = (trm_anno e2 B) -> (e1 = e2) /\ (A = B).
Proof.
  intros.
  induction e1; inversion H; eauto.
Qed.

Lemma anno_equal_split2 :
  forall (e1 e2 : trm) (A B : typ),
    (e1 = e2) /\ (A = B) -> (trm_anno e1 A) = (trm_anno e2 B).
Proof.
  intros.
  destruct H.
  rewrite H0.
  rewrite H. reflexivity.
Qed.

Lemma typing_sub_check :
  forall (e : trm) (A B : typ),
    typing nil nil check_mode e A ->
    sub A B ->
    typing nil nil check_mode e B.
Proof.
  intros e A B Htyp Hsub.
  induction Htyp.
Admitted.
