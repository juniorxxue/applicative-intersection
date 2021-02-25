Require Import Metalib.Metatheory.
Require Import Language.

Lemma anno_equal_split :
  forall (e1 e2 : trm) (A B : typ),
    (trm_anno e1 A) = (trm_anno e2 B) -> (e1 = e2) /\ (A = B).
Proof.
  intros.
  induction e1; inversion H; eauto.
Qed.
