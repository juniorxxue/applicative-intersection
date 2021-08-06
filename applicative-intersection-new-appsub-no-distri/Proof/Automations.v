Require Import Language.

Lemma ptype_construction :
  forall (A B : typ) (v1 v2 : trm),
    ptype v1 A -> ptype v2 B ->
    ptype (trm_merge v1 v2) (typ_and A B).
Proof.
  intros.
  eapply ptype_merge; eauto.
Qed.
