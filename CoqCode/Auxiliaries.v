Require Import Metalib.Metatheory.
Require Import Language.

Lemma value_to_term : forall (e : trm),
    value e -> term e.
Proof.
  intros e Hval.
  induction Hval.
  - constructor.
  - constructor.
  - inversion H; subst. assumption.
  - constructor. assumption. assumption.
Qed.
