Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language Subtyping Auxiliaries Notations.

Lemma sub_int_toplike :
  forall (A : typ),
    toplike A -> sub typ_int A.
Proof.
  intros.
  dependent induction H; eauto.
  eapply sub_top_arr.
  eapply toplike_sub_top; eauto.
Qed.

Hint Resolve sub_int_toplike : core.
