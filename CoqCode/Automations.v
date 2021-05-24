Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language Subtyping Auxiliaries Notations.

Lemma trm_top_checked_by_toplike :
  forall (A : typ),
    toplike A ->
    typing nil nil check_mode trm_top A.
Proof.
  intros.
  eapply typing_sub; eauto.
  eapply toplike_sub_top. assumption.
Qed.

Hint Resolve trm_top_checked_by_toplike : core.
    
