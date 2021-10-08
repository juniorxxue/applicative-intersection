Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language LibTactics.

Lemma toplike_or_not_toplike :
  forall (A : typ),
    toplike A \/ not (toplike A).
Proof.
  intros A.
  dependent induction A; eauto;
    try solve [right; intros Hcontra; inversion Hcontra].
  - destruct IHA1; destruct IHA2; eauto;
      try solve [right; intros H1; dependent destruction H1; contradiction].
  - destruct IHA1; destruct IHA2; eauto;
      try solve [right; intros H1; dependent destruction H1; contradiction].
Qed.

Lemma toplike_int_false :
  toplike typ_int -> False.
Proof.
  intros. inversion H.
Qed.

Hint Resolve toplike_int_false : core.

Lemma split_and_toplike :
  forall (A B C : typ),
    not (toplike A) -> splitable A B C ->
    not (toplike B) \/ not (toplike C).
Proof.
Admitted.
    
  

      

    

