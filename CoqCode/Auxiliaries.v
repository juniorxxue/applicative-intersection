Require Import Metalib.Metatheory.
Require Import Language Notations.
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


(*aux lemma for sub_to_app *)
Lemma toplike_sub_top :
  forall (A : typ),
    sub typ_top A -> toplike A.
Proof.
  intros A Hsub.
  induction A.
  - inversion Hsub.
  - constructor.
  - inversion Hsub; subst.
    constructor. apply IHA2. assumption.
  - inversion Hsub; subst.
    constructor.
    + apply IHA1. assumption.
    + apply IHA2. assumption.
Qed.

Lemma toplike_sub_toplike :
  forall (A B : typ),
    toplike A ->
    sub A B ->
    toplike B.
Proof.
  intros A B Htop Hsub.
  dependent induction Hsub; eauto.
  - apply tl_arrow. apply IHHsub2. inversion Htop; subst. assumption.
  - inversion Htop; subst. apply IHHsub. assumption.
  - inversion Htop; subst. apply IHHsub. assumption.
Qed.

(* Lemma lambda_sub_check : *)
(*   forall (e : trm) (A B D : typ), *)
(*     typing nil nil check_mode (trm_abs e) (typ_arrow A B) -> *)
(*     sub (typ_arrow A B) (typ_arrow A D) -> *)
(*     typing nil nil check_mode (trm_abs e) (typ_arrow A D). *)
(* Proof. *)
(*   intros e A B D Htyp Hsub. *)
(*   inversion Htyp; subst. *)
(*   - assert (Htl: toplike (typ_arrow A D)). *)
(*     eapply toplike_sub_toplike; eauto 3. *)
(*     apply typing_top_value; eauto 3. *)
(*   - eapply typing_abs1. *)


(* Version: all value can be checked by toplike *)
Lemma typing_sub_check :
  forall (T : ctx) (v : trm) (A B : typ),
    (* value v -> *)
    typing T nil check_mode v A ->
    sub A B ->
    typing T nil check_mode v B.
Proof.
  intros T e A B Htyp Hsub.
  dependent induction Htyp.
  - eapply typing_top_value.
    eapply toplike_sub_toplike; eauto 3.
  - inversion Hsub; subst.
    + eapply typing_top_value; eauto 3.
    + eapply typing_top_value.
      eapply tl_arrow. apply toplike_sub_top. assumption.
    + apply typing_abs1 with (L:=L). intros x Hvar.
      pose proof (H x) as Hx. apply Hx in Hvar.
Admitted.
