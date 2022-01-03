Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language Subtyping Auxiliaries Notations.


(* Lemma tred_to_sub: forall (e e' : trm) (A B : typ), *)
(*     value e -> typedred e A e' -> typing nil nil infer_mode e B -> sub B A. *)
(* Proof. *)
(*   intros e e' A B Hval Hred Htyp. *)
(*   generalize dependent B. *)
(*   induction Hred; eauto. *)
(*   - intros B Htyp. *)
(*     inversion Htyp; subst. inversion H3; subst. *)
(*     + constructor. *)
(*   - intros B Htyp. *)
(*     apply toplike_sub_top in H0. *)
(*     pose proof (sub_transitivity typ_top B A) as sub_trans'. *)
(*     assert (H_sub1: sub B typ_top). *)
(*     constructor. apply sub_trans' in H_sub1. assumption. assumption. *)
(*   - inversion Hval. *)
(*   - intros B Htyp. *)
(*     inversion Hval; inversion Htyp; subst. *)
(*     apply sub_and_l. *)
(*     apply IHHred. assumption. assumption. *)
(*   - intros B Htyp. *)
(*     inversion Hval; inversion Htyp; subst. *)
(*     apply sub_and_r. *)
(*     apply IHHred. assumption. assumption. *)
(* Qed. *)

(* Lemma tred_transitivity : forall (e1 e2 e3: trm) (A B : typ), *)
(*     value e1 -> typedred e1 A e2 -> typedred e2 B e3 -> typedred e1 B e3. *)
(* Proof. *)
(*   intros e1 e2 e3 A B Hval Hred1 Hred2. *)
(*   generalize dependent e3. *)
(*   generalize dependent B. *)
(*   dependent induction Hred1; eauto. *)
(*   - intros B e3 Hred2. dependent induction Hred2; eauto. *)
(*   - intros B0 e3 Hred2. dependent induction Hred2; eauto. *)
(*     + constructor. assumption. assumption. assumption. *)
(*       pose proof (sub_transitivity D B D0) as Hsub. *)
(*       apply Hsub in H2. assumption. assumption. *)
(*   - intros B e3 Hred2. *)
(*     inversion Hval; subst; clear Hval. *)
(*     induction Hred2; eauto. *)
(*   - intros B e3 Hred2. inversion Hval; subst; clear Hval. *)
(*     induction Hred2; eauto. *)
(*   - intros B0 e0 Hred2. *)
(*     generalize dependent e0. *)
(*     induction B0; intros e0 Hred2; eauto. *)
(*     + inversion Hred2; subst; clear Hred2; eauto. *)
(*       * inversion H0. *)
(*     + inversion Hred2; subst; clear Hred2; eauto. *)
(*       * apply tred_top. apply value_to_term in Hval. assumption. assumption. assumption. *)
(*     + inversion Hred2; subst; clear Hred2; eauto. *)
(*       * apply tred_top. apply value_to_term in Hval. assumption. assumption. assumption. *)
(*     + inversion Hred2; subst; clear Hred2; eauto. *)
(*       * constructor. apply value_to_term in Hval. assumption. assumption. assumption. *)
(* Qed. *)

Lemma disjoint_value_consistent : forall (A B : typ) (e1 e2 : trm),
    disjoint_spec A B -> value e1 -> value e2 -> typing nil nil infer_mode e1 A -> typing nil nil infer_mode e2 B ->
    consistency_spec e1 e2.
Proof.
  intros A B e1 e2 Hdisj Hval1 Hval2 Htyp1 Htyp2.
  unfold consistency_spec.
  intros A0 e1' e2' Hred1 Hred2.
  assert (Htop : toplike A0). unfold disjoint_spec in Hdisj. apply Hdisj.
  pose proof (tred_to_sub e1 e1' A0 A) as Hsub1.
  apply Hsub1. assumption. assumption. assumption.
  pose proof (tred_to_sub e2 e2' A0 B) as Hsub2.
  apply Hsub2. assumption. assumption. assumption.
  apply tred_toplike with (A:=A0) (e1:=e1) (e2:=e2).
  assumption. assumption. assumption.
Qed.

Lemma tred_determinism : forall (e1 e2 e3 : trm) (A : typ),
    value e1 -> (exists (B : typ), typing nil nil infer_mode e1 B) -> typedred e1 A e2 -> typedred e1 A e3 -> e2 = e3.
Proof.
  intros e1 e2 e3 A Hval Htyp Hred1 Hred2.
  generalize dependent e3.
  induction Hred1; eauto.
  - intros e3 Hred2.
    inversion Hred2; subst; clear Hred2.
    + reflexivity.
    + inversion H0.
  - intros e3 Hred2.
    symmetry. apply tred_ord_toplike_normal with (e:=e) (e':=e3) (A:=A).
    assumption. assumption. assumption.
  - intros e3 Hred2.
    inversion Hred2; subst; clear Hred2.
    + inversion H4; subst; clear H4. congruence.
    + reflexivity.
  - intros e3 Hred2.
    destruct Htyp as [B Htyp'].
    inversion Hval; subst; clear Hval.
    inversion Hred2; subst; eauto.
    + apply tred_ord_toplike_normal with (e:=e1) (e':=e1') (A:=A).
      assumption. assumption. assumption.
    + inversion Htyp'; subst; clear Htyp'.
      apply IHHred1. assumption. exists A0. assumption. assumption.
    + inversion Htyp'; subst; clear Htyp'.
      eapply disjoint_value_consistent.
      apply H7. apply H3. apply H4. apply H10. apply H11. apply Hred1. apply H6.
    + inversion H0.
  - intros e3 Hred2.
    destruct Htyp as [B Htyp'].
    inversion Hval; subst; clear Hval.
    inversion Hred2; subst; eauto.
    + apply tred_ord_toplike_normal with (e:=e2) (e':=e2') (A:=A).
      assumption. assumption. assumption.
    + inversion Htyp'; subst; clear Htyp'.
      assert (Hcon: consistency_spec e1 e2).
      eapply disjoint_value_consistent.
      apply H7. apply H3. apply H4. apply H10. apply H11.
      symmetry. eapply Hcon.
      apply H6. apply Hred1.
    + inversion Htyp'; eauto.
    + inversion H0.
  - intros e0 Hred2.
    inversion Hred2; subst; eauto.
    + inversion H1.
    + inversion H1.
    + inversion H1.
    + assert (Heq1: e2 = e5).
      apply IHHred1_1. assumption. assumption. assumption.
      assert (Heq2: e3 = e6).
      apply IHHred1_2. assumption. assumption. assumption.
      rewrite Heq1. rewrite Heq2.
      reflexivity.
Qed.

Lemma consistent_after_tred :
  forall (e e1 e2 : trm) (A B C : typ),
    value e -> typing nil nil infer_mode e C ->
    typedred e A e1 -> typedred e B e2 -> consistency_spec e1 e2.
Proof.
  intros e e1 e2 A B C Hval Htyp Hred1 Hred2.
  unfold consistency_spec.
  intros D e1' e2' Hred1' Hred2'.
  assert (Hred11: typedred e D e1').
  eapply tred_transitivity. assumption.
  apply Hred1. apply Hred1'.
  assert (Hred21: typedred e D e2').
  eapply tred_transitivity. assumption.
  apply Hred2. apply Hred2'.
  eapply tred_determinism. apply Hval.
  exists C. apply Htyp. apply Hred11. apply Hred21.
Qed.

Lemma tred_preservation :
  forall (e e' : trm) (A : typ),
    value e -> typedred e A e' -> typing nil nil check_mode e A ->
    exists (B : typ), typing nil nil infer_mode e' B.
Proof with auto.
  intros e e' A Hval Hred Htyp.
  induction Hred; eauto.
Admitted.

Lemma tred_progress :
  forall (e : trm) (A : typ),
    value e -> typing nil nil check_mode e A -> exists (e' : trm), typedred e A e'.
Proof.
  intros e A Hval Htyp.
Admitted.
