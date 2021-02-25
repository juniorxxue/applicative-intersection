Require Import Coq.Program.Equality.
Require Import Language Notations Auxiliaries Subtyping.
Require Import Strings.String.

Set Printing Parentheses.

Lemma tred_ord_toplike : forall (e e' : trm) (A : typ),
    ordinary A -> toplike A -> typedred e A e' -> e' = (trm_anno trm_top typ_top).
Proof.
  intros e e' A H_ord H_top H_tred.
  dependent induction H_tred; subst; eauto.
  - inversion H_top.
  - inversion H_top. contradiction.
  - inversion H_ord.
Qed.

Lemma tred_toplike :
  forall (A : typ),
    toplike A -> forall e1 e2 e1' e2' : trm, typedred e1 A e1' -> typedred e2 A e2' -> e1' = e2'.
Proof.
  intros A Htop.
  dependent induction Htop; intros e1 e2 e1' e2' H_tred1 H_tred2.
  - eapply tred_ord_toplike in H_tred1. eapply tred_ord_toplike in H_tred2.
    rewrite H_tred1. rewrite H_tred2. reflexivity.
    constructor. constructor. constructor. constructor.
  - inversion H_tred1; subst; eauto 3.
    + inversion H1.
    + inversion H3.
    + inversion H3.
    + inversion H_tred2; subst; eauto 3.
      * inversion H4.
      * inversion H8.
      * inversion H8.
      * assert (Heq1: (trm_anno p1 D) = (trm_anno p0 D0)).
        eapply IHHtop1; eauto 3.
        assert (Heq2: (trm_anno p2 E) = (trm_anno p3 E0)).
        eapply IHHtop2; eauto 3.
        eapply anno_equal_split in Heq1.
        destruct Heq1 as [Heq11 Heq12].
        eapply anno_equal_split in Heq2.
        destruct Heq2 as [Heq21 Heq22].
        rewrite Heq11. rewrite Heq12. rewrite Heq21. rewrite Heq22. reflexivity.
  - assert (HAB: toplike (typ_arrow A B)).
    constructor. assumption.
    eapply tred_ord_toplike in H_tred2; eauto.
    eapply tred_ord_toplike in H_tred1; eauto.
    rewrite H_tred1. rewrite H_tred2. reflexivity.
Qed.

Lemma toplike_sub_top :
  forall (A : typ),
    toplike A <-> sub typ_top A.
Proof.
  intro A. split.
  - intro H. induction H.
    + constructor.
    + constructor. assumption. assumption.
    + constructor. assumption.
  - intro H. induction A; eauto.
    + inversion H; subst; eauto.
    + inversion H; subst. constructor.
      apply IHA2. assumption.
    + constructor; inversion H; subst.
      apply IHA1. assumption.
      apply IHA2. assumption.
Qed.

Lemma tred_sub :
  forall (A B : typ) (v1 v2 : trm),
    value v1 -> typedred v1 A v2 ->
    typing nil nil infer_mode v1 B ->
    sub B A.
Proof.
  intros A B v1 v2 Hval Hred Htyp.
  generalize dependent B.
  induction Hred; eauto.
  - intros B Htyp.
    inversion Htyp; subst.
    inversion H3; subst. constructor.
  - intros B Htyp.
    eapply toplike_sub_top in H0.
    eapply sub_transitivity.
    constructor. assumption.
  - intros B0 Htyp.
    inversion Hval; subst; clear Hval.
    inversion Htyp; subst; clear Htyp.
    inversion H7; subst.
    apply sub_arrow. assumption. assumption.
  - intros B0 Htyp.
    inversion Htyp; subst; clear Htyp.
    inversion H7; subst; clear H7.
    apply sub_and_l.
    eapply IHHred. constructor. assumption.
    inversion H8; subst.
    Focus 2.
    + apply typing_anno. constructor. assumption.
Admitted.
  (* pose proof (tred_to_sub e1 e1' A0 A) as Hsub1. *)
  (* apply Hsub1. assumption. assumption. assumption. *)
  (* pose proof (tred_to_sub e2 e2' A0 B) as Hsub2. *)
  (* apply Hsub2. assumption. assumption. assumption. *)
  (* apply tred_toplike with (A:=A0) (e1:=e1) (e2:=e2). *)
(*   (* assumption. assumption. assumption. *) *)
(* Qed. *)

Lemma tred_determinism :
  forall (v v1 v2 : trm) (A : typ),
    value v -> (exists B, typing nil nil infer_mode v B) ->
    typedred v A v1 -> typedred v A v2 -> v1 = v2.
Proof.
  intros v v1 v2 A Hval Htyp Hred1.
  generalize dependent v2.
  induction Hred1.
  - intros v2 Hred2. inversion Hred2; subst.
    + reflexivity.
    + inversion H0.
  - intros v2 Hred2.
    inversion Hred2; subst; clear Hred2.
    + inversion H0.
    + reflexivity.
    + inversion H0. contradiction.
    + symmetry. eapply tred_ord_toplike; eauto.
    + symmetry. eapply tred_ord_toplike; eauto.
    + inversion H1.
  - intros v2 Hred2.
    inversion Hred2; subst; clear Hred2.
    + inversion H3. contradiction.
    + reflexivity.
  - intros v2 Hred2.
    inversion Hred2; subst; eauto.
    + eapply tred_ord_toplike; eauto 3.
    + eapply IHHred1.
      * constructor. assumption.
      * destruct Htyp. inversion H3; subst.
        inversion H14; subst.
        inversion H4; subst.
        inversion H5; subst.
        unfold disjoint_spec in H15.
    (* + assert (Hval1 : value (trm_anno p1 A)). constructor. assumption. *)
    (*   eapply IHHred1 in Hval1. apply Hval1. *)
Admitted.

Lemma papp_determinism :
  forall (v1 v2 e1 e2 : trm),
    papp v1 v2 e1 -> papp v1 v2 e2 -> e1 = e2.
Proof.
  intros v1 v2 e1 e2 Hp1.
  generalize dependent e2.
  induction Hp1.
  - intros e2 Hp2. inversion Hp2. reflexivity.
  - intros e2 Hp2. inversion Hp2. reflexivity.
  - intros e2 Hp2. inversion Hp2; subst.
    Admitted.

Lemma step_determinism :
  forall (e e1 e2 : trm) (A : typ),
    typing nil nil check_mode e A ->
    step e e1 -> step e e2 -> e1 = e2.
Proof.
  intros e e1 e2 A Htyp Hred1.
  generalize dependent e2.
  generalize dependent A.
  induction Hred1.
  - intros A Htyp e2 Hred2.
    inversion Hred2; subst.
    reflexivity.
  - intros A0 Htyp e2 Hred2.
    inversion Hred2; subst.
Admitted.
