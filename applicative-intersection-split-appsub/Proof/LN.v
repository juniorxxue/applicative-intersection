Require Import Metalib.Metatheory.
Require Import Metalib.LibTactics.
Require Import Metalib.LibDefaultSimp.
Require Import Metalib.LibLNgen.
Require Import Coq.Program.Equality.
Require Import Coq.Strings.String.
Require Import Language.

Lemma subst_fresh : forall (x : atom) e u,
    x `notin` fv e -> subst_exp x u e = e.
Proof.
  intros.
  induction e; eauto.
  - Case "fvar".
    simpl.
    destruct (a == x).
    + SCase "a = x".
      subst. simpl fv in H. fsetdec.
    + SCase "a <> x".
      auto.
  - Case "abs".
    simpl.
    f_equal.
    auto.
  - Case "app".
    simpl in *.
    f_equal; auto.
  - Case "merge".
    simpl in *.
    f_equal; auto.
  - Case "anno".
    simpl in *.
    f_equal; auto.
Qed.

Lemma subst_eq_var:
  forall (x : atom) u,
    subst_exp x u x = u.
Proof.
  intros.
  simpl.
  destruct (x == x); eauto.
  destruct n; eauto.
Qed.

Lemma subst_neq_var :
  forall (x y : atom) u,
    y <> x -> subst_exp x u y = y.
Proof.
  intros x y u.
  simpl.
  intro Neq.
  destruct (y == x); eauto.
  contradiction.
Qed.

Lemma open_rec_lc_core : forall e j v i u,
    i <> j ->
    open_rec j v e = open_rec i u (open_rec j v e) ->
    e = open_rec i u e.
Proof with try solve [eauto | congruence].
  induction e; intros j v i u Neq H; simpl in *;
    try solve [inversion H; f_equal; eauto].
  Case "bvar".
  destruct (j == n)...
  destruct (i == n)...
Qed.

Lemma open_rec_lc : forall k u e,
    lc e -> e = open_rec k u e.
Proof.
  intros k u e LC.
  generalize dependent k.
  induction LC; eauto.
  - simpl. intros k. f_equal.
    unfold open in *.
    pick fresh x for L.
    apply open_rec_lc_core with
      (i := S k) (j := 0) (u := u) (v := trm_fvar x); eauto.
  - intro k. simpl. f_equal; eauto.
  - intro k. simpl. f_equal; eauto.
  - intro k. simpl. f_equal; eauto.
Qed.

(* free variable substitution distributes over index substitution. *)
Lemma subst_open_rec :
  forall e1 e2 u (x : atom) k,
    lc u ->
    subst_exp x u (open_rec k e2 e1) = open_rec k (subst_exp x u e2) (subst_exp x u e1).
Proof.
  induction e1; intros e2 u x k H; simpl in *; f_equal; eauto.
  - destruct (k == n); eauto.
  - destruct (a == x); subst; eauto.
    apply open_rec_lc; eauto.
Qed.

Lemma subst_open_var :
  forall (x y : atom) u e,
    y <> x ->
    lc u ->
    open (subst_exp x u e) y = subst_exp x u (open e y).
Proof.
  intros x y u e Neq H.
  unfold open.
  rewrite subst_open_rec with (e2 := (trm_fvar y)); eauto.
  rewrite subst_neq_var; eauto.
Qed.

Lemma subst_lc :
  forall (x : atom) u e,
    lc e ->
    lc u ->
    lc (subst_exp x u e).
Proof.
  intros x u e He Hu.
  induction He; try solve [simpl; eauto].
  - simpl. destruct (x0 == x); eauto.
  - simpl.
    apply lc_abs with (L := L `union` singleton x).
    intros x0 Fr.
    rewrite subst_open_var; eauto.
Qed.

Lemma subst_intro :
  forall (x : atom) u e,
    x `notin` (fv e) ->
    open e u = subst_exp x u (open e x).
Proof.
  intros.
  unfold open.
  generalize 0.
  induction e; intros n0; simpl; eauto.
  - destruct (n0 == n).
    + now rewrite subst_eq_var.
    + simpl. auto.
  - destruct (a == x); eauto.
    simpl in H. fsetdec.
  - f_equal. simpl in H.
    now eapply IHe.
  - simpl in H.
    f_equal; eauto.
  - simpl in H.
    f_equal; eauto.
  - simpl in H.
    f_equal; eauto.
Qed.

Lemma subst_notin_fv : forall x y u e,
   x `notin` fv e -> x `notin` fv u ->
   x `notin` fv (subst_exp y u e).
Proof.
  intros x y u e Fr1 Fr2.
  induction e; try solve [simpl in *; eauto].
  simpl.
  destruct (a == y); eauto.
Qed.

Lemma typing_to_lc :
  forall T e A,
    typing T e A -> lc e.
Proof.
  intros T e A H.
  induction H; eauto.
Qed.

Hint Resolve typing_to_lc : core.

Ltac bind_empty :=
  match goal with
  | [H: binds _ _ nil |- _] => (inversion H)
  end.

Hint Extern 5 => bind_empty : core.

Lemma open_abs :
  forall e u A B,
    lc (trm_abs e A B) ->
    lc u ->
    lc (open e u).
Proof.
  intros e u A B H1 H2.
  dependent destruction H1.
  pick fresh x.
  rewrite (subst_intro x); eauto.
  apply subst_lc; eauto.
Qed.

Hint Resolve open_abs : lc.
