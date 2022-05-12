Require Import Metalib.Metatheory.
Require Import Metalib.LibTactics.
Require Import Metalib.LibDefaultSimp.
Require Import Metalib.LibLNgen.
Require Import Coq.Program.Equality.
Require Import Coq.Strings.String.
Require Import Language Value.

Lemma subst_fresh : forall (x : atom) e u,
    x `notin` fv e -> substitution x u e = e.
Proof.
  intros. induction e; eauto; try solve [simpl in *; f_equal; auto].
  - Case "fvar".
    simpl.
    destruct (a == x).
    + SCase "a = x".
      subst. simpl fv in H. fsetdec.
    + SCase "a <> x".
      auto.
Qed.

Lemma subst_eq_var:
  forall (x : atom) u,
    substitution x u x = u.
Proof.
  intros. simpl.
  destruct (x == x); eauto.
  destruct n; eauto.
Qed.

Lemma subst_neq_var :
  forall (x y : atom) u,
    y <> x -> substitution x u y = y.
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
      (i := S k) (j := 0) (u := u) (v := Fvar x); eauto.
  - intro k. simpl. f_equal; eauto.
  - intro k. simpl. f_equal; eauto.
  - intro k. simpl. f_equal; eauto.
  - intro k. simpl. f_equal; eauto.
  - intro k. simpl. f_equal; eauto.
Qed.

(* free variable substitution distributes over index substitution. *)
Lemma subst_open_rec :
  forall e1 e2 u (x : atom) k,
    lc u ->
    substitution x u (open_rec k e2 e1) = open_rec k (substitution x u e2) (substitution x u e1).
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
    open (substitution x u e) y = substitution x u (open e y).
Proof.
  intros x y u e Neq H.
  unfold open.
  rewrite subst_open_rec with (e2 := (Fvar y)); eauto.
  rewrite subst_neq_var; eauto.
Qed.

Lemma subst_lc :
  forall (x : atom) u e,
    lc e ->
    lc u ->
    lc (substitution x u e).
Proof.
  intros x u e He Hu.
  induction He; try solve [simpl; econstructor; eauto].
  - simpl. destruct (x0 == x); eauto. econstructor.
  - simpl. eapply Lc_Lam with (L := L `union` singleton x).
    intros x0 Fr.
    rewrite subst_open_var; eauto.
Qed.

Lemma subst_intro :
  forall (x : atom) u e,
    x `notin` (fv e) ->
    open e u = substitution x u (open e x).
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
  - simpl in H.
    f_equal; eauto.
  - simpl in H.
    f_equal; eauto.
Qed.

Lemma subst_notin_fv : forall x y u e,
   x `notin` fv e -> x `notin` fv u ->
   x `notin` fv (substitution y u e).
Proof.
  intros x y u e Fr1 Fr2.
  induction e; try solve [simpl in *; eauto].
  simpl.
  destruct (a == y); eauto.
Qed.

Lemma open_abs :
  forall e u A B,
    lc (Lam A e B) ->
    lc u ->
    lc (open e u).
Proof.
  intros e u A B H1 H2.
  dependent destruction H1.
  pick fresh x.
  rewrite (subst_intro x); eauto.
  apply subst_lc; eauto.
Qed.

Hint Resolve open_abs : core.

Lemma fv_open_lower :
  forall e1 e2 k,
    fv e1 [<=] fv (open_rec k e2 e1).
Proof with auto.
  intros.
  generalize dependent k.
  induction e1; intros; simpl; try fsetdec...
  - specialize (IHe1_1 k).
    specialize (IHe1_2 k).
    fsetdec...
  - specialize (IHe1_1 k).
    specialize (IHe1_2 k).
    fsetdec...
Qed.

Lemma add_notin_context :
  forall x T1 T2,
    T1 [<=] add x T2 ->
    x \notin T1 ->
    T1 [<=] T2.
Proof with auto.
  intros.
  fsetdec...
Qed.
