Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language.

Lemma typing_regular :
  forall (T : ctx) (e : trm) (A : typ),
    typing T nil infer_mode e A -> type A /\ uniq T.
Proof.
  split; induction H; eauto.
  - pick fresh y. pose proof (H1 y) as H1b. apply H1b in Fr.
    constructor. assumption. assumption.
  - pick fresh y. pose proof (H1 y) as H1b. apply H1b in Fr.
    constructor. assumption. assumption.
  - inversion IHtyping2; subst. assumption.
  - inversion IHtyping2. subst. assumption.
  - pick fresh y. pose proof (H1 y) as H1b. apply H1b in Fr.
    simpl in Fr. apply uniq_cons_1 in Fr. assumption.
  - pick fresh y. pose proof (H1 y) as H1b. apply H1b in Fr.
    simpl in Fr. apply uniq_cons_1 in Fr. assumption.
Qed.

Lemma typing_weaken :
  forall (T1 T2 T3: ctx) (e : trm) (A : typ),
    typing (T1 ++ T2) nil infer_mode e A ->
    uniq (T1 ++ T3 ++ T2) ->
    typing (T1 ++ T3 ++ T2) nil infer_mode e A.
Proof.
  intros.
  remember (T1 ++ T2) as T12.
  generalize dependent T1.
  induction H; intros; subst; eauto.
  - apply typing_abs1 with (L := dom (T1 ++ T3 ++ T2) \u L).
    assumption. intros x Frx.
    rewrite_env (([(x, A)] ++ T1) ++ T3 ++ T2).
    apply H1. auto. simpl_env. reflexivity.
    simpl_env. apply uniq_push. assumption. auto.
  - apply typing_abs2 with (L := dom (T1 ++ T3 ++ T2) \u L).
    assumption. intros x Frx.
    rewrite_env (([(x, A)] ++ T1) ++ T3 ++ T2).
    apply H1. auto. simpl_env. reflexivity.
    simpl_env. apply uniq_push. assumption. auto.
Qed.
