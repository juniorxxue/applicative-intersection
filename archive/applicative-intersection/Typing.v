Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language Subtyping Notations.

Lemma typing_regular :
  forall (T : ctx) (e : trm) (A : typ),
    typing T nil infer_mode e A -> uniq T.
Proof.
Admitted.

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
    intros x Frx.
    rewrite_env (([(x, A)] ++ T1) ++ T3 ++ T2).
    apply H0. auto. simpl_env. reflexivity.
    simpl_env. apply uniq_push. assumption. auto.
  - apply typing_abs2 with (L := dom (T1 ++ T3 ++ T2) \u L).
    intros x Frx.
    rewrite_env (([(x, A)] ++ T1) ++ T3 ++ T2).
    apply H0. auto. simpl_env. reflexivity.
    simpl_env. apply uniq_push. assumption. auto.
Qed.

Lemma typing_check_to_infer :
  forall (T : ctx) (e : trm) (A : typ),
    typing T nil check_mode e A ->
    exists (B : typ), typing T nil infer_mode e B /\ sub B A.
Proof.
  intros T e A Htyp.
  induction Htyp; eauto.
  - exists A. split.
    + constructor. assumption. assumption.
    + apply sub_reflexivity.
  - exists (typ_arrow A B). split.
Admitted.
(* this isn't working beacuse
to infer t_abs, we may require arguments *arg* to assist *)
