Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Strings.String.
Require Import Program.Tactics.
Require Import Language LibTactics.
Require Import SubAndTopLike.

Set Printing Parentheses.

Lemma appsub_to_auxas :
  forall (A B : typ) (S : arg),
    appsub S A B ->
    auxas S A.
Proof.
  intros.
  dependent induction H; eauto.
Qed.

Lemma auxas_false :
  forall (A B : typ) (S : arg),
    not (auxas S A) ->
    appsub S A B ->
    False.
Proof.
  intros.
  eapply appsub_to_auxas in H0.
  contradiction.
Qed.

Ltac solve_appsub :=
  match goal with
  | [H1: not (auxas ?S ?A), H2: appsub ?S ?A _ |- _] => (eapply auxas_false in H1; eauto; inversion H1)
  end.

Hint Extern 5 => solve_appsub : subtyping.

Lemma appsub_determinism :
  forall (A : typ) (B1 B2 : typ) (S : arg),
    appsub S A B1 ->
    appsub S A B2 ->
    B1 = B2.
Proof.
  intros A B1 B2 C Has1 Has2.
  generalize dependent B2.
  dependent induction Has1; intros;
    dependent destruction Has2; eauto with subtyping.
  assert (D1 = D0); eauto.
  assert (D2 = D3); eauto.
  congruence.
Qed.

Lemma appsub_sound :
  forall A B D,
    sub A (typ_arrow B D) ->
    exists C, appsub (Some B) A C /\ sub C D.
Proof.
  introv Hsub.
  gen B D.
  proper_ind A; intros.
  - dependent destruction Hsub.
    + dependent destruction H0.
Abort. (* not sound for toplike type *)

Lemma appsub_complete :
  forall A B C,
    appsub (Some B) A C -> sub A (typ_arrow B C).
Proof.
  introv Has.
  dependent induction Has; eauto.
  - eapply sub_arrow_gen; eauto.
  - pose proof (IHHas B).
    eapply sub_and_l_gen. eauto.
  - pose proof (IHHas B).
    eapply sub_and_r_gen. eauto.
  - pose proof (IHHas1 B).
    pose proof (IHHas2 B).
    eapply sub_and; eauto.
    eapply sub_and_l_gen. eauto.
    eapply sub_and_r_gen. eauto.
Qed.

Lemma auxas_iso1 :
  forall A B H,
    auxas (Some A) B ->
    isomorphic A H ->
    auxas (Some H) B.
Proof.
  introv Haux Hiso.
  gen A H.
  proper_ind B; intros.
  - inversion Haux.
  - inversion Haux.
  - dependent destruction Haux.
    pose proof (iso_to_sub _ _ Hiso).
    eapply aas_fun.
    eapply iso_to_sub' in Hiso.
    eapply sub_transitivity; eauto.
  - dependent destruction Haux.
    + eapply aas_fun. eapply iso_to_sub' in Hiso.
      eapply sub_transitivity; eauto.
    + dependent destruction H; eauto.
    + dependent destruction H; eauto.
Qed.

Lemma appsub_iso1 :
  forall A B C H,
    appsub (Some A) B C ->
    isomorphic H A ->
    exists D, appsub (Some H) B D /\ isomorphic D C.
Proof.
  introv Has Hiso.
  pose proof (iso_to_sub _ _ Hiso).
  exists C. split; eauto.
  dependent induction Has; eauto 3.
  - eapply as_fun; eauto.
    eapply sub_transitivity; eauto.
  - eapply as_and_l; eauto.
    intros Haux. eapply auxas_iso1 in Haux; eauto.
  - eapply as_and_r; eauto.
    intros Haux. eapply auxas_iso1 in Haux; eauto.
  - eapply as_and_both; eauto.
Qed.

Lemma appsub_split_inversion :
  forall A B C B1 B2,
    appsub (Some A) B C ->
    splitable B B1 B2 ->
    (appsub (Some A) B1 C) /\ (not (auxas (Some A) B2)) \/
      (appsub (Some A) B2 C) /\ (not (auxas (Some A) B1)) \/
      (exists C1 C2, (appsub (Some A) B1 C1) /\ (appsub (Some A) B2 C2) /\ (C = (typ_and C1 C2))).
Proof.
  introv Has Hspl.
  dependent destruction Hspl.
  - dependent destruction Has; eauto.
    right. right. exists D1. exists D2.
    split; eauto.
  - dependent destruction Has.
    right. right. exists C0. exists D0.
    split; eauto.
    (* oops, we can't say B is exactly C0 & D0 *)
    (* we need a induction here *)
Abort.

Lemma appsub_split_inversion :
  forall A B C B1 B2,
    appsub (Some A) B C ->
    splitable B B1 B2 ->
    (appsub (Some A) B1 C) /\ (not (auxas (Some A) B2)) \/
      (appsub (Some A) B2 C) /\ (not (auxas (Some A) B1)) \/
      (exists C1 C2, (appsub (Some A) B1 C1) /\ (appsub (Some A) B2 C2) /\ (C = (typ_and C1 C2))).
Proof.
  introv Has Hspl.
  gen A C B1 B2.
  proper_ind B; intros.
  - inversion Hspl.
  - inversion Hspl.
  - dependent destruction Hspl.
    eauto with subtyping.
  - eapply split_determinism in H; eauto.
    destruct H. subst.
    dependent destruction Hspl; eauto.
    + dependent destruction Has; eauto.
      right. right. exists D1. exists D2.
      split; eauto.
    + right. right.
      dependent destruction Has.    
      assert (Has1: appsub (Some A0) (typ_arrow A C) C) by eauto.
      pose proof (IHr1 _ _ Has1).
      assert (Has2: appsub (Some A0) (typ_arrow A D) D) by eauto.
      pose proof (IHr2 _ _ Has2).
      destruct (split_or_ord C); destruct (split_or_ord D).
      * clear H0. clear H1. clear IHr1. clear IHr2.
        clear Has1. clear Has2.
        dependent destruction Hspl.
        ** exists A1. exists B. split; eauto.
        ** admit. (* looks like we do something wrong *)
Admitted.

Lemma appsub_split_inversion_abort :
  forall A B C B1 B2,
    appsub (Some A) B C ->
    splitable B B1 B2 ->
    (appsub (Some A) B1 C) /\ (not (auxas (Some A) B2)) \/
      (appsub (Some A) B2 C) /\ (not (auxas (Some A) B1)) \/
      (exists C1 C2, (appsub (Some A) B1 C1) /\ (appsub (Some A) B2 C2) /\ (C = (typ_and C1 C2))).
Proof.
  introv Has Hspl.
  gen B1 B2.
  dependent induction Has; intros.
  - dependent destruction Hspl.
    admit. (* no IH here *)
  - dependent destruction Hspl; eauto.
  - dependent destruction Hspl; eauto.
  - dependent destruction Hspl; eauto.
    right. right. exists D1. exists D2.
    split; eauto.
Abort.

Lemma auxas_iso :
  forall A B H,
    auxas (Some A) B ->
    isomorphic B H ->
    auxas (Some A) H.
Proof.
  introv Has Hiso.
  gen A H.
  proper_ind B; intros.
  - inversion Has.
  - inversion Has.
  - dependent destruction Hiso. eauto.
  - dependent destruction H.
    + (* essence *)
      dependent destruction Hiso.
      * assumption.
      * (* H have two cases: arrow and intersection *)
        dependent destruction H.
        ** dependent destruction Has.
           *** pose proof (IHr1 _ Has _ Hiso1). eauto.
           *** pose proof (IHr2 _ Has _ Hiso2). eauto.
        ** eapply aas_fun; eauto.
           admit.
    + dependent destruction Hiso. auto.
Admitted.
     
Lemma appsub_iso2 :
  forall A B C H,
    appsub (Some A) B C ->
    isomorphic H B ->
    (exists D, appsub (Some A) H D /\ isomorphic D C).
Proof.
  introv Has Hiso.
  gen A C H.
  proper_ind B; intros.
  - inversion Has.
  - inversion Has.
  - dependent destruction Hiso; eauto.
    dependent destruction H0.
    eauto with subtyping.
  - dependent destruction Hiso; eauto.
    eapply split_determinism in H; eauto.
    destruct H. subst.
    eapply appsub_split_inversion in H0; eauto.
    destruct H0.
    + Case "L".
      destruct H.
      pose proof (IHr1 _ _ H _ Hiso1).
      destruct H1. destruct H1.
      exists x. split; eauto. eapply as_and_l; eauto.
      intros Hcontra. eapply auxas_iso in Hcontra; eauto.
    + destruct H.
      * Case "R".
        destruct H.
        pose proof (IHr2 _ _ H _ Hiso2).
        destruct H1. destruct H1.
        exists x. split; eauto. eapply as_and_r; eauto.
        intros Hcontra. eapply auxas_iso in Hcontra; eauto.
      * Case "Both".
        destruct H. destruct H. destruct H. destruct H0.
        pose proof (IHr1 _ _ H _ Hiso1).
        pose proof (IHr2 _ _ H0 _ Hiso2).
        destruct H2. destruct H2. destruct H3. destruct H3.
        exists (typ_and x1 x2). split.
        ** eapply as_and_both; eauto.
        ** subst. eauto.
Qed.
  
Lemma appsub_iso2_abort :
  forall A B C H,
    appsub (Some A) B C ->
    isomorphic H B ->
    (exists D, appsub (Some A) H D /\ isomorphic D C).
Proof.
  introv Has Hiso.
  gen A C H.
  proper_ind B; intros; eauto.
  - inversion Has.
  - inversion Has.
  - dependent destruction Has.
    dependent destruction Hiso; eauto.
    dependent destruction H1. eauto with subtyping.
  - dependent destruction H.
    + dependent destruction Hiso; eauto.
      dependent destruction H.
      admit.
    + pose proof (IHr1 A0 B).
Abort.
    
Lemma isomorphic_transitivity :
  forall A B C,
    isomorphic A B -> isomorphic B C ->
    isomorphic A C.
Proof.
  introv H1 H2.
  gen A. dependent induction H2; intros; eauto.
  dependent destruction H1; eauto.
  dependent destruction H0; eauto.
Qed.

Lemma appsub_iso :
  forall A B C H1 H2,
    appsub (Some A) B C ->
    isomorphic H1 A ->
    isomorphic H2 B ->
    (exists D, appsub (Some H1) H2 D /\ isomorphic D C).
Proof.
  introv Has Hiso1 Hiso2.
  pose proof (appsub_iso1 A B C H1 Has Hiso1).
  destruct H. destruct H.
  pose proof (appsub_iso2 _ _ _ _ H Hiso2).
  destruct H3. destruct H3.
  exists x0. split; eauto.
  eapply isomorphic_transitivity; eauto.
Qed.
