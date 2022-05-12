Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Strings.String.
Require Import Program.Tactics.
Require Import Language Tactical.
Require Import Subtyping.Subtyping.
Require Import Subtyping.Splitable.

Set Printing Parentheses.

(** * Definitions *)

(** ** Arguments *)

Inductive arg :=
| Avt : type -> arg
| Alt : label -> arg.

(** ** Applicative Subtyping (Binary) *)

Inductive auxas : option arg -> type -> Prop :=
| Aas_Refl : forall A,
    auxas None A
| Aas_Arr : forall A B C,
    sub C A ->
    auxas (Some (Avt C)) (Arr A B)
| Aas_Lbl : forall A l,
    auxas (Some (Alt l)) (Rcd l A)
| Aas_And_L : forall A B S,
    auxas (Some S) A ->
    auxas (Some S) (And A B)
| Aas_And_R : forall A B S,
    auxas (Some S) B ->
    auxas (Some S) (And A B).

Hint Constructors auxas : core.
Notation "appsub? S A" := (auxas S A) (at level 40).

(** ** Applicative Subtyping *)

Inductive appsub : option arg -> type -> type -> Prop :=
| As_Refl : forall A,
    appsub None A A
| As_Arr : forall A B C,
    sub C A ->
    appsub (Some (Avt C)) (Arr A B) B
| As_Lbl : forall A l,
    appsub (Some (Alt l)) (Rcd l A) A
| As_And_L : forall A B S C,
    appsub (Some S) A C ->
    not (auxas (Some S) B) ->
    appsub (Some S) (And A B) C
| As_And_R : forall A B S C,
    appsub (Some S) B C ->
    not (auxas (Some S) A) ->
    appsub (Some S) (And A B) C
| As_And_P : forall A B S C1 C2,
    appsub (Some S) A C1 ->
    appsub (Some S) B C2 ->
    appsub (Some S) (And A B) (And C1 C2).

Hint Constructors appsub : core.
Notation "S ⊢ A <: B" := (appsub S A B) (at level 40).

(** * Automations *)

(** ** Structural Inversions *)

Ltac solve_auxas :=
  match goal with
  | [H: auxas _ Int |- _] => (inversion H)
  | [H: auxas _ Top |- _] => (inversion H)
  | [H: auxas (Some (Avt _)) (Rcd _ _) |- _] => (inversion H)
  | [H: auxas (Some (Alt _)) (Arr _ _) |- _] => (inversion H)
  end.

Ltac solve_appsub :=
  match goal with
  | [H: appsub _ Int _ |- _] => (inversion H)
  | [H: appsub _ Top _ |- _] => (inversion H)
  | [H: appsub (Some (Avt _)) (Rcd _ _) _ |- _] => (inversion H)
  | [H: appsub (Some (Alt _)) (Arr _ _) _ |- _] => (inversion H)
  end.

Hint Extern 5 => solve_auxas : core.
Hint Extern 5 => solve_appsub : core.

(** ** Contradictions *)

Lemma appsub_to_auxas :
  forall A B S,
    appsub S A B ->
    auxas S A.
Proof.
  intros.
  dependent induction H; eauto.
Qed.

Hint Resolve appsub_to_auxas : core.

Lemma auxas_false :
  forall A B S,
    not (auxas S A) ->
    appsub S A B ->
    False.
Proof.
  intros.
  eapply appsub_to_auxas in H0.
  contradiction.
Qed.

Ltac contra_appsub :=
  match goal with
  | [H1: not (auxas ?S ?A), H2: appsub ?S ?A _ |- _] =>
      (pose proof (auxas_false _ _ _ H1 H2) as Contra; inversion Contra)
  | [H1: not (auxas ?S ?A), H2: auxas ?S ?A |- _] =>
      (contradiction)
  end.

Hint Extern 5 => contra_appsub : core.

(** * Properties *)

(** ** Determinism *)

Lemma appsub_determinism :
  forall A B1 B2 S,
    appsub S A B1 ->
    appsub S A B2 ->
    B1 = B2.
Proof.
  introv As1 As2. gen B2.  
  dependent induction As1; intros;
    dependent destruction As2; eauto.
  pose proof (IHAs1_1 _ As2_1).
  pose proof (IHAs1_2 _ As2_2).
  congruence.
Qed.

(** ** Completeness *)

(** After adding records to appsub, we lose the standard completeness property *)

Lemma appsub_complete :
  forall A B C,
    appsub (Some (Avt B)) A C -> sub A (Arr B C).
Proof.
Abort.

(** * Appsub & Isomorphic Subtyping *)

(** ** Inversion Lemmas *)

Lemma appsub_split_inversion :
  forall A B C B1 B2,
    appsub (Some A) B C ->
    splitable B B1 B2 ->
    (appsub (Some A) B1 C) /\ (not (auxas (Some A) B2)) \/
      (appsub (Some A) B2 C) /\ (not (auxas (Some A) B1)) \/
      (exists C1 C2, (appsub (Some A) B1 C1) /\ (appsub (Some A) B2 C2) /\ (isosub (And C1 C2) C)).
Proof.
  introv Has Hspl.
  gen A C B1 B2.
  proper_ind B; intros; eauto. subst_splitable.
  dependent destruction Hspl; eauto.
  - Case "And".
    dependent destruction Has; eauto.
    right. right. exists C1. exists C2.
    split; eauto.
  - Case "Arr".
    right. right.
    dependent destruction Has.
    pose proof (As_Arr _ B1 _ H) as As1.
    pose proof (As_Arr _ B2 _ H) as As2.
    pose proof (IHPr1 _ _ As1).
    pose proof (IHPr2 _ _ As2).
    dependent destruction Hspl.
    * exists A0. exists B. split; eauto.
    * exists (Arr A0 B1). exists (Arr A0 B2). split; eauto.
    * exists (Rcd l A1). exists (Rcd l A2). split; eauto.
  - Case "Rcd".
    right. right.
    dependent induction Has.
    exists A1. exists A2. split; eauto.
Qed.

(** ** Arguments *)

Lemma auxas_iso_v1 :
  forall A B H,
    auxas (Some (Avt A)) B ->
    isosub A H ->
    auxas (Some (Avt H)) B.
Proof.
  introv Aas Isub.
  gen A H.
  proper_ind B; intros; eauto.
  - Case "Arr".
    dependent destruction Aas.
    pose proof (isosub_sound _ _ Isub) as Isub'.
    destruct Isub'.
    eapply Aas_Arr.
    eapply sub_transitivity; eauto.
  - Case "Split".
    dependent destruction Aas.
    + econstructor.
      eapply isosub_to_sub2 in Isub.
      eapply sub_transitivity; eauto.
    + dependent destruction H; eauto.
    + dependent destruction H; eauto.
Qed.

Lemma appsub_iso_v1 :
  forall A B C H,
    appsub (Some (Avt A)) B C ->
    isosub H A ->
    exists D, appsub (Some (Avt H)) B D /\ isosub D C.
Proof.
  introv As Isub.
  pose proof (isosub_to_sub1 _ _ Isub).
  exists C. split; eauto.
  dependent induction As.
  - eapply As_Arr; eauto.
    eapply sub_transitivity; eauto.
  - eapply As_And_L; eauto.
    intros Contra. eapply auxas_iso_v1 in Contra; eauto.
  - eapply As_And_R; eauto.
    intros Contra. eapply auxas_iso_v1 in Contra; eauto.
  - eapply As_And_P; eauto.
Qed.

(** ** Functions *)

Lemma auxas_iso_v2 :
  forall A B H,
    auxas (Some (Avt A)) B ->
    isosub B H ->
    auxas (Some (Avt A)) H.
Proof.
  introv As Isub. gen A H.
  proper_ind B; intros; eauto.
  - Case "Arr".
    dependent destruction Isub. eauto.
  - Case "Split".
    dependent destruction H.
    + SCase "And".
      dependent destruction Isub.
      * SSCase "Refl".
        assumption.
      * SSCase "Split".
        (* H have two cases: arrow and intersection *)
        dependent destruction H.
        ** SSSCase "And".
           dependent destruction As.
           *** pose proof (IHPr1 _ As _ Isub1). eauto.
           *** pose proof (IHPr2 _ As _ Isub2). eauto.
        ** SSSCase "Arr".
           eapply Aas_Arr; eauto.
           dependent destruction As.
           *** pose proof (IHPr1 _ As _ Isub1).
               dependent destruction H0; eauto.
           *** pose proof (IHPr2 _ As _ Isub2).
               dependent destruction H0; eauto.
        ** dependent destruction As.
           *** pose proof (IHPr1 _ As _ Isub1) as IH1. inversion IH1.
           *** pose proof (IHPr2 _ As _ Isub2) as IH2. inversion IH2.
    + SCase "Arr".
      dependent destruction Isub; eauto.
    + SCase "Rcd".
      inversion As.      
Qed.

Lemma auxas_iso_l2 :
  forall A l H,
    auxas (Some (Alt l)) A ->
    isosub A H ->
    auxas (Some (Alt l)) H.
Proof.
  Proof.
  introv As Isub. gen l H.
  proper_ind A; intros; eauto.
  - Case "Fld".
    dependent destruction As.
    dependent destruction Isub; eauto.
  - Case "Split".
    dependent destruction H.
    + SCase "And".
      dependent destruction Isub.
      * SSCase "Refl".
        assumption.
      * SSCase "Split".
        (* H have two cases: arrow and intersection *)
        dependent destruction H.
        ** SSSCase "And".
           dependent destruction As.
           *** pose proof (IHPr1 _ As _ Isub1). eauto.
           *** pose proof (IHPr2 _ As _ Isub2). eauto.
        ** SSSCase "Arr".
           dependent destruction As.
           *** pose proof (IHPr1 _ As _ Isub1) as IH1. inversion IH1.
           *** pose proof (IHPr2 _ As _ Isub2) as IH2. inversion IH2.
        ** SSSCase "Lbl".
           dependent destruction As.
           *** pose proof (IHPr1 _ As _ Isub1) as IH1.
               dependent destruction IH1; eauto.
           *** pose proof (IHPr2 _ As _ Isub2) as IH2.
               dependent destruction IH2; eauto.
    + SCase "Arr".
      dependent destruction Isub; eauto.
    + SCase "Rcd".
      dependent destruction As; eauto.
      dependent destruction Isub; eauto.
Qed.

Lemma appsub_iso_v2 :
  forall A B C H,
    appsub (Some (Avt A)) B C ->
    isosub H B ->
    (exists D, appsub (Some (Avt A)) H D /\ isosub D C).
Proof.
  introv As Isub. gen A C H.
  proper_ind B; intros; eauto.
  - Case "Arrow".
    dependent destruction Isub; eauto.
  - Case "Split".
    dependent destruction Isub; eauto.
    subst_splitable.
    eapply appsub_split_inversion in H0; eauto.
    destruct H0.
    + SCase "L".
      destruct H.
      pose proof (IHPr1 _ _ H _ Isub1).
      destruct H1. destruct H1.
      exists x. split; eauto. eapply As_And_L; eauto.
      intros Hcontra. eapply auxas_iso_v2 in Hcontra; eauto.
    + destruct H.
      * SCase "R".
        destruct H.
        pose proof (IHPr2 _ _ H _ Isub2).
        destruct H1. destruct H1.
        exists x. split; eauto. eapply As_And_R; eauto.
        intros Hcontra. eapply auxas_iso_v2 in Hcontra; eauto.
      * SCase "P".
        destruct H. destruct H. destruct H. destruct H0.
        pose proof (IHPr1 _ _ H _ Isub1).
        pose proof (IHPr2 _ _ H0 _ Isub2).
        destruct H2. destruct H2. destruct H3. destruct H3.
        exists (And x1 x2). split.
        ** eapply As_And_P; eauto.
        ** assert (isosub (And x1 x2) (And x x0)) by eauto.
           eapply isosub_transitivity; eauto.
Qed.

Lemma appsub_iso_l2 :
  forall A B H l,
    appsub (Some (Alt l)) A B ->
    isosub H A ->
    (exists C, appsub (Some (Alt l)) H C /\ isosub C B).
Proof.
  introv As Isub. gen B H l.
  proper_ind A; intros; eauto.
  - Case "Fld".
    dependent destruction As; eauto.
    dependent destruction Isub; eauto.
  - Case "Split".
    dependent destruction Isub; eauto.
    dependent destruction As; eauto.
    subst_splitable.
    eapply appsub_split_inversion in H0; eauto.
    destruct H0.
    + SCase "L".
      destruct H.
      pose proof (IHPr1 _ _ Isub1 _ H).
      destruct H1. destruct H1.
      exists x. split; eauto. eapply As_And_L; eauto.
      intros Hcontra. eapply auxas_iso_l2 in Hcontra; eauto.
    + destruct H.
      * SCase "R".
        destruct H.
        pose proof (IHPr2 _ _ Isub2 _ H).
        destruct H1. destruct H1.
        exists x. split; eauto. eapply As_And_R; eauto.
        intros Hcontra. eapply auxas_iso_l2 in Hcontra; eauto.
      * SCase "P".
        destruct H. destruct H. destruct H. destruct H0.
        pose proof (IHPr1 _ _ Isub1 _ H).
        pose proof (IHPr2 _ _ Isub2 _ H0).
        destruct H2. destruct H2. destruct H3. destruct H3.
        exists (And x1 x2). split.
        ** eapply As_And_P; eauto.
        ** assert (isosub (And x1 x2) (And x x0)) by eauto.
           eapply isosub_transitivity; eauto.
Qed.

(** ** Generalization *)

Lemma appsub_iso_v :
  forall A B C H1 H2,
    appsub (Some (Avt A)) B C ->
    isosub H1 A ->
    isosub H2 B ->
    (exists D, appsub (Some (Avt H1)) H2 D /\ isosub D C).
Proof.
  introv As Isub1 Isub2.
  pose proof (appsub_iso_v1 A B C H1 As Isub1) as Iso1.
  destruct Iso1. destruct H.
  pose proof (appsub_iso_v2 _ _ _ _ H Isub2).
  destruct_conjs. eexists. split; eauto.
  eapply isosub_transitivity; eauto.
Qed.

Lemma appsub_iso_l :
  forall A B H l,
    appsub (Some (Alt l)) A B ->
    isosub H A ->
    (exists C, appsub (Some (Alt l)) H C /\ isosub C B).
Proof.
  eapply appsub_iso_l2.
Qed.
