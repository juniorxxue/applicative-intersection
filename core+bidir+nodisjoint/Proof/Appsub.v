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
| Avt : type -> arg.

(** ** Applicative Subtyping (Binary) *)

Inductive auxas : option arg -> type -> Prop :=
| Aas_Refl : forall A,
    auxas None A
| Aas_Arr : forall A B C,
    sub C A ->
    auxas (Some (Avt C)) (Arr A B)
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
| As_And_L : forall A B C D,
    appsub (Some C) A D ->
    not (auxas (Some C) B) ->
    appsub (Some C) (And A B) D
| As_And_R : forall A B C D,
    appsub (Some C) B D ->
    not (auxas (Some C) A) ->
    appsub (Some C) (And A B) D
| As_And_P : forall A B C D1 D2,
    appsub (Some C) A D1 ->
    appsub (Some C) B D2 ->
    appsub (Some C) (And A B) (And D1 D2).

Hint Constructors appsub : core.
Notation "S ⊢ A <: B" := (appsub S A B) (at level 40).

(** * Automations *)

(** ** Structural Inversions *)

Ltac solve_auxas :=
  match goal with
  | [H: auxas _ Int |- _] => (inversion H)
  | [H: auxas _ Top |- _] => (inversion H)
  end.

Ltac solve_appsub :=
  match goal with
  | [H: appsub _ Int _ |- _] => (inversion H)
  | [H: appsub _ Top _ |- _] => (inversion H)
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

Lemma appsub_complete :
  forall A B C,
    appsub (Some (Avt B)) A C -> sub A (Arr B C).
Proof.
  introv As.
  dependent induction As; eauto.
  - pose proof (IHAs1 B).
    pose proof (IHAs2 B).
    eapply Sub_And; eauto.
Qed.

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
    right. right. exists D1. exists D2.
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
    * exists (Arr A0 B1). exists (Arr A0 B2).
      split; eauto.
Qed.

(** ** Arguments *)

Lemma auxas_iso1 :
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

Lemma appsub_iso1 :
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
    intros Contra. eapply auxas_iso1 in Contra; eauto.
  - eapply As_And_R; eauto.
    intros Contra. eapply auxas_iso1 in Contra; eauto.
  - eapply As_And_P; eauto.
Qed.

(** ** Functions *)

Lemma auxas_iso2 :
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
    + SCase "Arr".
      dependent destruction Isub; eauto.
Qed.

Lemma appsub_iso2 :
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
      intros Hcontra. eapply auxas_iso2 in Hcontra; eauto.
    + destruct H.
      * SCase "R".
        destruct H.
        pose proof (IHPr2 _ _ H _ Isub2).
        destruct H1. destruct H1.
        exists x. split; eauto. eapply As_And_R; eauto.
        intros Hcontra. eapply auxas_iso2 in Hcontra; eauto.
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

(** ** Generalization *)

Lemma appsub_iso :
  forall A B C H1 H2,
    appsub (Some (Avt A)) B C ->
    isosub H1 A ->
    isosub H2 B ->
    (exists D, appsub (Some (Avt H1)) H2 D /\ isosub D C).
Proof.
  introv As Isub1 Isub2.
  pose proof (appsub_iso1 A B C H1 As Isub1) as Iso1.
  destruct Iso1. destruct H. 
  pose proof (appsub_iso2 _ _ _ _ H Isub2).
  destruct_conjs. eexists. split; eauto.
  eapply isosub_transitivity; eauto.
Qed.

(** * Unified Subtyping *)

(** ** Definition *)

Definition result := option type.

Inductive upartype : Set :=
| uT : type -> upartype
| uV : arg -> upartype
| uP : arg -> upartype.

Inductive uunisub : type -> upartype -> result -> Prop :=
| UUs_Int :
    uunisub Int (uT Int) None
| UUs_Top : forall A,
    uunisub A (uT Top) None
| UUs_Arr : forall A B C D,
    uunisub C (uT A) None ->
    uunisub B (uT D) None ->
    uunisub (Arr A B) (uT (Arr C D)) None
| UUs_And : forall A B B1 B2,
    splitable B B1 B2 ->
    uunisub A (uT B1) None ->
    uunisub A (uT B2) None ->
    uunisub A (uT B) None
| UUs_And_L : forall A B C,
    ordinary C ->
    uunisub A (uT C) None ->
    uunisub (And A B) (uT C) None
| UUs_And_R : forall A B C,
    ordinary C ->
    uunisub B (uT C) None ->
    uunisub (And A B) (uT C) None
| UUs_As_Arr : forall A1 A2 B,
    uunisub B (uT A1) None ->
    uunisub (Arr A1 A2) (uP (Avt B)) (Some A2)
| UUs_As_L : forall A1 A2 S C,
    uunisub A1 (uP S) (Some C) ->
    ~ (auxas (Some S) A2) ->
    uunisub (And A1 A2) (uP S) (Some C)
| UUs_As_R : forall A1 A2 S C,
    uunisub A2 (uP S) (Some C) ->
    ~ (auxas (Some S) A1) ->
    uunisub (And A1 A2) (uP S) (Some C)
| UUs_As_P : forall A1 A2 S C1 C2,
    uunisub A1 (uP S) (Some C1) ->
    uunisub A2 (uP S) (Some C2) ->
    uunisub (And A1 A2) (uP S) (Some (And C1 C2))
| UUs_V_As_Arr : forall A1 A2 B,
    uunisub B (uT A1) None ->
    uunisub (Arr A1 A2) (uV (Avt B)) None
| UUs_V_As_L : forall A1 A2 S,
    uunisub A1 (uV S) None ->
    uunisub (And A1 A2) (uV S) None
| UUs_V_As_R : forall A1 A2 S,
    uunisub A2 (uV S) None ->
    uunisub (And A1 A2) (uV S) None.

Hint Constructors uunisub : core.

(** ** Soundness *)

Lemma uunisub_sound_normal :
  forall A B,
    uunisub A (uT B) None ->
    sub A B.
Proof.
  introv Uusub.
  dependent induction Uusub; eauto.
Qed.

Lemma uunisub_sound_appsub :
  forall A S C,
    uunisub A (uP S) (Some C) ->
    appsub (Some S) A C.
Proof.
  introv UUsub.
  dependent induction UUsub; eauto.
  eapply As_Arr.
  now eapply uunisub_sound_normal.
Qed.

Lemma uunisub_sound_auxas :
  forall A S,
    uunisub A (uV S) None ->
    auxas (Some S) A.
Proof.
  introv Uusub.
  dependent induction Uusub; eauto.
  eapply Aas_Arr.
  now eapply uunisub_sound_normal.
Qed.

(** ** Completeness *)

Lemma uunisub_complete_normal :
  forall A B,
    sub A B ->
    uunisub A (uT B) None.
Proof.
  introv Sub.
  dependent induction Sub; eauto.
Qed.

Lemma uunisub_complete_appsub :
  forall A S B,
    appsub (Some S) A B ->
    uunisub A (uP S) (Some B).
Proof.
  introv As.
  dependent induction As; eauto.
  eapply UUs_As_Arr.
  now eapply uunisub_complete_normal.
Qed.

Lemma uunisub_complete_auxas :
  forall A S,
    auxas (Some S) A ->
    uunisub A (uV S) None.
Proof.
  introv Aas.
  dependent induction Aas; eauto.
  eapply UUs_V_As_Arr.
  now eapply uunisub_complete_normal.
Qed.


(** * Automations *)

Lemma uunisub_auxas_false1 :
  forall B S,
    ~ uunisub B (uV S) None ->
    auxas (Some S) B ->
    False.
Proof.
  introv nUs Aux.
  eapply uunisub_complete_auxas in Aux. contradiction.
Qed.


Lemma uunisub_auxas_false2 :
  forall S B,
    uunisub B (uV S) None ->
    ~ auxas (Some S) B ->
    False.
Proof.
  introv Us nAux.
  eapply nAux. now eapply uunisub_sound_auxas.
Qed.


Lemma uunisub_appsub_false :
  forall S B C,
    ~ uunisub B (uV S) None ->
    appsub (Some S) B C ->
    False.
Proof.
  introv nUs As.
  eapply appsub_to_auxas in As.
  eapply uunisub_auxas_false1; eauto.
Qed.


Ltac contra_uunisub :=
  match goal with
  | H1: ~ uunisub ?B (uV ?S) _, H2: auxas (Some ?S) ?B |- _ =>
      pose proof (uunisub_auxas_false1 _ _ H1 H2) as Contra; inversion Contra
  | H1: uunisub ?B (uV ?S) _, H2: ~ auxas (Some ?S) ?B |- _ =>
      pose proof (uunisub_auxas_false2 _ _ H1 H2) as Contra; inversion Contra
  | H1: ~ uunisub ?B (uV ?S) _, H2: appsub (Some ?S) ?B _ |- _ =>
      pose proof (uunisub_appsub_false _ _ _ H1 H2) as Contra; inversion Contra
  end.

Hint Extern 5 => contra_uunisub : core.

Lemma appsub_to_uunisub :
  forall S A C,
    appsub (Some S) A C ->
    uunisub A (uV S) None.
Proof.
  introv As.
  eapply appsub_to_auxas in As.
  now eapply uunisub_complete_auxas.
Qed.

Hint Resolve appsub_to_uunisub : core.
