Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Strings.String.
Require Import Program.Tactics.
Require Import Lia.

Require Import Language Tactical.
Require Import Subtyping.Splitable.
Require Import Subtyping.Subtyping.

Set Printing Parentheses.

(** * Definition *)

Inductive arg : Set :=
| Avt : type -> arg
| Alt : label -> arg.

Inductive partype : Set :=
| T : type -> partype
| P : arg -> partype.

(** * Applicative subtyping *)

Inductive appsub : type -> partype -> option type -> Prop :=
| As_Int :
    appsub Int (T Int) None
| As_Top : forall A,
    appsub A (T Top) None
| As_Arr : forall A B C D,
    appsub C (T A) None ->
    appsub B (T D) None ->
    appsub (Arr A B) (T (Arr C D)) None
| As_Rcd : forall A B l,
    ordinary B ->
    appsub A (T B) None ->
    appsub (Rcd l A) (T (Rcd l B)) None
| As_And : forall A B B1 B2,
    splitable B B1 B2 ->
    appsub A (T B1) None ->
    appsub A (T B2) None ->
    appsub A (T B) None
| As_And_L : forall A B C,
    ordinary C ->
    appsub A (T C) None ->
    appsub (And A B) (T C) None
| As_And_R : forall A B C,
    ordinary C ->
    appsub B (T C) None ->
    appsub (And A B) (T C) None

           
| As_Par_Arr : forall A1 A2 B,
    appsub B (T A1) None ->
    appsub (Arr A1 A2) (P (Avt B)) (Some A2)
| As_Par_Arr_Fail : forall A1 A2 B,
    not (sub B A1) ->
    appsub (Arr A1 A2) (P (Avt B)) None
| As_Par_Rcd : forall l A,    
    appsub (Rcd l A) (P (Alt l)) (Some A)
| As_Par_Rcd_Fail : forall l1 l2 A,
    l1 <> l2 ->
    appsub (Rcd l1 A) (P (Alt l2)) None
| As_Par_And_L : forall A1 A2 S C,
    appsub A1 (P S) (Some C) ->
    appsub A2 (P S) None ->
    appsub (And A1 A2) (P S) (Some C)
| As_Par_And_R : forall A1 A2 S C,
    appsub A2 (P S) (Some C) ->
    appsub A1 (P S) None ->
    appsub (And A1 A2) (P S) (Some C)
| As_Par_And_P : forall A1 A2 S C1 C2,
    appsub A1 (P S) (Some C1) ->
    appsub A2 (P S) (Some C2) ->
    appsub (And A1 A2) (P S) (Some (And C1 C2)).

Hint Constructors appsub : core.

Notation "A ≤ B" := (appsub A (T B) None) (at level 40).
Notation "A ≤ B ~>? ∅" := (appsub A (P B) None) (at level 40).
Notation "A <: B ->? ~> C" := (appsub A (P B) (Some C)) (at level 40).
    
(** ** Coq negation handler *)

(** we use subtype negation in premise to avoid positivity check,
    we prove the soundness and completeness with rules in paper **)

Lemma appsub_sound_normal :
  forall A B,
    appsub A (T B) None ->
    sub A B.
Proof.
  introv As.
  dependent induction As; eauto.
Qed.

Lemma appsub_complete_normal :
  forall A B,
    sub A B ->
    appsub A (T B) None.
Proof.
  introv Sub.
  dependent induction Sub; eauto.
Qed.

(** ** Determinism *)

Lemma appsub_determinism :
  forall A B C1 C2,
    appsub A (P (Avt B)) (Some C1) ->
    appsub A (P (Avt B)) (Some C2) ->
    C1 = C2.
Proof.
  introv As1 As2.
  dependent induction As1.
  - dependent induction As2; eauto.
  - dependent induction As2; eauto.
Admitted.

(** ** Soundness and Completeness *)

Lemma appsub_sound1 :
  forall A B C,
    appsub A (P (Avt B)) (Some C) ->
    sub A (Arr B C).
Proof.
  introv As.
  dependent induction As; eauto.
  - eapply appsub_sound_normal in As. eauto.
  - eapply Sub_And; eauto.
Qed.

Lemma appsub_sound2 :
  forall A l B,
    appsub A (P (Alt l)) (Some B) ->
    sub A (Rcd l B).
Proof.
  introv As.
  dependent induction As; eauto.
  eapply Sub_And; eauto.
Qed.

Lemma appsub_complete1 :
  forall A B C,
    sub A (Arr B C) ->
    exists D, appsub A (P (Avt B)) (Some D) /\ sub D C.
Proof.
  introv Sub.
  dependent induction Sub.
  - exists B0. split; eauto.
    eapply As_Par_Arr.
    eapply appsub_complete_normal. eauto.
  - dependent destruction H.
    pose proof (IHSub1 _ _ eq_refl). destruct H0. destruct H0.
    pose proof (IHSub2 _ _ eq_refl). destruct H2. destruct H2.
Admitted.


    
  
