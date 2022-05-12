Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Strings.String.
Require Import Program.Tactics.
Require Import Lia.
Require Import Language Tactical.
Require Import Subtyping.Toplike.
Require Import Subtyping.Splitable.
Require Import Subtyping.Subtyping.
Require Import Appsub.

Set Printing Parentheses.

(** * Definition *)

Definition result := option type.

Inductive partype : Set :=
| T : type -> partype
| P : arg -> partype.

Inductive unisub : type -> partype -> result -> Prop :=
| Us_Int :
    unisub Int (T Int) None
| Us_Top : forall A B,
    ordinary B -> toplike B ->
    unisub A (T B) None
| Us_Arr : forall A B C D,
    unisub C (T A) None ->
    unisub B (T D) None ->
    unisub (Arr A B) (T (Arr C D)) None
| Us_Rcd : forall A B l,
    ordinary B ->
    unisub A (T B) None ->
    unisub (Rcd l A) (T (Rcd l B)) None
| Us_And : forall A B B1 B2,
    splitable B B1 B2 ->
    unisub A (T B1) None ->
    unisub A (T B2) None ->
    unisub A (T B) None
| Us_And_L : forall A B C,
    ordinary C ->
    unisub A (T C) None ->
    unisub (And A B) (T C) None
| Us_And_R : forall A B C,
    ordinary C ->
    unisub B (T C) None ->
    unisub (And A B) (T C) None
| Us_As_Arr : forall A1 A2 B,
    unisub B (T A1) None ->
    unisub (Arr A1 A2) (P (Avt B)) (Some A2)
| Us_As_Lbl : forall l A,    
    unisub (Rcd l A) (P (Alt l)) (Some A)
| Us_As_L : forall A1 A2 S C,
    unisub A1 (P S) (Some C) ->
    ~ (auxas (Some S) A2) ->
    unisub (And A1 A2) (P S) (Some C)
| Us_As_R : forall A1 A2 S C,
    unisub A2 (P S) (Some C) ->
    ~ (auxas (Some S) A1) ->
    unisub (And A1 A2) (P S) (Some C)
| Us_As_P : forall A1 A2 S C1 C2,
    unisub A1 (P S) (Some C1) ->
    unisub A2 (P S) (Some C2) ->
    unisub (And A1 A2) (P S) (Some (And C1 C2)).

Hint Constructors unisub : core.

Notation "A <: B ~> ∅" := (unisub A (T B) None) (at level 40).
Notation "A <: B ->? ~> C" := (unisub A (P B) (Some C)) (at level 40).

(** * Unified Subtyping & Normal Subtyping *)

(** ** Soundness *)

(** A <: B->? ~> . -> A <: B *)

Lemma unisub_sound_normal :
  forall A B,
    unisub A (T B) None ->
    sub A B.
Proof.
  introv Usub.
  dependent induction Usub; eauto.
Qed.

Lemma unisub_sound_appsub :
  forall A S C,
    unisub A (P S) (Some C) ->
    appsub (Some S) A C.
Proof.
  introv Usub.
  dependent induction Usub; eauto.
  eapply As_Arr.
  now eapply unisub_sound_normal.
Qed.

(** ** Completeness *)

Lemma unisub_complete_normal :
  forall A B,
    sub A B ->
    unisub A (T B) None.
Proof.
  introv Sub.
  dependent induction Sub; eauto.
Qed.

Lemma unisub_complete_appsub :
  forall A S B,
    appsub (Some S) A B ->
    unisub A (P S) (Some B).
Proof.
  introv As.
  dependent induction As; eauto.
  eapply Us_As_Arr.
  now eapply unisub_complete_normal.
Qed.


(** * Ultimate Unisubtyping *)

Inductive upartype : Set :=
| uT : type -> upartype
| uV : arg -> upartype
| uP : arg -> upartype.

Inductive uunisub : type -> upartype -> result -> Prop :=
| UUs_Int :
    uunisub Int (uT Int) None
| UUs_Top : forall A B,
    ordinary B -> toplike B ->
    uunisub A (uT B) None
| UUs_Arr : forall A B C D,
    uunisub C (uT A) None ->
    uunisub B (uT D) None ->
    uunisub (Arr A B) (uT (Arr C D)) None
| UUs_Rcd : forall A B l,
    ordinary B ->
    uunisub A (uT B) None ->
    uunisub (Rcd l A) (uT (Rcd l B)) None
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
| UUs_As_Lbl : forall l A,    
    uunisub (Rcd l A) (uP (Alt l)) (Some A)
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
| UUs_V_As_Lbl : forall l A,
    uunisub (Rcd l A) (uV (Alt l)) None    
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
