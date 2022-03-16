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
