Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Strings.String.
Require Import Program.Tactics.
Require Import Language Tactical.
Require Import Subtyping.

Set Printing Parentheses.

(** * Definitions *)

(** ** Arguments *)

Inductive Result :=
| Just     : type -> Result
| Nothing  : Result
| Amb      : Result.


Fixpoint psub (A : type) (B : type) : Result :=
  match A with
  | Arr A1 A2 => if dec_sub B A1 then Just A2 else Nothing
  | And A1 A2 =>
    match psub A1 B, psub A2 B with
    | Amb, _            => Amb
    | _, Amb            => Amb
    | Just C1, Just C2  => Amb    (* Without distributivity we change the algorithm here *)
    | Just C1, _        => Just C1
    | _, Just C2        => Just C2
    | _,_               => Nothing
    end
  | _ => Nothing
  end.

(** * Soundness *)

Require Import FunInd FMapInterface.
Functional Scheme psub_ind := Induction for psub Sort Prop.

Lemma sound :
  forall A B C,
    psub A B = Just C ->
    sub A (Arr B C).
  intros A B.
  functional induction psub A B; intros; try (inversion H); subst; eauto.
Defined.

(** * Completeness *)

Lemma complete :
  forall A B C,
    sub A (Arr B C) ->
    (exists D, psub A B = Just D /\ sub D C) \/ psub A B = Amb.
Proof.
  intros.
  dependent induction H.
  - left. exists B0.
    split; eauto. simpl.
    destruct (dec_sub B A); eauto.
    contradiction.
  - destruct (IHsub _ _ eq_refl). destruct H0.
    assert (exists r, psub B0 B = r).
    exists (psub B0 B); eauto.
    destruct H0.
    destruct H1.
    destruct x0.
    + right. 
      simpl; eauto. rewrite H0; rewrite H1; eauto.
    + left.
      exists x.
      split; eauto.
      simpl. rewrite H0. rewrite H1.
      eauto.
    + right.
      simpl. rewrite H0. rewrite H1.
      eauto.
    + right.
      simpl. rewrite H0.
      eauto.
  - destruct (IHsub _ _ eq_refl). destruct H0.
    assert (exists r, psub A B = r).
    exists (psub A B); eauto.
    destruct H0.
    destruct H1.
    destruct x0.
    + right. 
      simpl; eauto. rewrite H0; rewrite H1; eauto.
    + left.
      exists x.
      split; eauto.
      simpl. rewrite H0. rewrite H1.
      eauto.
    + right.
      simpl. rewrite H0. rewrite H1.
      eauto.
    + right.
      simpl. rewrite H0.
      destruct (psub A B); eauto.
Defined.
