(**

The motivation of top-like comes from defining disjointness for types: "Two types are disjoint if they have no common super types".
However, since we introduce [Top] to our type system, now every two types have at least one common supertype: [Top].

Situation is becoming more complicated after we introduce intersection types and its subtyping,
Top, Top & Top, Top & Top & Top ... are supertypes of all types. We need to generalize the idea of top-like types like these.

 **)

Require Import Coq.Program.Equality.
Require Import Strings.String.
Require Import Metalib.LibTactics.
Require Import Language.


(** * Definition *)

Inductive toplike : type -> Prop :=
| Tl_Top :
    toplike Top
| Tl_And : forall A B,
    toplike A ->
    toplike B ->
    toplike (And A B)
| Tl_Arr : forall A B,
    toplike B ->
    toplike (Arr A B).

Hint Constructors toplike : core.

(** * Automations *)

(** ** Structural Inversion *)

Ltac solve_toplike :=
  match goal with
  | [H: toplike Int |- _] =>
      (inversion H)
  | [H: toplike (Arr _ ?B) |- toplike ?B] =>
      (dependent destruction H; assumption)
  end.

Hint Extern 5 => solve_toplike : core.

(** ** Contradictions *)

Ltac contra_toplike :=
  match goal with
  | [H1: toplike ?A, H2: not (toplike ?A) |- _] =>
      (contradiction)
  | [H1: toplike (Arr _ ?A), H2: not (toplike ?A) |- _] =>
      (dependent destruction H1; contradiction)
  | [H1: toplike (And ?A _), H2: not (toplike ?A) |- _] =>
      (dependent destruction H1; contradiction)
  | [H1: toplike (And _ ?A), H2: not (toplike ?A) |- _] =>
      (dependent destruction H1; contradiction)
  end.

Hint Extern 5 => contra_toplike : core.

(** * Properties *)

(** ** Decidablility *)

(** For any type A, it's toplike or not toplike *)

Lemma toplike_decidable:
  forall A,
    toplike A \/ ~ toplike A.
Proof.
  intro A.
  induction A.
  - Case "Int".
    right. intro Contra. inversion Contra.
  - Case "Top".
    left. constructor.
  - Case "Arr".
    destruct IHA1; destruct IHA2; eauto;
      try solve [right; intros Contra; eauto].
  - Case "And".
    destruct IHA1; destruct IHA2; eauto;
      try solve [right; intros Contra; eauto].
Qed.
