Require Import Coq.Program.Equality.
Require Import Strings.String.
Require Import Program.Tactics.
Require Import Psatz. (* lia *)
Require Import Metalib.LibTactics.
Require Import Language Tactical.

(** * Definitions *)

Inductive ordinary : type -> Prop :=
| Ord_Top : ordinary Top
| Ord_Tnt : ordinary Int
| Ord_Arrow : forall A B,
    ordinary B -> ordinary (Arr A B).

Hint Constructors ordinary : core.

Inductive splitable : type -> type -> type -> Prop :=
| Spl_And : forall A B,
    splitable (And A B) A B
| Spl_Arr : forall A B B1 B2,
    splitable B B1 B2 ->
    splitable (Arr A B) (Arr A B1) (Arr A B2).

Hint Constructors splitable : core.

Notation "A1 ↩ A ↪ A2" := (splitable A A1 A2) (at level 40).

(** * Splitable and Ordinary *)

(** splitable is not ordinary *)

Lemma splitable_not_ordinary :
  forall A A1 A2,
    splitable A A1 A2 -> ~ ordinary A.
Proof.
  introv Spl Ord. gen A1 A2.
  dependent induction Ord; intros; try solve [inversion Spl; eauto | eauto].
Qed.

(** * Automations *)

(** add this lemma to hint base to exclude absurd cases *)

Ltac solve_splitable :=
  match goal with
  | [H1: splitable ?A _ _, H2: ordinary ?A |- _] =>
      (pose proof (splitable_not_ordinary _ _ _ H1) as Contra; contradiction)
  | [H1: splitable (Arr _ ?B) _ _, H2: ordinary ?B |- _] =>
      (dependent destruction H1; pose proof (splitable_not_ordinary _ _ _ H1) as Contra; contradiction)
  | [H: splitable Int _ _ |- _] =>
      (inversion H)
  | [H: splitable Top _ _ |- _] =>
      (inversion H)
  end.

Hint Extern 5 => solve_splitable : core.

Ltac solve_ordinary :=
  match goal with
  | [H: ordinary (And _ _) |- _] =>
      (inversion H)
  end.

Hint Extern 5 => solve_ordinary : core.

(** [contra_ordinary] solves contradiction cases of ordinary *)

Ltac contra_ordinary :=
  match goal with
  | [H1: ordinary ?A, H2: not (ordinary ?A) |- _] =>
      (contradiction)
  | [H1: ordinary (Arr _ ?A), H2: not (ordinary ?A) |- _] =>
      (dependent destruction H1; contradiction)
     end.

(** * Splitable or Ordinary *)

(** For any type A, it's [ordinary] or [splitable] **)

Lemma splitable_or_ordinary :
  forall A,
    ordinary A \/ exists A1 A2, splitable A A1 A2.
Proof.
  introv. dependent induction A; eauto.
  destruct IHA1; destruct IHA2; eauto.
  - right. destruct_conjs; eauto.
  - right. destruct_conjs; eauto.
Qed.

(** * Determinism of Splitable *)

Lemma splitable_determinism :
  forall A A1 A2 A3 A4,
    splitable A A1 A2 -> splitable A A3 A4 ->
    A1 = A3 /\ A2 = A4.
Proof.
  introv Spl1 Spl2. gen A3 A4.
  dependent induction Spl1; eauto; intros.
  - dependent destruction Spl2.
    split; eauto.
  - dependent destruction Spl2.
    assert (B1 = B3 /\ B2 = B4); eauto.
    destruct_conjs. split; congruence.
Qed.

(** * Unify Splitable Varialbes *)

(** unify variables into same names *)

Ltac subst_splitable :=
  match goal with
  | [H1: splitable ?A ?A1 ?A2, H2: splitable ?A ?A3 ?A4 |- _] =>
      (pose proof (splitable_determinism _ _ _ _ _ H1 H2) as Eqs; destruct Eqs; subst; clear H1)
  end.

(** * Decidablility of Ordinary *)

Lemma ordinary_decidable :
  forall A,
    ordinary A \/ not (ordinary A).
Proof.
  introv. induction A; eauto.
  destruct IHA1; destruct IHA2; eauto.
  - right. intros Contra. contra_ordinary.
  - right. intros Contra. contra_ordinary.
Qed.

(** * Splitable & Size *)

(** If A can split into A1 and A2, the size of A1 and A2 is smaller than A *)

Lemma splitable_decrease_size:
  forall A A1 A2,
    splitable A A1 A2 -> size_type A1 < size_type A /\ size_type A2 < size_type A.
Proof.
  introv H. dependent induction H; simpl; lia.
Qed.
