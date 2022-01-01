Require Import Coq.Program.Equality.
Require Import Language.
Require Import Value.

(** * Definition *)

Inductive ptype : term -> type -> Prop :=
| Pt_Int : forall (n : nat),
    ptype (Lit n) Int
| Pt_Arr : forall (e : term) (A B : type),
    lc (Lam A e B) ->
    ptype (Lam A e B) (Arr A B)
| Pt_Ann : forall (e : term) (A : type),
    lc e ->
    ptype (Ann e A) A
| Pt_Mrg : forall (e1 e2 : term) (A B : type),
    ptype e1 A ->
    ptype e2 B ->
    ptype (Mrg e1 e2) (And A B).

Hint Constructors ptype : core.

(** * Properties *)

(** ** Determinism *)

Lemma ptype_determinism :
  forall e A B,
    ptype e A -> ptype e B ->
    A = B.
Proof.
  intros * Pt1 Pt2. generalize dependent B.
  induction Pt1; eauto; intros;
    try solve [dependent destruction Pt2; eauto].
  - dependent destruction Pt2; eauto.
    pose proof (IHPt1_1 _ Pt2_1).
    pose proof (IHPt1_2 _ Pt2_2).
    congruence.
Qed.

(** unify ptype varialbes *)

Ltac subst_ptype :=
  match goal with
  | [H1: ptype ?v ?A1, H2: ptype ?v ?A2 |- _] =>
      (pose proof (ptype_determinism _ _ _ H1 H2) as Eqs; subst; clear H2)
  end.