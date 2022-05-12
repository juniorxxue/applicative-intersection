(** This file is syntax of Applicative Intersection Types, which is a extension of "Disjoint Intersection Types"

What makes this calculus different from classical simply typed lambda calculus

- It has intersection types
- It has merge operator (create inhabitants of intersection types)
- It has subtyping (BCD-style: allow distribuivity upon function types and intersection types)
- It's type safe: we will prove determinism, preservation and progress
- Enhanced subtyping algorithms can solve overloading problems

 *)

Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Coq.Strings.String.
Require Import Tactical.

Import ListNotations.

Set Printing Parentheses.

(** * Types

[type] is:

- [Int] is integer type
- [Top] is top type (supertype of all types)
- [Arr] is function type
- [And] is intersection type

*)

Definition label := nat.

Inductive type : Set :=
| Int : type
| Top : type          
| Arr : type -> type -> type
| And : type -> type -> type
| Rcd : label -> type -> type.

Hint Constructors type : core.

(** Notation is only used for prettifying goals, we never explicity write customized notation *)

Notation "A → B" := (Arr A B) (at level 20).
Notation "A & B" := (And A B) (at level 20).
Notation "{ l : A }" := (Rcd l A) (at level 20).

(** * Terms

[term] is :

- [Lit] for integers: 1, 2, 3 ...
- [Bvar] and [Fvar] for binded variables and free variables in locally nameless representation
- [Lam] for lambda: \x: A. e : B
- [App] for application: e1 e2
- [Mrg] for merge operator, which creates inhabitants of intersection types: e1 ,, e2
- [Ann] for annotated terms: e : A

*)

Inductive term : Set :=
| Lit : nat -> term
| Bvar : nat -> term
| Fvar : var -> term
| Lam : type -> term -> type -> term
| App : term -> term -> term
| Mrg : term -> term -> term
| Ann : term -> type -> term
| Fld : label -> term -> term
| Prj : term -> label -> term.

Hint Constructors term : core.

Notation "e ∷ A" := (Ann e A) (at level 20).
Notation "ƛ A . e : B" := (Lam A e B) (at level 20).
Notation "{ l = e }" := (Fld l e) (at level 20).
Notation "e ◍ l" := (Prj e l) (at level 20).

(** coerce atom x to (Fvar x) *)

Check (Prj (Fld 1 (Lit 1)) 1).

Coercion Fvar : atom >-> term.

(** * Size of types and terms *)

(** [size_type] and [size_term] are defined for more powerful induction principle: induction on size *)

Fixpoint size_type (A : type) {struct A} : nat :=
  match A with
  | Int => 1
  | Top => 1
  | Arr A B => 1 + (size_type A) + (size_type B)
  | And A B => 1 + (size_type A) + (size_type B)
  | Rcd l A => 1 + (size_type A)
  end.

Fixpoint size_term (e : term) {struct e} : nat :=
  match e with
  | Lit n => 1
  | Bvar n => 1
  | Fvar x => 1
  | Lam A e B => 1 + (size_type A) + (size_term e) + (size_type B)
  | App e1 e2 => 1 + (size_term e1) + (size_term e2)
  | Mrg e1 e2 => 1 + (size_term e1) + (size_term e2)
  | Ann e A => 1 + (size_term e) + (size_type A)
  | Fld l e => 1 + (size_term e)
  | Prj e l => 1 + (size_term e)
  end.

(** induction on size *)

Ltac ind_type_size s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with
         | [ h : type |- _ ] => (gen h)
         end;
  induction i as [|i IH]; [
      intros; match goal with
              | [ H : _ < 0 |- _ ] => (dependent destruction H)
              end
    | intros ].

(** * Substituion *)

Fixpoint substitution (z : atom) (u : term) (e : term) {struct e} : term :=
  match e with
  | Lit n => Lit n
  | Bvar i => Bvar i
  | Fvar x => if x == z then u else (Fvar x)
  | Lam A e B => Lam A (substitution z u e) B
  | App e1 e2 => App (substitution z u e1) (substitution z u e2)
  | Mrg e1 e2 => Mrg (substitution z u e1) (substitution z u e2)
  | Ann e A => Ann (substitution z u e) A
  | Fld l e => Fld l (substitution z u e)
  | Prj e l => Prj (substitution z u e) l
  end.

Notation "{ z ↦ u } e" := (substitution z u e) (at level 69).

(** * Free variables *)

Fixpoint fv (e : term) {struct e} : atoms :=
  match e with
  | Lit n => empty
  | Bvar i => empty
  | Fvar x => singleton x
  | Lam A e B => fv e
  | App e1 e2 => (fv e1) `union` (fv e2)
  | Mrg e1 e2 => (fv e1) `union` (fv e2)
  | Ann e A => fv e
  | Fld l e => fv e
  | Prj e l => fv e
  end.

(** * Context *)

Definition ctx : Set := list (var * type).

(** * Opening *)

Fixpoint open_rec (k : nat) (u : term) (e : term) {struct e} : term :=
  match e with
  | Lit n => Lit n
  | Bvar i => if k == i then u else (Bvar i)
  | Fvar x => Fvar x
  | Lam A e B => Lam A (open_rec (S k) u e) B
  | App e1 e2 => App (open_rec k u e1) (open_rec k u e2)
  | Mrg e1 e2 => Mrg (open_rec k u e1) (open_rec k u e2)
  | Ann e A => Ann (open_rec k u e) A
  | Fld l e => Fld l (open_rec k u e)
  | Prj e l => Prj (open_rec k u e) l
  end.

Definition open e u := open_rec 0 u e.

(** Auxiliary functions for building contexts automatically *)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (atom * type) => dom x) in
  let D := gather_atoms_with (fun x : term => fv x) in
  constr:(A `union` B `union` C `union` D).
