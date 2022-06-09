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
| And : type -> type -> type.

Hint Constructors type : core.

(** Notation is only used for prettifying goals, we never explicity write customized notation *)

Notation "A → B" := (Arr A B) (at level 20).
Notation "A & B" := (And A B) (at level 20).

(** coerce atom x to (Fvar x) *)

(** * Size of types *)

(** [size_type] and [size_term] are defined for more powerful induction principle: induction on size *)

Fixpoint size_type (A : type) {struct A} : nat :=
  match A with
  | Int => 1
  | Top => 1
  | Arr A B => 1 + (size_type A) + (size_type B)
  | And A B => 1 + (size_type A) + (size_type B)
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
