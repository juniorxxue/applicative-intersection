Require Import Language.

Notation "e ∷ A" := (trm_anno e A) (at level 20).

Notation "A → B" := (typ_arrow A B) (at level 20).
Notation "A & B" := (typ_and A B) (at level 20).
(* Notation "⌉ A ⌈" := (toplike A) (at level 30). *)

(* Notation "( e : A )" := (trm_anno e A) (at level 20). *)
(* Notation "( a  ,, b )" := (trm_merge a b) (at level 20). *)

Notation "A <: B" := (sub A B) (at level 40).
Notation "S ⤞ A" := (typ_stack S A) (at level 40).
Notation "S ⊢ A <: B" := (appsub S A B) (at level 40).
Notation "e ~->> A e'" := (typedred e A e') (at level 68).

Notation "T S ⊢ e ⇒ A" := (typing T S infer_mode e A) (at level 50).
Notation "T S ⊢ e ⇐ A" := (typing T S check_mode e A) (at level 50).

Notation "e ~-> e'" := (step e e') (at level 68).
