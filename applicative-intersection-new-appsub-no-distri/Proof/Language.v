Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.

Import ListNotations.

Set Printing Parentheses.

Inductive typ : Set :=
| typ_int : typ
| typ_top : typ
| typ_arrow : typ -> typ -> typ
| typ_and : typ -> typ -> typ.

Hint Constructors typ : core.

Notation "A → B" := (typ_arrow A B) (at level 20).
Notation "A & B" := (typ_and A B) (at level 20).

Inductive trm : Set :=
| trm_int : nat -> trm
| trm_bvar : nat -> trm
| trm_fvar : var -> trm
| trm_abs : trm -> typ -> typ -> trm
| trm_app : trm -> trm -> trm
| trm_merge : trm -> trm -> trm
| trm_anno : trm -> typ -> trm.

Hint Constructors trm : core.

Notation "e ∷ A" := (trm_anno e A) (at level 20).
Notation "ƛ. e ∷ A → B" := (trm_abs e A B) (at level 20).

Coercion trm_fvar : atom >-> trm.

Definition ctx : Set := list (var * typ).

Fixpoint open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_int n => trm_int n
  | trm_bvar i => if k == i then u else (trm_bvar i)
  | trm_fvar x => trm_fvar x
  | trm_abs t1 A B => trm_abs (open_rec (S k) u t1) A B
  | trm_app t1 t2 => trm_app (open_rec k u t1) (open_rec k u t2)
  | trm_merge t1 t2 => trm_merge (open_rec k u t1) (open_rec k u t2)
  | trm_anno t1 A => trm_anno (open_rec k u t1) A
  end.

Definition open t u := open_rec 0 u t.

Inductive pvalue : trm -> Prop :=
| pvalue_nat : forall (n : nat), pvalue (trm_int n)
| pvalue_abs : forall (e : trm) (A B : typ), pvalue (trm_abs e A B).

Inductive value : trm -> Prop :=
| value_anno : forall (A : typ) (e : trm),
    pvalue e -> value (trm_anno e A)
| value_merge : forall (v1 v2 : trm),
    value v1 -> value v2 -> value (trm_merge v1 v2).

Inductive rvalue : trm -> Prop :=
| rvalue_v : forall (v : trm),
    value v -> rvalue v
| rvalue_apps : forall (v r : trm),
    rvalue r -> value v -> rvalue (trm_app r v).

Hint Constructors pvalue : core.
Hint Constructors value : core.
Hint Constructors rvalue : core.

Inductive toplike : typ -> Prop :=
| tl_top : toplike typ_top
| tl_and : forall (A B : typ), toplike A -> toplike B -> toplike (typ_and A B)
| tl_arrow : forall (A B : typ), toplike B -> toplike (typ_arrow A B).

Hint Constructors toplike : core.

Inductive ordinary : typ -> Prop :=
| ord_top : ordinary typ_top
| ord_int : ordinary typ_int
| ord_arrow : forall (A B : typ), ordinary (typ_arrow A B).

Hint Constructors ordinary : core.

Inductive sub : typ -> typ -> Prop :=
| sub_int :
    sub typ_int typ_int
| sub_top : forall (A:typ),
    sub A typ_top
| sub_top_arr : forall (A B C : typ),
    sub typ_top C -> sub A (typ_arrow B C)
| sub_arrow : forall (A B C D:typ),
    sub C A -> sub B D -> sub (typ_arrow A B) (typ_arrow C D)
| sub_and : forall (A B C:typ),
    sub A B -> sub A C -> sub A (typ_and B C)
| sub_and_l : forall (A B C:typ),
    sub A C -> sub (typ_and A B) C
| sub_and_r : forall (A B C:typ),
    sub B C -> sub (typ_and A B) C.

Hint Constructors sub : core.

Notation "A <: B" := (sub A B) (at level 40).

Definition arg := list typ.
Definition argv := list trm.

Inductive auxas : arg -> typ -> Prop :=
| aas_refl : forall (A : typ),
    auxas nil A
| aas_fun : forall (A B C : typ) (S : arg),
    sub C A ->
    auxas S B ->
    auxas (cons C S) (typ_arrow A B)
| aas_and_l : forall (A B C : typ) (S : arg),
    auxas (cons C S) A ->
    auxas (cons C S) (typ_and A B)
| aas_and_r : forall (A B C : typ) (S : arg),
    auxas (cons C S) B ->
    auxas (cons C S) (typ_and A B).

Inductive appsub : arg -> typ -> typ -> Prop :=
| as_refl : forall (A : typ),
    appsub nil A A
| as_fun : forall (A B C D : typ) (S : arg),
    sub C A ->
    appsub S B D ->
    appsub (cons C S) (typ_arrow A B) (typ_arrow C D)
| as_and_l : forall (A B C D: typ) (S : arg),
    appsub (cons C S) A D ->
    not (auxas (cons C S) B) ->
    appsub (cons C S) (typ_and A B) D
| as_and_r : forall (A B C D : typ) (S : arg),
    appsub (cons C S) B D ->
    not (auxas (cons C S) A) ->
    appsub (cons C S) (typ_and A B) D
| as_and_both : forall (A B C D1 D2: typ) (S : arg),
    appsub (cons C S) A D1 ->
    appsub (cons C S) B D2 ->
    appsub (cons C S) (typ_and A B) (typ_and D1 D2).

Hint Constructors auxas : core.
Hint Constructors appsub : core.

Notation "S ⊢ A <: B" := (appsub S A B) (at level 40).
Notation "appsub? S A" := (auxas S A) (at level 40).

Definition disjoint_spec A B :=
  forall (C : typ), sub A C -> sub B C -> toplike C.

Inductive disjoint : typ -> typ -> Prop :=
| disj_top_l : forall (A : typ),
    disjoint typ_top A
| disj_top_r : forall (A : typ),
    disjoint A typ_top
| disjoint_and_l : forall (A1 A2 B : typ),
    disjoint A1 B -> disjoint A2 B ->
    disjoint (typ_and A1 A2) B
| disjoint_and_r : forall (A B1 B2 : typ),
    disjoint A B1 -> disjoint A B2 ->
    disjoint A (typ_and B1 B2)
| disjoint_int_arr : forall (A1 A2 : typ),
    disjoint typ_int (typ_arrow A1 A2)
| disjoint_arr_int : forall (A1 A2 : typ),
    disjoint (typ_arrow A1 A2) typ_int
| disjoint_arr_arr : forall (A1 A2 B1 B2 : typ),
    disjoint B1 B2 ->
    disjoint (typ_arrow A1 B1) (typ_arrow A2 B2).

Hint Constructors disjoint : core.

Inductive typedred : trm -> typ -> trm -> Prop :=
| tred_int_anno : forall (n : nat) (A : typ),
    sub A typ_int ->
    typedred (trm_anno (trm_int n) A) typ_int (trm_anno (trm_int n) typ_int)
| tred_top : forall (A : typ) (v : trm),
    toplike A -> ordinary A ->
    typedred v A (trm_anno (trm_int 1) A)
| tred_arrow_anno : forall (A B C D E : typ) (e : trm),
    not (toplike D) -> sub E (typ_arrow C D) ->
    typedred (trm_anno (trm_abs e A B) E)
             (typ_arrow C D)
             (trm_anno (trm_abs e A B) (typ_arrow C D))
| tred_merge_l : forall (v1 v2 v1': trm) (A : typ),
    typedred v1 A v1' -> ordinary A ->
    typedred (trm_merge v1 v2) A v1'
| tred_merge_r : forall (v1 v2 v2': trm) (A : typ),
    typedred v2 A v2' -> ordinary A ->
    typedred (trm_merge v1 v2) A v2'
| tred_and : forall (v1 v2 v : trm) (A B : typ),
    typedred v A v1 ->
    typedred v B v2 ->
    typedred v (typ_and A B) (trm_merge v1 v2).

Hint Constructors typedred : core.

Notation "e ~->> A e'" := (typedred e A e') (at level 68).

Definition consistency_spec e1 e2 :=
  forall (A : typ) (e1' e2' : trm), typedred e1 A e1' -> typedred e2 A e2' -> e1' = e2'.

Inductive typing : ctx -> arg -> trm -> typ -> Prop :=
| typing_int : forall (T : ctx) (n : nat),
    uniq T -> typing T nil (trm_int n) typ_int
| typing_var : forall (T : ctx) (x : var) (A : typ),
    uniq T -> binds x A T -> typing T nil (trm_fvar x) A
| typing_var_stack : forall (T : ctx) (x : var) (S : arg) (A B : typ),
    uniq T -> binds x A T -> appsub S A B ->
    typing T S (trm_fvar x) B
| typing_lam1 : forall (L : vars) (T : ctx) (A B : typ) (e : trm),
    (forall x, x \notin L -> (typing ((x ~ A) ++ T)) nil (open e (trm_fvar x)) B) ->
    typing T nil (trm_abs e A B) (typ_arrow A B)
| typing_lam2 : forall (L : vars) (S : arg) (T : ctx) (A B C D : typ) (e : trm),
    (forall x, x \notin L -> (typing ((x ~ A) ++ T)) nil (open e (trm_fvar x)) B) ->
    appsub (cons C S) (typ_arrow A B) D ->
    typing T (cons C S) (trm_abs e A B) D
| typing_anno : forall (S : arg) (T : ctx) (A B C : typ) (e : trm),
    typing T nil e C -> sub C A -> appsub S A B ->
    typing T S (trm_anno e A) B
| typing_app : forall (S : arg) (T : ctx) (A B : typ) (e1 e2 : trm),
    typing T nil e2 A ->
    typing T (cons A S) e1 (typ_arrow A B) ->
    typing T S (trm_app e1 e2) B
| typing_merge : forall (T : ctx) (A B : typ) (e1 e2 : trm),
    disjoint_spec A B ->
    typing T nil e1 A ->
    typing T nil e2 B ->
    typing T nil (trm_merge e1 e2) (typ_and A B)
| typing_merge_value : forall (T : ctx) (A B : typ) (v1 v2 : trm),
    value v1 -> value v2 ->
    consistency_spec v1 v2 ->
    typing nil nil v1 A ->
    typing nil nil v2 B ->
    typing T nil (trm_merge v1 v2) (typ_and A B)
(* | typing_merge_pick : forall (T : ctx) (S : arg) (A B C D : typ) (e1 e2 : trm), *)
(*     typing T nil (trm_merge e1 e2) (typ_and A B) -> *)
(*     appsub (cons C S) (typ_and A B) D -> *)
(*     typing T (cons C S) (trm_merge e1 e2) D. *)
| typing_merge_pick_l : forall (T : ctx) (S : arg) (A B C : typ) (e1 e2 : trm),
    disjoint_spec C B ->
    typing T (cons A S) e1 C ->
    typing T nil e2 B ->
    not (auxas (cons A S) B) ->
    typing T (cons A S) (trm_merge e1 e2) C
| typing_merge_pick_r : forall (T : ctx) (S : arg) (A B C : typ) (e1 e2 : trm),
    disjoint_spec B C ->
    typing T (cons A S) e2 C ->
    typing T nil e1 B ->
    not (auxas (cons A S) B) ->
    typing T (cons A S) (trm_merge e1 e2) C.

Hint Constructors typing : core.

Notation "T S ⊢ e ⇒ A" := (typing T S e A) (at level 50).

Inductive ptype : trm -> typ -> Prop :=
| ptype_anno : forall (e : trm) (A : typ),
    ptype (trm_anno e A) A
| ptype_merge : forall (e1 e2 : trm) (A B : typ),
    ptype e1 A ->
    ptype e2 B ->
    ptype (trm_merge e1 e2) (typ_and A B).

Inductive ptypes : argv -> arg -> Prop :=
| ptypes_empty :
    ptypes nil nil
| ptypes_cons : forall (L : argv) (S : arg) (v : trm) (A : typ),
    ptypes L S ->
    ptype v A ->
    ptypes (cons v L) (cons A S).

Hint Constructors ptype : core.
Hint Constructors ptypes : core.

Inductive auxast : argv -> trm -> Prop :=
| auxast_refl : forall (v : trm),
    auxast nil v
| auxast_fun : forall (v e : trm) (S : arg) (L : argv) (A B C D: typ),
    ptypes (cons v L) S ->
    auxas S (typ_arrow C D) ->
    auxast (cons v L) (trm_anno (trm_abs e A B) (typ_arrow C D))
| auxast_l : forall (L : argv) (v1 v2 v : trm),
    auxast (cons v L) v1 ->
    auxast (cons v L) (trm_merge v1 v2)
| auxast_r : forall (L : argv) (v1 v2 v : trm),
    auxast (cons v L) v2 ->
    auxast (cons v L) (trm_merge v1 v2).

Hint Constructors auxast : core.

Notation "appsubt? L v" := (auxast L v) (at level 40).

Inductive papp : argv -> trm -> trm -> trm -> Prop :=
| papp_top : forall (v vl : trm) (A : typ),
    ptype v A ->
    toplike A ->
    papp nil v vl (trm_anno (trm_int 1) A)
| papp_abs_anno : forall (A B C D E : typ) (e v v' : trm) (L : argv),
    typedred v C v' ->
    not (toplike D) ->
    auxast (cons v L) (trm_anno (trm_abs e A B) (typ_arrow C D)) ->
    papp L (trm_anno (trm_abs e A B) (typ_arrow C D)) v
         (trm_anno (open e v') D)
| papp_pick_l : forall (A B C : typ) (v1 v2 v' v e: trm) (L : argv) ,
    ptype v1 A -> ptype v2 B ->
    not (toplike (typ_and A B)) ->
    not (auxast (cons v L) v2) ->
    papp L v1 v e ->
    papp L (trm_merge v1 v2) v e
| papp_pick_r : forall (A B C : typ) (v1 v2 v' v e: trm) (L : argv) ,
    ptype v1 A -> ptype v2 B ->
    not (toplike (typ_and A B)) ->
    not (auxast (cons v L) v1) ->
    papp L v2 v e ->
    papp L (trm_merge v1 v2) v e
| papp_collect : forall (r v1 v2 e : trm) (L : argv),
    papp (cons v2 L) r v1 e ->
    papp L (trm_app r v1) v2 e.

Hint Constructors papp : core.

Notation "L ⊢ r ◐ v ~-> e" := (papp L r v e) (at level 69).

Inductive step : trm -> trm -> Prop :=
| step_int_anno : forall (n : nat),
    step (trm_int n) (trm_anno (trm_int n) typ_int)
| step_abs_anno : forall (e : trm) (A B : typ),
    step (trm_abs e A B) (trm_anno (trm_abs e A B) (typ_arrow A B))
| step_papp : forall (r v e : trm),
    rvalue r -> value v ->
    papp nil r v e ->
    step (trm_app r v) e
| step_anno_value : forall (v v' : trm) (A : typ),
    value v -> typedred v A v' ->
    step (trm_anno v A) v'
| step_anno : forall (e e' : trm) (A : typ),
    not (value (trm_anno e A)) ->
    step e e' -> step (trm_anno e A) (trm_anno e' A)
| step_app_l : forall (e1 e2 e1' : trm),
    step e1 e1' -> step (trm_app e1 e2) (trm_app e1' e2)
| step_app_r : forall (r e2 e2' : trm),
    rvalue r -> step e2 e2' -> step (trm_app r e2) (trm_app r e2')
| step_merge_l : forall (e1 e2 e1' : trm),
    step e1 e1' ->
    step (trm_merge e1 e2) (trm_merge e1' e2)
| step_merge_r : forall (v e2 e2' : trm),
    value v -> step e2 e2' ->
    step (trm_merge v e2) (trm_merge v e2').

Hint Constructors step : core.
Notation "e ~-> e'" := (step e e') (at level 68).
