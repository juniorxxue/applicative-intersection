Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.

Import ListNotations.

Set Printing Parentheses.

Inductive typ : Set :=
| typ_int
| typ_top
| typ_arrow (A : typ) (B : typ)
| typ_and (A : typ) (B : typ).

Hint Constructors typ : core.

Inductive trm : Set :=
| trm_top : trm
| trm_nat : nat -> trm
| trm_bvar : nat -> trm
| trm_fvar : var -> trm
| trm_abs : typ -> trm -> trm
| trm_app : trm -> trm -> trm
| trm_merge : trm -> trm -> trm
| trm_anno : trm -> typ -> trm.

Coercion trm_fvar : atom >-> trm.

Definition ctx : Set := list (var * typ).

Inductive mode := check_mode | infer_mode.

Fixpoint open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_top => trm_top
  | trm_nat n => trm_nat n
  | trm_bvar i => if k == i then u else (trm_bvar i)
  | trm_fvar x => trm_fvar x
  | trm_abs A t1 => trm_abs A (open_rec (S k) u t1)
  | trm_app t1 t2 => trm_app (open_rec k u t1) (open_rec k u t2)
  | trm_merge t1 t2 => trm_merge (open_rec k u t1) (open_rec k u t2)
  | trm_anno t1 A => trm_anno (open_rec k u t1) A
  end.

Definition open t u := open_rec 0 u t.

Inductive term : trm -> Prop :=
| term_top : term trm_top
| term_nat : forall (n : nat), term (trm_nat n)
| term_bvar : forall (n : nat), term (trm_bvar n)
| term_fvar : forall (x : var), term (trm_fvar x)
| term_abs : forall (e : trm) (L : vars) (A : typ),
    (forall x, x \notin L -> term (open e (trm_fvar x))) -> term (trm_abs A e)
| term_app : forall (e1 e2 : trm), term e1 -> term e2 -> term (trm_app e1 e2)
| term_merge : forall (e1 e2 : trm), term e1 -> term e2 -> term (trm_merge e1 e2)
| term_anno : forall (e : trm) (A : typ), term e -> term (trm_anno e A).

Hint Constructors trm : core.
Hint Constructors term : core.

Inductive pvalue : trm -> Prop :=
| pvalue_top : pvalue trm_top
| pvalue_nat : forall (n : nat), pvalue (trm_nat n)
| pvalue_abs : forall (e : trm) (A : typ), pvalue (trm_abs A e).

Inductive value : trm -> Prop :=
| value_anno : forall (A : typ) (e : trm),
    pvalue e -> value (trm_anno e A)
| value_merge : forall (v1 v2 : trm),
    value v1 -> value v2 -> value (trm_merge v1 v2).

Hint Constructors pvalue : core.
Hint Constructors value : core.

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
| sub_top_arr : forall (A B1 B2 : typ),
    sub typ_top B2 -> sub A (typ_arrow B1 B2)
| sub_arrow : forall (A B C D:typ),
    sub C A -> sub B D -> sub (typ_arrow A B) (typ_arrow C D)
| sub_and : forall (A B C:typ),
    sub A B -> sub A C -> sub A (typ_and B C)
| sub_and_l : forall (A B C:typ),
    sub A C -> sub (typ_and A B) C
| sub_and_r : forall (A B C:typ),
    sub B C -> sub (typ_and A B) C.

Hint Constructors sub : core.

Definition arg := list typ.

Fixpoint typ_stack (S : arg) (A : typ) : typ :=
  match S with
  | nil => A
  | cons A' S' => typ_arrow A' (typ_stack S' A)
  end.

(* Compute (typ_stack (cons type_int (cons type_int nil)) type_top). *)

Fixpoint next_inputs (A : typ) : list typ :=
  match A with
  | typ_top => [typ_top]
  | typ_int => [typ_int]
  | typ_arrow B C => [B]
  | typ_and B C => (next_inputs B) ++ (next_inputs C)
  end.

(* S |- A <: B *)
Inductive appsub : arg -> typ -> typ -> Prop :=
| as_refl : forall (A : typ),
    appsub nil A A
(* | as_top : forall (A : typ), *)
(*     appsub nil A typ_top *)
| as_fun : forall (C A B D : typ) (S : arg),
    sub C A ->
    appsub S B D ->
    appsub (cons C S) (typ_arrow A B) (typ_arrow C D)
| as_and_l : forall (A B C D: typ) (S : arg),
    appsub (cons C S) A D ->
    (* not (In C (next_inputs B)) -> *)
    (* forall (E : typ), not (sub B (typ_stack S E)) -> *)
    not (sub B D) ->
    (* not (appsub (cons C S) B D) -> *)
    (* appsub (cons C S) B D -> *)
    appsub (cons C S) (typ_and A B) D
| as_and_r : forall (A B C D: typ) (S : arg),
    appsub (cons C S) B D ->
    (* not (In C (next_inputs A)) -> *)
    (* not (exists E, A = (typ_stack (cons C S) E)) -> *)
    not (sub A D) ->
    appsub (cons C S) (typ_and A B) D.

Hint Constructors appsub : core.

Inductive typedred : trm -> typ -> trm -> Prop :=
| tred_int : forall (n : nat),
    typedred (trm_anno (trm_nat n) typ_int) typ_int (trm_anno (trm_nat n) typ_int)
| tred_top : forall (A : typ) (v : trm),
    toplike A -> ordinary A ->
    typedred v A (trm_anno trm_top A)
| tred_arrow_anno : forall (A B C D E : typ) (e : trm),
    not (toplike D) -> sub C A -> sub B D ->
    typedred (trm_anno (trm_abs E e) (typ_arrow A B))
             (typ_arrow C D)
             (trm_anno (trm_abs E e) (typ_arrow C D))
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

Definition consistency_spec e1 e2 :=
  forall (A : typ) (e1' e2' : trm), typedred e1 A e1' -> typedred e2 A e2' -> e1' = e2'.

Inductive disjoint : typ -> typ -> Prop :=
| dj_top_l : forall (A : typ), disjoint typ_top A
| dj_top_r : forall (A : typ), disjoint A typ_top
| dj_and_l : forall (A1 A2 B : typ), disjoint A1 B -> disjoint A2 B -> disjoint (typ_and A1 A2) B
| dj_and_r : forall (A B1 B2 : typ), disjoint A B1 -> disjoint A B2 -> disjoint A (typ_and B1 B2)
| dj_int_arr : forall (A1 A2 : typ), disjoint typ_int (typ_arrow A1 A2)
| dj_arr_int : forall (A1 A2 : typ), disjoint (typ_arrow A1 A2) typ_int
| dj_arr_arr : forall (A1 A2 B1 B2 : typ), disjoint B1 B2 -> disjoint (typ_arrow A1 B1) (typ_arrow A2 B2).

Hint Constructors disjoint : core.

(* int -> bool, int -> int is disjoint *)

Definition disjoint_spec A B :=
  forall (C : typ), sub A C -> sub B C -> toplike C.

Inductive typing : ctx -> arg -> mode -> trm -> typ -> Prop :=
| typing_int : forall (T: ctx) (n : nat),
    uniq T -> (typing T nil infer_mode (trm_nat n) typ_int)
| typing_top : forall (T : ctx),
    typing T nil infer_mode trm_top typ_top
| typing_var : forall (T : ctx) (x : var) (A : typ),
    uniq T -> binds x A T -> typing T nil infer_mode (trm_fvar x) A
| typing_abs : forall (L : vars) (T : ctx) (S : arg) (A B C D : typ) (e : trm),
    (forall x, x \notin L -> (typing ((x ~ A) ++ T)) S check_mode (open e (trm_fvar x)) B) ->
    sub (typ_arrow A B) D ->
    typing T (cons C S) check_mode (trm_anno (trm_abs A e) (typ_arrow A B)) D
| typing_anno : forall (T : ctx) (S : arg) (A B : typ) (e : trm),
    appsub S A B -> typing T nil check_mode e A ->
    typing T S infer_mode (trm_anno e A) B
| typing_app1 : forall (T : ctx) (S : arg) (A B : typ) (e1 e2 : trm),
    typing T nil infer_mode e2 A ->
    typing T (cons A S) infer_mode e1 (typ_arrow A B) ->
    typing T S infer_mode (trm_app e1 e2) B
| typing_app2 : forall (T : ctx) (A B : typ) (e1 e2 : trm),
    typing T nil infer_mode e2 A ->
    typing T nil check_mode e1 (typ_arrow A B) ->
    typing T nil check_mode (trm_app e1 e2) B
| typing_sub : forall (T : ctx) (A B : typ) (e : trm),
    typing T nil infer_mode e B ->
    (sub B A) ->
    typing T nil check_mode e A
| typing_merge : forall (T : ctx) (A B : typ) (e1 e2 : trm),
    disjoint_spec A B ->
    typing T nil infer_mode e1 A ->
    typing T nil infer_mode e2 B ->
    typing T nil infer_mode (trm_merge e1 e2) (typ_and A B)
| typing_merge_value : forall (T : ctx) (A B : typ) (v1 v2 : trm),
    value v1 -> value v2 ->
    typing nil nil infer_mode v1 A ->
    typing nil nil infer_mode v2 B ->
    consistency_spec v1 v2 ->
    typing T nil infer_mode (trm_merge v1 v2) (typ_and A B)
| typing_merge_pick : forall (T : ctx) (S : arg) (A B C : typ) (e1 e2 : trm),
    typing T S infer_mode (trm_merge e1 e2) B ->
    appsub (cons A S) B C ->
    typing T (cons A S) infer_mode (trm_merge e1 e2) C.

Hint Constructors typing : core.

Parameter Y : atom.

Inductive ptype : trm -> typ -> Prop :=
| ptype_int : forall (n : nat),
    ptype (trm_nat n) typ_int
| ptype_top :
    ptype trm_top typ_top
| ptype_anno : forall (e : trm) (A : typ),
    ptype (trm_anno e A) A
| ptype_merge : forall (e1 e2 : trm) (A B : typ),
    ptype e1 A ->
    ptype e2 B ->
    ptype (trm_merge e1 e2) (typ_and A B).

Inductive papp : trm -> trm -> trm -> Prop :=
| papp_top : forall (p vl : trm) (A : typ),
    toplike A ->
    pvalue p ->
    papp (trm_anno p A) vl (trm_anno trm_top typ_top)
| papp_abs_anno : forall (A B C : typ) (e v v' : trm),
    typedred v A v' ->
    not (toplike B) ->
    papp (trm_anno (trm_abs C e) (typ_arrow A B)) v
         (trm_anno (open e v') B)
| papp_merge_l : forall (A B C : typ) (v1 v2 v vl e : trm),
    ptype v1 A -> ptype vl B -> ptype (trm_merge v1 v2) C ->
    appsub (cons B nil) C A ->
    papp v1 vl e ->
    papp (trm_merge v1 v2) vl e
| papp_merge_r : forall (A B C : typ) (v1 v2 v vl e : trm),
    ptype v2 A -> ptype vl B -> ptype (trm_merge v1 v2) C ->
    appsub (cons B nil) C A ->
    papp v2 vl e ->
    papp (trm_merge v1 v2) vl e.

Inductive step : trm -> trm -> Prop :=
| step_int_anno : forall (n : nat),
    step (trm_nat n) (trm_anno (trm_nat n) typ_int)
| step_top_anno :
    step trm_top (trm_anno trm_top typ_top)
| step_papp : forall (v vl e : trm),
    value v -> value vl ->
    papp v vl e ->
    step (trm_app v vl) e
| step_anno_value : forall (v v' : trm) (A : typ),
    value v -> typedred v A v' ->
    step (trm_anno v A) v'
| step_anno : forall (e e' : trm) (A : typ),
    not (value (trm_anno e A)) ->
    step e e' -> step (trm_anno e A) (trm_anno e' A)
| step_app_l : forall (e1 e2 e1' : trm),
    step e1 e1' -> step (trm_app e1 e2) (trm_app e1' e2)
| step_app_v : forall (v e2 e2' : trm),
    value v -> step e2 e2' -> step (trm_app v e2) (trm_app v e2')
| step_merge_l : forall (e1 e2 e1' : trm),
    step e1 e1' ->
    step (trm_merge e1 e2) (trm_merge e1' e2)
| step_merge_r : forall (v e2 e2' : trm),
    value v -> step e2 e2' ->
    step (trm_merge v e2) (trm_merge v e2').

Hint Constructors step : core.
