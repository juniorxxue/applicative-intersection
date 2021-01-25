Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.

Inductive typ : Set :=
| typ_int
| typ_top
| typ_arrow (A:typ) (B:typ)
| typ_and (A:typ) (B:typ).

Hint Constructors typ : core.

Inductive trm : Set :=
| trm_top : trm
| trm_nat : nat -> trm
| trm_bvar : nat -> trm
| trm_fvar : var -> trm
| trm_abs : trm -> trm
| trm_app : trm -> trm -> trm
| trm_merge : trm -> trm -> trm
| trm_anno : trm -> typ -> trm.

(* term is locally closed *)

Definition ctx : Set := list (var * typ).

Inductive mode := check_mode | infer_mode.

Fixpoint open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_top => trm_top
  | trm_nat n => trm_nat n
  | trm_bvar i => if k == i then u else (trm_bvar i)
  | trm_fvar x => trm_fvar x
  | trm_abs t1 => trm_abs (open_rec (S k) u t1)
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
| term_abs : forall (e : trm) (L : vars),
    (forall x, x \notin L -> term (open e (trm_fvar x))) -> term (trm_abs e)
| term_app : forall (e1 e2 : trm), term e1 -> term e2 -> term (trm_app e1 e2)
| term_merge : forall (e1 e2 : trm), term e1 -> term e2 -> term (trm_merge e1 e2)
| term_anno : forall (e : trm) (A : typ), term e -> term (trm_anno e A).

Hint Constructors trm : core.
Hint Constructors term : core.

Inductive value : trm -> Prop :=
| value_top : value trm_top
| value_nat : forall (n : nat), value (trm_nat n)
| value_abs : forall (e : trm),
    term (trm_abs e) -> value (trm_abs e)
| value_merge : forall (e1 e2 : trm),
    value e1 -> value e2 -> value (trm_merge e1 e2).

Hint Constructors value : core.

Inductive toplike : typ -> Prop :=
| tl_top : toplike typ_top
| tl_and : forall (A B : typ), toplike A -> toplike B -> toplike (typ_and A B)
| tl_arrow : forall (A B : typ), toplike B -> toplike (typ_arrow A B).

Hint Constructors toplike : core.

(* ordinary types are those types aren't intersection *)
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

(* S |- A <: B *)
Inductive appsub : arg -> typ -> typ -> Prop :=
| as_refl : forall (A : typ),
    appsub nil A A
| as_top : forall (A : typ),
    appsub nil A typ_top
| as_fun : forall (C A B D : typ) (S : arg),
    sub C A ->
    appsub S B D ->
    appsub (cons C S) (typ_arrow A B) (typ_arrow C D)
| as_and_l : forall (A B D: typ) (S : arg),
    appsub S A D ->
    not (sub B (typ_stack S typ_top)) ->
    appsub S (typ_and A B) D
| as_and_r : forall (A B D: typ) (S : arg),
    appsub S B D ->
    not (sub A (typ_stack S typ_top)) ->
    appsub S (typ_and A B) D.

Hint Constructors appsub : core.

Inductive typedred : trm -> typ -> trm -> Prop :=
| tred_int : forall (n : nat),
    typedred (trm_nat n) typ_int (trm_nat n)
| tred_top : forall (A : typ) (e : trm),
    term e -> toplike A -> ordinary A -> typedred e A trm_top
| tred_arrow_anno : forall (A B C D : typ) (e : trm), (* A -> B <: C -> D *)
    term (trm_abs e) -> not (toplike D) -> sub C A -> sub B D ->
    typedred (trm_anno (trm_abs e) (typ_arrow A B))
             (typ_arrow C D)
             (trm_anno (trm_abs e) (typ_arrow A D))
| tred_merge_l : forall (e1 e1' e2 : trm) (A : typ),
    term e2 -> typedred e1 A e1' -> ordinary A -> typedred (trm_merge e1 e2) A e1'
| tred_merge_r : forall (e1 e2 e2' : trm) (A : typ),
    term e1 -> typedred e2 A e2' -> ordinary A -> typedred (trm_merge e1 e2) A e2'
| tred_and : forall (e1 e2 e3 : trm) (A B: typ),
    typedred e1 A e2 -> typedred e1 B e3 -> typedred e1 (typ_and A B) (trm_merge e2 e3).

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
| typing_abs1 : forall (L : vars) (T : ctx) (e : trm) (A B : typ),
    (forall x, x \notin L -> (typing ((x ~ A) ++ T)) nil check_mode (open e (trm_fvar x)) B) ->
    typing T nil check_mode (trm_abs e) (typ_arrow A B)
| typing_abs2 : forall (L: vars) (T : ctx) (S : arg) (A B : typ) (e : trm),
    (forall x, x \notin L -> (typing ((x ~ A) ++ T)) S infer_mode (open e (trm_fvar x)) B) ->
    typing T (cons A S) infer_mode (trm_abs e) (typ_arrow A B)
| typing_anno : forall (T : ctx) (S : arg) (A B : typ) (e : trm),
    appsub S A B -> typing T nil check_mode e A ->
    typing T S infer_mode (trm_anno e A) B
| typing_app1 : forall (T : ctx) (S : arg) (A B : typ) (e1 e2 : trm),
    typing T nil infer_mode e2 A ->
    typing T nil check_mode e1 (typ_arrow A B) ->
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
    typing T nil infer_mode (trm_merge e1 e2) (typ_and A B).

Hint Constructors typing : core.

Parameter Y : atom.
Compute (open (trm_abs (trm_bvar 0)) (trm_fvar Y)).

Inductive step : trm -> trm -> Prop :=
| step_top : forall (e : trm),
    value e -> step (trm_app trm_top e) trm_top
| step_beta : forall (e1 e2 e2' : trm) (A B : typ),
    term (trm_abs e1) -> value e2 -> typered e2 A e2' ->
    step (trm_app (trm_abs e1) e2) (open e1 e2')
| step_anno_typed : forall (e e' : trm) (A : typ),
    value e -> typedred e A e' -> step (trm_anno e A) e'
| step_app_l : forall (e1 e2 e1' : trm),
    term e2 -> step e1 e1' -> step (trm_app e1 e2) (trm_app e1' e2)
| step_app_r : forall (e1 e2 e2' : trm),
    value e1 -> step e2 e2' -> step (trm_app e1 e2) (trm_app e1 e2')
| step_merge_l : forall (e1 e2 e1' : trm),
    term e2 -> step e1 e1' -> step (trm_merge e1 e2) (trm_merge e1' e2)
| step_merge_r : forall (e1 e2 e2' : trm),
    value e2 -> step e2 e2' -> step (trm_merge e1 e2) (trm_merge e1 e2')
| step_anno : forall (e e' : trm) (A : typ),
    step e e' -> step (trm_anno e A) (trm_anno e' A).

Hint Constructors step : core.
