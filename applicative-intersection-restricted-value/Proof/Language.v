Require Import Metalib.Metatheory.
Require Import Metalib.LibTactics.
Require Import Coq.Program.Equality.
Require Import Coq.Strings.String.

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

Fixpoint size_typ (A : typ) {struct A} : nat :=
  match A with
  | typ_int => 1
  | typ_top => 1
  | typ_arrow A1 B1 => 1 + (size_typ A1) + (size_typ B1)
  | typ_and A1 B1 => 1 + (size_typ A1) + (size_typ B1)
  end.

Fixpoint size_trm (e : trm) {struct e} : nat :=
  match e with
  | trm_int n => 1
  | trm_bvar n => 1
  | trm_fvar x => 1
  | trm_abs e1 A B => 1 + (size_trm e1) + (size_typ A) + (size_typ B)
  | trm_app e1 e2 => 1 + (size_trm e1) + (size_trm e2)
  | trm_merge e1 e2 => 1 + (size_trm e1) + (size_trm e2)
  | trm_anno e1 A => 1 + (size_trm e1) + (size_typ A)
  end.

Notation "e ∷ A" := (trm_anno e A) (at level 20).
Notation "ƛ. e A → B" := (trm_abs e A B) (at level 20).

Coercion trm_fvar : atom >-> trm.

Fixpoint subst_exp (z : atom) (u : trm) (e : trm) {struct e} : trm :=
  match e with
  | trm_int n => trm_int n
  | trm_bvar i => trm_bvar i
  | trm_fvar x => if x == z then u else (trm_fvar x)
  | trm_abs e1 A B => trm_abs (subst_exp z u e1) A B
  | trm_app e1 e2 => trm_app (subst_exp z u e1) (subst_exp z u e2)
  | trm_merge e1 e2 => trm_merge (subst_exp z u e1) (subst_exp z u e2)
  | trm_anno e1 A => trm_anno (subst_exp z u e1) A
  end.

Notation "{ z ↦ u } e" := (subst_exp z u e) (at level 69).

Fixpoint fv (e : trm) {struct e} : atoms :=
  match e with
  | trm_int n => empty
  | trm_bvar i => empty
  | trm_fvar x => singleton x
  | trm_abs e1 A B => fv e1
  | trm_app e1 e2 => (fv e1) `union` (fv e2)
  | trm_merge e1 e2 => (fv e1) `union` (fv e2)
  | trm_anno e1 A => (fv e1)
  end.

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
    
Inductive lc : trm -> Prop :=
| lc_int : forall (n : nat),
    lc (trm_int n)
| lc_var : forall (x : atom),
    lc (trm_fvar x)
| lc_abs : forall (e : trm) (A B : typ) (L : atoms),
    (forall x : atom, x `notin` L -> lc (open e x)) ->
    lc (trm_abs e A B)
| lc_app : forall (e1 e2 : trm),
    lc e1 -> lc e2 ->
    lc (trm_app e1 e2)
| lc_merge : forall (e1 e2 : trm),
    lc e1 -> lc e2 ->
    lc (trm_merge e1 e2)
| lc_anno : forall (e : trm) (A : typ),
    lc e ->
    lc (trm_anno e A).

Hint Constructors lc : core.

Inductive ordinary : typ -> Prop :=
| ord_top : ordinary typ_top
| ord_int : ordinary typ_int
| ord_arrow : forall (A B : typ),
    ordinary B -> ordinary (typ_arrow A B).

Hint Constructors ordinary : core.

Inductive pvalue : trm -> Prop :=
| pvalue_nat : forall (n : nat), pvalue (trm_int n)
| pvalue_abs : forall (e : trm) (A B : typ),
    lc (trm_abs e A B) -> pvalue (trm_abs e A B).

Inductive value : trm -> Prop :=
| value_anno : forall (A : typ) (e : trm),
    pvalue e -> ordinary A -> value (trm_anno e A)
| value_merge : forall (v1 v2 : trm),
    value v1 -> value v2 -> value (trm_merge v1 v2).

Inductive uvalue : trm -> Prop :=
| uvalue_p : forall (p : trm),
    pvalue p -> uvalue p
| uvalue_anno : forall (e : trm) (A : typ),
    lc e ->
    uvalue (trm_anno e A)
| uvalue_merge : forall (u1 u2 : trm),
    uvalue u1 -> uvalue u2 -> uvalue (trm_merge u1 u2).

Hint Constructors pvalue : core.
Hint Constructors value : core.
Hint Constructors uvalue : core.

Inductive toplike : typ -> Prop :=
| tl_top : toplike typ_top
| tl_and : forall (A B : typ), toplike A -> toplike B -> toplike (typ_and A B)
| tl_arrow : forall (A B : typ), toplike B -> toplike (typ_arrow A B).

Hint Constructors toplike : core.

Inductive sub_dec : typ -> typ -> Prop :=
| subd_refl : forall (A : typ),
    sub_dec A A
| subd_trans : forall (A B C : typ),
    sub_dec A B -> sub_dec B C -> sub_dec A C
| subd_top : forall (A : typ),
    sub_dec A typ_top
| subd_top_arr :
    sub_dec typ_top (typ_arrow typ_top typ_top)
| subd_arr : forall (A B C D : typ),
    sub_dec B A -> sub_dec C D ->
    sub_dec (typ_arrow A C) (typ_arrow B D)
| subd_and : forall (A B C : typ),
    sub_dec A B -> sub_dec A C ->
    sub_dec A (typ_and B C)
| subd_and_l : forall (A B : typ),
    sub_dec (typ_and A B) A
| subd_and_r : forall (A B : typ),
    sub_dec (typ_and A B) B
| subd_distri_arr : forall (A B C : typ),
    sub_dec (typ_and (typ_arrow A B)
                     (typ_arrow A C))
            (typ_arrow A
                       (typ_and B C)).

Hint Constructors sub_dec : core.

Inductive splitable : typ -> typ -> typ -> Prop :=
| sp_and : forall (A B : typ),
    splitable (typ_and A B) A B
| sp_arrow : forall (A B C D : typ),
    splitable B C D ->
    splitable (typ_arrow A B) (typ_arrow A C) (typ_arrow A D).

Hint Constructors splitable : core.
Notation "B ↩ A ↪ C" := (splitable A B C) (at level 40).

Inductive sub : typ -> typ -> Prop :=
| sub_int :
    sub typ_int typ_int
| sub_top : forall (A B : typ),
    ordinary B -> toplike B ->
    sub A B
| sub_arrow : forall (A B C D : typ),
    sub B A -> sub C D -> ordinary D ->
    sub (typ_arrow A C) (typ_arrow B D)
| sub_and : forall (A B C D : typ),
    splitable D B C ->
    sub A B -> sub A C -> sub A D
| sub_and_l : forall (A B C : typ),
    sub A C -> ordinary C ->
    sub (typ_and A B) C
| sub_and_r : forall (A B C : typ),
    sub B C -> ordinary C ->
    sub (typ_and A B) C.

Hint Constructors sub : core.

Notation "A <: B" := (sub A B) (at level 40).

Definition arg := option typ.

Inductive auxas : arg -> typ -> Prop :=
| aas_refl : forall (A : typ),
    auxas None A
| aas_fun : forall (A B C : typ),
    sub C A ->
    auxas (Some C) (typ_arrow A B)
| aas_and_l : forall (A B C : typ),
    auxas (Some C) A ->
    auxas (Some C) (typ_and A B)
| aas_and_r : forall (A B C : typ),
    auxas (Some C) B ->
    auxas (Some C) (typ_and A B).

Inductive appsub : arg -> typ -> typ -> Prop :=
| as_refl : forall (A : typ),
    appsub None A A
| as_fun : forall (A B C D : typ),
    sub C A ->
    appsub (Some C) (typ_arrow A B) B
| as_and_l : forall (A B C D: typ),
    appsub (Some C) A D ->
    not (auxas (Some C) B) ->
    appsub (Some C) (typ_and A B) D
| as_and_r : forall (A B C D : typ),
    appsub (Some C) B D ->
    not (auxas (Some C) A) ->
    appsub (Some C) (typ_and A B) D
| as_and_both : forall (A B C D1 D2: typ),
    appsub (Some C) A D1 ->
    appsub (Some C) B D2 ->
    appsub (Some C) (typ_and A B) (typ_and D1 D2).

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
    lc v ->
    toplike A -> ordinary A ->
    typedred v A (trm_anno (trm_int 1) A)
| tred_arrow_anno : forall (A B C D E : typ) (e : trm),
    lc (trm_abs e A B) ->
    not (toplike D) -> sub E (typ_arrow C D) ->
    ordinary D ->
    typedred (trm_anno (trm_abs e A B) E)
             (typ_arrow C D)
             (trm_anno (trm_abs e A D) (typ_arrow C D))
| tred_merge_l : forall (v1 v2 v1': trm) (A : typ),
    typedred v1 A v1' -> ordinary A ->
    typedred (trm_merge v1 v2) A v1'
| tred_merge_r : forall (v1 v2 v2': trm) (A : typ),
    typedred v2 A v2' -> ordinary A ->
    typedred (trm_merge v1 v2) A v2'
| tred_and : forall (v1 v2 v : trm) (A B C : typ),
    splitable A B C ->
    typedred v B v1 ->
    typedred v C v2 ->
    typedred v A (trm_merge v1 v2).

Hint Constructors typedred : core.

Notation "e ~->> A e'" := (typedred e A e') (at level 68).

Inductive ptype : trm -> typ -> Prop :=
| ptype_int : forall (n : nat),
    ptype (trm_int n) typ_int
| ptype_arrow : forall (e : trm) (A B : typ),
    lc (trm_abs e A B) ->
    ptype (trm_abs e A B) (typ_arrow A B)
| ptype_anno : forall (e : trm) (A : typ),
    lc e ->
    ptype (trm_anno e A) A
| ptype_merge : forall (e1 e2 : trm) (A B : typ),
    ptype e1 A ->
    ptype e2 B ->
    ptype (trm_merge e1 e2) (typ_and A B).

Hint Constructors ptype : core.

Definition consistency_spec v1 v2 :=
  forall (A : typ) (v1' v2' : trm), ordinary A -> typedred v1 A v1' -> typedred v2 A v2' -> v1' = v2'.

Inductive consistent : trm -> trm -> Prop :=
| con_abs : forall (e : trm) (A B1 B2 : typ),
    lc (trm_abs e A B1) ->
    consistent (trm_abs e A B1) (trm_abs e A B2)
| con_abs_anno : forall (e : trm) (A B1 B2 C D : typ),
    lc (trm_abs e A B1) ->
    consistent (trm_anno (trm_abs e A B1) C) (trm_anno (trm_abs e A B2) D)
| con_anno : forall (e : trm) (A B : typ),
    lc e ->
    consistent (trm_anno e A) (trm_anno e B)
| con_disjoint : forall (u1 u2 : trm) (A B : typ),
    ptype u1 A -> ptype u2 B -> disjoint A B ->
    consistent u1 u2
| con_merge_l : forall (u u1 u2 : trm),
    consistent u1 u ->
    consistent u2 u ->
    consistent (trm_merge u1 u2) u
| con_merge_r : forall (u u1 u2 : trm),
    consistent u u1 ->
    consistent u u2 ->
    consistent u (trm_merge u1 u2).

Hint Constructors consistent : core.

Inductive typing : ctx -> trm -> typ -> Prop :=
| typing_int : forall (T : ctx) (n : nat),
    uniq T -> typing T (trm_int n) typ_int
| typing_var : forall (T : ctx) (x : var) (A : typ),
    uniq T -> binds x A T -> typing T (trm_fvar x) A
| typing_lam : forall (L : vars) (T : ctx) (A B C : typ) (e : trm),
    (forall x, x \notin L -> (typing ((x ~ A) ++ T)) (open e (trm_fvar x)) C) ->
    sub C B ->
    typing T (trm_abs e A B) (typ_arrow A B)
| typing_anno : forall (T : ctx) (A B C : typ) (e : trm),
    typing T e C -> sub C A ->
    typing T (trm_anno e A) A
| typing_app : forall (S : arg) (T : ctx) (A B C : typ) (e1 e2 : trm),
    typing T e2 A ->
    typing T e1 B ->
    appsub (Some A) B C ->
    typing T (trm_app e1 e2) C
| typing_merge : forall (T : ctx) (A B : typ) (e1 e2 : trm),
    disjoint A B ->
    typing T e1 A ->
    typing T e2 B ->
    typing T (trm_merge e1 e2) (typ_and A B)
| typing_merge_uvalue : forall (T : ctx) (A B : typ) (u1 u2 : trm),
    uniq T ->
    uvalue u1 -> uvalue u2 ->
    consistent u1 u2 ->
    typing nil u1 A ->
    typing nil u2 B ->
    typing T (trm_merge u1 u2) (typ_and A B).

Hint Constructors typing : core.

Notation "T ⊢ e ⇒ A" := (typing T e A) (at level 50).

Inductive papp : trm -> trm -> trm -> Prop :=
| papp_int_toplike : forall (A B : typ) (v vl : trm) (n : nat),
    toplike B ->
    papp (trm_anno (trm_int n) (typ_arrow A B)) vl (trm_anno (trm_int 1) B)
| papp_abs_toplike : forall (A B C D : typ) (e v v' : trm),
    lc (trm_abs e A B) ->
    toplike D ->
    papp (trm_anno (trm_abs e A B) (typ_arrow C D)) v
         (trm_anno (trm_int 1) D)         
| papp_abs_anno : forall (A B C D : typ) (e v v' : trm),
    lc (trm_abs e A B) ->
    typedred v A v' ->
    not (toplike D) ->
    papp (trm_anno (trm_abs e A B) (typ_arrow C D)) v
         (trm_anno (open e v') D)
| papp_merge_l : forall (A B C : typ) (v1 v2 vl e: trm),
    ptype v1 A -> ptype v2 B -> ptype vl C ->
    auxas (Some C) A ->
    not (auxas (Some C) B) ->
    papp v1 vl e ->
    papp (trm_merge v1 v2) vl e
| papp_merge_r : forall (A B C : typ) (v1 v2 vl e : trm),
    ptype v1 A -> ptype v2 B -> ptype vl C ->
    not (auxas (Some C) A) ->
    auxas (Some C) B ->
    papp v2 vl e ->
    papp (trm_merge v1 v2) vl e
| papp_merge_p : forall (A B C : typ) (v1 v2 vl e1 e2 : trm),
    ptype v1 A -> ptype v2 B -> ptype vl C ->
    auxas (Some C) A ->
    auxas (Some C) B ->
    papp v1 vl e1 ->
    papp v2 vl e2 ->
    papp (trm_merge v1 v2) vl (trm_merge e1 e2).

Hint Constructors papp : core.

Notation "v ◐ vl ~-> e" := (papp v vl e) (at level 69).

Inductive step : trm -> trm -> Prop :=
| step_int_anno : forall (n : nat),
    step (trm_int n) (trm_anno (trm_int n) typ_int)
| step_int_split : forall (A A1 A2 : typ) (n : nat),
    splitable A A1 A2 ->
    step (trm_anno (trm_int n) A) (trm_merge (trm_anno (trm_int n) A1) (trm_anno (trm_int n) A2))
| step_abs_anno : forall (e : trm) (A B : typ),
    step (trm_abs e A B) (trm_anno (trm_abs e A B) (typ_arrow A B))
| step_abs_split : forall (A B C C1 C2 : typ) (e : trm),
    splitable C C1 C2 ->
    step (trm_anno (trm_abs e A B) C) (trm_merge (trm_anno (trm_abs e A B) C1) (trm_anno (trm_abs e A B) C2))
| step_papp : forall (v vl e : trm) (A : typ),
    value v -> value vl ->
    papp v vl e ->
    step (trm_app v vl) e
| step_anno_value : forall (v v' : trm) (A : typ),
    value v -> typedred v A v' ->
    step (trm_anno v A) v'
| step_anno : forall (e e' : trm) (A : typ),
    not (pvalue e) ->
    step e e' -> step (trm_anno e A) (trm_anno e' A)
| step_app_l : forall (e1 e2 e1' : trm),
    lc e2 ->
    step e1 e1' -> step (trm_app e1 e2) (trm_app e1' e2)
| step_app_r : forall (v e2 e2' : trm),
    value v -> step e2 e2' -> step (trm_app v e2) (trm_app v e2')
| step_merge_bcd : forall (e1 e1' e2 e2' : trm),
    step e1 e1' ->
    step e2 e2' ->
    step (trm_merge e1 e2) (trm_merge e1' e2')         
| step_merge_l : forall (e1 v2 e1' : trm),
    value v2 ->
    step e1 e1' ->
    step (trm_merge e1 v2) (trm_merge e1' v2)
| step_merge_r : forall (v e2 e2' : trm),
    value v -> step e2 e2' ->
    step (trm_merge v e2) (trm_merge v e2').

Hint Constructors step : core.
Notation "e ~-> e'" := (step e e') (at level 68).

Inductive isomorphic : typ -> typ -> Prop :=
| iso_refl : forall (A : typ),
    isomorphic A A
| iso_and : forall (A1 A2 B B1 B2 : typ),
    splitable B B1 B2 ->
    isomorphic A1 B1 ->
    isomorphic A2 B2 ->
    isomorphic (typ_and A1 A2) B.

Hint Constructors isomorphic : core.

Notation "A ≋ B" := (isomorphic A B) (at level 40).

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (atom * typ) => dom x) in
  let D := gather_atoms_with (fun x : trm => fv x) in
  constr:(A `union` B `union` C `union` D).
