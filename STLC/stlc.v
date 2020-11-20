(* generated by Ott 0.31, locally-nameless from: stlc.ott *)
Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.
Require Import Ott.ott_list_core.
(** syntax *)
Definition tvar : Set := var. (*r term variable *)
Definition Tvar : Set := var. (*r term variable *)

Inductive type : Set :=  (*r type *)
 | type_int : type (*r int *)
 | type_top : type (*r top *)
 | type_arrow (A:type) (B:type) (*r function *)
 | type_intersection (A:type) (B:type) (*r intersection type *).

Inductive term : Set :=  (*r term *)
 | term_int : term (*r int *)
 | term_var_b (_:nat) (*r variable *)
 | term_var_f (x:tvar) (*r variable *)
 | term_abs (e:term) (*r abstraction *)
 | term_app (e1:term) (e2:term) (*r application *)
 | term_merge (e1:term) (e2:term) (*r merge *)
 | term_annotation (e:term) (A:type) (*r type annotation *).

Inductive arg : Set :=  (*r argument *)
 | arg_empty : arg (*r empty *)
 | arg_withargs (A:type) (*r with arg *).

Inductive env : Set :=  (*r env *)
 | env_empty : env (*r empty *)
 | env_bind (x:tvar) (A:type) (*r bind *).

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_term_wrt_term_rec (k:nat) (e_5:term) (e__6:term) {struct e__6}: term :=
  match e__6 with
  | term_int => term_int 
  | (term_var_b nat) => if (k === nat) then e_5 else (term_var_b nat)
  | (term_var_f x) => term_var_f x
  | (term_abs e) => term_abs (open_term_wrt_term_rec (S k) e_5 e)
  | (term_app e1 e2) => term_app (open_term_wrt_term_rec k e_5 e1) (open_term_wrt_term_rec k e_5 e2)
  | (term_merge e1 e2) => term_merge (open_term_wrt_term_rec k e_5 e1) (open_term_wrt_term_rec k e_5 e2)
  | (term_annotation e A) => term_annotation (open_term_wrt_term_rec k e_5 e) A
end.

Definition open_term_wrt_term e_5 e__6 := open_term_wrt_term_rec 0 e__6 e_5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_term *)
Inductive lc_term : term -> Prop :=    (* defn lc_term *)
 | lc_term_int : 
     (lc_term term_int)
 | lc_term_var_f : forall (x:tvar),
     (lc_term (term_var_f x))
 | lc_term_abs : forall (L:vars) (e:term),
      ( forall x , x \notin  L  -> lc_term  ( open_term_wrt_term e (term_var_f x) )  )  ->
     (lc_term (term_abs e))
 | lc_term_app : forall (e1 e2:term),
     (lc_term e1) ->
     (lc_term e2) ->
     (lc_term (term_app e1 e2))
 | lc_term_merge : forall (e1 e2:term),
     (lc_term e1) ->
     (lc_term e2) ->
     (lc_term (term_merge e1 e2))
 | lc_term_annotation : forall (e:term) (A:type),
     (lc_term e) ->
     (lc_term (term_annotation e A)).
(** free variables *)
(** substitutions *)

(** definitions *)

(* defns subtyping *)
Inductive sub : type -> type -> Prop :=    (* defn sub *)
 | sub_S_Int :
     sub type_int type_int
 | sub_S_Top : forall (A:type),
     sub A type_top
 | sub_S_Arrow : forall (A B C D:type),
     sub C A ->
     sub B D ->
     sub (type_arrow A B) (type_arrow C D)
 | sub_S_And : forall (A B C:type),
     sub A B ->
     sub A C ->
     sub A (type_intersection B C)
 | sub_S_AndL : forall (A B C:type),
     sub A C ->
     sub (type_intersection A B) C
 | sub_S_AndR : forall (A B C:type),
     sub B C ->
     sub (type_intersection A B) C.

(* defns appsubtyping *)
Inductive appsub : arg -> type -> type -> Prop :=    (* defn appsub *)
 | appsub_AS_Refl : forall (A:type),
     appsub arg_empty A A
 | appsub_AS_Fun : forall (C A B D:type) (S:arg),
     sub C A ->
     appsub S B D ->
     appsub (arg_withargs C) (type_arrow A B) D
 | appsub_AS_AndL : forall (C A B D:type),
     appsub (arg_withargs C) A D ->
     appsub (arg_withargs C) (type_intersection A B) D
 | appsub_AS_AndR : forall (C A B D:type),
     appsub (arg_withargs C) B D ->
     appsub (arg_withargs C) (type_intersection A B) D
 | appsub_AS_And1 : forall (A B C D:type),
     appsub (arg_withargs A) C D ->
     appsub (arg_withargs (type_intersection A B)) C D
 | appsub_AS_And2 : forall (A B C D:type),
     appsub (arg_withargs B) C D ->
     appsub (arg_withargs (type_intersection A B)) C D.


(** infrastructure *)
Hint Constructors sub appsub lc_term : core.

(* Subtyping Reflexivity and Transitivity *)
Check type.

Theorem sub_reflexivity :
  forall t, sub t t.
Proof.
  induction t.
  - apply sub_S_Int.
  - apply sub_S_Top.
  - apply sub_S_Arrow.
    + apply IHt1.
    + apply IHt2.
  - apply sub_S_And.
    + apply sub_S_AndL. apply IHt1.
    + apply sub_S_AndR. apply IHt2.
Qed.

Lemma sub_top :
  forall t, sub type_top t -> t = type_top.
Proof.
  intros t H.
  induction t.
Admitted.

Theorem sub_transitivity :
  forall t1 t2 t3, sub t1 t2 -> sub t2 t3 -> sub t1 t3.
Proof.
  intros t1 t2 t3 H1 H2.
  induction t1.
  - induction t2.
    + apply H2.
    + apply sub_top in H2. rewrite H2. apply sub_S_Top.
      Admitted.


