Require Import Metalib.Metatheory.
Require Import Metalib.LibTactics.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Strings.String.
Require Import Lia.

Require Import Language.
Require Import Tactical.
Require Import Subtyping.Subtyping.
Require Import Subtyping.Splitable.
Require Import Subtyping.Toplike.
Require Import Appsub.

Require Import Value.
Require Import Disjoint.
Require Import PrincipalTyping.
Require Import Consistent.
Require Import Typing.
Require Import Casting.
Require Import LocallyNameless.

(** * Definition *)

(** instead of using principal typing to get the type, we can define a function 
    atype : vl -> arg
    atype v = Some A
    atype l = Some l
 *)

(** value and label *)

Inductive vl : Set :=
| Av : term -> vl
| Al : label -> vl.

Hint Constructors vl : core.

(** I'm confused a little bit and try to think why not let merge to be general one (work both on type and label),
    Since we can't allow label to be merged, so merge case only account for types 
*)

Inductive atype : vl -> arg -> Prop :=
| At_Ann : forall e A,
    atype (Av (Ann e A)) (Avt A)
| At_Rcd : forall e l A,
    atype (Av e) (Avt A) ->
    atype (Av (Fld l e)) (Avt (Rcd l A))
| At_Mrg : forall e1 e2 A1 A2,
    atype (Av e1) (Avt A1) ->
    atype (Av e2) (Avt A2) ->
    atype (Av (Mrg e1 e2)) (Avt (And A1 A2))
| At_Lbl : forall l,
    atype (Al l) (Alt l).

Hint Constructors atype : core.

Inductive papp : term -> vl -> term -> Prop :=
| Pa_Lit_Tl : forall A B v n,
    toplike B ->
    papp (Ann (Lit n) (Arr A B)) (Av v)
         (Ann (Lit 1) B)
| Pa_Lit_Tl_R : forall A n l,
    toplike A ->
    papp (Ann (Lit n) (Rcd l A)) (Al l)
         (Ann (Lit 1) A)
| Pa_Lam_Tl : forall A B C D e v,
    lc (Lam A e B) ->
    toplike D ->
    papp (Ann (Lam A e B) (Arr C D)) (Av v)
         (Ann (Lit 1) D)
| Pa_Lam_Tl_R : forall A B C l e,
    lc (Lam A e B) ->
    toplike C ->
    papp (Ann (Lam A e B) (Rcd l C)) (Al l)
         (Ann (Lit 1) C)
| Pa_Lam : forall A B C D v v' e,
    lc (Lam A e B) ->
    casting v A v' ->
    not (toplike D) ->
    papp (Ann (Lam A e B) (Arr C D)) (Av v)
         (Ann (open e v') D)
| Pa_Rcd : forall v l,
    papp (Fld l v) (Al l) v
| Pa_Mrg_L : forall v1 v2 A B vl TA e,
    ptype v1 A -> ptype v2 B ->
    atype vl TA ->
    not (auxas (Some TA) B) ->
    papp v1 vl e ->
    papp (Mrg v1 v2) vl e
| Pa_Mrg_R : forall v1 v2 A B vl TA e,
    ptype v1 A -> ptype v2 B ->
    atype vl TA ->
    not (auxas (Some TA) A) ->
    papp v2 vl e ->
    papp (Mrg v1 v2) vl e
| Pa_Mrg_P : forall v1 v2 A B vl TA e1 e2,
    ptype v1 A -> ptype v2 B ->
    atype vl TA ->
    auxas (Some TA) A ->
    auxas (Some TA) B ->
    papp v1 vl e1 ->
    papp v2 vl e2 ->
    papp (Mrg v1 v2) vl (Mrg e1 e2).

Hint Constructors papp : core.

Notation "v · vl ⟹ e" := (papp v vl e) (at level 69).

(** * Determinism *)

Lemma atype_determinism :
  forall vl TA1 TA2,
    atype vl TA1 ->
    atype vl TA2 ->
    TA1 = TA2.
Proof.
  introv At1 At2. gen TA2.
  dependent induction At1; intros.
  - dependent destruction At2; eauto.
  - dependent destruction At2; eauto.
    pose proof (IHAt1 _ At2) as IH.
    dependent destruction IH; eauto.
  - dependent destruction At2.
    pose proof (IHAt1_1 _ At2_1) as IH1.
    pose proof (IHAt1_2 _ At2_2) as IH2.
    dependent destruction IH1. dependent induction IH2.
    auto.
  - dependent destruction At2; eauto.
Qed.

Ltac subst_atype :=
  match goal with
  | [H1: atype ?vl ?TA1, H2: atype ?vl ?TA2 |- _] =>
      (pose proof (atype_determinism _ _ _ H1 H2) as Eqs; subst; clear H2)
  end.

Lemma typing_to_atype :
  forall v A,
    value v ->
    typing nil v Inf A ->
    atype (Av v) (Avt A).
Proof.
  introv Val Typ. gen A.
  induction Val; intros.
  - dependent destruction Typ; eauto.
  - dependent destruction Typ; eauto.
  - dependent destruction Typ; eauto.
Qed.

Hint Resolve typing_to_atype : core.

(** Well-typed application term doesn't ensure that all subterms of function can accept its argument,
    but ensures part of its functions can accept *)

(** Notation: automation heavily relies on [contra_appsub] *)

Section papp_determinism.

Ltac solver1 := repeat match goal with
                       | Typ: typing nil ?v Inf ?A, Val: value ?v, Pt: ptype ?v _ |- _ =>
                           pose proof (typing_to_ptype _ _ (value_is_uvalue _ Val) Typ);
                           subst_ptype; clear Pt
                       | Typ: typing nil ?v Inf ?A, Val: value ?v, At: atype (Av ?v) _ |- _ =>
                           pose proof (typing_to_atype _ _ Val Typ);
                           subst_atype; clear At
                       end;
                match goal with
                | As: appsub _ _ _ |- _ => (dependent destruction As; eauto)
                end.

Lemma papp_determinism_v :
  forall f v e1 e2 A B C,
    value f -> value v ->
    typing nil f Inf A -> typing nil v Inf B ->
    appsub (Some (Avt B)) A C ->
    papp f (Av v) e1 ->
    papp f (Av v) e2 ->
    e1 = e2.
Proof.
  introv Valf Val Typ1 Typ2 As P1 P2. gen e2 A B C.
  dependent induction P1; intros.
  - Case "Lit Toplike".
    dependent destruction P2; eauto.
  - Case "Lam Toplike".
    dependent destruction P2; eauto.
  - Case "Lam".
    dependent destruction P2; eauto.
    repeat (f_equal). eapply casting_determinism; eauto.
  - Case "Merge L".
    dependent destruction P2;
      repeat subst_ptype; subst_atype;
      dependent destruction Valf; dependent destruction Typ1; solver1.
  - Case "Merge R".
    dependent destruction P2; eauto;
      repeat subst_ptype; subst_atype;
      dependent destruction Valf; dependent destruction Typ1; solver1.
  - Case "Merge P".
    dependent destruction P2; eauto;
      repeat subst_ptype; subst_atype;
      dependent destruction Valf; dependent destruction Typ1; solver1.
    + f_equal; solver1.
    + f_equal; solver1.
Qed.

Lemma papp_determinism_l :
  forall v l e1 e2 A B,
    value v ->
    typing nil v Inf A ->
    appsub (Some (Alt l)) A B ->
    papp v (Al l) e1 ->
    papp v (Al l) e2 ->
    e1 = e2.
Proof.
  introv Val Typ As P1 P2. gen e2 A B.
  dependent induction P1; intros.
  - Case "Lit Toplike".
    dependent destruction P2; eauto.
  - Case "Lam Toplike".
    dependent destruction P2; eauto.
  - Case "Prj".
    dependent destruction P2; eauto.
  - Case "Mrg L".
    dependent destruction P2;
      repeat subst_ptype; subst_atype;
      match goal with
      | At: atype (Al _) _ |- _ => dependent destruction At
      end; eauto;
      dependent destruction Val; dependent destruction Typ; solver1.
  - Case "Mrg R".
    dependent destruction P2;
      repeat subst_ptype; subst_atype;
      match goal with
      | At: atype (Al _) _ |- _ => dependent destruction At
      end; eauto;
      dependent destruction Val; dependent destruction Typ; solver1.
  - Case "Mrg P".
    dependent destruction P2;
      repeat subst_ptype; subst_atype;
      match goal with
      | At: atype (Al _) _ |- _ => dependent destruction At
      end; eauto;
      dependent destruction Val; dependent destruction Typ; solver1.
    + f_equal; eauto.
    + f_equal; eauto.
Qed.
      
End papp_determinism.

(** * App & Value *)

Lemma papp_lc_v :
  forall v vl e,
    lc v -> lc vl ->
    papp v (Av vl) e ->
    lc e.
Proof.
  introv Lc Lcl Pa.
  dependent induction Pa; try solve [econstructor; eauto 3].
  - econstructor. eapply open_abs; eauto 3.
    eapply casting_lc; eauto.
  - dependent destruction Lc; eauto 3.
  - dependent destruction Lc; eauto 3.
Qed.

Lemma papp_lc_l :
  forall v vl e,
    lc v ->
    papp v (Al vl) e ->
    lc e.
Proof.
  introv Lc Pa.
  dependent induction Pa; try solve [econstructor; eauto 3].
  - dependent destruction Lc. assumption.
  - dependent destruction Lc; eauto 3.
  - dependent destruction Lc; eauto 3.
Qed.

(** * Progress *)

Lemma papp_progress_v :
  forall f v A B C,
    value f -> value v ->
    typing nil f Inf A -> typing nil v Inf B ->
    appsub (Some (Avt B)) A C ->
    exists e, papp f (Av v) e.
Proof.
  introv Vf Vv Tf Tv As. gen A B C v.
  induction Vf; intros.
  - Case "Anno".
    destruct H.
    + SCase "Lit".
      repeat dependent destruction Tf.
      dependent destruction H1; eauto. dependent destruction As; eauto.
    + SCase "Lam".
      repeat dependent destruction Tf.
      dependent destruction H2; eauto.
      * dependent destruction As; eauto.
      * destruct (toplike_decidable D); eauto.
        dependent destruction As; eauto.
        assert (Sub: sub B1 A1) by (eapply sub_transitivity; eauto).
        pose proof (casting_progress' _ _ _ Vv Tv Sub) as Ct. destruct Ct.
        eexists. eapply Pa_Lam; eauto.
  - Case "Rcd".
    dependent destruction Tf; eauto.
  - Case "Merge".
    dependent destruction As.
    + inversion Tf.
    + dependent destruction Tf.
      * pose proof (IHVf1 _ Tf1 _ _ As _ Vv Tv) as IH. destruct IH.
        eexists. eapply Pa_Mrg_L; eauto.
      * pose proof (IHVf1 _ Tf1 _ _ As _ Vv Tv) as IH. destruct IH.
        eexists. eapply Pa_Mrg_L; eauto.
    + dependent destruction Tf.
      * pose proof (IHVf2 _ Tf2 _ _ As _ Vv Tv) as IH. destruct IH.
        eexists. eapply Pa_Mrg_R; eauto.
      * pose proof (IHVf2 _ Tf2 _ _ As _ Vv Tv) as IH. destruct IH.
        eexists. eapply Pa_Mrg_R; eauto.
    + dependent destruction Tf.
      * pose proof (IHVf1 _ Tf1 _ _ As1 _ Vv Tv) as IH1. destruct IH1.
        pose proof (IHVf2 _ Tf2 _ _ As2 _ Vv Tv) as IH2. destruct IH2.
        eexists. eapply Pa_Mrg_P; eauto.
      * pose proof (IHVf1 _ Tf1 _ _ As1 _ Vv Tv) as IH1. destruct IH1.
        pose proof (IHVf2 _ Tf2 _ _ As2 _ Vv Tv) as IH2. destruct IH2.
        eexists. eapply Pa_Mrg_P; eauto.
Qed.

Lemma papp_progress_l :
  forall v A B l,
    value v ->
    typing nil v Inf A ->
    appsub (Some (Alt l)) A B ->
    exists e, papp v (Al l) e.
Proof.
  introv Val Typ As. gen A B l.
  induction Val; intros.
  - Case "Ann". destruct H.
    + SCase "Lit".
      repeat dependent destruction Typ.
      dependent destruction H1; eauto. dependent destruction As; eauto.
    + SCase "Lam".
      repeat dependent destruction Typ.
      dependent destruction H2; eauto. dependent destruction As; eauto.
  - Case "Rcd".
    dependent destruction Typ; eauto.
    dependent destruction As. eauto.
  - Case "Merge".
    dependent destruction As.
    + inversion Typ.
    + dependent destruction Typ.
      * pose proof (IHVal1 _ Typ1 _ _ As) as IH. destruct IH.
        eexists. eapply Pa_Mrg_L; eauto.
      * pose proof (IHVal1 _ Typ1 _ _ As) as IH. destruct IH.
        eexists. eapply Pa_Mrg_L; eauto.
    + dependent destruction Typ.
      * pose proof (IHVal2 _ Typ2 _ _ As) as IH. destruct IH.
        eexists. eapply Pa_Mrg_R; eauto.
      * pose proof (IHVal2 _ Typ2 _ _ As) as IH. destruct IH.
        eexists. eapply Pa_Mrg_R; eauto.
    + dependent destruction Typ.
      * pose proof (IHVal1 _ Typ1 _ _ As1) as IH1. destruct IH1.
        pose proof (IHVal2 _ Typ2 _ _ As2) as IH2. destruct IH2.
        eexists. eapply Pa_Mrg_P; eauto.
      * pose proof (IHVal1 _ Typ1 _ _ As1) as IH1. destruct IH1.
        pose proof (IHVal2 _ Typ2 _ _ As2) as IH2. destruct IH2.
        eexists. eapply Pa_Mrg_P; eauto.
Qed.
