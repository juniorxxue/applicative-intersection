Require Import Strings.String.
Require Import Metalib.LibTactics.
Require Import Program.Equality.
Require Import Program.Tactics.
Require Import Language.
Require Import Tactical.
Require Import Value.
Require Import PrincipalTyping.
Require Import Disjoint.

(** * Definition *)

Inductive consistent : term -> term -> Prop :=
| Con_Lam : forall e A B1 B2 C D,
    lc (Lam A e B1) ->
    consistent (Ann (Lam A e B1) C) (Ann (Lam A e B2) D)
| Con_Ann : forall e A B,
    lc e ->
    consistent (Ann e A) (Ann e B)
| Con_Rcd : forall l u1 u2,
    consistent u1 u2 ->
    consistent (Fld l u1) (Fld l u2)
| Con_Dj : forall u1 u2 A B,
    ptype u1 A -> ptype u2 B ->
    disjoint A B ->
    consistent u1 u2
| Con_Mrg_L : forall u u1 u2,
    consistent u1 u ->
    consistent u2 u ->
    consistent (Mrg u1 u2) u
| Con_Mrg_R : forall u u1 u2,
    consistent u u1 ->
    consistent u u2 ->
    consistent u (Mrg u1 u2).

Hint Constructors consistent : core.

(** * Properties *)

(** ** Symmetry *)

Lemma consistent_symmetry :
  forall v1 v2,
    consistent v1 v2 -> consistent v2 v1.
Proof.
  introv Con.
  induction Con; eauto.
  eapply Con_Dj; eauto.
  now eapply disjoint_symmetry.
Qed.

(** * Inversion Lemmas *)

Lemma consistent_inv_merge_l :
  forall v1 v2 v,
    consistent (Mrg v1 v2) v ->
    consistent v1 v /\ consistent v2 v.
Proof.
  introv Con.
  dependent induction Con; eauto.
  - Case "Disjoint".
    dependent destruction H.
    eapply disjoint_splitable_l in H2; eauto.
    destruct_conjs; eauto.
  - Case "Merge".
    pose proof (IHCon1 v1 v2) as IH1.
    pose proof (IHCon2 v1 v2) as IH2.
    destruct IH1; destruct IH2; eauto.
Qed.

Lemma consistent_inv_merge_r :
  forall v1 v2 v,
    consistent v (Mrg v1 v2) ->
    consistent v v1 /\ consistent v v2.
Proof.
  introv Con.
  dependent induction Con; eauto.
  - Case "Disjoint".
    dependent destruction H0.
    eapply disjoint_splitable_r in H1; eauto.
    destruct_conjs; eauto.
  - Case "Merge".
    pose proof (IHCon1 v1 v2) as IH1.
    pose proof (IHCon2 v1 v2) as IH2.
    destruct IH1; destruct IH2; eauto.
Qed.
