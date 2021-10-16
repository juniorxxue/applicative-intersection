Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language LibTactics.
Require Import SubAndTopLike Ptype Appsub Tred Consistent.

Theorem papp_determinism :
  forall (v vl e1 e2 : trm) (A : typ),
    value v -> value vl ->
    papp v vl e1 ->
    papp v vl e2 ->
    typing nil (trm_app v vl) A ->
    e1 = e2.
Proof.
  introv Hv Hvl Hp1 Hp2 Htyp.
  gen e2 A.
  dependent induction Hp1; intros.
  - dependent destruction Hp2.
    + assert (A = A0) by (eapply ptype_determinism; eauto). subst.
      reflexivity.
    + dependent destruction H. dependent destruction H0. contradiction.
    + dependent destruction H.
      assert (A = A0) by (eapply ptype_determinism; eauto). subst.
      assert (B = B0) by (eapply ptype_determinism; eauto). subst.
      contradiction.
    + dependent destruction H.
      assert (A = A0) by (eapply ptype_determinism; eauto). subst.
      assert (B = B0) by (eapply ptype_determinism; eauto). subst.
      contradiction.
    + dependent destruction H.
      assert (A = A0) by (eapply ptype_determinism; eauto). subst.
      assert (B = B0) by (eapply ptype_determinism; eauto). subst.
      contradiction.
  - dependent destruction Hp2.
    + dependent destruction H1. dependent destruction H2.
      contradiction.
    + dependent destruction Htyp.
      assert (v' = v'0).
      eapply tred_determinism; eauto 3.
      eapply consistent_reflexivity; eauto.
      congruence.
  - dependent destruction Hp2.
Admitted.

Theorem papp_preservation :
  forall (v1 v2 e : trm) (A B C : typ),
    value v1 -> value v2 ->
    typing nil v1 A ->
    typing nil v2 B ->
    appsub (Some B) A C ->
    papp v1 v2 e ->
    (exists D, typing nil e D /\ isomorphic D C).
Proof.
  introv Hv1 Hv2 Htyp1 Htyp2 Has Hp.
  gen A B C.
  dependent induction Hp; intros.
  - dependent destruction Htyp1.
Admitted.

Inductive applicable : typ -> Prop :=
| applicable_arrow : forall (A B : typ),
    applicable (typ_arrow A B)
| applicable_merge_l : forall (A B : typ),
    applicable A -> applicable (typ_and A B)
| applicable_merge_r : forall (A B : typ),
    applicable B -> applicable (typ_and A B).

Hint Constructors applicable : core.

Lemma split_and_applicable :
  forall (A B C: typ),
    applicable A -> splitable A B C ->
    applicable B \/ applicable C.
Proof.
  introv Happ Hspl.
  dependent induction Hspl; eauto.
  - dependent destruction Happ; eauto.
Qed.

Lemma appsub_is_applicable :
  forall (A B : typ),
    auxas (Some B) A -> applicable A.
Proof.
  intros.
  dependent induction H; eauto.
Qed.

Theorem papp_progress :
  forall (v1 v2 : trm) (A B C: typ),
    value v1 -> value v2 ->
    typing nil v1 A ->
    typing nil v2 B ->
    appsub (Some B) A C ->
    exists e, papp v1 v2 e.
Proof.
  introv Hv1 Hv2 Htyp1 Htyp2 Has.
  gen A B C v2.
  dependent induction Hv1; intros.
  - dependent destruction H.
    + dependent destruction Htyp1.
      dependent destruction Htyp1.
      (* 1 : (Int -> Top) & Int *)
      admit.
    + dependent destruction Htyp1.
      dependent destruction Htyp1.
      admit.
  - dependent destruction Has.
    + inversion Htyp1.
    + dependent destruction Htyp1.
      * assert (exists e, papp v1 v0 e). (* from appsub *)
        eapply IHHv1_1. eapply Htyp1_1. eapply Has. eapply Hv2. eapply Htyp2.
        destruct H1. exists x. eapply papp_merge_l.
        eapply typing_to_ptype; eauto.
        eapply typing_to_ptype; eauto.
        eapply typing_to_ptype; eauto.
        (* talk about toplike later *) admit.
        eapply appsub_to_auxas; eauto. assumption. assumption.
      * admit. (* diff should be consistency *)
    + admit. (* merge_r *)
    + admit. (* merge_all *)
Admitted.
