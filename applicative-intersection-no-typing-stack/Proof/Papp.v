Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language LibTactics.
Require Import Subtyping Toplike Ptype Appsub Tred.

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
    dependent destruction Htyp.
    assert (v' = v'0).
    eapply tred_determinism; eauto 3. admit.
    congruence.
  - admit.
  - admit.
  - dependent destruction Hp2.
    + admit.
    + admit.
    + dependent destruction Hv.
      dependent destruction Htyp.
      assert (e1 = e0). eapply IHHp1_1; eauto 3.
      admit.
      assert (e2 = e3). eapply IHHp1_2; eauto 3.
      admit.
      congruence.
Admitted.

Theorem papp_preservation :
  forall (v1 v2 e : trm) (A B C : typ),
    value v1 -> value v2 ->
    typing nil v1 A ->
    typing nil v2 B ->
    appsub (Some B) A C ->
    not (toplike A) ->
    papp v1 v2 e ->
    (exists D, typing nil e D /\ isomorphic D C).
Proof.
  introv Hv1 Hv2 Htyp1 Htyp2 Has Htl Hp.
  gen A B C.
  dependent induction Hp; intros.
  - dependent destruction Htyp1. dependent destruction Htyp1.
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

Lemma applicable_cannot_sub_int :
  forall (A : typ),
    not (toplike A) ->
    applicable A -> sub typ_int A -> False.
Proof.
  introv Htl Ha Hs.
  dependent induction Hs; eauto.
  - inversion Ha.
Abort.
              
      
Theorem papp_progress :
  forall (v1 v2 : trm) (A B C: typ),
    not (toplike A) ->
    value v1 -> value v2 ->
    typing nil v1 A ->
    typing nil v2 B ->
    appsub (Some B) A C ->
    exists e, papp v1 v2 e.
Proof.
  introv Htl Hv1 Hv2 Htyp1 Htyp2 Has.
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
      * eapply split_and_toplike in Htl; eauto.
        destruct Htl.
        ** assert (exists e, papp v1 v0 e); eauto.
           destruct H2.
           assert (ptype v1 A); eauto.
           assert (ptype v2 B0); eauto.
           assert (ptype v0 B); eauto.
           exists x. eapply papp_merge_l; eauto.
           eapply appsub_to_auxas in Has. assumption.
        ** admit.        
      * admit.
    + admit.
    + admit.
Admitted.
