Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Language Automations Subtyping LibTactics.
Require Import Strings.String.

Theorem papp_determinism :
  forall (v vl e1 e2 : trm) (A : typ),
    papp v vl e1 ->
    papp v vl e2 ->
    typing nil (trm_app v vl) A ->
    e1 = e2.
Proof.
Admitted.

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
      admit.
    + dependent destruction Htyp1.
      dependent destruction Htyp1.
      admit.
  - dependent destruction Has.
    + inversion Htyp1.
    + dependent destruction Htyp1.
      * eapply not_toplike_and_inversion in Htl.
        destruct Htl.
        assert (exists e, papp v1 v0 e); eauto.
        destruct H3.
        assert (ptype v1 A); eauto.
        assert (ptype v2 B0); eauto.
        assert (ptype v0 B); eauto.
        exists x. eapply papp_merge_l; eauto.
        admit.
      * admit.
    + admit.
    + admit.
Admitted.
