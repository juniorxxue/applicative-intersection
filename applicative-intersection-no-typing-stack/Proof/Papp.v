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
  forall (v1 v2 : trm) (A : typ),
    typing nil (trm_app v1 v2) A ->
    exists e, papp v1 v2 e.
Proof.
  introv Htyp.
Admitted.
