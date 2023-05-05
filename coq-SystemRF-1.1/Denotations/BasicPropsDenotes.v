Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.Strengthenings.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.BasicPropsWellFormedness.
Require Import Denotations.ClosingSubstitutions.
Require Import Denotations.Denotations.
Require Import Denotations.BasicPropsCSubst.

Lemma lem_denotesenv_loc_closed : forall (g:env) (th:csub), 
    DenotesEnv g th -> loc_closed th.
Proof. intros; induction H; simpl; try split; trivial.
  - (* CCons *) apply lem_den_hasftype in H1; 
    apply lem_ftyp_islc in H1; assumption.
  - (* CConsT *) apply lem_wftype_islct in H2; assumption. 
  Qed.

Lemma lem_denotesenv_closed : forall (g:env) (th:csub), 
    DenotesEnv g th -> closed th.
Proof. intros; induction H; simpl; trivial.
  - (* CCons *) apply lem_den_hasftype in H1;
    apply lem_fv_subset_bindsF in H1; repeat split;
    try apply IHDenotesEnv; apply no_elem_empty; intuition.
  - (* CConsT *) apply lem_free_subset_binds in H2;repeat split;
    try apply IHDenotesEnv; apply no_elem_empty; intuition.
  Qed.

Lemma lem_denotesenv_substitutable : forall (g:env) (th:csub), 
    DenotesEnv g th -> substitutable th.
Proof. intros; induction H; simpl; try split; trivial.
  apply lem_den_isvalue with (ctsubst th t); apply H1. Qed.