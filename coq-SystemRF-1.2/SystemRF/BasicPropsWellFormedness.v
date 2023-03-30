Require Import Arith.

Require Import SystemRF.BasicDefinitions. 
Require Import SystemRF.Names.
Require Import SystemRF.LocalClosure.
Require Import SystemRF.SystemFWellFormedness.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.BasicPropsWFFT.
Require Import SystemRF.Typing.

(*------------------------------------------------------------------------------------------
-- | LEMMAS relating REFINEMENT ERASURE and WELL FORMEDNESS notions
------------------------------------------------------------------------------------------*)

Lemma lem_erase_wftype : forall (g:env) (t:type) (k:kind),
    WFtype g t k -> WFFT (erase_env g) (erase t) k.
Proof. intros g t k p_g_t ; induction p_g_t; simpl.
  - (* WFBase *) apply WFFTBasic; assumption.
  - (* WFRefn *) simpl in IHp_g_t; apply IHp_g_t; assumption.
  - (* WFVar *) apply WFFTFV; apply tvboundin_erase_env; assumption.
  - (* WFFunc *) apply WFFTFunc with k_x k; try apply IHp_g_t;
    assert (erase_env g = concatF (erase_env g) FEmpty) by reflexivity; rewrite H1;
    apply lem_strengthen_wfft with (fresh_varF nms (erase_env g)) (erase t_x);
    simpl; simpl in H0;
    try rewrite <- lem_erase_unbind with (fresh_varF nms (erase_env g)) t;
    try apply H0; pose proof (fresh_varF_not_elem nms (erase_env g));
    destruct H2; try apply intersect_empty_r; intuition.
  - (* WFExis *) assert (erase_env g = concatF (erase_env g) FEmpty) by reflexivity; rewrite H1;
    apply lem_strengthen_wfft with (fresh_varF nms (erase_env g)) (erase t_x);
    simpl; simpl in H0;
    try rewrite <- lem_erase_unbind with (fresh_varF nms (erase_env g)) t;
    try apply H0; pose proof (fresh_varF_not_elem nms (erase_env g));
    destruct H2; try apply intersect_empty_r; intuition.
  - (* WFPoly *) apply WFFTPoly with k_t (union nms (bindsF (erase_env g))); intros;
    simpl in H0; rewrite <-lem_erase_unbind_tvT; apply H0;
    apply not_elem_union_elim in H1; destruct H1; assumption.
  - (* WFKind *) apply WFFTKind; apply IHp_g_t; apply H. 
  Qed.

Lemma lem_erase_env_wfenv : forall (g:env), WFEnv g -> WFFE (erase_env g).
Proof. induction g; intro p_wf_g; simpl.
  - apply WFFEmpty.
  - inversion p_wf_g. apply WFFBind with k; unfold in_envF; 
    try rewrite <- binds_erase_env; try apply lem_erase_wftype; 
    try apply wfenv_unique; intuition.
  - inversion p_wf_g; apply WFFBindT; unfold in_envF;
    try rewrite <- binds_erase_env; intuition. 
  Qed.

Lemma lem_truncate_wfenv : forall (g g':env),(* -> { g':env | Set_emp (Set_cap (binds g) (binds g')) }*)
    WFEnv (concatE g g') -> WFEnv g.
Proof. intro g; induction g'; intro p_wf_g'g.
  - simpl in p_wf_g'g; assumption.
  - simpl in p_wf_g'g; inversion p_wf_g'g; intuition.
  - simpl in p_wf_g'g; inversion p_wf_g'g; intuition.
  Qed.
