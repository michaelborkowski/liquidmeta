Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.SystemFLemmasWeaken.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.Typing.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.BasicPropsWellFormedness.
Require Import SystemRF.LemmasWeakenWFTV.
Require Import SystemRF.SubstitutionLemmaWF.
Require Import SystemRF.SubstitutionLemmaWFTV.
Require Import Denotations.ClosingSubstitutions.
Require Import Denotations.Denotations.
Require Import Denotations.BasicPropsCSubst.
Require Import Denotations.BasicPropsDenotes.
Require Import Denotations.EnvironmentSubstitutions.

Lemma lem_ctsubst_wf' : forall (g g':env) (t:type) (k:kind) (th:csub),
    WFtype (concatE g g') t k -> WFEnv g
        -> unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> DenotesEnv g th
        -> WFtype (csubst_env th g') (ctsubst th t) k.
Proof. induction g; intros.
  - (* Empty *) inversion H4; simpl; 
    rewrite lem_empty_concatE in H; apply H.
  - (* Cons *)  inversion H4; subst x0 t1 g0;
    rewrite lem_unroll_csubst_env_left;
    try rewrite lem_unroll_ctsubst_left;
    try rewrite <- (lem_empty_concatE (esubFV x v (csubst_env th0 g')));
    try apply lem_subst_wf with (ctsubst th0 t); 
    assert (Cons x (ctsubst th0 t) Empty = csubst_env th0 (Cons x t Empty))
      by (symmetry; rewrite <- (lem_csubst_env_empty th0) at 2;
          apply lem_csubst_cons_env); try rewrite H5;
    try rewrite <- lem_csubst_env_concat; try apply IHg;
    apply lem_den_isvalue in H11 as Hv;
    apply lem_den_hasftype in H11 as p_v_tht;
    apply lem_fv_subset_bindsF in p_v_tht as Hfv; 
    simpl in Hfv; destruct Hfv as [Hfv Hftv];
    try rewrite <- lem_concat_shift; 
    simpl in H1;
    try apply intersect_names_add_elim_l in H3; fold binds in H3;
    inversion H0; destruct H1; destruct H3; subst x0 t1 g0;
    try apply unique_concat;
    try (unfold unique; split);
    unfold binds; fold binds;
    try apply intersect_names_add_intro_l;
    try apply intersect_empty_l; try apply H3;
    pose proof (lem_binds_concat (Cons x t Empty) g'); 
    unfold binds in H6; fold binds in H6; destruct H6;    
    try apply subset_in_intersect with (union (names_add x empty) (binds g'));
    pose proof (subset_union_names_add_l empty (binds g') x); destruct H12;
    try apply subset_in_intersect with (names_add x (union empty (binds g')));
    try apply intersect_names_add_intro_r;
    try apply subset_in_intersect with (binds g'); try apply union_empty_l;
    try apply csubst_env_unique;
    try apply lem_denotesenv_closed with g;
    try apply lem_denotesenv_substitutable with g;
    unfold in_csubst; unfold in_env; 
    try rewrite csubst_env_binds; 
    try rewrite <- lem_binds_env_th with g th0; auto;
    apply no_elem_empty; intros;
    try apply not_elem_subset with empty; auto.
  - (* ConsT *) inversion H4; subst a0 k1 g0; simpl;
    apply IHg; try apply lem_subst_tv_wf with k;
    inversion H0; subst a0 k1 g0;
    simpl in H1; destruct H1;
    apply intersect_names_add_elim_l in H3;
    fold binds in H3; destruct H3;
    try apply lem_erase_env_wfenv;
    try apply esubFTV_unique; try rewrite esubFTV_binds;
    trivial; rewrite <- lem_empty_concatE at 1;
    apply lem_weaken_many_wf; unfold unique; trivial.
  Qed.  
    
Lemma lem_ctsubst_wf : forall (g:env) (t:type) (k:kind) (th:csub),
    WFtype g t k -> WFEnv g -> unique g -> DenotesEnv g th
        -> WFtype Empty (ctsubst th t) k.
Proof. intros; assert (Empty = csubst_env th Empty)
      by (symmetry; apply lem_csubst_env_empty);
  rewrite H3; apply lem_ctsubst_wf' with g; simpl;
  try apply intersect_empty_r; trivial. Qed.

(*
{-@ lem_subst_wfenv :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> ProofOf(HasFType (erase_env g) v_x (erase t_x))
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') )
        -> ProofOf(WFEnv (concatE g (esubFV x v_x g')) ) / [envsize g'] @-}
lem_subst_wfenv :: Env -> Env -> Vname -> Expr -> Type -> HasFType -> WFEnv -> WFEnv
lem_subst_wfenv g Empty           x v_x t_x p_vx_tx p_xg_wf  = case p_xg_wf of
  (WFEBind  _g p_g_wf _x _tx _ _) -> p_g_wf
  (WFEBindT _g p_g_wf _  _)       -> p_g_wf
lem_subst_wfenv g (Cons z_ t_z g') x v_x t_x p_vx_tx p_env_wf = case p_env_wf of
  (WFEBind env' p_env'_wf _z _tz k_z p_env'_tz) 
    -> WFEBind env'' p_env''_wf z (tsubFV x v_x t_z) k_z p_env''_tzvx
      where
        z            = z_ ? lem_in_env_concat (Cons x t_x g) g' z_
                          ? lem_in_env_esub g' x v_x z_ 
                          ? lem_in_env_concat g (esubFV x v_x g') z_
        env''        = concatE g (esubFV x v_x g')
        p_env''_wf   = lem_subst_wfenv g g' x v_x t_x p_vx_tx p_env'_wf
        p_env''_tzvx = lem_subst_wf    g g' x v_x t_x p_vx_tx p_env'_wf t_z k_z p_env'_tz
lem_subst_wfenv g (ConsT a_ k_a g') x v_x t_x p_vx_tx p_env_wf = case p_env_wf of
  (WFEBindT env' p_env'_wf _a _ka)           -> WFEBindT env'' p_env''_wf a k_a
    where
      a          = a_ ? lem_in_env_concat (Cons x t_x g) g' a_
                      ? lem_in_env_esub g' x v_x a_ 
                      ? lem_in_env_concat g (esubFV x v_x g') a_
      env''      = concatE g (esubFV x v_x g')
      p_env''_wf = lem_subst_wfenv g g' x v_x t_x p_vx_tx p_env'_wf

{-@ lem_subst_wfenv' :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> ProofOf(HasType g v_x t_x)
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') )
        -> ProofOf(WFEnv (concatE g (esubFV x v_x g')) ) @-}
lem_subst_wfenv' :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv -> WFEnv
lem_subst_wfenv' g g' x v_x t_x p_vx_tx p_env_wf  
  = lem_subst_wfenv g g' x v_x t_x p_vx_er_tx p_env_wf
      where
        p_xg_wf    = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _ _) = p_xg_wf
        p_vx_er_tx = lem_typing_hasftype g v_x t_x p_vx_tx p_g_wf

{-@ lem_subst_tv_wfenv :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') )
        -> ProofOf(WFEnv (concatE g (esubFTV a t_a g')) ) / [envsize g'] @-}
lem_subst_tv_wfenv :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv -> WFEnv
lem_subst_tv_wfenv g Empty           a t_a k_a p_g_ta p_xg_wf  = case p_xg_wf of
  (WFEBind  _g p_g_wf _ _ _ _) -> p_g_wf
  (WFEBindT _g p_g_wf _ _)     -> p_g_wf
lem_subst_tv_wfenv g (Cons z_ t_z g') a t_a k_a p_g_ta p_env_wf = case p_env_wf of
  (WFEBind env' p_env'_wf _z _tz k_z p_env'_tz) 
    -> WFEBind env'' p_env''_wf z (tsubFTV a t_a t_z) k_z p_env''_tzta
      where
        z            = z_ ? lem_in_env_concat (ConsT a k_a g) g' z_
                          ? lem_in_env_esubFTV g' a t_a z_ 
                          ? lem_in_env_concat g (esubFTV a t_a g') z_
        env''        = concatE g (esubFTV a t_a g')
        p_env''_wf   = lem_subst_tv_wfenv g g' a t_a k_a p_g_ta p_env'_wf
        p_env''_tzta = lem_subst_tv_wf'   g g' a t_a k_a p_g_ta p_env'_wf t_z k_z p_env'_tz
lem_subst_tv_wfenv g (ConsT a1_ k1 g') a t_a k_a p_g_ta p_env_wf = case p_env_wf of
  (WFEBindT env' p_env'_wf _a1 _k1)          -> WFEBindT env'' p_env''_wf a1 k1
    where
      a1         = a1_ ? lem_in_env_concat (ConsT a k_a g) g' a1_
                       ? lem_in_env_esubFTV g' a t_a a1_ 
                       ? lem_in_env_concat g (esubFTV a t_a g') a1_
      env''      = concatE g (esubFTV a t_a g')
      p_env''_wf = lem_subst_tv_wfenv g g' a t_a k_a p_g_ta p_env'_wf

{-@ lem_csubst_wfenv :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> th:CSub -> ProofOf(DenotesEnv g th) -> ProofOf(WFEnv (concatE g g'))
        -> ProofOf(WFEnv (csubst_env th g')) / [envsize g] @-}
lem_csubst_wfenv :: Env -> Env -> CSub -> DenotesEnv -> WFEnv -> WFEnv
lem_csubst_wfenv Empty           g'  th   den_g_th p_g'_wf   = case den_g_th of 
  DEmp  -> p_g'_wf ? lem_empty_concatE g' 
lem_csubst_wfenv (Cons x t_x g)  g' xth den_xg_xth p_g'xg_wf = case den_xg_xth of
  (DExt _g th_ den_g_th _x _tx v_x den_thtx_vx) -> p_g'_wf
    where
      th         = th_ ? lem_binds_env_th g th_ den_g_th
      p_emp_vx_thtx  = get_ftyp_from_den (ctsubst th t_x) v_x den_thtx_vx ? lem_erase_ctsubst th t_x
      p_g'x_wf   = lem_csubst_wfenv g (concatE (Cons x t_x Empty) g') th den_g_th 
                                    (p_g'xg_wf ? lem_concat_shift g x t_x g')
                                    ? lem_csubst_env_concat th (Cons x t_x Empty) g'
                                    ? lem_csubst_cons_env th x t_x Empty
                                    ? lem_csubst_env_empty th
      p_g'_wf    = lem_subst_wfenv Empty (csubst_env th g') x v_x (ctsubst th t_x) p_emp_vx_thtx
                                   p_g'x_wf ? lem_empty_concatE (esubFV x v_x (csubst_env th g'))
                                           ? lem_unroll_csubst_env_left th x v_x g'
lem_csubst_wfenv (ConsT a k_a g) g' ath den_ag_ath p_g'ag_wf = case den_ag_ath of 
  (DExtT _g th_ den_g_th _a _ka t_a p_emp_ta) -> p_g'_wf
    where
      th         = th_ ? lem_binds_env_th g th_ den_g_th
      p_ag_wf    = lem_truncate_wfenv (ConsT a k_a g)  g' p_g'ag_wf
      (WFEBindT _ p_g_wf _ _) = p_ag_wf
      p_g_ta     = lem_weaken_many_wf' Empty g (p_g_wf ? lem_empty_concatE g) t_a k_a p_emp_ta
      p_g'g_wf   = lem_subst_tv_wfenv g g' a t_a k_a p_g_ta p_g'ag_wf
      p_g'_wf    = lem_csubst_wfenv g (esubFTV a t_a g') th den_g_th p_g'g_wf
  *)