Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.Typing.
(*Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.*)
Require Import Denotations.ClosingSubstitutions.
Require Import Denotations.Denotations.
Require Import Denotations.BasicPropsCSubst.
Require Import Denotations.PrimitivesDenotations.

Lemma lem_denote_sound : ( forall (g:env) (e:expr) (t:type),
    Hastype g e t -> forall (th:csub),
        WFEnv g -> DenotesEnv g th 
            -> EvalsDenotes (ctsubst th t) (csubst th e) ) /\ (
  forall (g:env) (t1 t2:type),
    Subtype g t1 t2 -> forall (k1:kind) (k2:kind) (th:csub),
        WFEnv g -> WFtype g t1 k1 -> WFtype g t2 k2 -> DenotesEnv g th
            -> (forall (v:expr), isValue v
                -> Denotes (ctsubst th t1) v -> Denotes (ctsubst th t2) v) ).
Proof. apply ( judgments_mutind
  (fun (g:env) (e:expr) (t:type) (p_e_t : Hastype g e t) =>
    forall (th:csub), WFEnv g -> DenotesEnv g th 
        -> EvalsDenotes (ctsubst th t) (csubst th e) )
  (fun (g:env) (t1 t2:type) (p_t1_t2 : Subtype g t1 t2) =>
    forall (k1 k2:kind) (th:csub),
      WFEnv g -> WFtype g t1 k1 -> WFtype g t2 k2 -> DenotesEnv g th
        -> (forall (v:expr), isValue v
              -> Denotes (ctsubst th t1) v -> Denotes (ctsubst th t2) v) ));
  intros.
  - (* TBC *) rewrite lem_csubst_bc; rewrite lem_ctsubst_nofree;
    try apply lem_den_evalsdenotes; try apply lem_den_tybc;
    unfold tybc; simpl; reflexivity.
  - (* TIC *) rewrite lem_csubst_ic; rewrite lem_ctsubst_nofree;
    try apply lem_den_evalsdenotes; try apply lem_den_tyic;
    unfold tyic; simpl; reflexivity.
  - (* TVar *) unfold EvalsDenotes.
  
  inversion H0; try (subst g; simpl in b; contradiction).

  (*
lem_denote_sound_typ_tvar1 g e t (TVar1 g' x t' k' p_g'_t') (WFEBind _ wf_g' _ _ _ _p_g'_t') th den_g_th  
  = case den_g_th of              -- e == FV x, t == self t x 
      (DExt _g' th' den_g'_th' _x _t' w den_th't'_w)  -- w = th(x)
        -> ValDen (csubst th e) (ctsubst th t) w ev_the_v' den_tht_thx
             where
               ev_the_v' = Refl w `withProof` lem_den_nofv w (ctsubst th' t') den_th't'_w
                                  `withProof` lem_den_nobv w (ctsubst th' t') den_th't'_w
                                  `withProof` lem_csubst_nofv th' w
               p_emp_th't' = lem_ctsubst_wf g' Empty t' k' p_g'_t' wf_g' th' den_g'_th'
                                        ? lem_csubst_env_empty th'
               p_w_erth't' = get_ftyp_from_den (ctsubst th' t') w den_th't'_w
               den_tht_thx = lem_denotations_selfify (ctsubst th' t') k' p_emp_th't' w p_w_erth't'
                                        w (Refl w) den_th't'_w 
                                        ? lem_free_bound_in_env g' t' k' p_g'_t' x
                                        ? lem_binds_env_th g' th' den_g'_th'
                                        ? lem_tsubFV_notin x w t'
                                        ? lem_ctsubst_self th t' (FV x) k'

{- @ ple lem_denote_sound_typ_tvar2 @-}
{-@ lem_denote_sound_typ_tvar2 :: g:Env -> e:Term -> t:Type 
                -> { p_e_t:HasType | propOf p_e_t == HasType g e t && isTVar2 p_e_t } -> ProofOf(WFEnv g) 
                ->  th:CSub  -> ProofOf(DenotesEnv g th)  
                -> ProofOf(ValueDenoted (csubst th e) (ctsubst th t)) / [typSize p_e_t, 0] @-}
lem_denote_sound_typ_tvar2 :: Env -> Expr -> Type -> HasType -> WFEnv -> CSub 
                            -> DenotesEnv -> ValueDenoted
lem_denote_sound_typ_tvar2 g e t (TVar2 g' x _t p_x_t y t_y) pf_g_wf th den_g_th
  = case den_g_th of 
      (DExt _g' th' den_g'_th' _y _ v_y den_tht_thy) 
        -> ValDen (csubst th e) (ctsubst th t) thx ev_the_v' den_tht_thx
            where
              (WFEBind _ pf_g'_wf _ _ _ p_g'_ty) = pf_g_wf
              {-@  thx :: Value @-} 
              (ValDen _ _ thx pf1 pf2) = lem_denote_sound_typ g' e t p_x_t pf_g'_wf th' den_g'_th' 
              p_g'_t      = lem_typing_wf g' (FV x) t p_x_t pf_g'_wf 
              ev_the_v'   = pf1 `withProof` lem_den_nofv thx (ctsubst th' t) pf2
                                `withProof` lem_csubst_nofv th' thx
              den_tht_thx = pf2 ? lem_free_bound_in_env g' t Star p_g'_t y
                                ? lem_binds_env_th g' th' den_g'_th' 
                                ? lem_tsubFV_notin y v_y t

{- @ ple lem_denote_sound_typ_tvar3 @-}
{-@ lem_denote_sound_typ_tvar3 :: g:Env -> e:Term -> t:Type 
                -> { p_e_t:HasType | propOf p_e_t == HasType g e t && isTVar3 p_e_t } -> ProofOf(WFEnv g) 
                ->  th:CSub  -> ProofOf(DenotesEnv g th)  
                -> ProofOf(ValueDenoted (csubst th e) (ctsubst th t)) / [typSize p_e_t, 0] @-}
lem_denote_sound_typ_tvar3 :: Env -> Expr -> Type -> HasType -> WFEnv -> CSub 
                            -> DenotesEnv -> ValueDenoted
lem_denote_sound_typ_tvar3 g e t (TVar3 g' x _t p_x_t a k_a) pf_g_wf th den_g_th
  = case den_g_th of 
      (DExtT _g' th' den_g'_th' _a _ka t_a p_emp_ta) 
        -> ValDen (csubst th e) (ctsubst th t) thx ev_the_v' den_tht_thx
             where
               (WFEBindT _ pf_g'_wf _ _) = pf_g_wf
               {-@ thx :: Value @-}
               (ValDen _ _ thx pf1 pf2) = lem_denote_sound_typ g' e t p_x_t pf_g'_wf th' den_g'_th'
               p_g'_t      = lem_typing_wf g' (FV x) t p_x_t pf_g'_wf 
               ev_the_v'   = pf1 `withProof` lem_den_nofv thx (ctsubst th' t) pf2
                                 `withProof` lem_csubst_nofv th' thx
               den_tht_thx = pf2 ? lem_free_bound_in_env g' t Star p_g'_t a
                                 ? lem_binds_env_th g' th' den_g'_th'
                                 ? lem_tsubFTV_notin a t_a t

{- @ ple lem_denote_sound_typ_tabs @-}
{-@ lem_denote_sound_typ_tabs :: g:Env -> e:Term -> t:Type 
                -> { p_e_t:HasType | propOf p_e_t == HasType g e t && isTAbs p_e_t } -> ProofOf(WFEnv g) 
                ->  th:CSub  -> ProofOf(DenotesEnv g th)  
                -> ProofOf(ValueDenoted (csubst th e) (ctsubst th t)) / [typSize p_e_t, 0] @-}
lem_denote_sound_typ_tabs :: Env -> Expr -> Type -> HasType -> WFEnv -> CSub 
                            -> DenotesEnv -> ValueDenoted
lem_denote_sound_typ_tabs g e t p_e_t@(TAbs _g x t_x k_x p_g_tx e' t' y p_yg_e'_t') p_g_wf th den_g_th
  = ValDen (csubst th e) (ctsubst th t) v ev_the_v den_tht_v
      where 
        {-@ v :: { z:Value | z == csubst th e && e == Lambda x e'} @-} -- need to show (Lambda x e') is value 
        v = Lambda x (csubst th e') ? lem_csubst_lambda th x e'        -- i.e. v = csubst th e
        ev_the_v    = Refl (csubst th e) ? lem_csubst_lambda th x e'
        p_er_g_wf   = lem_erase_env_wfenv  g p_g_wf 
        p_e_er_t    = lem_typing_hasftype  g e t p_e_t    p_g_wf
        p_v_er_txt' = lem_csubst_hasftype' g e t p_e_er_t p_er_g_wf th den_g_th
                                      ? lem_ctsubst_func th x t_x t'
        den_tht_v = DFunc x (ctsubst th t_x) (ctsubst th t') v p_v_er_txt' pf_den_tht'vx_vvx 
        {-@ pf_den_tht'vx_vvx :: v_x:Value -> ProofOf(Denotes (ctsubst th t_x) v_x)
                     -> ProofOf(ValueDenoted (App v v_x) (tsubBV x v_x (ctsubst th t'))) @-}
        pf_den_tht'vx_vvx :: Expr -> Denotes -> ValueDenoted
        pf_den_tht'vx_vvx v_x den_thtx_vx 
                  = ValDen (App v v_x) (tsubBV x v_x (ctsubst th t')) v' ev_vvx_v' 
                           (den_tht'vx_v' ? lem_ctsubst_and_unbindT x y v_x (erase (ctsubst th t_x)) 
                                                                    pf_vx_er_tx th t')
          where
            th'            = CCons y v_x (th ? lem_binds_env_th g th den_g_th)
            den_g'_th'     = DExt g th den_g_th y t_x (v_x ? lem_den_nofv v_x (ctsubst th t_x) den_thtx_vx
                                                           ? lem_den_nobv v_x (ctsubst th t_x) den_thtx_vx)
                                  den_thtx_vx
            pf_vx_er_tx    = get_ftyp_from_den (ctsubst th t_x) v_x den_thtx_vx 
            (ValDen _ _ v' ev_th'e'_v' den_tht'vx_v') = lem_denote_sound_typ (Cons y t_x g) (unbind x y e') 
                                            (unbindT x y t') p_yg_e'_t' 
                                            (WFEBind g p_g_wf y t_x k_x p_g_tx) th' den_g'_th'
            step_vvx_th'e' = EAppAbs x (csubst th e') v_x  
            ev_vvx_v'      = AddStep (App v v_x) (subBV x v_x (csubst th e')) step_vvx_th'e'
                                     v' (ev_th'e'_v' ? lem_csubst_and_unbind x y v_x 
                                                           (erase (ctsubst th t_x)) pf_vx_er_tx th e')
 
{- @ ple lem_denote_sound_typ_tapp @-}
{-@ lem_denote_sound_typ_tapp :: g:Env -> e:Term -> t:Type 
                -> { p_e_t:HasType | propOf p_e_t == HasType g e t && isTApp p_e_t } -> ProofOf(WFEnv g) 
                ->  th:CSub  -> ProofOf(DenotesEnv g th)  
                -> ProofOf(ValueDenoted (csubst th e) (ctsubst th t)) / [typSize p_e_t, 0] @-}
lem_denote_sound_typ_tapp :: Env -> Expr -> Type -> HasType -> WFEnv -> CSub 
                            -> DenotesEnv -> ValueDenoted
lem_denote_sound_typ_tapp g e t p_e_t@(TApp _g e' x t_x t' p_e_txt' e_x p_ex_tx) p_g_wf th den_g_th 
  = ValDen (csubst th e) (ctsubst th t)  v''  ev_the_v''  den_tht_v'' 
     where
      (ValDen _ _ v'  ev_the'_v' den_thtxt'_v'_) = lem_denote_sound_typ g e' (TFunc x t_x t') 
                                                       p_e_txt' p_g_wf th den_g_th
      (ValDen _ _ v_x ev_thex_vx den_thtx_vx)    = lem_denote_sound_typ g e_x t_x p_ex_tx 
                                                       p_g_wf th den_g_th
      {-@ den_thtxt'_v' :: { pf:Denotes | propOf pf == Denotes (ctsubst th (TFunc x t_x t')) v' } @-}
      den_thtxt'_v'  = den_thtxt'_v'_ ? lem_ctsubst_func th x t_x t'
      p_v'_ertxt'    = get_ftyp_from_den (ctsubst th (TFunc x t_x t')) v' den_thtxt'_v'
      reducer        = get_obj_from_dfunc x (ctsubst th t_x) (ctsubst th t') v' den_thtxt'_v'
      (ValDen _ _ v'' ev_v'vx_v'' den_tht'vx_v'') = reducer v_x den_thtx_vx
      ev_the_v'vx    = lemma_app_both_many (csubst th e')  v'  ev_the'_v'
                                           (csubst th e_x) v_x ev_thex_vx
                           `withProof` lem_csubst_app th e' e_x
      {-@ ev_the_v'' :: ProofOf(EvalsTo (csubst th e) v'') @-}
      ev_the_v''     = lemma_evals_trans (csubst th (App e' e_x)) (App v' v_x) v''
                                      ev_the_v'vx ev_v'vx_v''
                           `withProof` lem_csubst_app th e' e_x

      p_vx_ertx      = get_ftyp_from_den (ctsubst th t_x) v_x den_thtx_vx 
      p_v'vx_ert     = FTApp FEmpty v' (erase (ctsubst th t_x)) (erase (ctsubst th t'))
                             p_v'_ertxt' --`withProof` lem_ctsubst_func th x t_x t') 
                             v_x p_vx_ertx  
      p_v''_ert      = lemma_many_preservation (App v' v_x) (v'' ? lem_value_pred v'') 
                                       ev_v'vx_v'' (erase (ctsubst th t')) p_v'vx_ert 
      {-@ den_tht_v'' :: ProofOf(Denotes (ctsubst th t) v'') @-}
      den_tht_v''    = DExis x (ctsubst th t_x) (ctsubst th t') v'' p_v''_ert v_x 
                           den_thtx_vx den_tht'vx_v'' ? lem_ctsubst_exis th x t_x t' 

{- @ ple lem_denote_sound_typ_tabst @-}
{-@ lem_denote_sound_typ_tabst :: g:Env -> e:Term -> t:Type 
                -> { p_e_t:HasType | propOf p_e_t == HasType g e t && isTAbsT p_e_t } -> ProofOf(WFEnv g) 
                ->  th:CSub -> ProofOf(DenotesEnv g th)  
                -> ProofOf(ValueDenoted (csubst th e) (ctsubst th t)) / [typSize p_e_t, 0] @-}
lem_denote_sound_typ_tabst :: Env -> Expr -> Type -> HasType -> WFEnv -> CSub 
                            -> DenotesEnv -> ValueDenoted
lem_denote_sound_typ_tabst g e t p_e_t@(TAbsT _g a k e' t' k' a' p_e'_t' p_a'g_t') p_g_wf th den_g_th 
  = ValDen (csubst th e) (ctsubst th t) v ev_the_v den_tht_v
      where 
        {-@ v :: { z:Value | z == csubst th e && e == LambdaT a k e'} @-} -- WTS: (LambdaT a k e') isValue 
        v = LambdaT a k (csubst th e') ? lem_csubst_lambdaT th a k e' 
        ev_the_v  = Refl (csubst th e) ? lem_csubst_lambdaT th a k e'
        
        p_v_er_tht = lem_csubst_hasftype g e t p_e_t p_g_wf th den_g_th ? lem_ctsubst_poly th a k t'
        den_tht_v = DPoly a k (ctsubst th t') v p_v_er_tht -- a0 s' eqv_s_er_tht p_e_s
                          pf_den_tht'ta_vta
        {-@ pf_den_tht'ta_vta :: t_a:UserType -> ProofOf(WFType Empty t_a k)
                     -> ProofOf(ValueDenoted (AppT v t_a) (tsubBTV a t_a (ctsubst th t'))) @-}
        pf_den_tht'ta_vta :: Type -> WFType -> ValueDenoted
        pf_den_tht'ta_vta t_a p_emp_ta = ValDen (AppT v t_a) (tsubBTV a t_a (ctsubst th t'))
                                 v' ev_vta_v' (den_tht'ta_v' 
                                     ? lem_ctsubst_and_unbind_tvT a a' t_a k p_emp_ta th t')
          where
            th'            = CConsT a' t_a (th ? lem_binds_env_th g th den_g_th)
            den_g'_th'     = DExtT g th den_g_th a' k (t_a ? lem_free_subset_binds Empty t_a k p_emp_ta
                                                           ? lem_tfreeBV_empty Empty t_a k p_emp_ta)
                                   p_emp_ta

            (ValDen _ _ v' ev_th'e'_v' den_tht'ta_v') = lem_denote_sound_typ (ConsT a' k g) 
                                   (unbind_tv a a' e') (unbind_tvT a a' t') p_e'_t' 
                                   (WFEBindT g p_g_wf a' k) th' den_g'_th'
            step_vta_th'e' = EAppTAbs a k (csubst th e') t_a
            ev_vta_v'      = AddStep (AppT v t_a) (subBTV a t_a (csubst th e')) step_vta_th'e'
                                     v' (ev_th'e'_v' ? lem_csubst_and_unbind_tv a a' t_a k p_emp_ta th e')

{- @ ple lem_denote_sound_typ_tappt @-}
{-@ lem_denote_sound_typ_tappt :: g:Env -> e:Term -> t:Type 
                -> { p_e_t:HasType | propOf p_e_t == HasType g e t && isTAppT p_e_t } -> ProofOf(WFEnv g) 
                ->  th:CSub  -> ProofOf(DenotesEnv g th)  
                -> ProofOf(ValueDenoted (csubst th e) (ctsubst th t)) / [typSize p_e_t, 0] @-}
lem_denote_sound_typ_tappt :: Env -> Expr -> Type -> HasType -> WFEnv -> CSub 
                            -> DenotesEnv -> ValueDenoted
lem_denote_sound_typ_tappt g e t (TAppT _ e' a k s p_e_as t' p_g_t') p_g_wf th den_g_th  
  = ValDen (csubst th e) (ctsubst th t) v'' ev_the_v'' (den_tht_v''
                        ? lem_commute_ctsubst_tsubBTV th a t' s)
      where
        {-@ den_thas_v' :: { pf:Denotes | propOf pf == Denotes (TPoly a k (ctsubst th s)) v' } @-} 
        (ValDen _ _ v' ev_the'_v' den_thas_v') = lem_denote_sound_typ g e' (TPoly a k s)
                                                     p_e_as p_g_wf th den_g_th
                                                     ? lem_ctsubst_poly th a k s   
        ev_the_v'tht' = lemma_appT_many (csubst th e') v' 
                                        (ctsubst th t' ? lem_ctsubst_usertype th t') ev_the'_v'
                                        ? lem_csubst_appT th e' t'
        p_emp_tht'    = lem_ctsubst_wf g Empty t' k p_g_t' p_g_wf th den_g_th
                            ? lem_csubst_env_empty th
        prover        = get_obj_from_dpoly a k (ctsubst th s) v' den_thas_v'
        {-@ den_tht_v'' :: {pf:Denotes | propOf pf == Denotes (tsubBTV a (ctsubst th t') (ctsubst th s)) v''} @-}
        (ValDen _ _ v'' ev_v'tht'_v'' den_tht_v'') 
                      = prover (ctsubst th t' ? lem_ctsubst_usertype th t') p_emp_tht'
        ev_the_v''    = lemma_evals_trans (csubst th e) (AppT v' (ctsubst th t')) v''
                                          ev_the_v'tht' ev_v'tht'_v''

{- @ ple lem_denote_sound_typ_tlet @-}
{-@ lem_denote_sound_typ_tlet :: g:Env -> e:Term -> t:Type 
                -> { p_e_t:HasType | propOf p_e_t == HasType g e t && isTLet p_e_t } -> ProofOf(WFEnv g) 
                ->  th:CSub  -> ProofOf(DenotesEnv g th)  
                -> ProofOf(ValueDenoted (csubst th e) (ctsubst th t)) / [typSize p_e_t, 0] @-}
lem_denote_sound_typ_tlet :: Env -> Expr -> Type -> HasType -> WFEnv -> CSub 
                            -> DenotesEnv -> ValueDenoted
lem_denote_sound_typ_tlet g e t (TLet _g e_x t_x p_ex_tx x e' _t k p_g_t y p_yg_e'_t) p_g_wf th den_g_th 
  = case (lem_denote_sound_typ g e_x t_x p_ex_tx p_g_wf th den_g_th) of 
      (ValDen _ _ v_x_ ev_thex_vx den_thtx_vx) 
        -> ValDen (csubst th e) (ctsubst th t) v ev_the_v den_tht_v 
          where
            {-@ v_x :: { v_x:Value | Set_emp (fv v_x) && v_x == v_x_ } @-}
            v_x                = v_x_ ? lem_den_nofv v_x_ (ctsubst th t_x) den_thtx_vx
                                      ? lem_den_nobv v_x_ (ctsubst th t_x) den_thtx_vx
            p_vx_er_thtx       = get_ftyp_from_den (ctsubst th t_x) v_x den_thtx_vx
            th'                = CCons y v_x (th ? lem_binds_env_th g th den_g_th)
            den_g'_th'         = DExt g th den_g_th y t_x v_x den_thtx_vx 
            p_g_tx             = lem_typing_wf g e_x t_x p_ex_tx p_g_wf 
            {-@ v :: Value @-}
            (ValDen _ _ v ev_th'e'_v den_th't_v) = lem_denote_sound_typ (Cons y t_x g) (unbind x y e')
                                      (unbindT x y t) p_yg_e'_t
                                      (WFEBind g p_g_wf y t_x Star p_g_tx) th' den_g'_th'  
                                      ? lem_ctsubst_and_unbindT x y v_x (erase (ctsubst th t_x)) 
                                                                p_vx_er_thtx th t 
            ev_the_vxthe'      = lemma_let_many x (csubst th e_x) v_x (csubst th e') ev_thex_vx
            step_vxthe'_th'e'  = ELetV x v_x (csubst th e')
            ev_vxthe'_v        = AddStep (Let x v_x (csubst th e')) (subBV x v_x (csubst th e'))
                                   step_vxthe'_th'e' v 
                                   (ev_th'e'_v ? lem_csubst_and_unbind x y v_x (erase (ctsubst th t_x))
                                                                       p_vx_er_thtx  th e')
            ev_the_v           = lemma_evals_trans (csubst th e) (Let x v_x (csubst th e')) v
                                      (ev_the_vxthe' ? lem_csubst_let th x e_x e') ev_vxthe'_v
            {-@ den_tht_v :: ProofOf(Denotes (ctsubst th t) v) @-}
            den_tht_v          = den_th't_v ? lem_ctsubst_and_unbindT x y v_x (erase (ctsubst th t_x))
                                                                      p_vx_er_thtx th t
                                      ? lem_tfreeBV_empty g t k p_g_t
                                      ? lem_ctsubst_nofreeBV th t
                                      ? lem_tsubBV_notin x v_x (ctsubst th t) 

{- @ ple lem_denote_sound_typ_tann @-}
{-@ lem_denote_sound_typ_tann :: g:Env -> e:Term -> t:Type 
                -> { p_e_t:HasType | propOf p_e_t == HasType g e t && isTAnn p_e_t } -> ProofOf(WFEnv g) 
                ->  th:CSub  -> ProofOf(DenotesEnv g th)  
                -> ProofOf(ValueDenoted (csubst th e) (ctsubst th t)) / [typSize p_e_t, 0] @-}
lem_denote_sound_typ_tann :: Env -> Expr -> Type -> HasType -> WFEnv -> CSub 
                            -> DenotesEnv -> ValueDenoted
lem_denote_sound_typ_tann g e t (TAnn _g e' _t p_e'_t) p_g_wf th den_g_th  
  = ValDen (csubst th e) (ctsubst th t) v (ev_the_v ? lem_csubst_annot th e' t) den_tht_v
    where
      (ValDen _ _ v ev_the'_v den_tht_v) = lem_denote_sound_typ g e' t p_e'_t p_g_wf th den_g_th
      ev_the't_vt = lemma_annot_many (csubst th e') v (ctsubst th t) ev_the'_v 
      step_vt_v   = EAnnV v (ctsubst th t)
      ev_vt_v     = AddStep (Annot v (ctsubst th t)) v step_vt_v v (Refl v)
      {-@ ev_the_v :: { pf:EvalsTo | propOf pf == EvalsTo (Annot (csubst th e') (ctsubst th t)) v && 
                                             e == Annot e' t } @-}
      ev_the_v    = lemma_evals_trans (Annot (csubst th e') (ctsubst th t)) 
                                      (Annot v (ctsubst th t)) v ev_the't_vt ev_vt_v 

{- @ ple lem_denote_sound_typ_tsub @-}
{-@ lem_denote_sound_typ_tsub :: g:Env -> e:Term -> t:Type 
                -> { p_e_t:HasType | propOf p_e_t == HasType g e t && isTSub p_e_t } -> ProofOf(WFEnv g) 
                ->  th:CSub  -> ProofOf(DenotesEnv g th)  
                -> ProofOf(ValueDenoted (csubst th e) (ctsubst th t)) / [typSize p_e_t, 0] @-}
lem_denote_sound_typ_tsub :: Env -> Expr -> Type -> HasType -> WFEnv -> CSub 
                            -> DenotesEnv -> ValueDenoted
lem_denote_sound_typ_tsub g e t (TSub _g _e s p_e_s _t k p_g_t p_s_t) p_g_wf th den_g_th 
  = ValDen (csubst th e) (ctsubst th t) v ev_the_v den_tht_v
    where
      p_g_s     = lem_typing_wf g e s p_e_s p_g_wf
      (ValDen _ _ v ev_the_v den_ths_v) = lem_denote_sound_typ g e s p_e_s p_g_wf th den_g_th
      den_tht_v = lem_denote_sound_sub g s Star t k p_s_t p_g_wf p_g_s p_g_t th den_g_th v den_ths_v 
      
{-@ lem_wfftvar_tv_in_csubst :: g:Env -> a:Vname -> k:Kind 
        -> ProofOf(WFFT (erase_env g) (FTBasic (FTV a)) k) -> th:CSub -> ProofOf(DenotesEnv g th)
        -> { pf:_ | tv_in_env a g && tv_in_csubst a th } @-}
lem_wfftvar_tv_in_csubst :: Env -> Vname -> Kind -> WFFT -> CSub -> DenotesEnv -> Proof
lem_wfftvar_tv_in_csubst g a k p_g_a th den_g_th
  = () ? lem_wfftvar_tv_in_env (erase_env g) a k p_g_a
       ? lem_binds_env_th g th den_g_th

{-@ lem_make_denote_strengthen :: g:Env -> th:CSub  -> a:Vname
        -> x1:RVname -> { p1:Pred | Set_sub (fv p1) (vbinds g) && Set_sub (ftv p1) (tvbinds g) } 
        -> x2:RVname -> p2:Pred 
        -> { y:Vname | not (in_env y g) && not (in_csubst y th) && 
                       not (Set_mem y (fv p1)) && not (Set_mem y (fv p2)) }
        -> ProofOf(Entails (Cons y (TRefn (FTV a) x1 p1) g) (unbind 0 y p2))
        -> { b:Basic | b == TBool || b == TInt } -> z:RVname 
        -> { q:Pred | Set_emp (fv q) && Set_emp (ftv q) && (TRefn b z q) == csubst_tv th a } 
        -> v:Value -> ProofOf(HasFType FEmpty v (FTBasic b))
        -> ProofOf(DenotesEnv (Cons y (TRefn (FTV a) x1 p1) g) (CCons y v th))
        -> ProofOf(HasFType FEmpty (subBV 0 v (csubst th p2)) (FTBasic TBool))
        -> ProofOf(EvalsTo (subBV 0 v q) (Bc True))
        -> ProofOf(Denotes (TRefn b z (strengthen (csubst th p2) q)) v)  @-}
lem_make_denote_strengthen :: Env -> CSub -> Vname -> RVname -> Expr -> RVname -> Expr -> Vname -> Entails 
    -> Basic -> RVname -> Expr -> Expr -> HasFType -> DenotesEnv -> HasFType -> EvalsTo -> Denotes 
lem_make_denote_strengthen g th a x1 p1 x2 p2 y pf_ent_p2 b z q v_ p_v_b
                           den_g'_th' pf_thp2v_bl ev_qv_tt = den_t2_v 
    where
      v = v_ ? lem_fv_subset_bindsF FEmpty v_ (FTBasic b) p_v_b
             ? lem_freeBV_emptyB    FEmpty v_ (FTBasic b) p_v_b
      {-@ red_thp2_tt :: th':CSub -> ProofOf(DenotesEnv (Cons y (TRefn (FTV a) x1 p1) g) th')
                                  -> ProofOf(EvalsTo (csubst th' (unbind 0 y p2)) (Bc True)) @-}
      red_thp2_tt :: CSub -> DenotesEnv -> EvalsTo
      (EntPred y_g _p2 red_thp2_tt) = pf_ent_p2 -- this is unbind x2 y p2    
      {-@ ev_thp2v_tt :: ProofOf(EvalsTo (subBV 0 v (csubst th p2)) (Bc True)) @-} 
      ev_thp2v_tt  = red_thp2_tt (CCons y v th) den_g'_th' -- ? lem_subFV_unbind 0 y v p2
                                 ? lem_csubst_and_unbind 0 y v (FTBasic b) p_v_b th p2
      {-@ ev_thp2qv_tt :: ProofOf(EvalsTo (subBV 0 v (strengthen (csubst th p2) q)) (Bc True)) @-}
      ev_thp2qv_tt = lem_strengthen_evals_subBV (csubst th p2) q v pf_thp2v_bl ev_thp2v_tt ev_qv_tt 
      den_t2_v = DRefn b z (strengthen (csubst th p2) q) v p_v_b ev_thp2qv_tt          

{-@ lem_make_csubst_hasftype :: g:Env -> ProofOf(WFFE (erase_env g)) -> th:CSub
        -> a:Vname -> k:Kind -> ProofOf(WFFT (erase_env g) (FTBasic (FTV a)) k)
        -> x:RVname -> { p:Pred | Set_sub (fv p) (vbinds g) && Set_sub (ftv p) (tvbinds g) } 
        -> { y:Vname | not (in_env y g) && not (in_csubst y th) && not (Set_mem y (fv p)) }
        -> ProofOf(HasFType (FCons y (FTBasic (FTV a)) (erase_env g)) (unbind 0 y p) (FTBasic TBool))
        -> { b:Basic | b == TBool || b == TInt } -> z:RVname 
        -> { q:Pred | Set_emp (fv q) && Set_emp (ftv q) && (TRefn b z q) == csubst_tv th a } 
        -> k_a:Kind -> ProofOf(WFType Empty (TRefn b z q) k_a) -> ProofOf(DenotesEnv g th) -> v:Value
        -> ProofOf(HasFType FEmpty v (FTBasic b))
        -> ProofOf(HasFType FEmpty (subBV 0 v (csubst th p)) (FTBasic TBool)) @-}
lem_make_csubst_hasftype :: Env -> WFFE -> CSub -> Vname -> Kind -> WFFT -> RVname -> Expr  
        -> Vname -> HasFType -> Basic -> RVname -> Expr -> Kind -> WFType 
        -> DenotesEnv -> Expr -> HasFType -> HasFType
lem_make_csubst_hasftype g p_g_wf th a_ k p_g_a x p y pf_p_bl 
                         b z q k_a p_emp_ta den_g_th v_ p_v_b = pf_thpv_bl
    where
      a            = a_ ? lem_wfftvar_tv_in_env (erase_env g) a_ k p_g_a
                        ? lem_binds_env_th g th den_g_th
      v            = v_ ? lem_fv_subset_bindsF FEmpty v_ (FTBasic b) p_v_b
                        ? lem_freeBV_emptyB    FEmpty v_ (FTBasic b) p_v_b
      th'          = CCons y v th -- (th ? lem_binds_env_th g th den_g_th)
      p_yg_wf      = WFFBind (erase_env g) p_g_wf y (FTBasic (FTV a)) k p_g_a
                             ? lem_erase_concat g (Cons y (TRefn (FTV a) Z (Bc True)) Empty)
      p_emp_er_ta  = lem_erase_wftype Empty (TRefn b z q) k_a p_emp_ta
      p_y_wf       = WFFBind FEmpty WFFEmpty y (FTBasic b) k_a p_emp_er_ta

      {-@ pf_thp_bl :: ProofOf(HasFType (FCons y (FTBasic b) FEmpty) 
                                        (unbind 0 y (csubst th p)) (FTBasic TBool)) @-}
      pf_thp_bl    = lem_partial_csubst_hasftype g (Cons y (TRefn (FTV a) Z (Bc True)) Empty)
                             p_yg_wf th den_g_th (unbind 0 y p) (TRefn TBool Z (Bc True)) pf_p_bl 
                             ? lem_commute_csubst_subBV th 0 (FV y) p
                             ? lem_csubst_cons_env th y (TRefn (FTV a) Z (Bc True)) Empty
                             ? lem_csubst_env_empty th
                             ? lem_csubst_fv th y
                             ? lem_ctsubst_refn_tv' th a Z (Bc True) b z q
                             ? lem_ctsubst_nofree th (TRefn TBool Z (Bc True))
      {-@ pf_thpv_bl :: ProofOf(HasFType FEmpty (subBV 0 v (csubst th p)) (FTBasic TBool)) @-}
      pf_thpv_bl   = lem_subst_ftyp FEmpty FEmpty y v (FTBasic b) p_v_b p_y_wf
                             (unbind 0 y (csubst th p)) (FTBasic TBool) pf_thp_bl
                             ? lem_subFV_unbind 0 (y ? lem_csubst_no_more_fv th p) v (csubst th p)
                             ? lem_empty_concatF FEmpty

{-@ lem_denote_push_ent_pred_trefn :: g:Env -> ProofOf(WFFE (erase_env g)) 
        -> a:Vname -> k:Kind -> ProofOf(WFFT (erase_env g) (FTBasic (FTV a)) k)
        -> x1:RVname -> { p1:Pred | Set_sub (fv p1) (vbinds g) && Set_sub (ftv p1) (tvbinds g) } 
        -> x2:RVname -> { p2:Pred | Set_sub (fv p2) (vbinds g) && Set_sub (ftv p2) (tvbinds g) }
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p1)) && not (Set_mem y (fv p2)) }
        -> ProofOf(HasFType (FCons y (FTBasic (FTV a)) (erase_env g)) (unbind 0 y p1) (FTBasic TBool))
        -> ProofOf(HasFType (FCons y (FTBasic (FTV a)) (erase_env g)) (unbind 0 y p2) (FTBasic TBool))
        -> ProofOf(Entails (Cons y (TRefn (FTV a) x1 p1) g) (unbind 0 y p2))
        -> { th:CSub | not (in_csubst y th) } 
        -> { b:Basic | b == TBool || b == TInt } -> z:RVname 
        -> { q:Pred | Set_emp (fv q) && Set_emp (ftv q) && (TRefn b z q) == csubst_tv th a } 
        -> k_a:Kind -> ProofOf(WFType Empty (TRefn b z q) k_a) -> ProofOf(DenotesEnv g th) -> v:Value
        -> ProofOf(Denotes (TRefn b z (strengthen (csubst th p1) q)) v) 
        -> ProofOf(Denotes (TRefn b z (strengthen (csubst th p2) q)) v)  @-}
lem_denote_push_ent_pred_trefn :: Env -> WFFE -> Vname -> Kind -> WFFT -> RVname -> Expr -> RVname 
    -> Expr -> Vname -> HasFType -> HasFType -> Entails -> CSub -> Basic -> RVname -> Expr -> Kind -> WFType 
    -> DenotesEnv -> Expr -> Denotes ->     Denotes 
lem_denote_push_ent_pred_trefn g p_g_wf a_ k p_g_a x1 p1 x2 p2 y pf_p1_bl pf_p2_bl pf_ent_p2 th b z q 
                               k_a p_emp_ta den_g_th v den_thp1ta_v = den_t2_v 
    where
      a            = a_ ? lem_wfftvar_tv_in_csubst g a_ k p_g_a th den_g_th
      {-@ ev_thp1qv_tt :: ProofOf(EvalsTo (subBV 0 v (strengthen (csubst th p1) q)) (Bc True)) @-}
      (DRefn _b _z str_thp1_q _v p_v_b ev_thp1qv_tt) = den_thp1ta_v
      {-@ t1 :: { t1_:Type | t1_ == ctsubst th (TRefn (FTV a) x1 p1)  } @-}
      t1           = TRefn b z (strengthen (csubst th p1) q) ? lem_ctsubst_refn_tv' th a x1 p1 b z q
                                           
      th'          = CCons y v th -- (th ? lem_binds_env_th g th den_g_th)
      {-@ den_g'_th' :: ProofOf(DenotesEnv (Cons y (TRefn (FTV a) x1 p1) g) (CCons y v th)) @-}
      den_g'_th'   = DExt g th den_g_th y (TRefn (FTV a) x1 p1) 
                          (v ? lem_den_nobv v  t1 den_thp1ta_v 
                             ? lem_den_nofv v  t1 den_thp1ta_v) den_thp1ta_v

      {-@ pf_thp1v_bl :: ProofOf(HasFType FEmpty (subBV 0 v (csubst th p1)) (FTBasic TBool)) @-}
      pf_thp1v_bl  = lem_make_csubst_hasftype g p_g_wf th a k p_g_a x1 p1 y pf_p1_bl
                         b z q k_a p_emp_ta den_g_th v p_v_b
      {-@ pf_thp2v_bl :: ProofOf(HasFType FEmpty (subBV 0 v (csubst th p2)) (FTBasic TBool)) @-}
      pf_thp2v_bl  = lem_make_csubst_hasftype g p_g_wf th a k p_g_a x2 p2 y pf_p2_bl
                         b z q k_a p_emp_ta den_g_th v p_v_b

      y'_          = fresh_var Empty
      y'           = y'_ ? lem_free_bound_in_env Empty (TRefn b z q) k_a p_emp_ta y'_
      p_emp_er_ta  = lem_erase_wftype Empty (TRefn b z q) k_a p_emp_ta
      p_y'_wf      = WFFBind FEmpty WFFEmpty y' (FTBasic b) k_a p_emp_er_ta
      pf_y'_q_bl   = lem_ftyp_for_wf_trefn' Empty b z q k_a p_emp_ta WFFEmpty
      {-@ pf_qv_bl :: ProofOf(HasFType FEmpty (subBV 0 v q) (FTBasic TBool)) @-}
      pf_qv_bl     = lem_subst_ftyp FEmpty FEmpty y' v (FTBasic b) p_v_b p_y'_wf
                                  (unbind 0 y' q) (FTBasic TBool) pf_y'_q_bl
                                  ? lem_subFV_unbind 0 y' v q
                                  ? lem_empty_concatF FEmpty
      {-@ ev_qv_tt :: ProofOf(EvalsTo (subBV 0 v q) (Bc True)) @-} 
      (_,ev_qv_tt) = lem_strengthen_elimination (subBV 0 v (csubst th p1)) (subBV 0 v q)
                                                pf_thp1v_bl pf_qv_bl (ev_thp1qv_tt
                                  ? lem_subBV_strengthen 0 v (csubst th p1) q)
      den_t2_v = lem_make_denote_strengthen g th a x1 p1 x2 p2 y pf_ent_p2 b z q v p_v_b 
                                            den_g'_th' pf_thp2v_bl ev_qv_tt 

{-@ lem_denote_push_ent_pred :: g:Env -> ProofOf(WFFE (erase_env g)) 
        -> a:Vname -> k:Kind -> ProofOf(WFFT (erase_env g) (FTBasic (FTV a)) k)
        -> x1:RVname -> { p1:Pred | Set_sub (fv p1) (vbinds g) && Set_sub (ftv p1) (tvbinds g) } 
        -> x2:RVname -> { p2:Pred | Set_sub (fv p2) (vbinds g) && Set_sub (ftv p2) (tvbinds g) }
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p1)) && not (Set_mem y (fv p2)) }
        -> ProofOf(HasFType (FCons y (FTBasic (FTV a)) (erase_env g)) (unbind 0 y p1) (FTBasic TBool))
        -> ProofOf(HasFType (FCons y (FTBasic (FTV a)) (erase_env g)) (unbind 0 y p2) (FTBasic TBool))
        -> ProofOf(Entails (Cons y (TRefn (FTV a) x1 p1) g) (unbind 0 y p2))
        -> { th:CSub | not (in_csubst y th) } 
        -> { t_a:UserType | Set_emp (free t_a) && Set_emp (freeTV t_a) && t_a == csubst_tv th a } 
        -> k_a:Kind -> ProofOf(WFType Empty t_a k_a) -> ProofOf(DenotesEnv g th) -> v:Value
        -> ProofOf(Denotes (push (csubst th p1) t_a) v)
        -> ProofOf(Denotes (push (csubst th p2) t_a) v) / [tsize t_a] @-}
lem_denote_push_ent_pred :: Env -> WFFE -> Vname -> Kind -> WFFT -> RVname -> Expr -> RVname 
        -> Expr -> Vname -> HasFType -> HasFType -> Entails -> CSub -> Type -> Kind -> WFType 
        -> DenotesEnv -> Expr -> Denotes ->  Denotes 
lem_denote_push_ent_pred g p_g_wf a_ k p_g_a x1 p1 x2 p2 y pf_p1_bl pf_p2_bl pf_ent_p2 th (TRefn b z q) 
                         k_a p_emp_ta den_g_th v den_thp1ta_v 
  = lem_denote_push_ent_pred_trefn g p_g_wf a_ k p_g_a x1 p1 x2 p2 y pf_p1_bl pf_p2_bl pf_ent_p2 th 
                                   (b ? lem_free_subset_binds Empty (TRefn b z q) k_a p_emp_ta
                                      ? lem_tfreeBV_empty     Empty (TRefn b z q) k_a p_emp_ta) z 
                                   (q ? lem_refn_is_pred (TRefn b z q) b z q)
                                   k_a p_emp_ta den_g_th v den_thp1ta_v
lem_denote_push_ent_pred g _ a k _ x1 p1 x2 p2 y _ _ _ th (TFunc z t_z t') _ _ den_g_th v den_thp1ta_v
  = den_thp1ta_v
lem_denote_push_ent_pred g _ a k _ x1 p1 x2 p2 y _ _ _ th (TPoly a' k' t') _ _ den_g_th v den_thp1ta_v
  = den_thp1ta_v

{-@ lem_denote_sound_sub_sbase_ftv :: g:Env -> a:Vname -> x1:RVname -> p1:Pred -> k1:Kind
        -> x2:RVname -> p2:Pred -> k2:Kind 
        -> ProofOf(Subtype g (TRefn (FTV a) x1 p1) (TRefn (FTV a) x2 p2)) -> ProofOf(WFEnv g)
        -> ProofOf(WFType g (TRefn (FTV a) x1 p1) k1) -> ProofOf(WFType g (TRefn (FTV a) x2 p2) k2)
        ->  th:CSub -> ProofOf(DenotesEnv g th) -> v:Value 
        -> ProofOf(Denotes (ctsubst th (TRefn (FTV a) x1 p1)) v)
        -> ProofOf(Denotes (ctsubst th (TRefn (FTV a) x2 p2)) v) @-}
lem_denote_sound_sub_sbase_ftv :: Env -> Vname -> RVname -> Expr -> Kind -> RVname -> Expr -> Kind
        -> Subtype -> WFEnv -> WFType -> WFType -> CSub -> DenotesEnv -> Expr -> Denotes -> Denotes 
lem_denote_sound_sub_sbase_ftv g a x1 p1_ k1 x2 p2_ k2 (SBase _ _ _ _ _ _ y pf_ent_p2) p_g_wf
                               p_g_t1 p_g_t2 th den_g_th v den_tht1_v_
  = lem_denote_push_ent_pred g p_er_g_wf a k1 p_g_er_a x1 p1 x2 p2 y pf_y_p1_bl pf_y_p2_bl 
                             pf_ent_p2 (th ? lem_binds_env_th g th den_g_th) 
                             (t_a ? lem_free_subset_binds Empty t_a k_a p_emp_ta) k_a p_emp_ta
                             den_g_th v den_tht1_v
                             ? lem_ctsubst_refn_tv th 
                                     (a ? lem_wfftvar_tv_in_csubst g a k1 p_g_er_a th den_g_th) 
                                     x2 p2_
      where
        p1            = p1_ ? lem_free_subset_binds g (TRefn (FTV a) x1 p1_) k1 p_g_t1
        p2            = p2_ ? lem_free_subset_binds g (TRefn (FTV a) x2 p2_) k2 p_g_t2
        p_er_g_wf     = lem_erase_env_wfenv g p_g_wf 
        p_g_er_a      = lem_erase_wftype g (TRefn (FTV a) x1 p1) k1 p_g_t1

        y'            = fresh_var g
        p_y'g_wf      = WFFBind (erase_env g) p_er_g_wf y' (FTBasic (FTV a)) k1 p_g_er_a
        pf_y'_p1_bl   = lem_ftyp_for_wf_trefn' g (FTV a) x1 p1 k1 p_g_t1 p_er_g_wf
        pf_y'_p2_bl   = lem_ftyp_for_wf_trefn' g (FTV a) x2 p2 k2 p_g_t2 p_er_g_wf
        pf_y_p1_bl    = lem_change_var_ftyp (erase_env g) y' (FTBasic (FTV a)) FEmpty p_y'g_wf
                                            (unbind 0 y' p1) (FTBasic TBool) pf_y'_p1_bl y
                                            ? lem_subFV_unbind 0 y' (FV y) p1
        pf_y_p2_bl    = lem_change_var_ftyp (erase_env g) y' (FTBasic (FTV a)) FEmpty p_y'g_wf
                                            (unbind 0 y' p2) (FTBasic TBool) pf_y'_p2_bl y
                                            ? lem_subFV_unbind 0 y' (FV y) p2

        k_a        = kind_for_tv a (g ? lem_free_subset_binds g (TRefn (FTV a) x1 p1) k1 p_g_t1)
        {-@ t_a :: { t':UserType | t' == csubst_tv th a } @-}
        (t_a, p_emp_ta) = get_wftype_from_denv g th den_g_th a k_a
        {-@ den_tht1_v :: ProofOf(Denotes (push (csubst th p1_) (csubst_tv th a)) v) @-}
        den_tht1_v = den_tht1_v_ ? lem_ctsubst_refn_tv th 
                                     (a ? lem_wfftvar_tv_in_csubst g a k1 p_g_er_a th den_g_th) 
                                     x1 p1_

{-@ lem_denote_sound_sub_sbase :: g:Env -> t1:Type -> k1:Kind -> t2:Type -> k2:Kind 
                -> { p_t1_t2:_ | propOf p_t1_t2 == Subtype g t1 t2 && isSBase p_t1_t2}
                -> ProofOf(WFEnv g) -> ProofOf(WFType g t1 k1) -> ProofOf(WFType g t2 k2) 
                ->  th:CSub 
                -> ProofOf(DenotesEnv g th) -> v:Value -> ProofOf(Denotes (ctsubst th t1) v) 
                -> ProofOf(Denotes (ctsubst th t2) v) / [subtypSize p_t1_t2,0] @-}
lem_denote_sound_sub_sbase :: Env -> Type -> Kind -> Type -> Kind -> Subtype -> WFEnv -> WFType -> WFType
                            -> CSub -> DenotesEnv -> Expr -> Denotes -> Denotes 
lem_denote_sound_sub_sbase g t1 k1 t2 k2 p_t1_t2@(SBase _g x1 b p1 x2 p2 y pf_ent_p2) p_g_wf p_g_t1 p_g_t2
                    -- t1 = b{x1:p1}, t2 = b{x2:p2}  -- Pf(Entails g' p2[y/x2])
                       th den_g_th val_ den_t1_v 
  = case b of 
      (FTV a) -> lem_denote_sound_sub_sbase_ftv g a x1 p1 k1 x2 p2 k2 p_t1_t2 p_g_wf
                                                p_g_t1 p_g_t2 th den_g_th val_ den_t1_v
      (BTV a) -> impossible ("by lemma" ? lem_btv_not_wf g a x1 p1 k1 p_g_t1)
      _       -> case den_t1_v of
        (DRefn b_ _ _ also_val pf_v_b pf_th_p1v_tt) -> case (pf_ent_p2) of   -- EvalsTo th(p1[v/x1]) tt
          (EntPred y_g _p2 ev_thp2_tt)     -- forall th' in [[x1,g]]. EvalsTo th'(p2[x1/x2]) tt 
            -> DRefn b x2 (csubst th p2) also_val pf_v_b' pf_th'_p2v_tt
                     `withProof` lem_ctsubst_refn th b x2 p2
                 where
                   val           = val_ ? lem_den_nofv val_ (ctsubst th t1) den_t1_v
                                        ? lem_den_nobv val_ (ctsubst th t1) den_t1_v
                   pf_v_b'       = pf_v_b `withProof`  lem_ctsubst_refn th b x1 p1 
                   den_g'_th'    = DExt g th den_g_th y t1 val den_t1_v
                   th'           = CCons y val (th ? lem_binds_env_th g th den_g_th) -- y is fresh repl. x1
                                         -- th' = (y |-> v, th) \in [[ Cons y t1 g ]]
                   pf_th'_p2v_tt = ev_thp2_tt th' den_g'_th' 
                                     `withProof` lem_csubst_and_unbind 0 y val (FTBasic b) pf_v_b' th p2
        (_) -> impossible ("by lemma" ? lem_ctsubst_refn th b x1 p1) 
        
lem_denote_sound_sub_sfunc g t1 k1 t2 k2 p_t1_t2@(SFunc _g x1 s1 x2 s2 p_g_s2_s1 t1' t2' y p_g'_t1_t2) 
                           p_g_wf p_g_t1 p_g_t2 th den_g_th _v den_tht1_v  
  = case den_tht1_v of       -- p_t1_t2 :: Subtype (Cons y s2 g) t1'[y/x1] t2'[y/x2]
      (DFunc _x1 ths1 tht1' val pf_v_er_tht1 _pf_den_tht1'_vv')
        -> DFunc x2 (ctsubst th s2) (ctsubst th t2') val pf_v_er_tht2 
                  (pf_den_tht2'_vv') `withProof` lem_ctsubst_func th x1 s1 t1'
                                     `withProof` lem_ctsubst_func th x2 s2 t2'
          where
            (WFFunc _ _ _s1 k_s1 p_g_s1 _t1' k1' z p_zg_t1') = lem_wffunc_for_wf_tfunc g x1 s1 t1' k1 p_g_t1
            (WFFunc _ _ _s2 k_s2 p_g_s2 _t2' k2' w p_wg_t2') = lem_wffunc_for_wf_tfunc g x2 s2 t2' k2 p_g_t2
            p_zg_wf      = WFEBind g p_g_wf z s1 k_s1 p_g_s1
            p_wg_wf      = WFEBind g p_g_wf w s2 k_s2 p_g_s2
            _p_yg_t1'    = lem_change_var_wf' g z s1 Empty p_zg_wf (unbindT x1 z t1') k1' p_zg_t1' y
                                      `withProof` lem_tsubFV_unbindT x1 z (FV y) t1'
            {-@ p_yg_t1' :: ProofOf(WFType (Cons y s2 g) (unbindT x1 y t1') k1') @-}
            p_yg_t1'     = lem_subtype_in_env_wf g Empty y s2 s1 p_g_s2_s1 (unbindT x1 y t1') k1' _p_yg_t1'
            {-@ p_yg_t2' :: ProofOf(WFType (Cons y s2 g) (unbindT x2 y t2') k2') @-}
            p_yg_t2'     = lem_change_var_wf' g w s2 Empty p_wg_wf (unbindT x2 w t2') k2' p_wg_t2' y
                                      `withProof` lem_tsubFV_unbindT x2 w (FV y) t2'
            pf_v_er_tht2 = pf_v_er_tht1 ? lem_erase_subtype g t1 t2 p_t1_t2
                                        ? lem_erase_ctsubst th t1 t2
                                        ? lem_ctsubst_func th x1 s1 t1'
                                        ? lem_ctsubst_func th x2 s2 t2'
            g'           = Cons y s2 (g ? lem_binds_env_th g th den_g_th)
            ths2_ths1    = lem_denote_sound_sub g s2 k_s2 s1 k_s1 p_g_s2_s1 p_g_wf p_g_s2 p_g_s1 th den_g_th 
            tht1'_tht2'  = lem_denote_sound_sub g' (unbindT x1 y t1') k1' (unbindT x2 y t2') k2'
                                                p_g'_t1_t2 (WFEBind g p_g_wf y s2 k_s2 p_g_s2)
                                                p_yg_t1' p_yg_t2'

            {-@ pf_den_tht2'_vv' :: v':Value -> ProofOf(Denotes (ctsubst th s2) v') 
                   -> ProofOf(ValueDenoted (App val v') (tsubBV x2 v' (ctsubst th t2'))) @-}
            pf_den_tht2'_vv' v'_ den_ths2_v' = ValDen (App val v') (tsubBV x2 v' (ctsubst th t2'))
                                                    v''  evalpf   den_t2'v'_v'' 
              where
                v'             = v'_ ? lem_den_nofv v'_ (ctsubst th s2) den_ths2_v'
                                     ? lem_den_nobv v'_ (ctsubst th s2) den_ths2_v'
                pf_v'_er_ths2  = get_ftyp_from_den (ctsubst th s2)  v' den_ths2_v' 
                                     ? lem_erase_subtype g  s2 s1 p_g_s2_s1
                                     ? lem_erase_ctsubst th s2 s1
                th'            = CCons y v' th -- (y |-> v', th) in [[y:s2,g]]
                den_g'_th'     = DExt g th den_g_th y s2 v' den_ths2_v' 
                (ValDen _ _ v'' evalpf denpf) = get_obj_from_dfunc x1 (ctsubst th s1) (ctsubst th t1') 
                         val den_tht1_v v' 
                         (ths2_ths1 v' (den_ths2_v' `withProof` lem_ctsubst_func th x2 s2 t2')
                                                    `withProof` lem_ctsubst_func th x1 s1 t1')
                {-@ den_t2'v'_v'' :: ProofOf(Denotes (tsubBV x2 v' (ctsubst th t2')) v'') @-}
                den_t2'v'_v''  = tht1'_tht2' th' den_g'_th' v'' 
                                      (denpf `withProof` lem_ctsubst_and_unbindT 
                                                            x1 y v' (erase (ctsubst th s1)) 
                                                            pf_v'_er_ths2 th t1')
                                      `withProof` lem_ctsubst_func th x2 s2 t2'
                                      `withProof` lem_ctsubst_func th x1 s1 t1'
                                      `withProof` lem_ctsubst_and_unbindT x2 y v' (erase (ctsubst th s2))
                                                                          pf_v'_er_ths2 th t2'
      (_) -> impossible ("by lemma" ? lem_ctsubst_func th x1 s1 t1')

{- @ ple lem_denote_sound_sub_switn @-}
{-@ lem_denote_sound_sub_switn :: g:Env -> t1:Type -> k1:Kind -> t2:Type -> k2:Kind 
                -> { p_t1_t2:_ | propOf p_t1_t2 == Subtype g t1 t2 && isSWitn p_t1_t2}
                -> ProofOf(WFEnv g) -> ProofOf(WFType g t1 k1) -> ProofOf(WFType g t2 k2) 
                ->  th:CSub 
                -> ProofOf(DenotesEnv g th) -> v:Value -> ProofOf(Denotes (ctsubst th t1) v) 
                -> ProofOf(Denotes (ctsubst th t2) v) / [subtypSize p_t1_t2, 0] @-}
lem_denote_sound_sub_switn :: Env -> Type -> Kind -> Type -> Kind -> Subtype -> WFEnv -> WFType -> WFType
                            -> CSub -> DenotesEnv -> Expr -> Denotes -> Denotes 
lem_denote_sound_sub_switn g t1 k1 t2 k2 -- @(TExists x t_x t')  -----------------------------------
             p_t1_t2@(SWitn _g v_x t_x p_vx_tx _t1 x t2' p_t1_t2'vx) 
             p_g_wf p_g_t1 p_g_t2 th den_g_th v den_tht1_v 
    = DExis x (ctsubst th t_x) (ctsubst th t2') v p_v_ert2' thvx -- v'  
            den_thtx_thvx (den_tht2'vx_v `withProof` lem_value_refl also_thvx thvx pf1)
        where -- By the inductive hypothesis and mutual induction:
          (WFExis _ _ _tx k_x p_g_tx _ _ y _p_yg_t2') = lem_wfexis_for_wf_texists g x t_x t2' k2 p_g_t2 
                                                            ? toProof ( t2 === TExists x t_x t2' )
          {-@ p_yg_t2' :: ProofOf(WFType (concatE (Cons y t_x g) Empty) (unbindT x y t2') k2) @-}
          p_yg_t2' = _p_yg_t2' --`withProof` lem_tsubFV_unbindT x w (FV y) t2'
          p_yg_wf  = WFEBind g p_g_wf y t_x k_x p_g_tx
          {-@ p_g_t2'vx :: ProofOf(WFType g (tsubBV x v_x t2') k2) @-}
          p_g_t2'vx = lem_subst_wf' g Empty y v_x t_x p_vx_tx p_yg_wf (unbindT x y t2') k2 p_yg_t2'
                              `withProof` lem_tsubFV_unbindT x y v_x t2' 
          den_tht2'vx_v = lem_denote_sound_sub g t1 k1 (tsubBV x v_x t2') k2 p_t1_t2'vx p_g_wf 
                              p_g_t1 p_g_t2'vx th den_g_th v den_tht1_v -- v \in [[ t2'[v_x/x] ]]
                              `withProof` lem_ctsubst_exis th x t_x t2'    
                              `withProof` lem_commute_ctsubst_tsubBV th x v_x t2'
          also_thvx     = csubst th v_x `withProof` lem_csubst_value th v_x  -- new
          {-@ thvx :: { v:Expr | isValue v } @-} -- Set_emp freeBV v
          (ValDen _ _ thvx pf1 pf2)      = lem_denote_sound_typ g v_x t_x p_vx_tx p_g_wf th den_g_th
          {-@ den_thtx_thvx :: ProofOf(Denotes (ctsubst th t_x) thvx) @-}
          den_thtx_thvx = pf2  -- th(v_x) in [[th(t_x)]]. Let v' = th(v_x)...
                          `withProof` lem_commute_ctsubst_tsubBV th x v_x t2'
          -- these are ingredients to show that v \in [[th(TExists x t_x t2')]]
          p_v_ert2' = get_ftyp_from_den (ctsubst th (tsubBV x v_x t2')) v den_tht2'vx_v
                                        ? lem_commute_ctsubst_tsubBV th x v_x t2'
                                        ? lem_erase_tsubBV x (csubst th v_x) (ctsubst th t2')

{- @ ple lem_denote_sound_sub_sbind @-}
{-@ lem_denote_sound_sub_sbind :: g:Env -> t1:Type -> k1:Kind -> t2:Type -> k2:Kind 
                -> { p_t1_t2:_ | propOf p_t1_t2 == Subtype g t1 t2 && isSBind p_t1_t2}
                -> ProofOf(WFEnv g) -> ProofOf(WFType g t1 k1) -> ProofOf(WFType g t2 k2) 
                ->  th:CSub 
                -> ProofOf(DenotesEnv g th) -> v:Value -> ProofOf(Denotes (ctsubst th t1) v) 
                -> ProofOf(Denotes (ctsubst th t2) v) / [subtypSize p_t1_t2,0] @-}
lem_denote_sound_sub_sbind :: Env -> Type -> Kind -> Type -> Kind -> Subtype -> WFEnv -> WFType -> WFType
                            -> CSub -> DenotesEnv -> Expr -> Denotes -> Denotes 
lem_denote_sound_sub_sbind g t1 k1 t2 k2 -- t1 == (TExists x t_x t') 
             p_t1_t2@(SBind _g x t_x t' _t2 y p_t'yx_t2) p_g_wf p_g_t1 p_g_t2 th den_g_th v den_tht1_v 
    = case (t1, den_tht1_v) of 
        (TExists _ _ _, DExis _ thtx tht' _v pf_v_ertht' v_x den_thtx_vx den_tht'vx_v) 
          -> den_tht2_v
            where -- by the inductive hypothesis we have
              (WFExis _ _ _tx k_x p_g_tx _ _ w p_wg_t') =lem_wfexis_for_wf_texists g x t_x t' k1 p_g_t1
              g'         = Cons y t_x g
              p_wg_wf    = WFEBind g p_g_wf w t_x k_x p_g_tx
              p_g'_wf    = WFEBind g p_g_wf y t_x k_x p_g_tx 
              p_g'_t'    = lem_change_var_wf' g w t_x Empty p_wg_wf (unbindT x w t') k1 p_wg_t' y
                              `withProof` lem_tsubFV_unbindT x w (FV y) t' 
              p_g'_t2    = lem_weaken_wf' g Empty p_g_wf t2 k2 p_g_t2 y t_x -- p_g_tx
              den_g'_th' = DExt g th den_g_th y t_x v_x den_thtx_vx
              pf_vx_thtx = get_ftyp_from_den thtx v_x den_thtx_vx
              den_tht'_v = den_tht'vx_v `withProof` lem_ctsubst_exis th x t_x t'
                               `withProof` lem_ctsubst_and_unbindT x y v_x (erase thtx) pf_vx_thtx th t'
              den_tht2_v = lem_denote_sound_sub g' (unbindT x y t') k1 t2 k2 p_t'yx_t2 
                               p_g'_wf p_g'_t' p_g'_t2 th' den_g'_th' v den_tht'_v
                               `withProof` lem_ctsubst_head_not_free y v_x th t2
              th'        = CCons y (v_x ? lem_den_nofv v_x thtx den_thtx_vx
                                        ? lem_den_nobv v_x thtx den_thtx_vx)
                                   (th  ? lem_binds_env_th g th den_g_th)
        (_, _) -> impossible ("by lemma" ? lem_ctsubst_exis th x t_x t')

{- @ ple lem_denote_sound_sub_spoly @-}
{-@ lem_denote_sound_sub_spoly :: g:Env -> t1:Type -> k1:Kind -> t2:Type -> k2:Kind 
                -> { p_t1_t2:_ | propOf p_t1_t2 == Subtype g t1 t2 && isSPoly p_t1_t2}
                -> ProofOf(WFEnv g) -> ProofOf(WFType g t1 k1) -> ProofOf(WFType g t2 k2) 
                ->  th:CSub 
                -> ProofOf(DenotesEnv g th) -> v:Value -> ProofOf(Denotes (ctsubst th t1) v) 
                -> ProofOf(Denotes (ctsubst th t2) v) / [subtypSize p_t1_t2,0] @-}
lem_denote_sound_sub_spoly :: Env -> Type -> Kind -> Type -> Kind -> Subtype -> WFEnv -> WFType -> WFType
                            -> CSub -> DenotesEnv -> Expr -> Denotes -> Denotes 
lem_denote_sound_sub_spoly g t1 Star t2 Star p_t1_t2@(SPoly _g a1 k t1' a2 t2' a p_ag_t1'_t2')
                           p_g_wf p_g_t1 p_g_t2 th den_g_th _v den_tht1_v 
  = case den_tht1_v of   
      (DPoly _a1 _k tht1' val pf_v_er_a1tht1' {-a0 s eqv_a0s_ertht1 pf_v_a0s-} _pf_den_tht1'_vta)
        -> DPoly a2 k (ctsubst th t2') val pf_v_er_a2tht2' {-a0 s eqv_a0s_ertht2 pf_v_a0s-}  pf_den_tht2'_vta
                 ? lem_ctsubst_poly th a1 k t1'
          where                                                                   -- lem_ctsubst_poly
            (WFPoly _ _ _ _t1' k1' a1' p_a1'g_t1') = lem_wfpoly_for_wf_tpoly g a1 k t1' p_g_t1
            (WFPoly _ _ _ _t2' k2' a2' p_a2'g_t2') = lem_wfpoly_for_wf_tpoly g a2 k t2' p_g_t2
            p_a1'g_wf    = WFEBindT g p_g_wf a1' k
            p_a2'g_wf    = WFEBindT g p_g_wf a2' k
            {-@ p_ag_t1' :: ProofOf(WFType (ConsT a k g) (unbind_tvT a1 a t1') k1') @-}
            p_ag_t1'     = lem_change_tvar_wf' g a1' k Empty p_a1'g_wf (unbind_tvT a1 a1' t1') k1' 
                                   p_a1'g_t1' a ? lem_tchgFTV_unbind_tvT a1 a1' a t1'
            {-@ p_ag_t2' :: ProofOf(WFType (ConsT a k g) (unbind_tvT a2 a t2') k2') @-}
            p_ag_t2'     = lem_change_tvar_wf' g a2' k Empty p_a2'g_wf (unbind_tvT a2 a2' t2') k2' 
                                   p_a2'g_t2' a ? lem_tchgFTV_unbind_tvT a2 a2' a t2'
            g'           = ConsT a k (g ? lem_binds_env_th g th den_g_th)
            tht1'_tht2'  = lem_denote_sound_sub g' (unbind_tvT a1 a t1') k1' (unbind_tvT a2 a t2') k2'
                                   p_ag_t1'_t2' (WFEBindT g p_g_wf a k) p_ag_t1' p_ag_t2'
            pf_v_er_a2tht2' = pf_v_er_a1tht1' ? lem_erase_subtype g t1 t2 p_t1_t2
                                              ? lem_erase_ctsubst th t1 t2
                                              ? lem_ctsubst_poly th a1 k t1'
                                              ? lem_ctsubst_poly th a2 k t2'
            {-@ pf_den_tht2'_vta :: t_a:UserType -> ProofOf(WFType Empty t_a k)
                   -> ProofOf(ValueDenoted (AppT val t_a) (tsubBTV a2 t_a (ctsubst th t2'))) @-}
            pf_den_tht2'_vta t_a_ p_emp_ta = ValDen (AppT val t_a) (tsubBTV a2 t_a (ctsubst th t2'))
                                                    v''  evalpf   den_tht2'vta_v'' 
              where
                t_a              = t_a_ ? lem_free_subset_binds Empty t_a_ k p_emp_ta
                                        ? lem_tfreeBV_empty     Empty t_a_ k p_emp_ta 
                th'              = CConsT a t_a th -- (a |-> t_a, th) in [[a:k,g]]
                den_g'_th'       = DExtT g th den_g_th a k t_a p_emp_ta  
                (ValDen _ _ v'' evalpf denpf) = get_obj_from_dpoly a1 k (ctsubst th t1') val
                         (den_tht1_v ? lem_ctsubst_poly th a1 k t1') t_a p_emp_ta
                {-@ den_tht2'vta_v'' :: ProofOf(Denotes (tsubBTV a2 t_a (ctsubst th t2')) v'') @-}
                den_tht2'vta_v'' = tht1'_tht2' th' den_g'_th' v'' -- rest is v'' \in [[th(t1')]] :
                                      (denpf ? lem_ctsubst_and_unbind_tvT a1 a t_a k p_emp_ta th t1')
                                      `withProof` lem_ctsubst_poly th a2 k t2'
                                      `withProof` lem_ctsubst_poly th a1 k t1'
                                             ? lem_ctsubst_and_unbind_tvT a2 a t_a k p_emp_ta th t2'
      (_) -> impossible ("by lemma" ? lem_ctsubst_poly th a1 k t1')
lem_denote_sound_sub_spoly g t1 Base t2 k2   p_t1_t2@(SPoly _g a1 k t1' a2 t2' a p_ag_t1'_t2')
                           p_g_wf p_g_t1 p_g_t2 th den_g_th _v den_tht1_v
  = impossible ("by lemma" ? lem_wf_tpoly_star g a1 k t1' p_g_t1)
lem_denote_sound_sub_spoly g t1 k1   t2 Base p_t1_t2@(SPoly _g a1 k t1' a2 t2' a p_ag_t1'_t2')
                           p_g_wf p_g_t1 p_g_t2 th den_g_th _v den_tht1_v
  = impossible ("by lemma" ? lem_wf_tpoly_star g a2 k t2' p_g_t2)
  *)