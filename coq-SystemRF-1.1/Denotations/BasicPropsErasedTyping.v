Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.Strengthenings.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import Denotations.ClosingSubstitutions.
Require Import Denotations.Denotations.
Require Import Denotations.BasicPropsCSubst.

(*
{-@ lem_unbind_tvT_equals :: a:Vname -> a':Vname -> { t1:FType | not (Set_mem a' (ffreeTV t1)) }
        -> { t2:FType | unbindFT a a' t1 == unbindFT a a' t2 && not (Set_mem a' (ffreeTV t2)) } 
        -> { pf:_ | t1 == t2 } @-}
lem_unbind_tvT_equals :: Vname -> Vname -> FType -> FType -> Proof
lem_unbind_tvT_equals a a' (FTBasic b) (FTBasic _) = case b of
  (BTV a) -> ()
  _       -> ()
lem_unbind_tvT_equals a a' (FTFunc t11 t12) (FTFunc t21 t22) 
  = () ? lem_unbind_tvT_equals a a' t11 t21
       ? lem_unbind_tvT_equals a a' t12 t22
lem_unbind_tvT_equals a a' (FTPoly a1 k t1') (FTPoly _ _ t2')
  = () ? lem_unbind_tvT_equals a a' t1' t2'

-- LEMMA 6. If G |- s <: t, then if we erase the types then (erase s) and (erase t)
--               equiv up to alpha-renaming bound variables
{-@ lem_erase_subtype :: g:Env -> t1:Type -> t2:Type -> ProofOf(Subtype g t1 t2)
               -> { pf:_ | erase t1 == erase t2 } @-}
lem_erase_subtype :: Env -> Type -> Type -> Subtype -> Proof
lem_erase_subtype g t1 t2 (SBase _g x1 b p1 x2 p2 y _) = ()
lem_erase_subtype g t1 t2 (SFunc _g x1 s1 x2 s2 p_s2_s1 t1' t2' y p_t1'_t2')
  = () ? lem_erase_subtype  g s2 s1 p_s2_s1
       ? lem_erase_tsubBV x1 (FV y) t1'
       ? lem_erase_tsubBV x2 (FV y) t2'
       ? lem_erase_subtype (Cons y s2 g) (unbindT x1 y t1') (unbindT x2 y t2') p_t1'_t2'
lem_erase_subtype g t1 t2 (SWitn _g v t_x p_v_tx _t1 x t' p_t1_t'v)
  = () ? lem_erase_subtype g t1 (tsubBV x v t') p_t1_t'v
       ? lem_erase_tsubBV x v t'
{- toProof ( erase t1 ? lem_erase_subtype g t1 (tsubBV x v t') p_t1_t'v
            === erase (tsubBV x v t') ? lem_erase_tsubBV x v t'
            === erase t' === erase (TExists x t_x t') ) -}
lem_erase_subtype g t1 t2 (SBind _g x t_x t _t2 y p_t_t')
  = () ? lem_erase_subtype (Cons y t_x g) (unbindT x y t) t2 p_t_t'
       ? lem_erase_tsubBV x (FV y) t
lem_erase_subtype g t1 t2 (SPoly _g a1 k t1' a2 t2' a p_ag_t1'_t2') 
  = () ? lem_erase_subtype (ConsT a k g) (unbind_tvT a1 a t1') (unbind_tvT a2 a t2')
                           p_ag_t1'_t2' 
       ? lem_erase_unbind_tvT a1 a t1'
       ? lem_erase_unbind_tvT a2 a t2'
       ? lem_unbind_tvT_equals a1 a (erase t1' ? lem_erase_freeTV t1') 
                                    (erase t2' ? lem_erase_freeTV t2')

{-@ lem_erase_ctsubst :: th:CSub -> t1:Type 
        -> { t2:Type | erase t1 == erase t2 }
        -> { pf:_ | erase (ctsubst th t1) == erase (ctsubst th t2) } @-}
lem_erase_ctsubst :: CSub -> Type -> Type -> Proof
lem_erase_ctsubst CEmpty             t1 t2 = () 
lem_erase_ctsubst (CCons  x v_x th') t1 t2 
    = () ? lem_erase_ctsubst  th' (tsubFV x v_x t1 ? lem_erase_tsubFV x v_x t1) 
                                  (tsubFV x v_x t2 ? lem_erase_tsubFV x v_x t2) 
         ? lem_unroll_ctsubst_left th' x v_x t1
         ? lem_erase_tsubFV x v_x (ctsubst th' t1)
         ? lem_unroll_ctsubst_left th' x v_x t2
         ? lem_erase_tsubFV x v_x (ctsubst th' t2)
lem_erase_ctsubst (CConsT a t_a th') t1 t2 
    = () ? lem_erase_ctsubst  th' (tsubFTV a t_a t1 ? lem_erase_tsubFTV a t_a t1)
                                  (tsubFTV a t_a t2 ? lem_erase_tsubFTV a t_a t2)
         ? lem_unroll_ctsubst_tv_left th' a t_a t1
         ? lem_erase_tsubFTV a t_a (ctsubst th' t1)
         ? lem_unroll_ctsubst_tv_left th' a t_a t2
         ? lem_erase_tsubFTV a t_a (ctsubst th' t2)

{-@ lem_csubst_env_empty :: th:CSub -> { pf:_ | csubst_env th Empty == Empty } @-}
lem_csubst_env_empty :: CSub -> Proof
lem_csubst_env_empty CEmpty            = ()
lem_csubst_env_empty (CCons  z v_z th) = () ? lem_csubst_env_empty th
lem_csubst_env_empty (CConsT a t_a th) = () ? lem_csubst_env_empty th

{-@ lem_csubst_env_concat :: th:CSub -> { g:Env | Set_emp (Set_cap (bindsC th) (binds g)) }
        -> { g':Env | Set_emp (Set_cap (bindsC th) (binds g)) && Set_emp (Set_cap (binds g) (binds g')) }
        -> { pf:_ | csubst_env th (concatE g g') == concatE (csubst_env th g) (csubst_env th g') } @-}
lem_csubst_env_concat :: CSub -> Env -> Env -> Proof
lem_csubst_env_concat CEmpty            g g' = ()
lem_csubst_env_concat (CCons  z v_z th) g g' 
  = () ? lem_esubFV_concat z v_z g g'
       ? lem_csubst_env_concat th (esubFV z v_z g) (esubFV z v_z g')
lem_csubst_env_concat (CConsT a t_a th) g g'
   = () ? lem_esubFTV_concat a t_a g g'
        ? lem_csubst_env_concat th (esubFTV a t_a g) (esubFTV a t_a g')

{-@ lem_csubst_cons_env :: th:CSub -> x:Vname -> t_x:Type -> g:Env
        -> { pf:_ | csubst_env th (Cons x t_x g) == Cons x (ctsubst th t_x) (csubst_env th g) } @-}
lem_csubst_cons_env :: CSub -> Vname -> Type -> Env -> Proof
lem_csubst_cons_env CEmpty            x t_x g' = ()
lem_csubst_cons_env (CCons  z v_z th) x t_x g' 
  = () ? lem_csubst_cons_env th x (tsubFV z v_z t_x) (esubFV z v_z g')
lem_csubst_cons_env (CConsT a t_a th) x t_x g' 
  = () ? lem_csubst_cons_env th x (tsubFTV a t_a t_x) (esubFTV a t_a g')

{-@ lem_csubst_consT_env :: th:CSub -> a:Vname -> k_a:Kind -> g':Env
        -> { pf:_ | csubst_env th (ConsT a k_a g') == ConsT a k_a (csubst_env th g') } @-}
lem_csubst_consT_env :: CSub -> Vname -> Kind -> Env -> Proof
lem_csubst_consT_env CEmpty            a k_a g' = ()
lem_csubst_consT_env (CCons  z v_z th) a k_a g' 
  = () ? lem_csubst_consT_env th a k_a (esubFV z v_z g')
lem_csubst_consT_env (CConsT a' t' th) a k_a g'
  = () ? lem_csubst_consT_env th a k_a (esubFTV a' t' g')

{-@ lem_commute_esubFV :: x:Vname -> v:Value -> { y:Vname | not (y == x)}
        -> { v_y:Value | not (Set_mem x (fv v_y)) } -> g:Env
        -> { pf:_ | esubFV y v_y (esubFV x v g) == esubFV x (subFV y v_y v) (esubFV y v_y g) } @-}
lem_commute_esubFV :: Vname -> Expr -> Vname -> Expr -> Env -> Proof
lem_commute_esubFV x v y v_y Empty          = ()
lem_commute_esubFV x v y v_y (Cons z t_z g) = () ? lem_commute_tsubFV x v y v_y t_z
                                                 ? lem_commute_esubFV x v y v_y g
lem_commute_esubFV x v y v_y (ConsT a k g)  = () ? lem_commute_esubFV x v y v_y g

{-@ lem_commute_esubFV_esubFTV :: a:Vname -> t_a:UserType ->  y:Vname
        -> { v_y:Value | not (Set_mem a (ftv v_y)) } -> g:Env
        -> { pf:_ | esubFV y v_y (esubFTV a t_a g) ==
                    esubFTV a (tsubFV y v_y t_a) (esubFV y v_y g) } @-}
lem_commute_esubFV_esubFTV :: Vname -> Type -> Vname -> Expr -> Env -> Proof
lem_commute_esubFV_esubFTV a t_a x v Empty           = ()
lem_commute_esubFV_esubFTV a t_a x v (Cons  z t_z g) 
  = () ? lem_commute_tsubFV_tsubFTV a t_a x v t_z
       ? lem_commute_esubFV_esubFTV a t_a x v g
lem_commute_esubFV_esubFTV a t_a x v (ConsT a' k' g) 
  = () ? lem_commute_esubFV_esubFTV a t_a x v g  

{-@ lem_unroll_csubst_env_left :: th:CSub -> { x:Vname | not (in_csubst x th) }
        -> { v_x:Value | Set_emp (fv v_x) && Set_emp (ftv v_x) } 
        -> { g':Env | Set_emp (Set_cap (bindsC th) (binds g')) && not (in_env x g') }
        -> { pf:_ | csubst_env (CCons x v_x th) g' == esubFV x v_x (csubst_env th g') } @-}
lem_unroll_csubst_env_left :: CSub -> Vname -> Expr -> Env -> Proof
lem_unroll_csubst_env_left CEmpty           x v_x g' = ()
lem_unroll_csubst_env_left (CCons z v_z th) x v_x g'
  = () ? lem_subFV_notin x v_x v_z
       ? lem_commute_esubFV z v_z x v_x g'
       ? lem_unroll_csubst_env_left th x v_x (esubFV z v_z g')
lem_unroll_csubst_env_left (CConsT a t_a th) x v_x g'
  = () ? lem_tsubFV_notin x v_x t_a
       ? lem_commute_esubFV_esubFTV a t_a x v_x g'
       ? lem_unroll_csubst_env_left th x v_x (esubFTV a t_a g')

{-@ lem_csubst_wfft :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> th:CSub -> ProofOf(DenotesEnv g th) -> t_z:Type -> k_z:Kind
        -> ProofOf(WFFT (erase_env (concatE g g')) (erase t_z) k_z)
        -> ProofOf(WFFT (erase_env (csubst_env th g')) (erase (ctsubst th t_z)) k_z) @-}
lem_csubst_wfft :: Env -> Env -> CSub -> DenotesEnv -> Type -> Kind -> WFFT -> WFFT
lem_csubst_wfft Empty           g'  th   den_g_th t_z k_z p_g'g_tz  = case den_g_th of
  (DEmp) -> p_g'g_tz ? lem_binds_env_th Empty th den_g_th
                     ? lem_empty_concatE g'
lem_csubst_wfft (Cons x t_x g)  g' xth den_xg_xth t_z k_z p_g'xg_tz = case den_xg_xth of
  (DExt _g th den_g_th _x _tx v_x den_thtx_vx) -> p_xthg'_xthtz
    where
      p_vx_thtx     = get_ftyp_from_den (ctsubst th t_x) v_x den_thtx_vx
      p_g'g_tz      = lem_strengthen_wfft (erase_env g) x (erase t_x) (erase_env (esubFV x v_x g'))
                                          (erase (tsubFV x v_x t_z)) k_z 
                                          (p_g'xg_tz ? lem_erase_concat (Cons x t_x g)  g'
                                                     ? lem_erase_tsubFV x v_x t_z
                                                     ? lem_erase_esubFV x v_x g')
      p_xthg'_xthtz = lem_csubst_wfft g (esubFV x v_x g') th den_g_th (tsubFV x v_x t_z) 
                                      k_z (p_g'g_tz ? lem_erase_concat g (esubFV x v_x g'))
lem_csubst_wfft (ConsT a k_a g) g' ath den_ag_ath t_z k_z p_g'ag_tz = case den_ag_ath of
  (DExtT _g th den_g_th _a _ka t_a p_emp_ta) -> p_athg'_athtz
    where
      p_g_er_ta     = lem_weaken_many_wfft FEmpty (erase_env g) (erase t_a) k_a 
                                           (lem_erase_wftype Empty t_a k_a p_emp_ta)
                                           ? lem_empty_concatF (erase_env g)
      p_g'g_tzta    = lem_subst_tv_wfft (erase_env g) (erase_env g') a (erase t_a) k_a
                                        p_g_er_ta (erase t_z) k_z 
                                        (p_g'ag_tz ? lem_erase_concat (ConsT a k_a g) g')
                                        ? lem_erase_tsubFTV a t_a t_z
                                        ? lem_erase_esubFTV a t_a g'
                                        ? lem_erase_concat  g (esubFTV a t_a g')
      p_athg'_athtz = lem_csubst_wfft g (esubFTV a t_a g') th den_g_th (tsubFTV a t_a t_z)
                                      k_z p_g'g_tzta

{-@ lem_csubst_wffe :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> th:CSub -> ProofOf(DenotesEnv g th) -> ProofOf(WFFE (erase_env (concatE g g')))
        -> ProofOf(WFFE (erase_env (csubst_env th g'))) @-}
lem_csubst_wffe :: Env -> Env -> CSub -> DenotesEnv -> WFFE -> WFFE
lem_csubst_wffe g Empty            th den_g_th p_g'g_wf   
  = WFFEmpty ? lem_csubst_env_empty th 
lem_csubst_wffe g (Cons z t_z g')  th den_g_th p_zg'g_wf 
  = WFFBind  (erase_env (csubst_env (th ? lem_binds_env_th g th den_g_th) g')) p_thg'_wf z (erase (ctsubst th t_z)) k_z p_thg'_thtz
             ? lem_csubst_cons_env th z t_z g'
      where
        (WFFBind _ p_g'g_wf _z _ k_z p_g'g_tz) = p_zg'g_wf
        p_thg'_wf = lem_csubst_wffe g g' th den_g_th p_g'g_wf
        p_thg'_thtz = lem_csubst_wfft g g' th den_g_th t_z k_z p_g'g_tz
lem_csubst_wffe g (ConsT a k_a g') th den_g_th p_ag'g_wf 
  = WFFBindT (erase_env (csubst_env (th ? lem_binds_env_th g th den_g_th) g')) p_thg'_wf a k_a
             ? lem_csubst_consT_env th a k_a g'
      where
        (WFFBindT _ p_g'g_wf _ _) = p_ag'g_wf
        p_thg'_wf = lem_csubst_wffe g g' th den_g_th p_g'g_wf  

{-@ lem_csubst_hasftype' :: g:Env -> e:Expr -> t:Type -> ProofOf(HasFType (erase_env g) e (erase t))
        -> ProofOf(WFFE (erase_env g)) -> th:CSub -> ProofOf(DenotesEnv g th)
        -> ProofOf(HasFType FEmpty (csubst th e) (erase (ctsubst th t))) @-}
lem_csubst_hasftype' :: Env -> Expr -> Type -> HasFType -> WFFE -> CSub -> DenotesEnv -> HasFType
lem_csubst_hasftype' g e t p_e_t p_g_wf th den_g_th 
  = lem_partial_csubst_hasftype g Empty p_g_wf th den_g_th e t p_e_t
                                ? lem_csubst_env_empty th

{-@ lem_partial_csubst_hasftype :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFFE (erase_env (concatE g g'))) -> th0:CSub -> ProofOf(DenotesEnv g th0) 
        -> e:Expr -> t:Type -> ProofOf(HasFType (erase_env (concatE g g')) e (erase t))
        -> ProofOf(HasFType (erase_env (csubst_env th0 g')) (csubst th0 e) (erase (ctsubst th0 t))) @-}
lem_partial_csubst_hasftype :: Env -> Env -> WFFE -> CSub -> DenotesEnv -> Expr -> Type
                                   -> HasFType -> HasFType
lem_partial_csubst_hasftype Empty           g' p_env_wf  th den_g_th   e t p_e_t = case den_g_th of
  (DEmp) -> p_e_t ? lem_binds_env_th Empty th den_g_th
                  ? lem_empty_concatE g'
lem_partial_csubst_hasftype (Cons x t_x g)  g' p_env_wf xth den_xg_xth e t p_e_t = case den_xg_xth of
  (DExt _g th_ den_g_th _x _tx v_x den_thtx_vx) -> p_xthe_xtht
                                   ? lem_empty_concatF (erase_env (csubst_env th g')) 
                                   ? lem_erase_esubFV x v_x (csubst_env th g')
                                   ? lem_unroll_csubst_env_left th x v_x g'
                                   ? lem_unroll_csubst_left th x v_x e
                                   ? lem_erase_tsubFV x v_x (ctsubst th t)
                                   ? lem_unroll_ctsubst_left th x v_x t
    where
      th          = th_ ? lem_binds_env_th g th_ den_g_th
      p_vx_thtx   = get_ftyp_from_den (ctsubst th t_x) v_x den_thtx_vx
      p_emp_thtx  = lem_ftyping_wfft FEmpty v_x (erase (ctsubst th t_x)) p_vx_thtx WFFEmpty
      p_the_tht   = lem_partial_csubst_hasftype g (concatE (Cons x t_x Empty) g') 
                                (p_env_wf ? lem_concat_shift g x t_x g') th den_g_th 
                                e t (p_e_t ? lem_concat_shift g x t_x g')
                                ? lem_csubst_env_concat th (Cons x t_x Empty) g'
                                ? lem_erase_concat (csubst_env th (Cons x t_x Empty)) (csubst_env th g')
                                ? lem_csubst_cons_env th x t_x Empty
                                ? lem_csubst_env_empty th
      p_g'g_wf    = lem_strengthen_wffe (erase_env g) x (erase t_x) (erase_env g') 
                                        (p_env_wf ? lem_erase_concat (Cons x t_x g)  g')
                                        ? lem_erase_concat g g'
      p_thg'_wf   = lem_csubst_wffe g g' th den_g_th p_g'g_wf
                                    ? lem_empty_concatF (erase_env (csubst_env th g'))
      p_thg'x_wf  = lem_weaken_wffe FEmpty (erase_env (csubst_env th g')) p_thg'_wf
                                    x (erase (ctsubst th t_x)) Star p_emp_thtx
      p_xthe_xtht = lem_subst_ftyp FEmpty (erase_env (csubst_env th g')) x v_x (erase (ctsubst th t_x))
                                   p_vx_thtx p_thg'x_wf (csubst th e) (erase (ctsubst th t)) p_the_tht
lem_partial_csubst_hasftype (ConsT a k_a g) g' p_env_wf ath den_ag_ath e t p_e_t = case den_ag_ath of
  (DExtT _g th den_g_th _a _ka t_a p_emp_ta) -> p_athe_atht
    where
      p_g_ta      = lem_weaken_many_wfft FEmpty (erase_env g) (erase t_a) k_a
                                         (lem_erase_wftype Empty t_a k_a p_emp_ta)
                                         ? lem_empty_concatF (erase_env g)
      p_eta_tta   = lem_subst_tv_ftyp (erase_env g) (erase_env g') a t_a k_a
                                      p_g_ta (p_env_wf ? lem_erase_concat (ConsT a k_a g) g') e (erase t) 
                                      (p_e_t ? lem_erase_concat (ConsT a k_a g) g')
                                      ? lem_erase_tsubFTV a t_a t  
                                      ? lem_erase_esubFTV a t_a g'
                                      ? lem_erase_concat g (esubFTV a t_a g')
      p_g'g_wf    = lem_subst_tv_wffe (erase_env g) (erase_env g') a (erase t_a) k_a 
                                      p_g_ta (p_env_wf ? lem_erase_concat (ConsT a k_a g) g') 
                                      ? lem_erase_esubFTV a t_a g'
      p_athe_atht = lem_partial_csubst_hasftype g (esubFTV a t_a g') p_g'g_wf th den_g_th 
                                                (subFTV a t_a e) (tsubFTV a t_a t) p_eta_tta

{-@ lem_csubst_hasftype_basic :: g:Env -> e:Expr -> { b:Basic | b == TBool || b == TInt }
        -> ProofOf(HasFType (erase_env g) e (FTBasic b)) -> ProofOf(WFFE (erase_env g)) -> th:CSub 
        -> ProofOf(DenotesEnv g th)
        -> ProofOf(HasFType FEmpty (csubst th e) (FTBasic b)) @-}
lem_csubst_hasftype_basic :: Env -> Expr -> Basic -> HasFType -> WFFE -> CSub -> DenotesEnv -> HasFType
lem_csubst_hasftype_basic g e b p_e_b p_g_wf th den_g_th 
    = lem_csubst_hasftype' g e (TRefn b Z (Bc True)) p_e_b p_g_wf th den_g_th
                           ? lem_ctsubst_erase_basic th (TRefn b Z (Bc True)) b

{-@ lem_csubst_fv_in ::  y:Vname -> { v:Value | Set_emp (fv v) && Set_emp (ftv v) &&
                                         Set_emp (freeBV v) && Set_emp (freeBTV v) }
                                 -> { th:CSub | not (in_csubst y th ) }
                                 -> { pf:_ | csubst (CCons y v th) (FV y) == v } @-}
lem_csubst_fv_in :: Vname -> Expr -> CSub -> Proof
lem_csubst_fv_in y v th = () ? lem_csubst_nofv th v
*)