{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SubstitutionLemmaWF where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasSubstitution
import Typing

{-@ reflect foo41 @-}
foo41 x = Just x
foo41 :: a -> Maybe a

-- -- -- -- -- -- -- -- -- -- -- ---
-- Part of the Substitution Lemma --
-- -- -- -- -- -- -- -- -- -- -- ---

{-@ lem_subst_wf_wfrefn :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
          -> t_x:Type -> ProofOf(HasFType (erase_env g) v_x (erase t_x))
          -> t:Type -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (Cons x t_x g) g') t k && isWFRefn p_env_t}
          -> ProofOf(WFType (concatE g (esubFV x v_x g')) (tsubFV x v_x t) k) 
           / [tsize t, envsize g', ksize k, 0] @-}
lem_subst_wf_wfrefn :: Env -> Env -> Vname -> Expr -> Type -> HasFType 
                    -> Type -> Kind -> WFType -> WFType
lem_subst_wf_wfrefn g g' x v_x t_x p_vx_er_tx  t k (WFRefn env b p_env_b ps nms mk_p_env'_ps_bl)
  = WFRefn (concatE g (esubFV x v_x g')) b p_gg'_b (psubFV x v_x ps) nms' -- _env = g'; x:tx; g
           mk_p_ygg'_psvx_bl 
      where
        p_gg'_b       = lem_subst_wf g g' x v_x t_x p_vx_er_tx 
                                     (TRefn b PEmpty) Base p_env_b  
                                     ? lem_psubFV_notin x v_x PEmpty
        p_env_er_b    = lem_erase_wftype env (TRefn b PEmpty) Base p_env_b
        {-@ mk_p_ygg'_psvx_bl :: { y:Vname | NotElem y nms' }
              -> ProofOf(PHasFType (FCons y (FTBasic b) (erase_env (concatE g (esubFV x v_x g'))))
                                   (unbindP y (psubFV x v_x ps))) @-}
        mk_p_ygg'_psvx_bl y = lem_subst_pftyp (erase_env g) (FCons y (FTBasic b) (erase_env g')
                                                              ? lem_in_env_concat g  g' y ) x
                        v_x (erase t_x)  p_vx_er_tx  (unbindP y ps)  
                        (mk_p_env'_ps_bl y ? lem_erase_concat (Cons x t_x g) g')
                        ? lem_commute_psubFV_unbindP x 
                              (v_x ? lem_ftyp_islc (erase_env g) v_x (erase t_x) p_vx_er_tx) y ps
                        ? lem_erase_concat g (esubFV x v_x g')
                        ? lem_erase_esubFV x v_x g'
        nms'                = x:(unionEnv nms (concatE g g'))

{-@ lem_subst_wf_wfvar :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
          -> t_x:Type -> ProofOf(HasFType (erase_env g) v_x (erase t_x)) 
          -> t:Type -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (Cons x t_x g) g') t k && isWFVar p_env_t}
          -> ProofOf(WFType (concatE g (esubFV x v_x g')) (tsubFV x v_x t) k) 
           / [tsize t, envsize g', ksize k, 0] @-}
lem_subst_wf_wfvar :: Env -> Env -> Vname -> Expr -> Type -> HasFType 
                          -> Type -> Kind -> WFType -> WFType
lem_subst_wf_wfvar g g' x v_x t_x p_vx_er_tx  t k (WFVar1 _env' a k_a)
  = case g' of
      Empty              -> impossible "x <> a"
      (ConsT _a _ka g'') -> WFVar1 (concatE g (esubFV x v_x g''))
                                   (a ? lem_in_env_esub g'' x v_x a
                                      ? lem_in_env_concat g g'' a) k_a
                                   ? lem_psubFV_notin x v_x PEmpty
lem_subst_wf_wfvar g g' x v_x t_x p_vx_er_tx  t k (WFVar2 _env' a_ k_a p_env'_a y_ t_y)
  = case g' of 
      Empty{- x == y -} -> p_env'_a ? lem_psubFV_notin x v_x PEmpty
      (Cons _y _ty g'') -> case ( x == a_ ) of 
          True  -> impossible ("by lemma" ? lem_free_subset_binds (concatE (Cons x t_x g) g'') 
                                                                  (TRefn (FTV a) PEmpty) k_a p_env'_a) 
          False -> WFVar2 (concatE g (esubFV x v_x g'')) a k_a p_gg''_a y (tsubFV x v_x t_y)
        where
            a        = a_ ? lem_in_env_esub g'' x v_x a_
                          ? lem_in_env_concat (Cons x t_x g) g'' a_
            y        = y_ ? lem_in_env_esub g'' x v_x y_
                          ? lem_in_env_concat g g'' y_
            p_gg''_a = lem_subst_wf g g'' x v_x t_x p_vx_er_tx 
                                    (TRefn (FTV a) PEmpty) k_a p_env'_a 
                                    ? lem_psubFV_notin x v_x PEmpty
lem_subst_wf_wfvar g g' x v_x t_x p_vx_er_tx  t k (WFVar3 _env' a_ k_a p_env'_a a1_ k_a1) 
  = case g' of
      Empty               -> impossible "x <> a1"
      (ConsT _a1 _k1 g'') -> case (x == a_) of 
          True  -> impossible ("by lemma" ? lem_free_subset_binds (concatE (Cons x t_x g) g'')
                                                                  (TRefn (FTV a) PEmpty) k_a p_env'_a)
          False -> WFVar3 (concatE g (esubFV x v_x g'')) a k_a p_gg''_a a1 k_a1
        where
            a        = a_ ? lem_in_env_esub g'' x v_x a_
                          ? lem_in_env_concat (Cons x t_x g) g'' a_
            a1       = a1_ ? lem_in_env_esub g'' x v_x a1_
                           ? lem_in_env_concat g g'' a1_
            p_gg''_a = lem_subst_wf g g'' x v_x t_x p_vx_er_tx 
                                    (TRefn (FTV a) PEmpty) k_a p_env'_a 
                                    ? lem_psubFV_notin x v_x PEmpty

{-@ lem_subst_wf_wffunc :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
          -> t_x:Type -> ProofOf(HasFType (erase_env g) v_x (erase t_x)) 
          -> t:Type -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (Cons x t_x g) g') t k && isWFFunc p_env_t}
          -> ProofOf(WFType (concatE g (esubFV x v_x g')) (tsubFV x v_x t) k) 
           / [tsize t, envsize g', ksize k, 0] @-}
lem_subst_wf_wffunc :: Env -> Env -> Vname -> Expr -> Type -> HasFType 
                           -> Type -> Kind -> WFType -> WFType
lem_subst_wf_wffunc g g' x v_x t_x p_vx_er_tx t k (WFFunc _env t_z k_z p_env_tz t' k' nms mk_p_yenv_t')
  = WFFunc (concatE g (esubFV x v_x g')) (tsubFV x v_x t_z) k_z p_g'g_tzvx 
           (tsubFV x v_x t') k' nms' mk_p_yg'g_t'vx
      where
        p_g'g_tzvx  = lem_subst_wf g g'              x v_x t_x p_vx_er_tx   t_z k_z p_env_tz
        {-@ mk_p_yg'g_t'vx :: { y:Vname | NotElem y nms' }
              -> ProofOf(WFType (Cons y (tsubFV x v_x t_z) (concatE g (esubFV x v_x g')))
                                (unbindT y (tsubFV x v_x t')) k') @-}
        mk_p_yg'g_t'vx y = lem_subst_wf g (Cons y t_z g') x v_x t_x p_vx_er_tx  
                               (unbindT y t') k' (mk_p_yenv_t' y)
                               ? lem_commute_tsubFV_unbindT x 
                                   (v_x ? lem_ftyp_islc (erase_env g) v_x (erase t_x) p_vx_er_tx) y t'
        nms'             = x:(unionEnv nms (concatE g g'))

{-@ lem_subst_wf_wfexis :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
          -> t_x:Type -> ProofOf(HasFType (erase_env g) v_x (erase t_x)) 
          -> t:Type -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (Cons x t_x g) g') t k && isWFExis p_env_t}
          -> ProofOf(WFType (concatE g (esubFV x v_x g')) (tsubFV x v_x t) k) 
           / [tsize t, envsize g', ksize k, 0] @-}
lem_subst_wf_wfexis :: Env -> Env -> Vname -> Expr -> Type -> HasFType 
                           -> Type -> Kind -> WFType -> WFType
lem_subst_wf_wfexis g g' x v_x t_x p_vx_er_tx t k (WFExis _env t_z k_z p_env_tz t' k' nms mk_p_yenv_t')
  = WFExis (concatE g (esubFV x v_x g')) (tsubFV x v_x t_z) k_z p_g'g_tzvx 
           (tsubFV x v_x t') k' nms' mk_p_yg'g_t'vx
      where
        p_g'g_tzvx  = lem_subst_wf g g'              x v_x t_x p_vx_er_tx t_z k_z p_env_tz
        {-@ mk_p_yg'g_t'vx :: { y:Vname | NotElem y nms' }
              -> ProofOf(WFType (Cons y (tsubFV x v_x t_z) (concatE g (esubFV x v_x g')))
                                (unbindT y (tsubFV x v_x t')) k') @-}
        mk_p_yg'g_t'vx y = lem_subst_wf g (Cons y t_z g') x v_x t_x p_vx_er_tx 
                               (unbindT y t') k' (mk_p_yenv_t' y)
                               ? lem_commute_tsubFV_unbindT x 
                                   (v_x ? lem_ftyp_islc (erase_env g) v_x (erase t_x) p_vx_er_tx) y t'
        nms'             = x:(unionEnv nms (concatE g g'))

{-@ lem_subst_wf_wfpoly :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
          -> t_x:Type -> ProofOf(HasFType (erase_env g) v_x (erase t_x))
          -> t:Type -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (Cons x t_x g) g') t k && isWFPoly p_env_t}
          -> ProofOf(WFType (concatE g (esubFV x v_x g')) (tsubFV x v_x t) k) 
           / [tsize t, envsize g', ksize k, 0] @-}
lem_subst_wf_wfpoly :: Env -> Env -> Vname -> Expr -> Type -> HasFType 
                           -> Type -> Kind -> WFType -> WFType
lem_subst_wf_wfpoly g g' x v_x t_x p_vx_er_tx t k (WFPoly _env k_a1 t' k_t' nms mk_p_a1env_t')
  = WFPoly (concatE g (esubFV x v_x g')) k_a1 (tsubFV x v_x t') k_t' nms' mk_p_a1gg'_t'
      where
        {-@ mk_p_a1gg'_t' :: { a1:Vname | NotElem a1 nms' }
              -> ProofOf(WFType (ConsT a1 k_a1 (concatE g (esubFV x v_x g')))
                                (unbind_tvT a1 (tsubFV x v_x t')) k_t') @-}
        mk_p_a1gg'_t' a1 = lem_subst_wf g (ConsT a1 k_a1 g') x v_x t_x p_vx_er_tx
                               (unbind_tvT a1 t') k_t' (mk_p_a1env_t' a1)
                               ? lem_commute_tsubFV_unbind_tvT x 
                                   (v_x ? lem_ftyp_islc (erase_env g) v_x (erase t_x) p_vx_er_tx)
                                   a1 t'
        nms'             = x:(unionEnv nms (concatE g g'))

{-@ lem_subst_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
          -> t_x:Type -> ProofOf(HasFType (erase_env g) v_x (erase t_x))
          -> t:Type -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (Cons x t_x g) g') t k }
          -> ProofOf(WFType (concatE g (esubFV x v_x g')) (tsubFV x v_x t) k) 
           / [tsize t, envsize g', ksize k, 1] @-}
lem_subst_wf :: Env -> Env -> Vname -> Expr -> Type -> HasFType 
                    -> Type -> Kind -> WFType -> WFType
lem_subst_wf g g' x v_x t_x p_vx_tx  t k (WFBase _env b)
  = WFBase (concatE g (esubFV x v_x g')) b ? lem_psubFV_notin x v_x PEmpty
lem_subst_wf g g' x v_x t_x p_vx_tx  t k p_env_t@(WFRefn {})  
  = lem_subst_wf_wfrefn g g' x v_x t_x p_vx_tx t k p_env_t 
lem_subst_wf g g' x v_x t_x p_vx_tx  t k p_env_t@(WFVar1 {})
  = lem_subst_wf_wfvar g g' x v_x t_x p_vx_tx  t k p_env_t
lem_subst_wf g g' x v_x t_x p_vx_tx  t k p_env_t@(WFVar2 {})
  = lem_subst_wf_wfvar g g' x v_x t_x p_vx_tx  t k p_env_t
lem_subst_wf g g' x v_x t_x p_vx_tx  t k p_env_t@(WFVar3 {}) 
  = lem_subst_wf_wfvar g g' x v_x t_x p_vx_tx  t k p_env_t
lem_subst_wf g g' x v_x t_x p_vx_tx  t k p_env_t@(WFFunc {})
  = lem_subst_wf_wffunc g g' x v_x t_x p_vx_tx  t k p_env_t
lem_subst_wf g g' x v_x t_x p_vx_tx  t k p_env_t@(WFExis {})
  = lem_subst_wf_wfexis g g' x v_x t_x p_vx_tx  t k p_env_t
lem_subst_wf g g' x v_x t_x p_vx_tx  t k p_env_t@(WFPoly {})
  = lem_subst_wf_wfpoly g g' x v_x t_x p_vx_tx  t k p_env_t
lem_subst_wf g g' x v_x t_x p_vx_tx  t k (WFKind _env _t p_env_t_base)
  = WFKind (concatE g (esubFV x v_x g')) (tsubFV x v_x t) p_gg'_tvx_base
      where
        p_gg'_tvx_base = lem_subst_wf g g' x v_x t_x p_vx_tx  t Base p_env_t_base
