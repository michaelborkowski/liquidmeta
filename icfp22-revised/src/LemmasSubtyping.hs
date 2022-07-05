{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasSubtyping where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof,(?))
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import BasicPropsSubstitution
import BasicPropsEnvironments
import WellFormedness
import BasicPropsWellFormedness
import Typing
import LemmasWeakenWF
import SubstitutionLemmaWF
import LemmasTyping

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------

-- sizeOf p_t_t <= tdepth t * 2}
{-@ lem_sub_refl :: g:Env -> t:Type -> k:Kind -> { p_g_t:WFType | propOf p_g_t == WFType g t k } 
                          -> { p_t_t:Subtype | propOf p_t_t == Subtype g t t }
                           / [tsize t, ksize k] @-}
lem_sub_refl :: Env -> Type -> Kind -> WFType -> Subtype
lem_sub_refl g t k p_g_t@(WFBase _g b)  -- k == Base
    = SBase g b PEmpty PEmpty nms p_imp_emp_emp
        where
          p_imp_emp_emp y = IRefl (Cons y (TRefn b PEmpty) g) PEmpty
          nms = unionEnv [] g
lem_sub_refl g t k p_g_t@(WFRefn _g b p_g_b ps nms mk_pf_p_bl)  -- t = b{x:p} && k == Base
    = SBase g b ps ps nms' p_imp_emp_emp
        where
          p_imp_emp_emp y = IRefl (Cons y (TRefn b PEmpty) g) (unbindP y ps)
          nms' = unionEnv nms g
lem_sub_refl g t k (WFVar1 g' a k_a) 
    = SBase g (FTV a) PEmpty PEmpty nms p_imp_emp_emp
        where
          p_imp_emp_emp y = IRefl (Cons y (TRefn (FTV a) PEmpty) g) PEmpty
          nms = unionEnv [] g
lem_sub_refl g t k (WFVar2 g' a k_a p_g'_a y t_y) 
    = SBase g (FTV a) PEmpty PEmpty nms p_imp_emp_emp
        where
          p_imp_emp_emp y = IRefl (Cons y (TRefn (FTV a) PEmpty) g) PEmpty
          nms = unionEnv [] g
lem_sub_refl g t k (WFVar3 g' a k_a p_g'_a y t_y) 
    = SBase g (FTV a) PEmpty PEmpty nms p_imp_emp_emp
        where
          p_imp_emp_emp y = IRefl (Cons y (TRefn (FTV a) PEmpty) g) PEmpty
          nms = unionEnv [] g
lem_sub_refl g t k (WFFunc _g t_x k_x p_g_tx t' k' nms mk_p_yg_t')  -- t = (x:t_x -> t')
    = SFunc g t_x t_x p_tx_tx t' t' nms' mk_p_t'_t'
        where
          p_tx_tx = lem_sub_refl g t_x k_x p_g_tx 
          {-@ mk_p_t'_t' :: { y:Vname | NotElem y nms'}
                -> { pf:Subtype | propOf pf == Subtype (Cons y t_x g) (unbindT y t') (unbindT y t') } @-}
          mk_p_t'_t' y = lem_sub_refl (Cons y t_x g) (unbindT y t') k' (mk_p_yg_t' y)
          nms' = unionEnv nms g
lem_sub_refl g t k p_g_t@(WFExis _g t_x k_x p_g_tx t' k' nms mk_p_yg_t')  -- t = (\exists x:t_x. t')
    = SBind g t_x t' (TExists t_x t' ? lem_wftype_islct g t k p_g_t)
            nms' mk_p_yg_t'_ext'
        where
          p_g_tx_star  = if k_x == Star then p_g_tx else WFKind g t_x p_g_tx
          {-@ mk_p_yg_t'_ext' :: { y:Vname | NotElem y nms' }
                 -> { pf:Subtype | propOf pf == Subtype (Cons y t_x g) (unbindT y t') 
                                                        (TExists t_x t') } @-}
          mk_p_yg_t'_ext' y = SWitn (Cons y t_x g) (FV y) t_x p_y_tx 
                                    (unbindT y t') t' p_yg_t'_t' 
            where
              {-@ p_y_tx :: { pf:HasType | propOf pf == HasType (Cons y t_x g) (FV y) t_x } @-}
              p_y_tx       = TVar1 g y t_x Star p_g_tx_star ? toProof ( self t_x (FV y) Star == t_x )
              p_yg_t'_t'   = lem_sub_refl (Cons y t_x g) (unbindT y t') k' (mk_p_yg_t' y)
                                          ? lem_tsubBV_is_unbindT y t'
          nms' = unionEnv nms g
lem_sub_refl g t k (WFPoly _g k_a t' k_t' nms mk_p_ag_t') 
    = SPoly g k_a t' t' nms' mk_p_ag_t'_t'
        where
          mk_p_ag_t'_t' a = lem_sub_refl (ConsT a k_a g) (unbind_tvT a t') k_t' (mk_p_ag_t' a)
          nms'            = unionEnv nms g
lem_sub_refl g t k (WFKind _g _t p_g_t_base) 
    = lem_sub_refl g t Base p_g_t_base 

{-@ lem_witness_sub :: g:Env -> v_x:Value -> t_x:Type -> ProofOf(HasType g v_x t_x) 
        -> t':Type -> k:Kind  -> ProofOf(WFType g (TExists t_x t') k) -> ProofOf(WFEnv g)
        -> ProofOf(Subtype g (tsubBV v_x t') (TExists t_x t')) @-}
lem_witness_sub :: Env -> Expr -> Type -> HasType ->  Type -> Kind -> WFType -> WFEnv -> Subtype
lem_witness_sub g v_x t_x p_vx_tx  t' k p_g_txt' p_g_wf
  = case lem_wfexis_for_wf_texists g t_x t' k p_g_txt' of 
      (WFExis _ _ _ _ _ k_t' nms mk_p_yg_t') 
          -> SWitn g v_x t_x p_vx_tx (tsubBV v_x t') t' p_t'vx_t'vx
        where
          y           = fresh_var nms g
          p_vx_er_tx  = lem_typing_hasftype g v_x t_x p_vx_tx p_g_wf
          p_g_t'vx    = lem_subst_wf g Empty y v_x t_x p_vx_er_tx (unbindT y t') k_t' (mk_p_yg_t' y)
                            ? lem_tsubFV_unbindT y v_x 
                                  (t' ? lem_free_bound_in_env g (TExists t_x t') k p_g_txt' y)
          p_t'vx_t'vx = lem_sub_refl g (tsubBV v_x t') k_t' p_g_t'vx 

-- Suppose we know that G |- s <: t, G |- s : Star and G |- t : Base. Then we
--   can produce a judgment that G |- s : Base too.
{-@ lem_sub_pullback_wftype :: g:Env -> ProofOf(WFEnv g) -> s:Type -> t:Type 
        -> { p_s_t:Subtype | propOf p_s_t == Subtype g s t }
        -> ProofOf(WFType g s Star) -> ProofOf(WFType g t Base) -> ProofOf(WFType g s Base) 
         / [ tdepth s, tdepth t ] @-}
lem_sub_pullback_wftype :: Env -> WFEnv -> Type -> Type -> Subtype 
                                        -> WFType -> WFType -> WFType
lem_sub_pullback_wftype g p_g_wf s t p_s_t@(SBase _ b ps qs nms mk_imp_ps_qs) p_g_s p_g_t
  = case p_g_s of
        (WFVar1 {})           -> lem_wf_pempty_for_wf_trefn g b qs Base p_g_t
        (WFVar2 {})           -> lem_wf_pempty_for_wf_trefn g b qs Base p_g_t
        (WFVar3 {})           -> lem_wf_pempty_for_wf_trefn g b qs Base p_g_t
        (WFKind _ _s p_g_s_b) -> p_g_s_b
lem_sub_pullback_wftype g p_g_wf s t p_s_t@(SFunc _ s_x t_x _ s' t' _ _) p_g_s p_g_t
  = impossible ("by lemma" ? lem_wf_tfunc_star g t_x t' p_g_t)
lem_sub_pullback_wftype g p_g_wf s t p_s_t@(SWitn _ v_x t_x p_vx_tx _s t' p_s_t'vx) 
                        p_g_s p_g_t
  = lem_sub_pullback_wftype g p_g_wf s (tsubBV v_x t') p_s_t'vx p_g_s p_g_t'vx
      where
        (WFExis _ _tx k_x p_g_tx _ _ nms mk_p_wg_t')
                      = lem_wfexis_for_wf_texists g t_x t' Base p_g_t
        w             = fresh_var nms g
        p_vx_er_tx    = lem_typing_hasftype g v_x t_x p_vx_tx p_g_wf
        p_g_t'vx      = lem_subst_wf g Empty w v_x t_x p_vx_er_tx (unbindT w t') 
                                      Base (mk_p_wg_t' w)
                                      ? lem_tsubFV_unbindT w v_x (t' 
                                            ? lem_free_bound_in_env g t Base p_g_t w)
lem_sub_pullback_wftype g p_g_wf s t p_s_t@(SBind _ s_x s' _t nms mk_p_yg_s'_t) 
                        p_g_s p_g_t
  = WFExis g s_x k_x p_g_sx s' Base nms'' mk_p_wg_s'_b
      where
        {-@ mk_p_wg_s'_b :: { w:Vname | NotElem w nms''}
              -> ProofOf(WFType (Cons w s_x g) (unbindT w s') Base)  @-}
        mk_p_wg_s'_b w = lem_sub_pullback_wftype (Cons w s_x g) p_wg_wf (unbindT w s') t
                                         (mk_p_yg_s'_t w) (mk_p_wg_s' w) p_wg_t
          where
            p_wg_wf    = WFEBind g p_g_wf w s_x k_x p_g_sx
            p_wg_t     = lem_weaken_wf g Empty t Base p_g_t w s_x
        (WFExis _ _sx k_x p_g_sx _ _ nms' mk_p_wg_s')
                    = lem_wfexis_for_wf_texists g s_x s' Star p_g_s
        nms''          = unionEnv (union nms nms') g
lem_sub_pullback_wftype g p_g_wf s t p_s_t@(SPoly _ k' s' t' _ _) p_g_s p_g_t
  = impossible ("by lemma" ? lem_wf_tpoly_star g k' t' p_g_t)

{-@ lem_subtype_in_exists :: g:Env -> t_x:Type -> t:Type 
        -> { t':Type | isLCT (TExists t_x t') } -> k_x:Kind -> ProofOf(WFType g t_x k_x) -> nms:Names
        -> ({ y:Vname | NotElem y nms }
                -> ProofOf (Subtype (Cons y t_x g) (unbindT y t) (unbindT y t')) )
        -> { pf:Subtype | propOf pf == Subtype g (TExists t_x t) (TExists t_x t') } @-}
lem_subtype_in_exists :: Env -> Type -> Type -> Type -> Kind -> WFType -> Names
                             -> (Vname -> Subtype) -> Subtype
lem_subtype_in_exists g t_x t t' k_x p_g_tx nms mk_p_yg_t_t'
  = SBind g t_x t (TExists t_x t') nms' mk_p_yg_t_ext'
      where
        p_g_tx_star      = if k_x == Star then p_g_tx else WFKind g t_x p_g_tx
        mk_p_yg_t_ext' y = SWitn (Cons y t_x g) (FV y) t_x p_y_tx (unbindT y t) t'
                                 (mk_p_yg_t_t' y ? lem_tsubBV_is_unbindT y t')
          where
            p_y_tx       = TVar1 g y t_x Star p_g_tx_star  ? toProof (self t_x (FV y) Star === t_x )
        nms'             = unionEnv nms g
