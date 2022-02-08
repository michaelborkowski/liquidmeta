{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasSubtyping where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
--import LocalClosure
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
--import SystemFLemmasSubstitution
import Typing
--import BasicPropsCSubst
--import BasicPropsDenotes
--import BasicPropsEraseTyping
--import SubtypingFromEntailments
import LemmasWeakenWF
--import LemmasWeakenWFTV
--import LemmasWellFormedness
import LemmasTyping
import SubstitutionLemmaWF

{-@ reflect foo49 @-}
foo49 x = Just x
foo49 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------
{-
-- do I need this?    -> ProofOf(HasType g e t)
{-@ lem_self_is_subtype :: g:Env -> t:Type -> k:Kind -> { p_g_t:WFType | propOf p_g_t == WFType g t k }
        -> e:Term -> ProofOf(HasFType (erase_env g) e (erase t))
        -> ProofOf(WFEnv g) -> ProofOf(Subtype g (self t e k) t) / [tsize t, 1] @-}
lem_self_is_subtype :: Env -> Type -> Kind -> WFType -> Expr -> HasFType -> WFEnv -> Subtype 
lem_self_is_subtype g t@(TRefn b x p)      Base p_g_t e p_e_t p_g_wf 
  = lem_self_refn_sub g b x (p ? lem_refn_is_pred t b x p) p_g_wf p_g_t e p_e_t
lem_self_is_subtype g t@(TFunc x t_x t')   Base p_g_t e p_e_t p_g_wf 
  = lem_sub_refl g t Base p_g_t p_g_wf 
lem_self_is_subtype g t@(TExists x t_x t') Base p_g_t e_ p_e_t p_g_wf 
  = SBind g x t_x (self t' e Base) (TExists x t_x t' ? lem_free_bound_in_env g t Base p_g_t y
                                                     ? lem_tfreeBV_empty g t Base p_g_t)
          (y ? lem_fv_bound_in_fenv (erase_env g) e (erase t) p_e_t y) p_self_exis
      where
        e           = e_ ? lem_freeBV_emptyB    (erase_env g) e_ (erase t) p_e_t
                         ? lem_fv_subset_bindsF (erase_env g) e_ (erase t) p_e_t
        {-@ y :: { yy:Vname | not (in_env yy g) && not (Set_mem yy (free t')) && 
                                                   not (Set_mem yy (freeTV t')) } @-}
        (WFExis _ _ _tx k_x p_g_tx _t' _ y p_yg_t') 
                    = lem_wfexis_for_wf_texists g x t_x t' Base p_g_t
        p_er_g_wf   = lem_erase_env_wfenv g p_g_wf
        p_yg_wf     = WFEBind g p_g_wf y t_x k_x p_g_tx
        p_yg_tx     = lem_weaken_wf' g Empty p_g_wf t_x k_x p_g_tx y t_x
        p_y_er_tx   = FTVar1 (erase_env g) y (erase t_x)
        -- y:t_x, g |- (self t_x y) <: tx
        p_selftx_tx = lem_self_is_subtype (Cons y t_x g) (t_x ? toProof (tsize t_x < tsize (TExists x t_x t')))
                                          k_x p_yg_tx (FV y) p_y_er_tx p_yg_wf 
        p_yg_e_t    = lem_weaken_ftyp (erase_env g) FEmpty p_er_g_wf e (erase t) p_e_t y (erase t_x)
                          ? lem_erase_tsubBV x (FV y) t'
        -- y:t_x, g |- (unbindT x y (self t' e Base)) <: unbindT x y t'
        p_selft'_t' = lem_self_is_subtype (Cons y t_x g) (unbindT x y t') Base p_yg_t'
                                 e p_yg_e_t p_yg_wf ? lem_tsubBV_self x (FV y) t' e Base
                                                    ? toProof ( t === TExists x t_x t' )
        p_y_tx      = TSub (Cons y t_x g) (FV y) (self t_x (FV y) k_x) 
                           (TVar1 g y t_x k_x p_g_tx) t_x k_x p_yg_tx p_selftx_tx
        p_self_exis = SWitn (Cons y t_x g) (FV y) t_x p_y_tx (unbindT x y (self t' e Base)) 
                            x t' p_selft'_t' -- y,g |- (Self t' e)[y/x] <: \ex x:tx. t'
lem_self_is_subtype g t@(TPoly a k_a t')   Base p_g_t e p_e_t p_g_wf 
  = lem_sub_refl g t Base p_g_t p_g_wf
lem_self_is_subtype g t                    Star p_g_t e p_e_t p_g_wf 
  = lem_sub_refl g t Star p_g_t p_g_wf
-}

{-@ lem_sub_refl :: g:Env -> t:Type -> k:Kind -> { p_g_t:WFType | propOf p_g_t == WFType g t k } 
                          -> { p_t_t:Subtype | propOf p_t_t == Subtype g t t &&
                                               sizeOf p_t_t <= tdepth t } / [tsize t, ksize k] @-}
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
    = SFunc n g t_x t_x p_tx_tx t' t' nms' mk_p_t'_t'
        where
          p_tx_tx = lem_sub_refl g t_x k_x p_g_tx 
          {-@ mk_p_t'_t' :: { y:Vname | NotElem y nms'}
                -> { pf:Subtype | propOf pf == Subtype (Cons y t_x g) (unbindT y t') (unbindT y t') &&
                                  sizeOf pf <= tdepth t' } @-}
          mk_p_t'_t' y = lem_sub_refl (Cons y t_x g) (unbindT y t') k' (mk_p_yg_t' y)
          nms' = unionEnv nms g
          n    = max (tdepth t_x) (tdepth t')
lem_sub_refl g t k p_g_t@(WFExis _g t_x k_x p_g_tx t' k' nms mk_p_yg_t')  -- t = (\exists x:t_x. t')
    = SBind n g t_x t' (TExists t_x t' ? lem_wftype_islct g t k p_g_t)
            nms' mk_p_yg_t'_ext'
        where
          p_g_tx_star  = if k_x == Star then p_g_tx else WFKind g t_x p_g_tx
          {-@ mk_p_yg_t'_ext' :: { y:Vname | NotElem y nms' }
                 -> { pf:Subtype | propOf pf == Subtype (Cons y t_x g) (unbindT y t') 
                                                        (TExists t_x t') &&
                                   sizeOf pf <= tdepth t' + 1 } @-}
          mk_p_yg_t'_ext' y = SWitn (tdepth t') (Cons y t_x g) (FV y) t_x p_y_tx (unbindT y t') 
                                    t' p_yg_t'_t' 
            where
              {-@ p_y_tx :: { pf:HasType | propOf pf == HasType (Cons y t_x g) (FV y) t_x &&
                                           sizeOf pf == 0 } @-}
              p_y_tx       = TVar1 g y t_x Star p_g_tx_star ? toProof ( self t_x (FV y) Star == t_x )
              p_yg_t'_t'   = lem_sub_refl (Cons y t_x g) (unbindT y t') k' (mk_p_yg_t' y)
                                          ? lem_tsubBV_is_unbindT y t'
          nms' = unionEnv nms g
          n    = (tdepth t' + 1)
lem_sub_refl g t k (WFPoly _g k_a t' k_t' nms mk_p_ag_t') 
    = SPoly (tdepth t') g k_a t' t' nms' mk_p_ag_t'_t'
        where
          mk_p_ag_t'_t' a = lem_sub_refl (ConsT a k_a g) (unbind_tvT a t') k_t' (mk_p_ag_t' a)
          nms'            = unionEnv nms g
lem_sub_refl g t k (WFKind _g _t p_g_t_base) 
    = lem_sub_refl g t Base p_g_t_base 

{-
{-@ lem_witness_sub :: g:Env -> v_x:Value -> t_x:Type -> ProofOf(HasType g v_x t_x) 
        -> ProofOf(WFEnv g) -> x:Vname -> t':Type -> k':Kind 
        -> { y:Vname | not (in_env y g) && not (Set_mem y (free t')) && not (Set_mem y (freeTV t')) }
        -> ProofOf(WFType (Cons y t_x g) (unbindT x y t') k')
        -> ProofOf(Subtype g (tsubBV x v_x t') (TExists x t_x t')) @-}
lem_witness_sub :: Env -> Expr -> Type -> HasType -> WFEnv -> Vname -> Type -> Kind
                       -> Vname -> WFType -> Subtype
lem_witness_sub g v_x t_x p_vx_tx p_g_wf x t' k' y p_yg_t' 
  = SWitn g v_x t_x p_vx_tx (tsubBV x v_x t') x t' p_t'vx_t'vx
      where
      p_g_tx      = lem_typing_wf g v_x t_x p_vx_tx p_g_wf
      p_yg_wf     = WFEBind g p_g_wf y t_x Star p_g_tx
      p_g_t'vx    = lem_subst_wf' g Empty y v_x t_x p_vx_tx p_yg_wf (unbindT x y t') k' p_yg_t'
                                  ? lem_tsubFV_unbindT x y v_x t'
      p_t'vx_t'vx = lem_sub_refl g (tsubBV x v_x t') k' p_g_t'vx p_g_wf
-}

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
lem_sub_pullback_wftype g p_g_wf s t p_s_t@(SFunc _ _ s_x t_x _ s' t' _ _) p_g_s p_g_t
  = impossible ("by lemma" ? lem_wf_tfunc_star g t_x t' p_g_t)
lem_sub_pullback_wftype g p_g_wf s t p_s_t@(SWitn _ _ v_x t_x p_vx_tx _s t' p_s_t'vx) 
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
lem_sub_pullback_wftype g p_g_wf s t p_s_t@(SBind _ _ s_x s' _t nms mk_p_yg_s'_t) 
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
lem_sub_pullback_wftype g p_g_wf s t p_s_t@(SPoly _ _ k' s' t' _ _) p_g_s p_g_t
  = impossible ("by lemma" ? lem_wf_tpoly_star g k' t' p_g_t)

{-@ lem_subtype_in_exists :: n:Nat -> g:Env -> t_x:Type -> t:Type -> t':Type
        -> ProofOf(WFType g (TExists t_x t') Base) -> nms:Names
        -> ({ y:Vname | NotElem y nms }
                -> ProofOfN n (Subtype (Cons y t_x g) (unbindT y t) (unbindT y t')) )
        -> { pf:Subtype | propOf pf == Subtype g (TExists t_x t) (TExists t_x t') &&
                          sizeOf pf == n + 2 } @-}
lem_subtype_in_exists :: Int -> Env -> Type -> Type -> Type -> WFType -> Names
                             -> (Vname -> Subtype) -> Subtype
lem_subtype_in_exists n g t_x t t' p_g_txt' nms mk_p_yg_t_t'
  = SBind (n+1) g t_x t (TExists t_x t' ? lem_wftype_islct g (TExists t_x t') Base p_g_txt')
          nms' mk_p_yg_t_ext'
      where
        (WFExis _ _tx k_x p_g_tx _t' _k' _nms'' _p_yg_t')
                    = lem_wfexis_for_wf_texists g t_x t' Base p_g_txt'
        p_g_tx_star      = if k_x == Star then p_g_tx else WFKind g t_x p_g_tx
        mk_p_yg_t_ext' y = SWitn n (Cons y t_x g) (FV y) t_x p_y_tx (unbindT y t) t'
                                 (mk_p_yg_t_t' y ? lem_tsubBV_is_unbindT y t')
          where
            p_y_tx       = TVar1 g y t_x Star p_g_tx_star  ? toProof (self t_x (FV y) Star === t_x )
        nms'             = unionEnv nms g
