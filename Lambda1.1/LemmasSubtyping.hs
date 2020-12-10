{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasSubtyping where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFTyping
import WellFormedness
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import Entailments
import LemmasChangeVarWF
import LemmasWeakenWF
import LemmasWellFormedness
import LemmasTyping

{-@ reflect foo43 @-}
foo43 x = Just x
foo43 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------

--        -> { e:Expr | Set_emp ( freeBV e ) && Set_sub (fv e) (binds g) }
{-@ lem_self_is_subtype :: g:Env -> t:Type -> { p_g_t:WFType | propOf p_g_t == WFType g t }
        -> e:Expr -> ProofOf(HasFType (erase_env g) e (erase t))
        -> ProofOf(WFEnv g) -> ProofOf(Subtype g (self t e) t) / [tsize t, 1] @-}
lem_self_is_subtype :: Env -> Type -> WFType -> Expr -> HasFType -> WFEnv -> Subtype 
lem_self_is_subtype g t p_g_t@(WFRefn _ x b p _ _) e  p_e_t p_g_wf 
  = lem_self_refn_sub g b x p p_g_wf p_g_t e p_e_t      
lem_self_is_subtype g t p_g_t@(WFFunc {}) e  p_e_t p_g_wf 
  = lem_sub_refl g t p_g_t p_g_wf 
lem_self_is_subtype g t p_g_t@(WFExis _ x t_x p_g_tx t' y p_yg_t') e_ p_e_t p_g_wf 
  = SBind g x t_x (self t' e) (TExists x t_x t' ? lem_free_bound_in_env g t p_g_t y
                                                ? lem_tfreeBV_empty g t p_g_t {-p_g_wf-})
          y p_self_exis
      where
        e           = e_ ? lem_freeBV_emptyB    (erase_env g) e_ (erase t) p_e_t
                         ? lem_fv_subset_bindsF (erase_env g) e_ (erase t) p_e_t
--        {-@ y :: { y:Vname | not (in_env y g) && not (in_envF y (erase_env g)) } @-}
--        (WFExis _ _ _tx p_g_tx _t' y p_yg_t') = p_g_t
        p_yg_wf     = WFEBind g p_g_wf y t_x p_g_tx
        p_yg_tx     = lem_weaken_wf g Empty t_x p_g_tx y t_x
        -- y:t_x, g |- (self t_x y) <: tx
        p_y_er_tx   = FTVar1 (erase_env g) y (erase t_x)
        p_selftx_tx = lem_self_is_subtype (Cons y t_x g) (t_x ? toProof (tsize t_x < tsize (TExists x t_x t')))
                                          p_yg_tx (FV y) p_y_er_tx p_yg_wf
--                          ? toProof ( tsize t_x < tsize ( TExists x t_x t' ) )
        -- y:t_x, g |- (unbindT x y (self t' e)) <: unbindT x y t'
        p_yg_e_t    = lem_weaken_ftyp (erase_env g) FEmpty e (erase t) p_e_t y (erase t_x)
                          ? lem_erase_tsubBV x (FV y) t'
        p_selft'_t' = lem_self_is_subtype (Cons y t_x g) (unbindT x y t') p_yg_t' 
                                          e p_yg_e_t p_yg_wf ? lem_tsubBV_self x (FV y) t' e
                                                             ? toProof ( t === TExists x t_x t' )
        p_y_tx      = TSub (Cons y t_x g) (FV y) (self t_x (FV y)) 
                           (TVar1 g y t_x p_g_tx) t_x p_yg_tx p_selftx_tx
        p_self_exis = SWitn (Cons y t_x g) (FV y) t_x p_y_tx (unbindT x y (self t' e)) 
                            x t' p_selft'_t' -- y,g |- (Self t' e)[y/x] <: \ex x:tx. t'

{-@ lem_sub_refl :: g:Env -> t:Type -> { p_g_t:WFType | propOf p_g_t == WFType g t } 
                          -> ProofOf(WFEnv g) -> ProofOf(Subtype g t t) / [tsize t, 0] @-}
lem_sub_refl :: Env -> Type -> WFType -> WFEnv -> Subtype
lem_sub_refl g t (WFRefn _g x b p y pf_p_bl) p_g_wf-- t = b{x:p}
    = SBase g x b p x p y (EntPred (Cons y (TRefn b x p) g) (unbind x y p) eval_thp_func)
        where
          {-@ eval_thp_func :: th':CSub -> ProofOf(DenotesEnv (Cons y (TRefn b x p) g) th') 
                                          -> ProofOf(EvalsTo (csubst th' (unbind x y p)) (Bc True)) @-}
          eval_thp_func :: CSub -> DenotesEnv -> EvalsTo
          eval_thp_func th' den_yg_th' = case den_yg_th' of 
            (DEmp)                     -> impossible "Cons y t g != Empty"
            (DExt g th den_g_th _y _t v den_tht_v) -> case den_tht_v of 
              (DRefn _b _x _thp _v pf_v_b ev_thpv_tt) -> ev_thpv_tt 
                ? lem_subFV_unbind x y v p
                ? lem_ctsubst_refn th b x p
                ? lem_csubst_subBV x _v (FTBasic _b) pf_v_b th p
              (_)                      -> impossible ("by lemma" ? lem_ctsubst_refn th b x p)
lem_sub_refl g t@(TFunc x t_x t') p_g_t p_g_wf 
    = SFunc g x t_x x t_x p_tx_tx t' t' y p_t'_t'
        where
          (WFFunc _g _x _t_x p_g_tx _t' y p_yg_t') = p_g_t
          p_yg_wf = WFEBind g p_g_wf y t_x p_g_tx
          p_tx_tx = lem_sub_refl g t_x p_g_tx p_g_wf
          p_t'_t' = lem_sub_refl (Cons y t_x g) (unbindT x y t') p_yg_t' p_yg_wf
lem_sub_refl g t@(TExists x t_x t') p_g_t p_g_wf 
    = SBind g x t_x t' (TExists x t_x t' ? lem_tfreeBV_empty g t p_g_t)
            (y ? lem_free_bound_in_env g t p_g_t y) p_yg_t'_ext'
        where
          (WFExis _g x t_x p_g_tx t' y p_yg_t') = p_g_t
          p_y_self_tx  = TVar1 g y t_x p_g_tx
          p_y_er_tx    = FTVar1 (erase_env g) y (erase t_x) 
          p_selftx_tx  = lem_self_is_subtype (Cons y t_x g) t_x p_yg_tx (FV y) p_y_er_tx p_yg_wf
          {-@ p_y_tx :: ProofOf(HasType (Cons y t_x g) (FV y) t_x) @-}
          p_y_tx       = TSub (Cons y t_x g) (FV y) (self t_x (FV y)) p_y_self_tx 
                              t_x p_yg_tx p_selftx_tx
          p_yg_wf      = WFEBind g p_g_wf y t_x p_g_tx
          p_yg_tx      = lem_weaken_wf g Empty t_x p_g_tx y t_x
          p_yg_t'_t'   = lem_sub_refl (Cons y t_x g) (unbindT x y t') p_yg_t' p_yg_wf
          p_yg_t'_ext' = SWitn (Cons y t_x g) (FV y) t_x p_y_tx (unbindT x y t') 
                               x t' p_yg_t'_t'

{-@ lem_change_bv_sub_func :: g:Env -> x:Vname -> t_x:Type  
                                    -> t:Type -> x':Vname -> t':Type
        -> { y:Vname | not (in_env y g) && not (Set_mem y (free t)) && not (Set_mem y (free t')) 
                                      && unbindT x y t == unbindT x' y t' }
        -> ProofOf(WFType g t_x) -> ProofOf(WFType (Cons y t_x g) (unbindT x y t)) 
        -> ProofOf(WFEnv g) -> ProofOf(Subtype g (TFunc x t_x t) (TFunc x' t_x t')) @-}
lem_change_bv_sub_func :: Env -> Vname -> Type -> Type -> Vname -> Type -> Vname 
                              -> WFType -> WFType -> WFEnv -> Subtype
lem_change_bv_sub_func g x t_x t x' t' y p_g_tx p_yg_t p_g_wf
  = SFunc g x t_x x' t_x (lem_sub_refl g t_x p_g_tx p_g_wf) t t' y p_yg_t_t'
      where
        p_yg_t_t' = lem_sub_refl (Cons y t_x g) (unbindT x y t) p_yg_t p_yg_wf
        p_yg_wf   = WFEBind g p_g_wf y t_x p_g_tx
