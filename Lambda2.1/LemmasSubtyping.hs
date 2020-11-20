{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasSubtyping where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import SameBinders
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasSubstitution
import Typing
import SystemFAlphaEquivalence
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

{-@ lem_sub_refl :: g:Env -> t:Type -> k:Kind -> { p_g_t:WFType | propOf p_g_t == WFType g t k } 
                          -> ProofOf(WFEnv g) -> ProofOf(Subtype g t t) / [wftypSize p_g_t] @-}
lem_sub_refl :: Env -> Type -> Kind -> WFType -> WFEnv -> Subtype
lem_sub_refl g t k (WFBase _g b) p_g_wf
    = SBase g 1 b (Bc True) 1 (Bc True) y 
            (EntPred (Cons y (TRefn b 1 (Bc True)) g) (Bc True) eval_thp_func)
        where
          {-@ eval_thp_func :: th':CSub -> ProofOf(DenotesEnv (Cons y (TRefn b 1 (Bc True)) g) th') 
                                          -> ProofOf(EvalsTo (csubst th' (unbind 1 y (Bc True))) (Bc True)) @-}
          eval_thp_func :: CSub -> DenotesEnv -> EvalsTo
          eval_thp_func th' _ = Refl (Bc True) ? lem_csubst_bc th' True
          y = fresh_var g
lem_sub_refl g t k (WFRefn _g x b p_g_b p y pf_p_bl) p_g_wf-- t = b{x:p}
    = SBase g x b p x p y (EntPred (Cons y (TRefn b x p) g) (unbind x y p) eval_thp_func)
        where
          {-@ eval_thp_func :: th':CSub -> ProofOf(DenotesEnv (Cons y (TRefn b x p) g) th') 
                                          -> ProofOf(EvalsTo (csubst th' (unbind x y p)) (Bc True)) @-}
          eval_thp_func :: CSub -> DenotesEnv -> EvalsTo
          eval_thp_func th' den_yg_th' = undefined {- "type variables!"  case den_yg_th' of 
            (DEmp)                                 -> impossible "Cons y t g != Empty"
            (DExt g th den_g_th _y _t v den_tht_v) -> case den_tht_v of 
              (DRefn _b _x _thp _v pf_v_b ev_thpv_tt) -> ev_thpv_tt 
                ? lem_subFV_unbind x y v p
                -- ? lem_ctsubst_refn th b x p
                ? lem_csubst_subBV x v (FTBasic b) pf_v_b th p
              (_)                                     -> impossible "" -- ("by lemma" ? lem_ctsubst_refn th b x p)
          -}
lem_sub_refl g t k (WFVar1 {}) p_g_wf
    = undefined
lem_sub_refl g t k (WFVar2 {}) p_g_wf
    = undefined
lem_sub_refl g t k (WFVar3 {}) p_g_wf
    = undefined
lem_sub_refl g t k (WFFunc _g x t_x k_x p_g_tx t' k' y p_yg_t') p_g_wf -- t = (x:t_x -> t')
    = SFunc g x t_x x t_x p_tx_tx t' t' y p_t'_t'
        where
          p_yg_wf = WFEBind g p_g_wf y t_x k_x p_g_tx
          p_tx_tx = lem_sub_refl g t_x k_x p_g_tx p_g_wf
          p_t'_t' = lem_sub_refl (Cons y t_x g) (unbindT x y t') k' p_yg_t' p_yg_wf
lem_sub_refl g t k p_g_t@(WFExis _g x t_x k_x p_g_tx t' k' y p_yg_t') p_g_wf -- t = (\exists x:t_x. t')
    = undefined {-
    = SBind g x t_x t' (TExists x t_x t' {-? lem_tfreeBV_empty g t p_g_t p_g_wf-})
            (y ? lem_free_bound_in_env g t p_g_t y) p_yg_t'_ext'
        where
          p_y_self_tx  = TVar1 g y t_x
          {-@ p_y_tx :: ProofOf(HasType (Cons y t_x g) (FV y) t_x) @-}
          p_y_tx       = case t_x of 
            (TRefn b z p) -> TSub (Cons y t_x g) (FV y) (self t_x (FV y)) p_y_self_tx t_x k_x p_yg_tx p_selftx_tx
              where
                p_selftx_tx = lem_self_refn_sub g b z p p_g_tx y
            _             -> p_y_self_tx 
          p_yg_wf      = WFEBind g p_g_wf y t_x k_x p_g_tx
          p_yg_tx      = lem_weaken_wf g Empty (p_g_wf ? lem_empty_concatE g Empty) t_x k_x p_g_tx y t_x
          p_yg_t'_t'   = lem_sub_refl (Cons y t_x g) (unbindT x y t') k' p_yg_t' p_yg_wf
          p_yg_t'_ext' = SWitn (Cons y t_x g) (FV y) t_x p_y_tx (unbindT x y t') 
                               x t' p_yg_t'_t'-}
lem_sub_refl g t k (WFPoly {}) p_g_wf
    = undefined
lem_sub_refl g t k (WFKind _g _t p_g_t_base) p_g_wf
    = lem_sub_refl g t Base p_g_t_base p_g_wf

{-@ lem_change_bv_sub_func :: g:Env -> x:Vname -> t_x:Type -> k_x:Kind 
                                    -> t:Type -> k:Kind -> x':Vname -> t':Type
        -> { y:Vname | not (in_env y g) && not (Set_mem y (free t)) && not (Set_mem y (free t')) 
                                      && not (Set_mem y (freeTV t)) && not (Set_mem y (freeTV t'))
                                      && unbindT x y t == unbindT x' y t' }
        -> ProofOf(WFType g t_x k_x ) -> ProofOf(WFType (Cons y t_x g) (unbindT x y t) k) 
        -> ProofOf(WFEnv g) -> ProofOf(Subtype g (TFunc x t_x t) (TFunc x' t_x t')) @-}
lem_change_bv_sub_func :: Env -> Vname -> Type -> Kind -> Type -> Kind -> Vname -> Type -> Vname 
                              -> WFType -> WFType -> WFEnv -> Subtype
lem_change_bv_sub_func g x t_x k_x t k x' t' y p_g_tx p_yg_t p_g_wf
  = SFunc g x t_x x' t_x (lem_sub_refl g t_x k_x p_g_tx p_g_wf) t t' y p_yg_t_t'
      where
        p_yg_t_t' = lem_sub_refl (Cons y t_x g) (unbindT x y t) k p_yg_t p_yg_wf
        p_yg_wf   = WFEBind g p_g_wf y t_x k_x p_g_tx

