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
import SystemFLemmasFTyping2
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import BasicPropsEraseTyping
import SubtypingFromEntailments
import LemmasChangeVarWF
import LemmasWeakenWF
import LemmasWeakenWFTV
import LemmasWellFormedness
import LemmasTyping

{-@ reflect foo44 @-}
foo44 x = Just x
foo44 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------

-- do I need this?    -> ProofOf(HasType g e t)
{-@ lem_self_is_subtype :: g:Env -> t:Type -> k:Kind -> { p_g_t:WFType | propOf p_g_t == WFType g t k }
        -> e:Term -> ProofOf(HasFType (erase_env g) e (erase t))
        -> ProofOf(WFEnv g) -> ProofOf(Subtype g (self t e k) t) / [tsize t, 1] @-}
lem_self_is_subtype :: Env -> Type -> Kind -> WFType -> Expr -> HasFType -> WFEnv -> Subtype 
lem_self_is_subtype g (TRefn b x p)        Base p_g_t e p_e_t p_g_wf 
  = lem_self_refn_sub g b x p p_g_wf p_g_t e p_e_t
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

{-@ lem_sub_refl :: g:Env -> t:Type -> k:Kind -> { p_g_t:WFType | propOf p_g_t == WFType g t k } 
                          -> ProofOf(WFEnv g) -> ProofOf(Subtype g t t) / [tsize t, 0] @-}
lem_sub_refl :: Env -> Type -> Kind -> WFType -> WFEnv -> Subtype
lem_sub_refl g t k (WFBase _g b tt) p_g_wf
    = SBase g Z b tt Z tt (y ? lem_trivial_nofv tt)
            (EntPred (Cons y (TRefn b Z tt) g) (unbind 0 y tt) eval_thp_func)
--                     ? lem_subBV_notin 0 (FV y) (tt ? lem_trivial_nobv tt)))
        where
          {-@ eval_thp_func :: th':CSub -> ProofOf(DenotesEnv (Cons y (TRefn b Z tt) g) th') 
                                        -> ProofOf(EvalsTo (csubst th' (unbind 0 y tt)) (Bc True)) @-}
          eval_thp_func :: CSub -> DenotesEnv -> EvalsTo
          eval_thp_func th' _ = lem_evals_trivial tt ? lem_subBV_notin 0 (FV y) (tt ? lem_trivial_nobv tt)
                                                     ? lem_csubst_trivial th' tt
          y                   = fresh_var g
lem_sub_refl g t k (WFRefn _g x b tt p_g_b p y pf_p_bl) p_g_wf-- t = b{x:p}
    = SBase g x b p x p y (EntPred (Cons y (TRefn b x p) g) (unbind 0 y p) eval_thp_func)
        where
          {-@ eval_thp_func :: th':CSub -> ProofOf(DenotesEnv (Cons y (TRefn b x p) g) th') 
                                        -> ProofOf(EvalsTo (csubst th' (unbind 0 y p)) (Bc True)) @-}
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
lem_sub_refl g t k (WFVar1 g' a tt k_a) p_g_wf
    = undefined
lem_sub_refl g t k (WFVar2 g' a tt k_a p_g'_a y t_y) p_g_wf
    = undefined
lem_sub_refl g t k (WFVar3 g' a tt k_a p_g'_a y t_y) p_g_wf
    = undefined
lem_sub_refl g t k (WFFunc _g x t_x k_x p_g_tx t' k' y p_yg_t') p_g_wf -- t = (x:t_x -> t')
    = SFunc g x t_x x t_x p_tx_tx t' t' y p_t'_t'
        where
          p_yg_wf = WFEBind g p_g_wf y t_x k_x p_g_tx
          p_tx_tx = lem_sub_refl g t_x k_x p_g_tx p_g_wf
          p_t'_t' = lem_sub_refl (Cons y t_x g) (unbindT x y t') k' p_yg_t' p_yg_wf
lem_sub_refl g t k p_g_t@(WFExis _g x t_x k_x p_g_tx t' k' y p_yg_t') p_g_wf -- t = (\exists x:t_x. t')
 = undefined {- update
    = SBind g x t_x t' (TExists x t_x t' {-? lem_tfreeBV_empty g t p_g_t p_g_wf-})
            (y ? lem_free_bound_in_env g t k p_g_t y) p_yg_t'_ext'
        where
          p_y_self_tx  = TVar1 g y t_x
          {-@ p_y_tx :: ProofOf(HasType (Cons y t_x g) (FV y) t_x) @-}
          p_y_tx       = case t_x of 
            (TRefn b z p) -> TSub (Cons y t_x g) (FV y) (self t_x (FV y) k_x) p_y_self_tx t_x k_x p_yg_tx p_selftx_tx
              where
                p_selftx_tx = lem_self_refn_sub g b z p p_g_wf p_g_tx y p_y_tx
            _             -> p_y_self_tx 
          p_yg_wf      = WFEBind g p_g_wf y t_x k_x p_g_tx
          p_yg_tx      = lem_weaken_wf g Empty (p_g_wf ? lem_empty_concatE g Empty) t_x k_x p_g_tx y t_x
          p_yg_t'_t'   = lem_sub_refl (Cons y t_x g) (unbindT x y t') k' p_yg_t' p_yg_wf
          p_yg_t'_ext' = SWitn (Cons y t_x g) (FV y) t_x p_y_tx (unbindT x y t') 
                               x t' p_yg_t'_t'
-}
lem_sub_refl g t k (WFPoly _g a k_a t' k_t' a' p_a'g_t') p_g_wf
    = SPoly g a k_a t' a t' a' p_a'g_t'_t'
        where
          p_a'g_wf    = WFEBindT g p_g_wf a' k_a
          p_a'g_t'_t' = lem_sub_refl (ConsT a' k_a g) (unbind_tvT a a' t') k_t' p_a'g_t' p_a'g_wf
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
