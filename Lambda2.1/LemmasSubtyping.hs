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
import SubstitutionWFAgain

{-@ reflect foo49 @-}
foo49 x = Just x
foo49 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------

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

{-@ lem_sub_refl :: g:Env -> t:Type -> k:Kind -> { p_g_t:WFType | propOf p_g_t == WFType g t k } 
                          -> ProofOf(WFEnv g) -> ProofOf(Subtype g t t) / [tsize t, 0] @-}
lem_sub_refl :: Env -> Type -> Kind -> WFType -> WFEnv -> Subtype
lem_sub_refl g t k p_g_t@(WFBase _g b tt) p_g_wf -- k == Base
    = lem_subtype_itself g p_er_g_wf b Z tt p_g_t
        where
          p_er_g_wf = lem_erase_env_wfenv g p_g_wf
lem_sub_refl g t k p_g_t@(WFRefn _g x b tt p_g_b p y pf_p_bl) p_g_wf -- t = b{x:p} && k == Base
    = lem_subtype_itself g p_er_g_wf b x p p_g_t
        where
          p_er_g_wf = lem_erase_env_wfenv g p_g_wf
lem_sub_refl g t k (WFVar1 g' a tt k_a) p_g_wf
    = lem_subtype_itself_trivial g p_er_g_wf (FTV a) Z tt
        where
          p_er_g_wf = lem_erase_env_wfenv g p_g_wf
lem_sub_refl g t k (WFVar2 g' a tt k_a p_g'_a y t_y) p_g_wf
    = lem_subtype_itself_trivial g p_er_g_wf (FTV a) Z tt
        where
          p_er_g_wf = lem_erase_env_wfenv g p_g_wf
lem_sub_refl g t k (WFVar3 g' a tt k_a p_g'_a y t_y) p_g_wf
    = lem_subtype_itself_trivial g p_er_g_wf (FTV a) Z tt
        where
          p_er_g_wf = lem_erase_env_wfenv g p_g_wf
lem_sub_refl g t k (WFFunc _g x t_x k_x p_g_tx t' k' y p_yg_t') p_g_wf -- t = (x:t_x -> t')
    = SFunc g x t_x x t_x p_tx_tx t' t' y p_t'_t'
        where
          p_yg_wf = WFEBind g p_g_wf y t_x k_x p_g_tx
          p_tx_tx = lem_sub_refl g t_x k_x p_g_tx p_g_wf
          p_t'_t' = lem_sub_refl (Cons y t_x g) (unbindT x y t') k' p_yg_t' p_yg_wf
lem_sub_refl g t k p_g_t@(WFExis _g x t_x k_x p_g_tx t' k' y p_yg_t') p_g_wf -- t = (\exists x:t_x. t')
    = SBind g x t_x t' (TExists x t_x t' ? lem_tfreeBV_empty g t k p_g_t)
            (y ? lem_free_bound_in_env g t k p_g_t y) p_yg_t'_ext'
        where
          p_g_tx_star  = if k_x == Star then p_g_tx else WFKind g t_x p_g_tx
          {-@ p_y_tx :: ProofOf(HasType (Cons y t_x g) (FV y) t_x) @-}
          p_y_tx       = TVar1 g y t_x Star p_g_tx_star ? toProof ( self t_x (FV y) Star == t_x )
          p_yg_wf      = WFEBind g p_g_wf y t_x k_x p_g_tx
          p_er_g_wf    = lem_erase_env_wfenv g p_g_wf
          p_yg_tx      = lem_weaken_wf g Empty p_er_g_wf t_x k_x p_g_tx y t_x
          p_yg_t'_t'   = lem_sub_refl (Cons y t_x g) (unbindT x y t') k' p_yg_t' p_yg_wf
          p_yg_t'_ext' = SWitn (Cons y t_x g) (FV y) t_x p_y_tx (unbindT x y t') 
                               x t' p_yg_t'_t'
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

{-@ lem_sub_sbase_pullback_wftype :: g:Env -> ProofOf(WFEnv g) -> s:Type -> t:Type 
        -> { p_s_t:Subtype | propOf p_s_t == Subtype g s t && isSBase p_s_t }
        -> k_s:Kind -> ProofOf(WFType g s k_s) -> k:Kind -> ProofOf(WFType g t k) 
                    -> ProofOf(WFType g s k) @-}
lem_sub_sbase_pullback_wftype :: Env -> WFEnv -> Type -> Type -> Subtype 
                                     -> Kind -> WFType -> Kind -> WFType -> WFType
lem_sub_sbase_pullback_wftype g p_g_wf s t p_s_t@(SBase _ x1 b p1 x2 p2 y ent_yg_p2) 
                              k_s p_g_s k p_g_t
  = case p_g_t of
        (WFBase _ _ tt)                  -> WFRefn g x1 b tt p_g_t  p1 y' p_y'_p1_bl 
        (WFRefn _ _ _ tt p_g_tt _p2 _ _) -> WFRefn g x1 b tt p_g_tt p1 y' p_y'_p1_bl
        (WFVar1 _ a tt _)                -> case (k_s, k) of
          (_,    Base) -> WFRefn g x1 b tt p_g_t p1 y' p_y'_p1_bl
          (Base, Star) -> WFKind g s p_g_s
          (Star, Star) -> p_g_s 
        (WFVar2 _ a tt _ _ _ _)          -> case (k_s, k) of  
          (_,    Base) -> WFRefn g x1 b tt p_g_t p1 y' p_y'_p1_bl
          (Base, Star) -> WFKind g s p_g_s
          (Star, Star) -> p_g_s 
        (WFVar3 _ a tt _ _ _ _)          -> case (k_s, k) of  
          (_,    Base) -> WFRefn g x1 b tt p_g_t p1 y' p_y'_p1_bl
          (Base, Star) -> WFKind g s p_g_s
          (Star, Star) -> p_g_s 
        (WFKind _ _ _) -> if k_s == Star then p_g_s else WFKind g s p_g_s
      where
        y'_        = fresh_var g
        y'         = y'_ ? lem_free_bound_in_env g s k_s p_g_s y'_
        p_er_g_wf  = lem_erase_env_wfenv    g p_g_wf
        p_y'_p1_bl = lem_ftyp_for_wf_trefn' g b x1 p1 k_s p_g_s p_er_g_wf
