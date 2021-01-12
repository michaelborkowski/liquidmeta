{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SubstitutionWFAgain where

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
import SystemFLemmasSubstitution
import Typing
import SystemFAlphaEquivalence
import BasicPropsCSubst
import BasicPropsDenotes
import Entailments
import LemmasChangeVarWF
import LemmasWeakenWF
import LemmasWeakenWFTV
import LemmasWellFormedness
import SubstitutionLemmaWF
import SubstitutionLemmaWFTV
import LemmasTyping
import LemmasSubtyping

{-@ reflect foo45 @-}
foo45 x = Just x
foo45 :: a -> Maybe a


{-@ lem_subst_wf_eqvft :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
          -> t_x:Type -> ProofOf(EqvFTyping (erase_env g) v_x (erase t_x))
          -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> t:Type -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (Cons x t_x g) g') t k }
          -> ProofOf(WFType (concatE g (esubFV x v_x g')) (tsubFV x v_x t) k) / [wftypSize p_env_t, 1] @-}
lem_subst_wf_eqvft :: Env -> Env -> Vname -> Expr -> Type -> EqvFTyping -> WFEnv 
                    -> Type -> Kind -> WFType -> WFType
lem_subst_wf_eqvft g g' x v_x t_x eqv_vx_tx p_env_wf t k p_env_t = case eqv_vx_tx of
  (AEWitness _ _ _ s_x ae_sx_tx p_vx_sx) -> lem_subst_wf g g' x v_x s_x p_vx_sx p_env'_wf t k p_env'_t
    where
      (s_x', p_sx'_tx) = lem_alpha_subtype g s_x t_x ae_sx_tx 
      p_env'_wf        = lem_narrow_wfenv g g' x s_x' t_x p_sx'_tx ?? ?? p_env_wf
      p_env'_t         = lem_subtype_in_env_wf g g' s_x' t_x p_sx'_tx y p_env_t

-- this version takes a regular typing judgment
{-@ lem_subst_wf' :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
          -> t_x:Type -> ProofOf(HasType g v_x t_x) 
          -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> t:Type -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (Cons x t_x g) g') t k }
          -> ProofOf(WFType (concatE g (esubFV x v_x g')) (tsubFV x v_x t) k) @-} 
lem_subst_wf' :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv 
                     -> Type -> Kind -> WFType -> WFType
lem_subst_wf' g g' x v_x t_x p_vx_tx p_env_wf t k p_env_t
  = lem_subst_wf g g' x v_x t_x p_vx_er_tx p_env_wf t k p_env_t 
      where
        p_xg_wf     = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _ _) = p_xg_wf
        p_vx_er_tx = lem_typing_hasftype g v_x t_x p_vx_tx p_g_wf -- update this

-- the legacy version of TV substitution in WFType that takes WFEnv as a parameter
{-@ lem_subst_tv_wf' :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:Type
          -> k_a:Kind -> ProofOf(WFType g t_a k_a) -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) 
          -> { t:Type | same_binders t_a t || isTrivial t } -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (ConsT a k_a g) g') t k }
          -> ProofOf(WFType (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k) / [wftypSize p_env_t, 1] @-}
lem_subst_tv_wf' :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv 
                    -> Type -> Kind -> WFType -> WFType
lem_subst_tv_wf' g g' a t_a k_a p_g_ta p_env_wf t k p_e_t
  = lem_subst_tv_wf g g' a t_a k_a p_g_ta p_er_env_wf t k p_e_t 
      where
        p_er_env_wf = lem_erase_env_wfenv (concatE (ConsT a k_a g) g') p_env_wf
                                          ? lem_erase_concat (ConsT a k_a g) g'

-----------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
-----------------------------------------------------------

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
