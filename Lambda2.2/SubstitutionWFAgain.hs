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
import BasicPropsCSubst
import BasicPropsDenotes
import LemmasChangeVarWF
import LemmasWeakenWF
import LemmasWeakenWFTV
import LemmasWellFormedness
import SubstitutionLemmaWF
import SubstitutionLemmaWFTV
import LemmasTyping

{-@ reflect foo44 @-}
foo44 x = Just x
foo44 :: a -> Maybe a

-- this legacy version takes a regular typing judgment
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
        p_vx_er_tx = lem_typing_hasftype g v_x t_x p_vx_tx p_g_wf 

-- the legacy version of TV substitution in WFType that takes WFEnv as a parameter
{-@ lem_subst_tv_wf' :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
          -> k_a:Kind -> ProofOf(WFType g t_a k_a) -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) 
          -> t:Type -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (ConsT a k_a g) g') t k }
          -> ProofOf(WFType (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k) / [wftypSize p_env_t, 1] @-}
lem_subst_tv_wf' :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv 
                    -> Type -> Kind -> WFType -> WFType
lem_subst_tv_wf' g g' a t_a k_a p_g_ta p_env_wf t k p_e_t
  = lem_subst_tv_wf g g' a t_a k_a p_g_ta p_er_env_wf t k p_e_t 
      where
        p_er_env_wf = lem_erase_env_wfenv (concatE (ConsT a k_a g) g') p_env_wf
                                          ? lem_erase_concat (ConsT a k_a g) g'
