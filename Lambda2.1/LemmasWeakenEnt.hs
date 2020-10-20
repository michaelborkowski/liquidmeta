{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasWeakenEnt where

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
import Entailments

{-@ reflect foo33 @-}
foo33 x = Just x
foo33 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------

{-@ lem_weaken_ent :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> { p:Pred | Set_sub (fv p) (binds (concatE g g')) }
        -> { ent_g_p:Entails | propOf ent_g_p == Entails (concatE g g') p } 
        -> { x:Vname | not (in_env x g) && not (in_env x g') && not (Set_mem x (fv p)) } -> t_x:Type
        -> ProofOf(Entails (concatE (Cons x t_x g) g') p) @-}
lem_weaken_ent :: Env -> Env -> WFEnv -> Pred -> Entails -> Vname -> Type -> Entails
lem_weaken_ent g g' p_env_wf p (EntPred env_ _p evals_func) x t_x 
    = EntPred (concatE (Cons x t_x g) g') p evals_func'
        where
          env' = (concatE (Cons x t_x g) g')
          evals_func' ::  CSub -> DenotesEnv -> EvalsTo
          evals_func' th' den_env'_th' = evals_func th den_env_th
                ? lem_remove_csubst th' x ( p ? lem_binds_env_th (concatE g g') th den_env_th)
            where
              th         = remove_fromCS th' x 
              den_env_th = lem_remove_var_denote_env g x t_x g' p_env_wf th' den_env'_th'
                               ? lem_binds_env_th env' th' den_env'_th' 

{-@ lem_weaken_tv_ent :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> { p:Pred | Set_sub (fv p) (binds (concatE g g')) }
        -> { ent_g_p:Entails | propOf ent_g_p == Entails (concatE g g') p } 
        -> { a:Vname | not (in_env a g) && not (in_env a g') && not (Set_mem a (fv p)) } -> k_a:Kind
        -> ProofOf(Entails (concatE (ConsT a k_a g) g') p) @-}
lem_weaken_tv_ent :: Env -> Env -> WFEnv -> Pred -> Entails -> Vname -> Kind -> Entails
lem_weaken_tv_ent g g' p_env_wf p (EntPred env_ _p evals_func) a k_a
    = EntPred env' p evals_func'
        where
          env' = (concatE (ConsT a k_a g) g')
          evals_func' ::  CSub -> DenotesEnv -> EvalsTo
          evals_func' th' den_env'_th' = evals_func th den_env_th
                ? lem_remove_csubst th' a ( p ? lem_binds_env_th (concatE g g') th den_env_th)
            where
              th         = remove_fromCS th' a
              den_env_th = lem_remove_tvar_denote_env g a k_a g' p_env_wf th' den_env'_th'
                               ? lem_binds_env_th env' th' den_env'_th' 

