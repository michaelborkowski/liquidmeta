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
import BasicPropsEnvironments
import Typing
import BasicPropsCSubst
import BasicPropsDenotes

{-@ reflect foo36 @-}
foo36 x = Just x
foo36 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------

{-@ lem_weaken_ent :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> ps:Preds 
        -> { ent_g_p:Entails | propOf ent_g_p == Entails (concatE g g') ps } 
        -> { x:Vname | not (in_env x g) && not (in_env x g') 
                    && not (Set_mem x (fvP ps)) && not (Set_mem x (ftvP ps)) } -> t_x:Type
        -> ProofOf(Entails (concatE (Cons x t_x g) g') ps) @-}
lem_weaken_ent :: Env -> Env -> WFEnv -> Preds -> Entails -> Vname -> Type -> Entails
lem_weaken_ent g g' p_env_wf ps (EntPred env_ _p evals_func) x t_x 
    = EntPred (concatE (Cons x t_x g) g') ps evals_func'
        where
          env' = (concatE (Cons x t_x g) g')
          evals_func' th' den_env'_th' = evals_func th den_env_th ? lem_remove_cpsubst th' x ps 
            where
              th         = remove_fromCS th' x 
              den_env_th = lem_remove_var_denotes_env g x t_x g' p_env_wf th' den_env'_th'
                               ? lem_binds_env_th env' th' den_env'_th' 

{-@ lem_weaken_tv_ent :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> ps:Preds 
        -> { ent_g_p:Entails | propOf ent_g_p == Entails (concatE g g') ps } 
        -> { a:Vname | not (in_env a g) && not (in_env a g') 
                    && not (Set_mem a (fvP ps)) && not (Set_mem a (ftvP ps)) } -> k_a:Kind
        -> ProofOf(Entails (concatE (ConsT a k_a g) g') ps) @-}
lem_weaken_tv_ent :: Env -> Env -> WFEnv -> Preds -> Entails -> Vname -> Kind -> Entails
lem_weaken_tv_ent g g' p_env_wf ps (EntPred env_ _p evals_func) a k_a
    = EntPred env' ps evals_func'
        where
          env' = (concatE (ConsT a k_a g) g')
          evals_func' th' den_env'_th' = evals_func th den_env_th ? lem_remove_cpsubst th' a ps 
            where
              th         = remove_fromCS th' a
              den_env_th = lem_remove_tvar_denotes_env g a k_a g' p_env_wf th' den_env'_th'
                               ? lem_binds_env_th env' th' den_env'_th' 
