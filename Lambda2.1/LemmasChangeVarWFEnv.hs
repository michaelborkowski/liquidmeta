{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasChangeVarWFEnv where

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
import BasicPropsCSubst
import BasicPropsDenotes
import LemmasChangeVarWF

{-@ reflect foo35 @-}
foo35 x = Just x
foo35 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas  
------------------------------------------------------------------------------

{-@ lem_change_var_wfenv :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> ProofOf(WFEnv (concatE (Cons y t_x g) (esubFV x (FV y) g'))) @-}
lem_change_var_wfenv :: Env -> Vname -> Type -> Env -> WFEnv -> Vname -> WFEnv
lem_change_var_wfenv g x t_x Empty           p_env_wf y = case p_env_wf of
  (WFEBind _g p_g_wf _x _tx k_x p_g_tx)         -> WFEBind g p_g_wf y t_x k_x p_g_tx
lem_change_var_wfenv g x t_x (Cons z t_z g') p_env_wf y = case p_env_wf of
  (WFEBind env' p_env'_wf _z _tz k_z p_env'_tz) 
    -> WFEBind env'' p_env''_wf z (tsubFV x (FV y) t_z) k_z p_env''_tz
      where
        env''      = concatE (Cons y t_x g) (esubFV x (FV y) g')
        p_env''_wf = lem_change_var_wfenv g x t_x g' p_env'_wf y
        p_env''_tz = lem_change_var_wf'   g x t_x g' p_env'_wf t_z k_z p_env'_tz y
lem_change_var_wfenv g x t_x (ConsT a k_a g') p_env_wf y = case p_env_wf of
  (WFEBindT env' p_env'_wf _a _ka) -> WFEBindT  env'' p_env''_wf a k_a
    where
        env''      = concatE (Cons y t_x g) (esubFV x (FV y) g')
        p_env''_wf = lem_change_var_wfenv g x t_x g' p_env'_wf y

{-@ lem_change_tvar_wfenv :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
      -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (ConsT a k_a g) g'))
      -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
      -> ProofOf(WFEnv (concatE (ConsT a' k_a g) (echgFTV a a' g'))) @-}
lem_change_tvar_wfenv :: Env -> Vname -> Kind -> Env -> WFEnv -> Vname -> WFEnv
lem_change_tvar_wfenv g a k_a Empty           p_env_wf a' = case p_env_wf of
  (WFEBindT _g p_g_wf _a _ka)           -> WFEBindT g p_g_wf a' k_a
lem_change_tvar_wfenv g a k_a (Cons z t_z g') p_env_wf a' = case p_env_wf of
  (WFEBind env' p_env'_wf _z _tz k_z p_env'_tz)
    -> WFEBind env'' p_env''_wf z (tchgFTV a a' t_z) k_z p_env''_tz
      where     
        env''      = concatE (ConsT a' k_a g) (echgFTV a a' g')
        p_env''_wf = lem_change_tvar_wfenv g a k_a g' p_env'_wf a'
        p_env''_tz = lem_change_tvar_wf'   g a k_a g' p_env'_wf t_z k_z p_env'_tz a'
lem_change_tvar_wfenv g a k_a (ConsT a1 k1 g') p_env_wf a' = case p_env_wf of
  (WFEBindT env' p_env'_wf _a1 _k1) -> WFEBindT  env'' p_env''_wf a1 k1
    where
        env''      = concatE (ConsT a' k_a g) (echgFTV a a' g')
        p_env''_wf = lem_change_tvar_wfenv g a k_a g' p_env'_wf a'
