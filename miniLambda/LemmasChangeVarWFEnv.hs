{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasChangeVarWFEnv where

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

{-@ reflect foo36 @-}
foo36 x = Just x
foo36 :: a -> Maybe a

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
  (WFEBind _g p_g_wf _x _tx p_g_tx)         -> WFEBind g p_g_wf y t_x p_g_tx
lem_change_var_wfenv g x t_x (Cons z t_z g') p_env_wf y = case p_env_wf of
  (WFEBind env' p_env'_wf _z _tz  p_env'_tz) 
    -> WFEBind env'' p_env''_wf z (tsubFV x (FV y) t_z) p_env''_tz
      where
        env''      = concatE (Cons y t_x g) (esubFV x (FV y) g')
        p_env''_wf = lem_change_var_wfenv g x t_x g' p_env'_wf y
        p_env''_tz = lem_change_var_wf    g x t_x g' t_z p_env'_tz y
