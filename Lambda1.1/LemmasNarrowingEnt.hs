{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasNarrowingEnt where

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
import LemmasSubtyping
import LemmasChangeVarTyp
import LemmasWeakenTyp
import SubstitutionLemmaWF
import DenotationsSelfify
import DenotationsSoundness
import PrimitivesSemantics
import PrimitivesDenotations
import LemmasExactness
import SubstitutionLemmaEnt
import SubstitutionLemmaTyp

{-@ reflect foo55 @-}
foo55 x = Just x
foo55 :: a -> Maybe a

{-@ lem_narrow_wfenv :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
        -> t_x:Type -> ProofOf(Subtype g s_x t_x) -> ProofOf(WFType g s_x)
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') )
        -> ProofOf(WFEnv (concatE (Cons x s_x g) g') ) / [envsize g'] @-}
lem_narrow_wfenv :: Env -> Env -> Vname -> Type -> Type -> Subtype -> WFType -> WFEnv -> WFEnv
lem_narrow_wfenv g Empty           x s_x t_x p_sx_tx p_g_sx p_xg_wf  = case p_xg_wf of
  (WFEBind  _g p_g_wf _x _tx p_env'_tx) -> WFEBind g p_g_wf x s_x p_g_sx
lem_narrow_wfenv g (Cons z t_z g') x s_x t_x p_sx_tx p_g_sx p_env_wf = case p_env_wf of
  (WFEBind env' p_env'_wf _z _tz p_env'_tz) -> WFEBind env'' p_env''_wf z t_z p_env''_tz
      where
        env''        = concatE (Cons x s_x g) g'
        p_env''_wf   = lem_narrow_wfenv      g g' x s_x t_x p_sx_tx p_g_sx p_env'_wf
        p_env''_tz   = lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t_z p_env'_tz

-- -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) 
{-@ lem_narrow_ent :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
            -> t_x:Type -> ProofOf(Subtype g s_x t_x) 
            -> { p:Pred | Set_sub (fv p) (binds (concatE (Cons x t_x g) g')) }
            -> ProofOf(Entails (concatE (Cons x t_x g) g') p) 
            -> ProofOf(Entails (concatE (Cons x s_x g) g') p) @-}
lem_narrow_ent :: Env -> Env -> Vname -> Type -> Type -> Subtype -> Pred -> Entails -> Entails
lem_narrow_ent g g' x s_x t_x p_sx_tx {-p_env_wf-} p (EntPred env _p evals_func)
  = EntPred env' p evals_func'
      where
        {-@ evals_func' :: th':CSub -> ProofOf(DenotesEnv env' th')
                                -> ProofOf(EvalsTo (csubst th' p) (Bc True)) @-}
        evals_func' :: CSub -> DenotesEnv -> EvalsTo  
        evals_func' th' den_env'_th' = evals_func th' den_env_th' 
          where
            den_env_th' = undefined {-
            (InsertInCS _ _ _ _ _ _ th den_env_th eq_func _) 
                = lem_add_var_csubst g g' x v_x t_x p_vx_tx p_env_wf th' den_env'_th' -}
        env'         = concatE (Cons x s_x g) g'
{-
{-@ lem_widen_denotes :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
            -> t_x:Type -> ProofOf(Subtype g s_x t_x) -> th:CSub
            -> ProofOf(DenotesEnv (concatE (Cons x t_x g) g') th) 
            -> ProofOf(DenotesEnv (concatE (Cons x s_x g) g') th) @-}
lem_widen_denotes :: Env -> Env -> Vname -> Type -> Type -> Subtype 
                         -> CSub -> DenotesEnv -> DenotesEnv
lem_widen_denotes g Empty           x s_x t_x p_sx_tx th den_env_th = undefined
lem_widen_denotes g (Cons z t_z g') x s_x t_x p_sx_tx th den_env_th = undefined
-}
