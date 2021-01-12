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
import LemmasChangeVarWF
import LemmasWeakenWF
import LemmasWellFormedness
import LemmasTyping
import LemmasSubtyping
import LemmasChangeVarTyp
import LemmasWeakenTyp
import SubstitutionLemmaWF
import DenotationsSelfify
import DenotationsSoundnessSub
import PrimitivesSemantics
import PrimitivesDenotations
import DenotationsSoundnessTyp
import LemmasExactness
import SubstitutionLemmaEnt
import SubstitutionLemmaTyp

{-@ reflect foo55 @-}
foo55 x = Just x
foo55 :: a -> Maybe a

{- This one moved to Lemmas Well Formedness -- delete the below
{-@ lem_narrow_wfenv :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
        -> t_x:Type -> ProofOf(Subtype g s_x t_x)
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') )
        -> ProofOf(WFEnv (concatE (Cons x s_x g) g') ) / [envSize g'] @-}
lem_narrow_wfenv :: Env -> Env -> Vname -> Type -> Type -> Subtype -> WFEnv -> WFEnv
lem_narrow_wfenv g Empty           x s_x t_x p_sx_tx p_xg_wf  = case p_xg_wf of
  (WFEBind  _g p_g_wf _x _tx k_x p_env'_tx) -> WFEBind g p_g_wf x s_x k_x p_env''_sx
      where
        p_env''_sx   = undefined     
lem_narrow_wfenv g (Cons z t_z g') x s_x t_x p_sx_tx p_env_wf = case p_env_wf of
  (WFEBind env' p_env'_wf _z _tz k_z p_env'_tz) 
    -> undefined {-WFEBind env'' p_env''_wf z (tsubFV x v_x t_z) k_z p_env''_tzvx
      where
        env''        = concatE g (esubFV x v_x g')
        p_env''_wf   = lem_subst_wfenv g g' x v_x t_x p_vx_tx p_env'_wf
        p_env''_tzvx = lem_subst_wf g g' x v_x t_x p_vx_tx p_env'_wf t_z k_z p_env'_tz-}
lem_narrow_wfenv g (ConsT a k_a g') x s_x t_x p_sx_tx p_env_wf = case p_env_wf of
  (WFEBindT env' p_env'_wf _a _ka)           -> undefined {-WFEBindT env'' p_env''_wf a k_a
    where
      env''      = concatE (Cons x s_x g) g'
      p_env''_wf = lem_subst_wfenv g g' x v_x t_x p_vx_tx p_env'_wf-}
-}

-- -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) 
{-@ lem_narrow_ent :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
            -> t_x:Type -> ProofOf(Subtype g s_x t_x) 
            -> { p:Pred | Set_sub (Set_cup (fv p) (ftv p)) (binds (concatE (Cons x t_x g) g')) }
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
            den_env_th' = undefined {- (InsertInCS _ _ _ _ _ _ th den_env_th eq_func _) 
                = lem_add_var_csubst g g' x v_x t_x p_vx_tx p_env_wf th' den_env'_th' -}
        env'         = concatE (Cons x s_x g) g'

{-@ lem_widen_denotes :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
            -> t_x:Type -> ProofOf(Subtype g s_x t_x) -> th:CSub
            -> ProofOf(DenotesEnv (concatE (Cons x t_x g) g') th) 
            -> ProofOf(DenotesEnv (concatE (Cons x s_x g) g') th) @-}
lem_widen_denotes :: Env -> Env -> Vname -> Type -> Type -> Subtype 
                         -> CSub -> DenotesEnv -> DenotesEnv
lem_widen_denotes g Empty           x s_x t_x p_sx_tx th den_env_th = undefined
lem_widen_denotes g (Cons z t_z g') x s_x t_x p_sx_tx th den_env_th = undefined
lem_widen_denotes g (ConsT a k g')  x s_x t_x p_sx_tx th den_env_th = undefined
