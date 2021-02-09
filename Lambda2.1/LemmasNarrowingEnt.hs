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
import SubstitutionLemmaWF
import DenotationsSelfify
import PrimitivesSemantics
import PrimitivesDenotations
import DenotationsSoundness
import SubstitutionLemmaEnt

{-@ reflect foo69 @-}
foo69 x = Just x
foo69 :: a -> Maybe a

{-@ lem_narrow_ent :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
            -> t_x:Type -> ProofOf(Subtype g s_x t_x)  -> k_x:Kind -> ProofOf(WFType g s_x k_x)
            -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) 
            -> { p:Pred | Set_sub (Set_cup (fv p) (ftv p)) (binds (concatE (Cons x t_x g) g')) }
            -> ProofOf(Entails (concatE (Cons x t_x g) g') p) 
            -> ProofOf(Entails (concatE (Cons x s_x g) g') p) @-}
lem_narrow_ent :: Env -> Env -> Vname -> Type -> Type -> Subtype -> Kind -> WFType -> WFEnv
                      -> Expr -> Entails -> Entails
lem_narrow_ent g g' x s_x t_x p_sx_tx k_sx p_g_sx p_env_wf p (EntPred env _p evals_func)
  = EntPred env' p evals_func'
      where
        {-@ evals_func' :: th':CSub -> ProofOf(DenotesEnv env' th')
                                    -> ProofOf(EvalsTo (csubst th' p) (Bc True)) @-}
        evals_func' :: CSub -> DenotesEnv -> EvalsTo  
        evals_func' th' den_env'_th' = evals_func th' den_env_th' 
          where
            den_env_th' = lem_widen_denotes g g' x s_x t_x p_sx_tx k_tx p_g_tx p_env'_wf
                                            th' den_env'_th'
        env'         = concatE (Cons x s_x g) g'
        p_env'_wf    = lem_narrow_wfenv   g g' x s_x t_x p_sx_tx k_sx p_g_sx p_env_wf
        p_xg_wf      = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _g _ _x _tx k_tx p_g_tx) = p_xg_wf

{-@ lem_widen_denotes :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
            -> t_x:Type -> ProofOf(Subtype g s_x t_x) -> k_x:Kind -> ProofOf(WFType g t_x k_x)
            -> ProofOf(WFEnv (concatE (Cons x s_x g) g')) -> th:CSub
            -> ProofOf(DenotesEnv (concatE (Cons x s_x g) g') th) 
            -> ProofOf(DenotesEnv (concatE (Cons x t_x g) g') th) @-}
lem_widen_denotes :: Env -> Env -> Vname -> Type -> Type -> Subtype -> Kind -> WFType -> WFEnv
                         -> CSub -> DenotesEnv -> DenotesEnv
lem_widen_denotes g Empty           x s_x t_x p_sx_tx k_tx p_g_tx p_env_wf th den_env_th 
  = case den_env_th of
      (DExt _g th0 den_g_th0 _x _sx v_x den_th0sx_vx)
        -> DExt g th0 den_g_th0 x t_x v_x den_th0tx_vx
             where
               (WFEBind _g p_g_wf _ _ k_sx p_g_sx) = p_env_wf
               den_th0tx_vx = lem_denote_sound_sub g s_x k_sx t_x k_tx p_sx_tx p_g_wf 
                                                   p_g_sx p_g_tx th0 den_g_th0 v_x den_th0sx_vx
lem_widen_denotes g (Cons z_ t_z g') x s_x t_x p_sx_tx k_tx p_g_tx p_env_wf th den_env_th 
  = case den_env_th of
      (DExt env0 th0 den_env0_th0 _z _tz v_z den_th0tz_vz)
        -> DExt env0' th0 den_env0'_th0 z t_z v_z den_th0tz_vz
             where
               z             = z_ ? lem_in_env_concat (Cons x s_x g) g' z_
                                  ? lem_in_env_concat (Cons x t_x g) g' z_
               env0'         = concatE (Cons x t_x g) g'
               (WFEBind _env0 p_env0_wf _ _ _ _) = p_env_wf
               den_env0'_th0 = lem_widen_denotes g g' x s_x t_x p_sx_tx k_tx p_g_tx p_env0_wf
                                                 th0 den_env0_th0
lem_widen_denotes g (ConsT a_ k g')  x s_x t_x p_sx_tx k_tx p_g_tx p_env_wf th den_env_th 
  = case den_env_th of
      (DExtT env0 th0 den_env0_th0 _a _k t_a p_emp_ta)
        -> DExtT env0' th0 den_env0'_th0 a k t_a p_emp_ta
             where
               a             = a_ ? lem_in_env_concat (Cons x s_x g) g' a_
                                  ? lem_in_env_concat (Cons x t_x g) g' a_
               env0'         = concatE (Cons x t_x g) g'
               (WFEBindT _env0 p_env0_wf _ _) = p_env_wf
               den_env0'_th0 = lem_widen_denotes g g' x s_x t_x p_sx_tx k_tx p_g_tx p_env0_wf
                                                 th0 den_env0_th0
