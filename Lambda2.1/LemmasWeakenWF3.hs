{-# LANGUAGE GADTs #-}

{-@ LIQUID "--no-totality" @-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasWeakenWF where

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
--import LemmasWeakenWF.LemmasWeakenWFRefn

{-@ reflect foo32 @-}
foo32 x = Just x
foo32 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------
{-@ lem_weaken_wfexis :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> ProofOf(WFEnv (concatE g g')) -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && isWFExis p_t_wf }
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> t_x:Type 
            -> WeakenWFHypothesis (wftypSize p_t_wf)
            -> { pf:WFType | propOf pf == (WFType (concatE (Cons x t_x g) g') t k) } / [wftypSize p_t_wf] @-}
lem_weaken_wfexis :: Env -> Env -> WFEnv -> Type -> Kind -> WFType 
                         -> Vname -> Type -> WeakenWFHypothesis -> WFType 
lem_weaken_wfexis g g' p_env_wf t k p_t_wf@(WFExis env y t_y k_y p_ty_wf t' k' y' p_y'_t'_wf) x t_x ind_hyp
    = WFExis (concatE (Cons x t_x g) g') y 
             t_y k_y (ind_hyp{-lem_weaken_wf-} g g' p_env_wf t_y k_y p_ty_wf x t_x) 
             t' k' (y'' `withProof` lem_free_bound_in_env (concatE g g') t k p_t_wf y'')
             (ind_hyp{-lem_weaken_wf-} g (Cons y'' t_y g') p_y''env_wf (unbindT y y'' t') k'
                         (p_y''_t'_wf `withProof` lem_tsubFV_unbindT y y' (FV y'')  t')
                         x t_x) -- p_ tx)
        where
          y''_        = fresh_var(concatE (Cons x t_x g) g')
          y''         = y''_  `withProof` lem_in_env_concat g g' y''_
                              `withProof` lem_in_env_concat (Cons x t_x g) g' y''_
          p_y'env_wf  = WFEBind env p_env_wf y'  t_y k_y p_ty_wf
          p_y''env_wf = WFEBind env p_env_wf y'' t_y k_y p_ty_wf
          p_y''_t'_wf = lem_change_var_wf (concatE g g') y' t_y Empty p_y'env_wf
                             (unbindT y y' t') k' p_y'_t'_wf y''

{-@ type WeakenWFHypothesis N = g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> ProofOf(WFEnv (concatE g g')) -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && wftypSize p_t_wf < N }
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> t_x:Type 
            -> { pf:WFType | propOf pf == (WFType (concatE (Cons x t_x g) g') t k) } @-}
type WeakenWFHypothesis = Env -> Env -> WFEnv -> Type -> Kind -> WFType -> Vname -> Type -> WFType 

{-@ lem_weaken_wf_ind :: { n:Int | n >= 0 } -> g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> ProofOf(WFEnv (concatE g g')) -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && wftypSize p_t_wf < n }
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> t_x:Type 
            -> { pf:WFType | propOf pf == (WFType (concatE (Cons x t_x g) g') t k) } / [n] @-}
lem_weaken_wf_ind :: Int -> Env -> Env -> WFEnv -> Type -> Kind -> WFType -> Vname -> Type -> WFType
lem_weaken_wf_ind n g g' p_env_wf t k p_t_wf@(WFExis {}) x t_x
  = lem_weaken_wfexis g g' p_env_wf t k p_t_wf x t_x (lem_weaken_wf_ind (n-1))

{-@ lem_weaken_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> ProofOf(WFEnv (concatE g g')) -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k }
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> t_x:Type 
            -> { pf:WFType | propOf pf == (WFType (concatE (Cons x t_x g) g') t k) } @-}
lem_weaken_wf :: Env -> Env -> WFEnv -> Type -> Kind -> WFType -> Vname -> Type -> WFType 
lem_weaken_wf g g' p_env_wf t k p_t_wf x t_x 
  = lem_weaken_wf_ind ((wftypSize p_t_wf)+1) g g' p_env_wf t k p_t_wf x t_x 
