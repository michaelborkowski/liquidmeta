{-# LANGUAGE GADTs #-}

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasChangeVarWF where

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
import Entailments

{-@ reflect foo34 @-}
foo34 x = Just x
foo34 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas  
------------------------------------------------------------------------------

{-@ lem_change_var_wf :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) } 
      -> ProofOf(WFEnv (concatE (Cons x t_x g) g')) -> t:Type
      -> k:Kind -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (Cons x t_x g) g') t k }
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
             (tsubFV x (FV y) t) k) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf ] @-}
lem_change_var_wf :: Env -> Vname -> Type -> Env -> WFEnv 
                         -> Type -> Kind -> WFType -> Vname -> WFType
lem_change_var_wf g x t_x g' p_env_wf t k p_t_wf@(WFBase gg b) y
    = WFBase (concatE (Cons y t_x g) (esubFV x (FV y) g')) b
lem_change_var_wf g x t_x g' p_env_wf t k p_t_wf@(WFRefn gg z b pf_gg_b p z' p_z'_p_b) y_ 
    = WFRefn (concatE (Cons y t_x g) (esubFV x (FV y) g')) z b pf_env'_b (subFV x (FV y) p) z''
             (lem_change_var_ftyp (erase_env g) x (erase t_x) 
                  (FCons z'' (FTBasic b) (erase_env g')) 
                  (lem_erase_env_wfenv (Cons z'' (TRefn b 1 (Bc True)) gg) pf_z''env_wf)
                  (unbind z z'' p) (FTBasic TBool) 
                  (p_z''_p_b {-`withProof` lem_subFV_unbind z z' (FV z'')
                       (p `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') 
                                                            t k p_t_wf z')-})  
                  y ? lem_commute_subFV_unbind x y z z'' p )
        where
            y             = y_ ? lem_erase_concat (Cons y_ t_x g) (esubFV x (FV y_) g')
                               ? lem_erase_esubFV x (FV y_) g'
            z''_          = fresh_var_excluding (concatE (Cons x t_x g) g') y
            z''           = z''_ ? lem_erase_concat (Cons x t_x g) g'
                                 ? lem_erase_concat g g'
                                 ? lem_free_bound_in_env (concatE (Cons x t_x g) g') t k p_t_wf z''_
            pf_z'env_wf   = WFEBind gg p_env_wf z'  (TRefn b 1 (Bc True)) Base pf_gg_b
            pf_z''env_wf  = WFEBind gg p_env_wf z'' (TRefn b 1 (Bc True)) Base pf_gg_b
            p_z''_p_b     = lem_change_var_ftyp (erase_env (concatE (Cons x t_x g) g')) 
                                z' (FTBasic b) FEmpty 
                                (lem_erase_env_wfenv (Cons z' (TRefn b 1 (Bc True)) gg) pf_z'env_wf)
                                (unbind z z' p) (FTBasic TBool) p_z'_p_b z''
                                ? lem_subFV_unbind z z' (FV z'') 
                                      (p ? lem_free_bound_in_env (concatE (Cons x t_x g) g') t k p_t_wf z')
            pf_env'_b     = lem_change_var_wf g x t_x g' p_env_wf (TRefn b 1 (Bc True)) Base pf_gg_b y
lem_change_var_wf g x t_x g' p_env_wf t k p_t_wf@(WFVar1 {}) y = undefined
lem_change_var_wf g x t_x g' p_env_wf t k p_t_wf@(WFVar2 {}) y = undefined
lem_change_var_wf g x t_x g' p_env_wf t k p_t_wf@(WFVar3 {}) y = undefined
lem_change_var_wf g x t_x g' p_env_wf t k p_t_wf@(WFFunc gg z t_z k_z p_tz_wf t' k' z' p_z'_t'_wf) y
    = undefined {-
    = WFFunc (concatE (Cons y t_x g) (esubFV x (FV y) g')) z (tsubFV x (FV y) t_z) k_z
             (lem_change_var_wf g x t_x g' t_z p_tz_wf y) (tsubFV x (FV y) t') k'
             (z'' `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') t p_t_wf z'')
             (lem_change_var_wf g x t_x (Cons z'' t_z g') (unbindT z z'' t') k'
                 (p_z''_t'_wf `withProof` lem_tsubFV_unbindT z z' (FV z'')
                      (t' `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') 
                                                        t p_t_wf z'))
                 y `withProof` lem_commute_tsubFV_unbindT x y z z'' t')
--             `withProof` lem_esubFV_tsubFV x (FV y) z'' t_z g'
        where
            z''         = fresh_var_excluding (concatE (Cons x t_x g) g') y
            p_z''_t'_wf = lem_change_var_wf (concatE (Cons x t_x g) g') z' t_z Empty 
                                    (unbindT z z' t') k' p_z'_t'_wf --z''
                                    (z'' `withProof` lem_in_env_concat g g' z''
                                         `withProof` lem_in_env_concat (Cons x t_x g) g' z'')
-}
lem_change_var_wf g x t_x g' p_env_wf t k p_t_wf@(WFExis gg z t_z k_z p_tz_wf t' k' z' p_z'_t'_wf) y
    = undefined {-
    = WFExis (concatE (Cons y t_x g) (esubFV x (FV y) g')) z (tsubFV x (FV y) t_z) k_z
             (lem_change_var_wf g x t_x g' t_z p_tz_wf y) (tsubFV x (FV y) t') k'
             (z'' `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') t p_t_wf z'')
             ((lem_change_var_wf g x t_x (Cons z'' t_z g') (unbindT z z'' t') 
                  (p_z''_t'_wf `withProof` lem_tsubFV_unbindT z z' (FV z'') 
                      (t' `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') 
                                                        t p_t_wf z'))
                  y `withProof` lem_commute_tsubFV_unbindT x y z z'' t') -- this the key
             )--     `withProof` lem_esubFV_tsubFV x (FV y) z'' t_z g')
        where
            z''_        = fresh_var_excluding (concatE (Cons x t_x g) g') y
            z''         = z''_ ? lem_in_env_concat g g' z''_
                               ? lem_in_env_concat (Cons x t_x g) g' z''_
            p_z''_t'_wf = lem_change_var_wf (concatE (Cons x t_x g) g') z' t_z Empty 
                                    (unbindT z z' t') k' p_z'_t'_wf z''
{-                                    (z'' `withProof` lem_in_env_concat g g' z''
                                         `withProof` lem_in_env_concat (Cons x t_x g) g' z'')-}
-}
lem_change_var_wf g x t_x g' p_env_wf t k p_t_wf@(WFPoly gg a1 k1 t1 k_t1 a1' p_a1'_t1) y
    = undefined
lem_change_var_wf g x t_x g' p_env_wf t k p_t_wf@(WFKind gg _t pf_gg_t_b) y
    = undefined

{-@ lem_change_tvar_wf :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
      -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) } 
      -> ProofOf(WFEnv (concatE (ConsT a k_a g) g')) -> t:Type
      -> k:Kind -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (ConsT a k_a g) g') t k }
      -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
               (tchgFTV a a' t) k) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf ] @-}
lem_change_tvar_wf :: Env -> Vname -> Kind -> Env -> WFEnv 
                          -> Type -> Kind -> WFType -> Vname -> WFType
lem_change_tvar_wf g a k_a g' p_env_wf t k p_t_wf{- @(WFRefn gg z b pf_gg_b p z' p_z'_p_b)-} a' 
  = undefined {- 9 -}
