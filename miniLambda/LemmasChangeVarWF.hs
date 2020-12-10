{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasChangeVarWF where

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

{-@ reflect foo34 @-}
foo34 x = Just x
foo34 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas  
------------------------------------------------------------------------------

{-@ lem_change_var_wf_wfrefn :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) } -> t:Type
      -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (Cons x t_x g) g') t && isWFRefn p_t_wf }
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
             (tsubFV x (FV y) t)) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf,0] @-}
lem_change_var_wf_wfrefn :: Env -> Vname -> Type -> Env 
                         -> Type -> WFType -> Vname -> WFType
lem_change_var_wf_wfrefn g x t_x g' t p_t_wf@(WFRefn gg z b p z' p_z'_p_b) y_ 
    = WFRefn (concatE (Cons y t_x g) (esubFV x (FV y) g')) z b (subFV x (FV y) p) z''
             (lem_change_var_ftyp (erase_env g) x (erase t_x) 
                  (FCons z'' (FTBasic b) (erase_env g')) 
                  (unbind z z'' p) (FTBasic TBool) 
                  p_z''_p_b 
                  y ? lem_commute_subFV_unbind x y z z'' p )
        where
            y             = y_ ? lem_erase_concat (Cons y_ t_x g) (esubFV x (FV y_) g')
                               ? lem_erase_esubFV x (FV y_) g'
            z''_          = fresh_var_excluding (concatE (Cons x t_x g) g') y
            z''           = z''_ ? lem_erase_concat (Cons x t_x g) g'
                                 ? lem_erase_concat g g'
                                 ? lem_free_bound_in_env (concatE (Cons x t_x g) g') t p_t_wf z''_
            p_z''_p_b     = lem_change_var_ftyp (erase_env (concatE (Cons x t_x g) g')) 
                                z' (FTBasic b) FEmpty 
                                (unbind z z' p) (FTBasic TBool) p_z'_p_b z''
                                ? lem_subFV_unbind z z' (FV z'') 
                                      (p ? lem_free_bound_in_env (concatE (Cons x t_x g) g') t p_t_wf z')

{-@ lem_change_var_wf_wffunc :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) } -> t:Type 
      -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (Cons x t_x g) g') t && isWFFunc p_t_wf}
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
             (tsubFV x (FV y) t)) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf,0] @-}
lem_change_var_wf_wffunc :: Env -> Vname -> Type -> Env -> Type -> WFType -> Vname -> WFType
lem_change_var_wf_wffunc g x t_x g' t p_t_wf@(WFFunc gg z t_z p_tz_wf t' z' p_z'_t'_wf) y
    = WFFunc (concatE (Cons y t_x g) (esubFV x (FV y) g')) z (tsubFV x (FV y) t_z) 
             (lem_change_var_wf g x t_x g' t_z p_tz_wf y) (tsubFV x (FV y) t') 
             (z'' `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') t p_t_wf z'')
             (lem_change_var_wf g x t_x (Cons z'' t_z g') (unbindT z z'' t') 
                 (p_z''_t'_wf `withProof` lem_tsubFV_unbindT z z' (FV z'')
                      (t' `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') 
                                                        t p_t_wf z'))
                 y `withProof` lem_commute_tsubFV_unbindT x y z z'' t')
        where
            z''         = fresh_var_excluding (concatE (Cons x t_x g) g') y
            p_z''_t'_wf = lem_change_var_wf (concatE (Cons x t_x g) g') z' t_z Empty 
                                    (unbindT z z' t') p_z'_t'_wf z''
--                                    (z'' `withProof` lem_in_env_concat g g' z''
--                                         `withProof` lem_in_env_concat (Cons x t_x g) g' z'')

{-@ lem_change_var_wf_wfexis :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) } -> t:Type 
      -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (Cons x t_x g) g') t && isWFExis p_t_wf}
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
             (tsubFV x (FV y) t)) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf, 0] @-}
lem_change_var_wf_wfexis :: Env -> Vname -> Type -> Env -> Type  -> WFType -> Vname -> WFType
lem_change_var_wf_wfexis g x t_x g' t p_t_wf@(WFExis gg z t_z p_tz_wf t' z' p_z'_t'_wf) y
    = WFExis (concatE (Cons y t_x g) (esubFV x (FV y) g')) z (tsubFV x (FV y) t_z)
             (lem_change_var_wf g x t_x g' t_z p_tz_wf y) (tsubFV x (FV y) t') 
             (z'' `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') t p_t_wf z'')
             (lem_change_var_wf g x t_x (Cons z'' t_z g') (unbindT z z'' t') 
                  (p_z''_t'_wf `withProof` lem_tsubFV_unbindT z z' (FV z'') 
                      (t' `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') 
                                                        t p_t_wf z'))
                  y `withProof` lem_commute_tsubFV_unbindT x y z z'' t') -- this the key
        where
            z''_        = fresh_var_excluding (concatE (Cons x t_x g) g') y
            z''         = z''_ ? lem_in_env_concat g g' z''_
                               ? lem_in_env_concat (Cons x t_x g) g' z''_
            p_z''_t'_wf = lem_change_var_wf (concatE (Cons x t_x g) g') z' t_z Empty 
                                    (unbindT z z' t') p_z'_t'_wf z''

{-@ lem_change_var_wf :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) } -> t:Type 
      -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (Cons x t_x g) g') t }
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
             (tsubFV x (FV y) t)) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf, 1] @-}
lem_change_var_wf :: Env -> Vname -> Type -> Env -> Type -> WFType -> Vname -> WFType
lem_change_var_wf g x t_x g' t p_t_wf@(WFRefn gg z b p z' p_z'_p_b) y
    = lem_change_var_wf_wfrefn g x t_x g' t p_t_wf y 
lem_change_var_wf g x t_x g' t p_t_wf@(WFFunc gg z t_z p_tz_wf t' z' p_z'_t'_wf) y
    = lem_change_var_wf_wffunc g x t_x g' t p_t_wf y
lem_change_var_wf g x t_x g' t p_t_wf@(WFExis gg z t_z p_tz_wf t' z' p_z'_t'_wf) y
    = lem_change_var_wf_wfexis g x t_x g' t p_t_wf y
