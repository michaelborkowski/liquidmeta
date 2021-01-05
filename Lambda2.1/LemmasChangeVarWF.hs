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
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasSubstitution
import Typing
import SystemFAlphaEquivalence
import BasicPropsCSubst
import BasicPropsDenotes
--import Entailments

{-@ reflect foo34 @-}
foo34 x = Just x
foo34 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas  
------------------------------------------------------------------------------

{-@ lem_change_var_wf_wfrefn :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) } 
      -> ProofOf(WFFE (concatF (FCons x (erase t_x) (erase_env g)) (erase_env g'))) -> t:Type -> k:Kind 
      -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (Cons x t_x g) g') t k && isWFRefn p_t_wf }
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
             (tsubFV x (FV y) t) k) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf, 0] @-}
lem_change_var_wf_wfrefn :: Env -> Vname -> Type -> Env -> WFFE 
                         -> Type -> Kind -> WFType -> Vname -> WFType
lem_change_var_wf_wfrefn g x t_x g' p_env_wf t k p_t_wf@(WFRefn gg z b tt pf_gg_b p z'_ p_z'_p_b) y_ 
 = undefined {- CHECKED
    = WFRefn (concatE (Cons y t_x g) (esubFV x (FV y) g')) z b tt pf_env'_b (subFV x (FV y) p) z''
             (lem_change_var_ftyp (erase_env g) x (erase t_x) 
                  (FCons z'' (FTBasic b) (erase_env g')) pf_z''env_wf
                  (unbind 0 z'' p) (FTBasic TBool) 
                  (p_z''_p_b {-`withProof` lem_subFV_unbind z z' (FV z'')
                       (p `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') 
                                                            t k p_t_wf z')-})  
                  y ? lem_commute_subFV_unbind x y 0 z'' p )
        where
            y             = y_ ? lem_erase_concat (Cons y_ t_x g) (esubFV x (FV y_) g')
                               ? lem_erase_esubFV x (FV y_) g'
            z'            = z'_  ? lem_erase_concat (Cons x t_x g) g'
            z''_          = fresh_var_excluding (concatE (Cons x t_x g) g') y
            z''           = z''_ ? lem_erase_concat (Cons x t_x g) g'
                                 ? lem_erase_concat g g'
                                 ? lem_free_bound_in_env (concatE (Cons x t_x g) g') t k p_t_wf z''_
            p_gg_er_b     = lem_erase_wftype gg (TRefn b Z tt) Base pf_gg_b
            pf_z'env_wf   = WFFBind (erase_env gg) p_env_wf z'  (FTBasic b) Base p_gg_er_b
            pf_z''env_wf  = WFFBind (erase_env gg) p_env_wf z'' (FTBasic b) Base p_gg_er_b
            p_z''_p_b     = lem_change_var_ftyp (erase_env (concatE (Cons x t_x g) g')) 
                                z' (FTBasic b) FEmpty pf_z'env_wf
                                (unbind 0 z' p) (FTBasic TBool) p_z'_p_b z''
                                ? lem_subFV_unbind 0 z' (FV z'') 
                                      (p ? lem_free_bound_in_env (concatE (Cons x t_x g) g') t k p_t_wf z')
            pf_env'_b     = lem_change_var_wf g x t_x g' p_env_wf (TRefn b Z tt) Base pf_gg_b y
                                              ? lem_subFV_notin x (FV y) (tt ? lem_trivial_nofv tt)
-}

{-@ lem_change_var_wf_wfvar1 :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) } 
      -> ProofOf(WFFE (concatF (FCons x (erase t_x) (erase_env g)) (erase_env g'))) -> t:Type -> k:Kind
      -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (Cons x t_x g) g') t k && isWFVar1 p_t_wf}
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
             (tsubFV x (FV y) t) k) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf, 0] @-}
lem_change_var_wf_wfvar1 :: Env -> Vname -> Type -> Env -> WFFE 
                         -> Type -> Kind -> WFType -> Vname -> WFType
lem_change_var_wf_wfvar1 g x t_x g' p_env_wf t k p_t_wf@(WFVar1 env a' tt k') y = undefined {- CHECKED = case g' of
  (ConsT _a' _k' g'') -> WFVar1 (concatE (Cons y t_x g) (esubFV x (FV y) g'')) a' tt k'
                                ? lem_subFV_notin x (FV y) (tt ? lem_trivial_nofv tt)
-}

{-@ lem_change_var_wf_wfvar2 :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) } 
      -> ProofOf(WFFE (concatF (FCons x (erase t_x) (erase_env g)) (erase_env g'))) -> t:Type -> k:Kind
      -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (Cons x t_x g) g') t k && isWFVar2 p_t_wf}
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
             (tsubFV x (FV y) t) k) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf, 0] @-}
lem_change_var_wf_wfvar2 :: Env -> Vname -> Type -> Env -> WFFE 
                         -> Type -> Kind -> WFType -> Vname -> WFType
lem_change_var_wf_wfvar2 g x t_x g' p_env_wf t k p_t_wf@(WFVar2 {}) y = undefined

{-@ lem_change_var_wf_wfvar3 :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) } 
      -> ProofOf(WFFE (concatF (FCons x (erase t_x) (erase_env g)) (erase_env g'))) -> t:Type -> k:Kind
      -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (Cons x t_x g) g') t k && isWFVar3 p_t_wf}
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
             (tsubFV x (FV y) t) k) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf, 0] @-}
lem_change_var_wf_wfvar3 :: Env -> Vname -> Type -> Env -> WFFE 
                         -> Type -> Kind -> WFType -> Vname -> WFType
lem_change_var_wf_wfvar3 g x t_x g' p_env_wf t k p_t_wf@(WFVar3 {}) y = undefined

{-@ lem_change_var_wf_wffunc :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) } 
      -> ProofOf(WFFE (concatF (FCons x (erase t_x) (erase_env g)) (erase_env g'))) -> t:Type -> k:Kind
      -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (Cons x t_x g) g') t k && isWFFunc p_t_wf}
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
             (tsubFV x (FV y) t) k) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf, 0] @-}
lem_change_var_wf_wffunc :: Env -> Vname -> Type -> Env -> WFFE 
                         -> Type -> Kind -> WFType -> Vname -> WFType
lem_change_var_wf_wffunc g x t_x g' p_env_wf t k 
                         p_t_wf@(WFFunc gg z t_z k_z p_tz_wf t' k' z'_ p_z'_t'_wf) y_ 
 = undefined {- CHECKED
    = WFFunc (concatE (Cons y t_x g) (esubFV x (FV y) g')) z (tsubFV x (FV y) t_z) k_z
             p_env'_tz (tsubFV x (FV y) t') k' z'' p_z''y_t'_wf
        where
            y            = y_ ? lem_erase_concat (Cons y_ t_x g) (esubFV x (FV y_) g')
                              ? lem_erase_esubFV x (FV y_) g'
            z'           = z'_  ? lem_erase_concat (Cons x t_x g) g'
            z''_         = fresh_var_excluding (concatE (Cons x t_x g) g') y
            z''          = z''_ ? lem_in_env_concat g g' z''_
                                ? lem_in_env_concat (Cons x t_x g) g' z''_
                                ? lem_free_bound_in_env (concatE (Cons x t_x g) g') t k p_t_wf z''_
            p_env'_tz    = lem_change_var_wf g x t_x g' p_env_wf t_z k_z p_tz_wf y
            p_er_tz_wf   = lem_erase_wftype gg t_z k_z p_tz_wf
            p_z'env_wf   = WFFBind (erase_env gg) p_env_wf z'  (erase t_z) k_z p_er_tz_wf 
            p_z''env_wf  = WFFBind (erase_env gg) p_env_wf z'' (erase t_z) k_z p_er_tz_wf 
            p_z''_t'_wf  = lem_change_var_wf (concatE (Cons x t_x g) g') z' t_z Empty p_z'env_wf
                                (unbindT z z' t') k' p_z'_t'_wf z''
                                ? lem_tsubFV_unbindT z z' (FV z'') (t'
                                      ? lem_free_bound_in_env (concatE (Cons x t_x g) g')
                                                              t k p_t_wf z')
            p_z''y_t'_wf = lem_change_var_wf g x t_x (Cons z'' t_z g') p_z''env_wf 
                                (unbindT z z'' t') k' p_z''_t'_wf y  
                                ? lem_commute_tsubFV_unbindT x y z z'' t'
-}

{-@ lem_change_var_wf_wfexis :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) } 
      -> ProofOf(WFFE (concatF (FCons x (erase t_x) (erase_env g)) (erase_env g'))) -> t:Type -> k:Kind
      -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (Cons x t_x g) g') t k && isWFExis p_t_wf}
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
             (tsubFV x (FV y) t) k) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf, 0] @-}
lem_change_var_wf_wfexis :: Env -> Vname -> Type -> Env -> WFFE 
                         -> Type -> Kind -> WFType -> Vname -> WFType
lem_change_var_wf_wfexis g x t_x g' p_env_wf t k 
                         p_t_wf@(WFExis gg z t_z k_z p_tz_wf t' k' z'_ p_z'_t'_wf) y_ 
    = WFExis (concatE (Cons y t_x g) (esubFV x (FV y) g')) z (tsubFV x (FV y) t_z) k_z
             p_env'_tz (tsubFV x (FV y) t') k' z'' p_z''y_t'_wf
        where
            y            = y_ ? lem_erase_concat (Cons y_ t_x g) (esubFV x (FV y_) g')
                              ? lem_erase_esubFV x (FV y_) g'
            z'           = z'_  ? lem_erase_concat (Cons x t_x g) g'
            z''_         = fresh_var_excluding (concatE (Cons x t_x g) g') y
            z''          = z''_ ? lem_in_env_concat g g' z''_
                                ? lem_in_env_concat (Cons x t_x g) g' z''_
                                ? lem_free_bound_in_env (concatE (Cons x t_x g) g') t k p_t_wf z''_
            p_env'_tz    = lem_change_var_wf g x t_x g' p_env_wf t_z k_z p_tz_wf y
            p_er_tz_wf   = lem_erase_wftype gg t_z k_z p_tz_wf
            p_z'env_wf   = WFFBind (erase_env gg) p_env_wf z'  (erase t_z) k_z p_er_tz_wf 
            p_z''env_wf  = WFFBind (erase_env gg) p_env_wf z'' (erase t_z) k_z p_er_tz_wf 
            p_z''_t'_wf  = lem_change_var_wf (concatE (Cons x t_x g) g') z' t_z Empty p_z'env_wf
                                (unbindT z z' t') k' p_z'_t'_wf z''
                                ? lem_tsubFV_unbindT z z' (FV z'') (t'
                                      ? lem_free_bound_in_env (concatE (Cons x t_x g) g')
                                                              t k p_t_wf z')
            p_z''y_t'_wf = lem_change_var_wf g x t_x (Cons z'' t_z g') p_z''env_wf 
                                (unbindT z z'' t') k' p_z''_t'_wf y  
                                ? lem_commute_tsubFV_unbindT x y z z'' t'

{-@ lem_change_var_wf_wfpoly :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) } 
      -> ProofOf(WFFE (concatF (FCons x (erase t_x) (erase_env g)) (erase_env g'))) -> t:Type -> k:Kind
      -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (Cons x t_x g) g') t k && isWFPoly p_t_wf}
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
             (tsubFV x (FV y) t) k) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf, 0] @-}
lem_change_var_wf_wfpoly :: Env -> Vname -> Type -> Env -> WFFE 
                         -> Type -> Kind -> WFType -> Vname -> WFType
lem_change_var_wf_wfpoly g x t_x g' p_env_wf t k p_t_wf@(WFPoly gg a1 k1 t1 k_t1 a1' p_a1'_t1) y
    = undefined

{-@ lem_change_var_wf :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) } 
      -> ProofOf(WFFE (concatF (FCons x (erase t_x) (erase_env g)) (erase_env g'))) -> t:Type -> k:Kind
      -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (Cons x t_x g) g') t k }
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
             (tsubFV x (FV y) t) k) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf, 1] @-}
lem_change_var_wf :: Env -> Vname -> Type -> Env -> WFFE 
                         -> Type -> Kind -> WFType -> Vname -> WFType
lem_change_var_wf g x t_x g' p_env_wf t k p_t_wf@(WFBase gg b tt) y
    = WFBase (concatE (Cons y t_x g) (esubFV x (FV y) g')) b tt 
             ? lem_subFV_notin x (FV y) (tt ? lem_trivial_nofv tt)
lem_change_var_wf g x t_x g' p_env_wf t k p_t_wf@(WFRefn gg z b tt pf_gg_b p z' p_z'_p_b) y
    = lem_change_var_wf_wfrefn g x t_x g' p_env_wf t k p_t_wf y 
lem_change_var_wf g x t_x g' p_env_wf t k p_t_wf@(WFVar1 {}) y 
    = lem_change_var_wf_wfvar1 g x t_x g' p_env_wf t k p_t_wf y
lem_change_var_wf g x t_x g' p_env_wf t k p_t_wf@(WFVar2 {}) y 
    = lem_change_var_wf_wfvar2 g x t_x g' p_env_wf t k p_t_wf y
lem_change_var_wf g x t_x g' p_env_wf t k p_t_wf@(WFVar3 {}) y 
    = lem_change_var_wf_wfvar3 g x t_x g' p_env_wf t k p_t_wf y
lem_change_var_wf g x t_x g' p_env_wf t k p_t_wf@(WFFunc gg z t_z k_z p_tz_wf t' k' z' p_z'_t'_wf) y
    = lem_change_var_wf_wffunc g x t_x g' p_env_wf t k p_t_wf y
lem_change_var_wf g x t_x g' p_env_wf t k p_t_wf@(WFExis gg z t_z k_z p_tz_wf t' k' z' p_z'_t'_wf) y
    = lem_change_var_wf_wfexis g x t_x g' p_env_wf t k p_t_wf y
lem_change_var_wf g x t_x g' p_env_wf t k p_t_wf@(WFPoly gg a1 k1 t1 k_t1 a1' p_a1'_t1) y
    = lem_change_var_wf_wfpoly g x t_x g' p_env_wf t k p_t_wf y
lem_change_var_wf g x t_x g' p_env_wf t k p_t_wf@(WFKind gg _t pf_gg_t_b) y
    = WFKind (concatE (Cons y t_x g) (esubFV x (FV y) g')) (tsubFV x (FV y) t) pf_env'_t_b
        where
          pf_env'_t_b = lem_change_var_wf g x t_x g' p_env_wf t Base pf_gg_t_b y

{-@ lem_change_var_wf' :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) } 
      -> ProofOf(WFEnv (concatE (Cons x t_x g) g')) -> t:Type
      -> k:Kind -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (Cons x t_x g) g') t k }
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
             (tsubFV x (FV y) t) k) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf, 2] @-}
lem_change_var_wf' :: Env -> Vname -> Type -> Env -> WFEnv 
                         -> Type -> Kind -> WFType -> Vname -> WFType
lem_change_var_wf' g x t_x g' p_env_wf t k p_t_wf y
  = lem_change_var_wf g x t_x g' p_er_env_wf t k p_t_wf y
      where
        p_er_env_wf = lem_erase_env_wfenv (concatE (Cons x t_x g) g') p_env_wf
                                          ? lem_erase_concat (Cons x t_x g) g'

-- ---> move to another file -->
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
