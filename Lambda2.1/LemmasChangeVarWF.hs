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
import BasicPropsCSubst
import BasicPropsDenotes

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

{-@ lem_change_var_wf_wfvar1 :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) } 
      -> ProofOf(WFFE (concatF (FCons x (erase t_x) (erase_env g)) (erase_env g'))) -> t:Type -> k:Kind
      -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (Cons x t_x g) g') t k && isWFVar1 p_t_wf}
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
             (tsubFV x (FV y) t) k) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf, 0] @-}
lem_change_var_wf_wfvar1 :: Env -> Vname -> Type -> Env -> WFFE 
                         -> Type -> Kind -> WFType -> Vname -> WFType
lem_change_var_wf_wfvar1 g x t_x g' p_env_wf t k p_t_wf@(WFVar1 env a' tt k') y = case g' of
  (ConsT _a' _k' g'') -> WFVar1 (concatE (Cons y t_x g) (esubFV x (FV y) g'')) a' tt k'
                                ? lem_subFV_notin x (FV y) (tt ? lem_trivial_nofv tt)

{-@ lem_change_var_wf_wfvar2 :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) } 
      -> ProofOf(WFFE (concatF (FCons x (erase t_x) (erase_env g)) (erase_env g'))) -> t:Type -> k:Kind
      -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (Cons x t_x g) g') t k && isWFVar2 p_t_wf}
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
             (tsubFV x (FV y) t) k) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf, 0] @-}
lem_change_var_wf_wfvar2 :: Env -> Vname -> Type -> Env -> WFFE 
                         -> Type -> Kind -> WFType -> Vname -> WFType
lem_change_var_wf_wfvar2 g x t_x g' p_zenv_wf t k p_t_wf@(WFVar2 env a' tt k' p_env_a' z t_z) y 
  = case g' of 
      Empty             -> case ( x == a' ) of
          True             -> impossible "x <> a'"
          False            -> WFVar2 env a' tt k' p_env_a' (y
                                ? lem_free_bound_in_env env (TRefn (FTV a') Z tt) k' p_env_a' y) 
                                (t_z ? lem_ffreeTV_bound_in_fenv (erase_env env) (erase t_z) 
                                                                 k_z p_env_tz x)
                                ? lem_subFV_notin x (FV y) (tt ? lem_trivial_nofv tt)
        where
          (WFFBind _ p_env_wf _ _ k_z p_env_tz) = p_zenv_wf
      (Cons _z _tz g'') -> case ( x == a' ) of 
          True  -> impossible ("by lemma" ? lem_wfvar_tv_in_env (concatE (Cons x t_x g) g'')
                                                                a' tt k' p_env_a')
          False -> WFVar2 (concatE (Cons y t_x g) (esubFV x (FV y) g'')) 
                                  (a' ? lem_in_env_esub g'' x (FV y) a'
                                      ? lem_in_env_concat g g'' a'
                                      ? lem_in_env_concat (Cons x t_x g) g'' a') tt k'
                                  p_env'_a' z (tsubFV x (FV y) t_z)
        where
          (WFFBind _ p_env_wf _ _ k_z _) = p_zenv_wf
          p_env'_a' = lem_change_var_wf g x t_x g'' p_env_wf (TRefn (FTV a') Z tt) k' p_env_a' y
                                  ? lem_subFV_notin x (FV y) (tt ? lem_trivial_nofv tt)

{-@ lem_change_var_wf_wfvar3 :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) } 
      -> ProofOf(WFFE (concatF (FCons x (erase t_x) (erase_env g)) (erase_env g'))) -> t:Type -> k:Kind
      -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (Cons x t_x g) g') t k && isWFVar3 p_t_wf}
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
             (tsubFV x (FV y) t) k) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf, 0] @-}
lem_change_var_wf_wfvar3 :: Env -> Vname -> Type -> Env -> WFFE 
                         -> Type -> Kind -> WFType -> Vname -> WFType
lem_change_var_wf_wfvar3 g x t_x g' p_a1env_wf t k p_t_wf@(WFVar3 env a'_ tt k' p_env_a' a1 k1) y 
  = case g' of
      Empty               -> impossible "x <> a1"
      (ConsT _a1 _k1 g'') -> case ( x == a' ) of 
          True  -> impossible ("by lemma" ? lem_wfvar_tv_in_env (concatE (Cons x t_x g) g'') 
                                                                a'_ tt k' p_env_a')
          False -> WFVar3 (concatE (Cons y t_x g) (esubFV x (FV y) g'')) a' tt k'
                          p_env'_a' a1 k1
        where
          a'      = a'_ ? lem_in_env_esub g'' x (FV y) a'_
                        ? lem_in_env_concat g g'' a'_
                        ? lem_in_env_concat (Cons x t_x g) g'' a'_
                        ? lem_in_env_concat (Cons y t_x g) (esubFV x (FV y) g'') a'_ 
          (WFFBindT _ p_env_wf _ _) = p_a1env_wf
          p_env'_a' = lem_change_var_wf g x t_x g'' p_env_wf (TRefn (FTV a') Z tt) k' p_env_a' y
                                  ? lem_subFV_notin x (FV y) (tt ? lem_trivial_nofv tt)

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
lem_change_var_wf_wfpoly g x t_x g' p_env_wf t k p_t_wf@(WFPoly gg a1 k1 t1 k_t1 a1'_ p_a1'_t1) y_
    = WFPoly (concatE (Cons y t_x g) (esubFV x (FV y) g')) a1 k1 (tsubFV x (FV y) t1) k_t1
             a1'' p_a1''env'_t1
        where
            y             = y_ ? lem_erase_concat (Cons y_ t_x g) (esubFV x (FV y_) g')
                               ? lem_erase_esubFV x (FV y_) g'
            a1'           = a1'_  ? lem_erase_concat (Cons x t_x g) g'
            a1''_         = fresh_var_excluding (concatE (Cons x t_x g) g') y
            a1''          = a1''_ ? lem_in_env_concat g g' a1''_
                                  ? lem_in_env_concat (Cons x t_x g) g' a1''_
                                  ? lem_free_bound_in_env (concatE (Cons x t_x g) g') t k p_t_wf a1''_
            p_a1'env_wf   = WFFBindT (erase_env gg) p_env_wf a1'  k1  
            p_a1''env_wf  = WFFBindT (erase_env gg) p_env_wf a1'' k1
            p_a1''env_t1  = lem_change_tvar_wf (concatE (Cons x t_x g) g') a1' k1 Empty p_a1'env_wf
                                 (unbind_tvT a1 a1' t1) k_t1 p_a1'_t1 a1''
                                 ? lem_tchgFTV_unbind_tvT a1 a1' a1'' (t1
                                       ? lem_free_bound_in_env (concatE (Cons x t_x g) g')
                                                              t k p_t_wf a1')
            p_a1''env'_t1 = lem_change_var_wf g x t_x (ConsT a1'' k1 g') p_a1''env_wf 
                                 (unbind_tvT a1 a1'' t1) k_t1 p_a1''env_t1 y  
                                 ? lem_commute_tsubFV_unbind_tvT x (FV y) a1 a1'' t1

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

{-@ lem_change_tvar_wf_wfrefn :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
      -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) } 
      -> ProofOf(WFFE (concatF (FConsT a k_a (erase_env g)) (erase_env g'))) -> t:Type -> k:Kind 
      -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (ConsT a k_a g) g') t k && isWFRefn p_t_wf }
      -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
               (tchgFTV a a' t) k) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf, 0] @-}
lem_change_tvar_wf_wfrefn :: Env -> Vname -> Kind -> Env -> WFFE 
                         -> Type -> Kind -> WFType -> Vname -> WFType
lem_change_tvar_wf_wfrefn g a k_a g' p_env_wf t k p_t_wf@(WFRefn gg z b tt pf_gg_b p z'_ p_z'_p_b) a'_
  = case b of 
        (FTV a1) | a1 == a -> WFRefn env' z (FTV a') tt pf_env'_b (chgFTV a a' p) z'' pf_z''y_p_b
        _                  -> WFRefn env' z b        tt pf_env'_b (chgFTV a a' p) z'' pf_z''y_p_b
      where
            a'            = a'_ ? lem_erase_concat (ConsT a'_ k_a g) (echgFTV a a'_ g')
                                ? lem_erase_echgFTV a a'_ g'
            z'            = z'_  ? lem_erase_concat (ConsT a k_a g) g'
            z''_          = fresh_var_excluding (concatE (ConsT a k_a g) g') a'
            z''           = z''_ ? lem_erase_concat (ConsT a k_a g) g'
                                 ? lem_erase_concat g g'
                                 ? lem_free_bound_in_env (concatE (ConsT a k_a g) g') t k p_t_wf z''_
            env'          = concatE (ConsT a' k_a g) (echgFTV a a' g')
            p_gg_er_b     = lem_erase_wftype gg (TRefn b Z tt) Base pf_gg_b
            pf_z'env_wf   = WFFBind (erase_env gg) p_env_wf z'  (FTBasic b) Base p_gg_er_b
            pf_z''env_wf  = WFFBind (erase_env gg) p_env_wf z'' (FTBasic b) Base p_gg_er_b
            pf_env'_b     = lem_change_tvar_wf g a k_a g' p_env_wf (TRefn b Z tt) Base pf_gg_b a'
                                              ? lem_chgFTV_notin a a' (tt ? lem_trivial_nofv tt)
            p_z''_p_b     = lem_change_var_ftyp (erase_env (concatE (ConsT a k_a g) g')) 
                                z' (FTBasic b) FEmpty pf_z'env_wf
                                (unbind 0 z' p) (FTBasic TBool) p_z'_p_b z''
                                ? lem_subFV_unbind 0 z' (FV z'') 
                                    (p ? lem_free_bound_in_env (concatE (ConsT a k_a g) g') t k p_t_wf z')
            pf_z''y_p_b   = lem_change_tvar_ftyp (erase_env g) a k_a 
                                (FCons z'' (FTBasic b) (erase_env g')) pf_z''env_wf
                                (unbind 0 z'' p) (FTBasic TBool) p_z''_p_b a'
                                ? lem_commute_chgFTV_subBV 0 (FV z'') a a' p
                                ? lem_chgFTV_notin a a' (FV z'')
         
{-@ lem_change_tvar_wf_wfvar1 :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
      -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) } 
      -> ProofOf(WFFE (concatF (FConsT a k_a (erase_env g)) (erase_env g'))) -> t:Type -> k:Kind 
      -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (ConsT a k_a g) g') t k && isWFVar1 p_t_wf}
      -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
               (tchgFTV a a' t) k) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf, 0] @-}
lem_change_tvar_wf_wfvar1 :: Env -> Vname -> Kind -> Env -> WFFE 
                         -> Type -> Kind -> WFType -> Vname -> WFType
lem_change_tvar_wf_wfvar1 g a k_a g' p_env_wf t k p_t_wf@(WFVar1 env a' tt k') aa = case g' of
  Empty               -> WFVar1 g aa tt k'
                                ? lem_chgFTV_notin a aa (tt ? lem_trivial_nofv tt)
  (ConsT _a' _k' g'') -> WFVar1 (concatE (ConsT aa k_a g) (echgFTV a aa g'')) a' tt k'
                                ? lem_chgFTV_notin a aa (tt ? lem_trivial_nofv tt)

{-@ lem_change_tvar_wf_wfvar2 :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
      -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) } 
      -> ProofOf(WFFE (concatF (FConsT a k_a (erase_env g)) (erase_env g'))) -> t:Type -> k:Kind 
      -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (ConsT a k_a g) g') t k && isWFVar2 p_t_wf}
      -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
               (tchgFTV a a' t) k) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf, 0] @-}
lem_change_tvar_wf_wfvar2 :: Env -> Vname -> Kind -> Env -> WFFE 
                         -> Type -> Kind -> WFType -> Vname -> WFType
lem_change_tvar_wf_wfvar2 g a k_a g' p_zenv_wf t k p_t_wf@(WFVar2 env a' tt k' p_env_a' z t_z) aa
  = case g' of 
      Empty             -> impossible "a <> z"
      (Cons _z _tz g'') -> case ( a == a' ) of
          True              -> WFVar2 (concatE (ConsT aa k_a g) (echgFTV a aa g''))
                                  (aa ? lem_in_env_concat g g'' aa
                                      ? lem_in_env_concat (ConsT a k_a g) g'' aa) tt k'
                                  p_env'_a' z (tchgFTV a aa t_z)
          False             -> WFVar2 (concatE (ConsT aa k_a g) (echgFTV a aa g'')) 
                                  (a' ? lem_in_env_echgFTV g'' a aa a'
                                      ? lem_in_env_concat g g'' a'
                                      ? lem_in_env_concat (ConsT a k_a g) g'' a') tt k'
                                  p_env'_a' z (tchgFTV a aa t_z)
--                                  ? lem_chgFTV_notin a aa (tt ? lem_trivial_nofv tt)
        where
          (WFFBind _ p_env_wf _ _ k_z _) = p_zenv_wf
          p_env'_a' = lem_change_tvar_wf g a k_a g'' p_env_wf (TRefn (FTV a') Z tt) k' p_env_a' aa
                                  ? lem_chgFTV_notin a aa (tt ? lem_trivial_nofv tt)

{-@ lem_change_tvar_wf_wfvar3 :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
      -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) } 
      -> ProofOf(WFFE (concatF (FConsT a k_a (erase_env g)) (erase_env g'))) -> t:Type -> k:Kind 
      -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (ConsT a k_a g) g') t k && isWFVar3 p_t_wf}
      -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
               (tchgFTV a a' t) k) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf, 0] @-}
lem_change_tvar_wf_wfvar3 :: Env -> Vname -> Kind -> Env -> WFFE 
                         -> Type -> Kind -> WFType -> Vname -> WFType
lem_change_tvar_wf_wfvar3 g a k_a g' p_a1env_wf t k p_t_wf@(WFVar3 env a'_ tt k' p_env_a' a1 k1) aa
  = case g' of
      Empty               -> case ( a == a'_ ) of
          True              -> impossible "a == a1, not a'"
          False             -> WFVar3 env a'_ tt k' p_env_a' (aa
                                   ? lem_free_bound_in_env env (TRefn (FTV a'_) Z tt) k' p_env_a' aa) k1
                                   ? lem_chgFTV_notin a aa (tt ? lem_trivial_nofv tt)
      (ConsT _a1 _k1 g'') -> case ( a == a'_ ) of 
          True  -> WFVar3 (concatE (ConsT aa k_a g) (echgFTV a aa g'')) aa tt k' p_env'_a' a1 k1
          False -> WFVar3 (concatE (ConsT aa k_a g) (echgFTV a aa g'')) a' tt k'
                          p_env'_a' a1 k1
        where
          a'      = a'_ ? lem_in_env_echgFTV g'' a aa a'_
                        ? lem_in_env_concat g g'' a'_
                        ? lem_in_env_concat (ConsT a  k_a g) g'' a'_
                        ? lem_in_env_concat (ConsT aa k_a g) (echgFTV a aa g'') a'_ 
          (WFFBindT _ p_env_wf _ _) = p_a1env_wf
          p_env'_a' = lem_change_tvar_wf g a k_a g'' p_env_wf (TRefn (FTV a') Z tt) k' p_env_a' aa
                                  ? lem_chgFTV_notin a aa (tt ? lem_trivial_nofv tt)

{-@ lem_change_tvar_wf_wffunc :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
      -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) } 
      -> ProofOf(WFFE (concatF (FConsT a k_a (erase_env g)) (erase_env g'))) -> t:Type -> k:Kind 
      -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (ConsT a k_a g) g') t k && isWFFunc p_t_wf}
      -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
               (tchgFTV a a' t) k) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf, 0] @-}
lem_change_tvar_wf_wffunc :: Env -> Vname -> Kind -> Env -> WFFE 
                         -> Type -> Kind -> WFType -> Vname -> WFType
lem_change_tvar_wf_wffunc g a k_a g' p_env_wf t k 
                         p_t_wf@(WFFunc gg z t_z k_z p_tz_wf t' k' z'_ p_z'_t'_wf) a'_ 
    = WFFunc (concatE (ConsT a' k_a g) (echgFTV a a' g')) z (tchgFTV a a' t_z) k_z
             p_env'_tz (tchgFTV a a' t') k' z'' p_z''y_t'_wf
        where
            a'           = a'_ ? lem_erase_concat (ConsT a'_ k_a g) (echgFTV a a'_ g')
                               ? lem_erase_echgFTV a a'_ g'
            z'           = z'_  ? lem_erase_concat (ConsT a k_a g) g'
            z''_         = fresh_var_excluding (concatE (ConsT a k_a g) g') a'
            z''          = z''_ ? lem_in_env_concat g g' z''_
                                ? lem_in_env_concat (ConsT a k_a g) g' z''_
                                ? lem_free_bound_in_env (concatE (ConsT a k_a g) g') t k p_t_wf z''_
            p_env'_tz    = lem_change_tvar_wf g a k_a g' p_env_wf t_z k_z p_tz_wf a'
            p_er_tz_wf   = lem_erase_wftype gg t_z k_z p_tz_wf
            p_z'env_wf   = WFFBind (erase_env gg) p_env_wf z'  (erase t_z) k_z p_er_tz_wf 
            p_z''env_wf  = WFFBind (erase_env gg) p_env_wf z'' (erase t_z) k_z p_er_tz_wf 
            p_z''_t'_wf  = lem_change_var_wf (concatE (ConsT a k_a g) g') z' t_z Empty p_z'env_wf
                                (unbindT z z' t') k' p_z'_t'_wf z''
                                ? lem_tsubFV_unbindT z z' (FV z'') (t'
                                      ? lem_free_bound_in_env (concatE (ConsT a k_a g) g')
                                                              t k p_t_wf z')
            p_z''y_t'_wf = lem_change_tvar_wf g a k_a (Cons z'' t_z g') p_z''env_wf 
                                (unbindT z z'' t') k' p_z''_t'_wf a'
                                ? lem_commute_tchgFTV_tsubBV z (FV z'') a a' t'
                                ? lem_chgFTV_notin a a' (FV z'')

{-@ lem_change_tvar_wf_wfexis :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
      -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) } 
      -> ProofOf(WFFE (concatF (FConsT a k_a (erase_env g)) (erase_env g'))) -> t:Type -> k:Kind 
      -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (ConsT a k_a g) g') t k && isWFExis p_t_wf}
      -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
               (tchgFTV a a' t) k) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf, 0] @-}
lem_change_tvar_wf_wfexis :: Env -> Vname -> Kind -> Env -> WFFE 
                         -> Type -> Kind -> WFType -> Vname -> WFType
lem_change_tvar_wf_wfexis g a k_a g' p_env_wf t k 
                         p_t_wf@(WFExis gg z t_z k_z p_tz_wf t' k' z'_ p_z'_t'_wf) a'_ 
    = WFExis (concatE (ConsT a' k_a g) (echgFTV a a' g')) z (tchgFTV a a' t_z) k_z
             p_env'_tz (tchgFTV a a' t') k' z'' p_z''y_t'_wf
        where
            a'           = a'_ ? lem_erase_concat (ConsT a'_ k_a g) (echgFTV a a'_ g')
                               ? lem_erase_echgFTV a a'_ g'
            z'           = z'_  ? lem_erase_concat (ConsT a k_a g) g'
            z''_         = fresh_var_excluding (concatE (ConsT a k_a g) g') a'
            z''          = z''_ ? lem_in_env_concat g g' z''_
                                ? lem_in_env_concat (ConsT a k_a g) g' z''_
                                ? lem_free_bound_in_env (concatE (ConsT a k_a g) g') t k p_t_wf z''_
            p_env'_tz    = lem_change_tvar_wf g a k_a g' p_env_wf t_z k_z p_tz_wf a'
            p_er_tz_wf   = lem_erase_wftype gg t_z k_z p_tz_wf
            p_z'env_wf   = WFFBind (erase_env gg) p_env_wf z'  (erase t_z) k_z p_er_tz_wf 
            p_z''env_wf  = WFFBind (erase_env gg) p_env_wf z'' (erase t_z) k_z p_er_tz_wf 
            p_z''_t'_wf  = lem_change_var_wf (concatE (ConsT a k_a g) g') z' t_z Empty p_z'env_wf
                                (unbindT z z' t') k' p_z'_t'_wf z''
                                ? lem_tsubFV_unbindT z z' (FV z'') (t'
                                      ? lem_free_bound_in_env (concatE (ConsT a k_a g) g')
                                                              t k p_t_wf z')
            p_z''y_t'_wf = lem_change_tvar_wf g a k_a (Cons z'' t_z g') p_z''env_wf 
                                (unbindT z z'' t') k' p_z''_t'_wf a'  
                                ? lem_commute_tchgFTV_tsubBV z (FV z'') a a' t'
                                ? lem_chgFTV_notin a a' (FV z'')

{-@ lem_change_tvar_wf_wfpoly :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
      -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) } 
      -> ProofOf(WFFE (concatF (FConsT a k_a (erase_env g)) (erase_env g'))) -> t:Type -> k:Kind 
      -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (ConsT a k_a g) g') t k && isWFPoly p_t_wf }
      -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
               (tchgFTV a a' t) k) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf, 0] @-}
lem_change_tvar_wf_wfpoly :: Env -> Vname -> Kind -> Env -> WFFE 
                         -> Type -> Kind -> WFType -> Vname -> WFType
lem_change_tvar_wf_wfpoly g a k_a g' p_env_wf t k p_t_wf@(WFPoly gg a1 k1 t1 k_t1 a1'_ p_a1'_t1) a'_
    = WFPoly (concatE (ConsT a' k_a g) (echgFTV a a' g')) a1 k1 (tchgFTV a a' t1) k_t1
             a1'' p_a1''env'_t1
        where
            a'            = a'_ ? lem_erase_concat (ConsT a'_ k_a g) (echgFTV a a'_ g')
                                ? lem_erase_echgFTV a a'_ g'
            a1'           = a1'_  ? lem_erase_concat (ConsT a k_a g) g'
            a1''_         = fresh_var_excluding (concatE (ConsT a k_a g) g') a'
            a1''          = a1''_ ? lem_in_env_concat g g' a1''_
                                  ? lem_in_env_concat (ConsT a k_a g) g' a1''_
                                  ? lem_free_bound_in_env (concatE (ConsT a k_a g) g') t k p_t_wf a1''_
            p_a1'env_wf   = WFFBindT (erase_env gg) p_env_wf a1'  k1  
            p_a1''env_wf  = WFFBindT (erase_env gg) p_env_wf a1'' k1
            p_a1''env_t1  = lem_change_tvar_wf (concatE (ConsT a k_a g) g') a1' k1 Empty p_a1'env_wf
                                 (unbind_tvT a1 a1' t1) k_t1 p_a1'_t1 a1''
                                 ? lem_tchgFTV_unbind_tvT a1 a1' a1'' (t1
                                       ? lem_free_bound_in_env (concatE (ConsT a k_a g) g')
                                                              t k p_t_wf a1')
            p_a1''env'_t1 = lem_change_tvar_wf g a k_a (ConsT a1'' k1 g') p_a1''env_wf 
                                 (unbind_tvT a1 a1'' t1) k_t1 p_a1''env_t1 a'
                                 ? lem_commute_tchgFTV_unbind_tvT a a' a1 a1'' t1

{-@ lem_change_tvar_wf :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
      -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) } 
      -> ProofOf(WFFE (concatF (FConsT a k_a (erase_env g)) (erase_env g'))) -> t:Type
      -> k:Kind -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (ConsT a k_a g) g') t k }
      -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
               (tchgFTV a a' t) k) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf, 1] @-}
lem_change_tvar_wf :: Env -> Vname -> Kind -> Env -> WFFE 
                          -> Type -> Kind -> WFType -> Vname -> WFType
lem_change_tvar_wf g a k_a g' p_env_wf t k p_t_wf@(WFBase gg b tt) a'
    = WFBase (concatE (ConsT a' k_a g) (echgFTV a a' g')) b tt 
             ? lem_chgFTV_notin a a' (tt ? lem_trivial_nofv tt)
lem_change_tvar_wf g a k_a g' p_env_wf t k p_t_wf@(WFRefn gg z b tt pf_gg_b p z' p_z'_p_b) a'
    = lem_change_tvar_wf_wfrefn g a k_a g' p_env_wf t k p_t_wf a' 
lem_change_tvar_wf g a k_a g' p_env_wf t k p_t_wf@(WFVar1 {}) a'
    = lem_change_tvar_wf_wfvar1 g a k_a g' p_env_wf t k p_t_wf a'
lem_change_tvar_wf g a k_a g' p_env_wf t k p_t_wf@(WFVar2 {}) a'
    = lem_change_tvar_wf_wfvar2 g a k_a g' p_env_wf t k p_t_wf a'
lem_change_tvar_wf g a k_a g' p_env_wf t k p_t_wf@(WFVar3 {}) a'
    = lem_change_tvar_wf_wfvar3 g a k_a g' p_env_wf t k p_t_wf a'
lem_change_tvar_wf g a k_a g' p_env_wf t k p_t_wf@(WFFunc gg z t_z k_z p_tz_wf t' k' z' p_z'_t'_wf) a'
    = lem_change_tvar_wf_wffunc g a k_a g' p_env_wf t k p_t_wf a'
lem_change_tvar_wf g a k_a g' p_env_wf t k p_t_wf@(WFExis gg z t_z k_z p_tz_wf t' k' z' p_z'_t'_wf) a'
    = lem_change_tvar_wf_wfexis g a k_a g' p_env_wf t k p_t_wf a'
lem_change_tvar_wf g a k_a g' p_env_wf t k p_t_wf@(WFPoly gg a1 k1 t1 k_t1 a1' p_a1'_t1) a'
    = lem_change_tvar_wf_wfpoly g a k_a g' p_env_wf t k p_t_wf a'
lem_change_tvar_wf g a k_a g' p_env_wf t k p_t_wf@(WFKind gg _t pf_gg_t_b) a'
    = WFKind (concatE (ConsT a' k_a g) (echgFTV a a' g')) (tchgFTV a a' t) pf_env'_t_b
        where
          pf_env'_t_b = lem_change_tvar_wf g a k_a g' p_env_wf t Base pf_gg_t_b a'

{-@ lem_change_tvar_wf' :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
      -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) } 
      -> ProofOf(WFEnv (concatE (ConsT a k_a g) g')) -> t:Type
      -> k:Kind -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (ConsT a k_a g) g') t k }
      -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
               (tchgFTV a a' t) k) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf, 2] @-}
lem_change_tvar_wf' :: Env -> Vname -> Kind -> Env -> WFEnv 
                         -> Type -> Kind -> WFType -> Vname -> WFType
lem_change_tvar_wf' g a k_a g' p_env_wf t k p_t_wf a'
  = lem_change_tvar_wf g a k_a g' p_er_env_wf t k p_t_wf a'
      where
        p_er_env_wf = lem_erase_env_wfenv (concatE (ConsT a k_a g) g') p_env_wf
                                          ? lem_erase_concat (ConsT a k_a g) g'
