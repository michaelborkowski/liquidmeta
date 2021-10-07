{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasWeakenWFTV where

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
import SystemFLemmasFTyping2
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import LemmasChangeVarWF
import LemmasWeakenWF

{-@ reflect foo35 @-}
foo35 x = Just x
foo35 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------

{-@ lem_weaken_tv_wf_wfrefn :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> ProofOf(WFFE (concatF (erase_env g) (erase_env g'))) -> t:Type -> k:Kind
        -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && isWFRefn p_t_wf }
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> k_a:Kind
        -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a k_a g) g') t k) } / [wftypSize p_t_wf, 0] @-}
lem_weaken_tv_wf_wfrefn :: Env -> Env -> WFFE -> Type -> Kind -> WFType -> Vname -> Kind -> WFType 
lem_weaken_tv_wf_wfrefn g g' p_env_wf t k p_t_wf@(WFRefn env y b tt pf_env_b p y'_ pf_p_bl) a k_a
    = WFRefn (concatE (ConsT a k_a g) g') y b tt pf_env'_b p y''
          (lem_weaken_tv_ftyp (erase_env g) (FCons y'' (FTBasic b) (erase_env g')) pf_y''env_wf
               (unbind 0 y'' p) (FTBasic TBool) pf_y''_p_bl
               a k_a ? lem_erase_concat (ConsT a k_a g) g')
        where
          y'           = y'_ ? lem_erase_concat g g'
          y''_         = fresh_var (concatE (ConsT a k_a g) g')
          y''          = y''_ ? lem_in_env_concat g g' y''_
                              ? lem_in_env_concat (ConsT a k_a g) g' y''_
                              ? lem_erase_concat g g'
                              ? lem_free_bound_in_env (concatE g g') t k p_t_wf y''_
          pf_env_er_b  = lem_erase_wftype env (TRefn b Z tt) Base pf_env_b
          pf_y'env_wf  = WFFBind (erase_env env) p_env_wf y'  (FTBasic b) Base pf_env_er_b
          pf_y''env_wf = WFFBind (erase_env env) p_env_wf y'' (FTBasic b) Base pf_env_er_b
          pf_y''_p_bl  = lem_change_var_ftyp (erase_env (concatE g g')) y' (FTBasic b) FEmpty
                             pf_y'env_wf (unbind 0 y' p) (FTBasic TBool) pf_p_bl y''
                             ? lem_subFV_unbind 0 y' (FV y'')
                                   (p ? lem_free_bound_in_env (concatE g g') t k p_t_wf y')
          pf_env'_b    = lem_weaken_tv_wf g g' p_env_wf (TRefn b Z tt) Base pf_env_b a k_a

{-@ lem_weaken_tv_wf_wfvar1 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> ProofOf(WFFE (concatF (erase_env g) (erase_env g'))) -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && isWFVar1 p_t_wf }
            -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> k_a:Kind
            -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a k_a g) g') t k) } / [wftypSize p_t_wf, 0] @-}
lem_weaken_tv_wf_wfvar1 :: Env -> Env -> WFFE -> Type -> Kind -> WFType -> Vname -> Kind -> WFType 
lem_weaken_tv_wf_wfvar1 g g' p_a'env_wf t k p_t_wf@(WFVar1 env a' tt k') a k_a  = case g' of
  Empty               -> WFVar3 (concatE g g') a' tt k' p_t_wf a k_a
  (ConsT _a' _k' g'') -> WFVar1 (concatE (ConsT a k_a g) g'') a' tt k'


{-@ lem_weaken_tv_wf_wfvar2 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> ProofOf(WFFE (concatF (erase_env g) (erase_env g'))) -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && isWFVar2 p_t_wf }
            -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> k_a:Kind
            -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a k_a g) g') t k) } / [wftypSize p_t_wf, 0] @-}
lem_weaken_tv_wf_wfvar2 :: Env -> Env -> WFFE -> Type -> Kind -> WFType -> Vname -> Kind -> WFType 
lem_weaken_tv_wf_wfvar2 g g' p_zenv_wf t k p_t_wf@(WFVar2 env a'_ tt k' p_env_a' z t_z) a k_a = case g' of
  Empty             -> WFVar3 (concatE g g') a'_ tt k' p_t_wf a k_a 
  (Cons _z _tz g'') -> WFVar2 (concatE (ConsT a k_a g) g'') a' tt k' p_env'_a' z t_z
    where
      a'        = a'_ ? lem_in_env_concat g g'' a'_
                      ? lem_in_env_concat (ConsT a k_a g) g'' a'_
      (WFFBind _ p_env_wf _ _ _ _) = p_zenv_wf
      p_env'_a' = lem_weaken_tv_wf g g'' p_env_wf t k p_env_a' a k_a


{-@ lem_weaken_tv_wf_wfvar3 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> ProofOf(WFFE (concatF (erase_env g) (erase_env g'))) -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && isWFVar3 p_t_wf }
            -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> k_a:Kind
            -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a k_a g) g') t k) } / [wftypSize p_t_wf, 0] @-}
lem_weaken_tv_wf_wfvar3 :: Env -> Env -> WFFE -> Type -> Kind -> WFType -> Vname -> Kind -> WFType 
lem_weaken_tv_wf_wfvar3 g g' p_a1env_wf t k p_t_wf@(WFVar3 env a'_ tt k' p_env_a' a1 k1) a k_a = case g' of
  Empty               -> WFVar3 (concatE g g') a'_ tt k' p_t_wf a k_a
  (ConsT _a1 _k1 g'') -> WFVar3 (concatE (ConsT a k_a g) g'') a' tt k' p_env'_a' a1 k1
    where
      a'        = a'_ ? lem_in_env_concat g g'' a'_
                      ? lem_in_env_concat (ConsT a k_a g) g'' a'_
      (WFFBindT _ p_env_wf _ _) = p_a1env_wf
      p_env'_a' = lem_weaken_tv_wf g g'' p_env_wf t k p_env_a' a k_a


{-@ lem_weaken_tv_wf_wffunc :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> ProofOf(WFFE (concatF (erase_env g) (erase_env g'))) -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && isWFFunc p_t_wf  }
            -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> k_a:Kind
            -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a k_a g) g') t k) } / [wftypSize p_t_wf, 0] @-}
lem_weaken_tv_wf_wffunc :: Env -> Env -> WFFE -> Type -> Kind -> WFType -> Vname -> Kind -> WFType 
lem_weaken_tv_wf_wffunc g g' p_env_wf t k p_t_wf@(WFFunc env y t_y k_y p_ty_wf t' k' y' p_y'_t'_wf) a k_a
  = WFFunc (concatE (ConsT a k_a g) g') y
             t_y k_y (lem_weaken_tv_wf g g' p_env_wf t_y k_y p_ty_wf a k_a) 
             t' k' (y'' ? lem_free_bound_in_env (concatE g g') t k p_t_wf y'')
             (lem_weaken_tv_wf g (Cons y'' t_y g') p_y''env_wf (unbindT y y'' t') k' p_y''_t'_wf a k_a)
        where
          y''_        = fresh_var(concatE (ConsT a k_a g) g')
          y''         = y''_  ? lem_in_env_concat g g' y''_
                              ? lem_in_env_concat (ConsT a k_a g) g' y''_
          p_er_ty_wf  = lem_erase_wftype env t_y k_y p_ty_wf ? lem_erase_concat g g'
          p_y'env_wf  = WFFBind (erase_env env) p_env_wf y'  (erase t_y) k_y p_er_ty_wf
          p_y''env_wf = WFFBind (erase_env env) p_env_wf y'' (erase t_y) k_y p_er_ty_wf
          p_y''_t'_wf = lem_change_var_wf (concatE g g') y' t_y Empty p_y'env_wf
                             (unbindT y y' t') k' p_y'_t'_wf y''
                             ? lem_tsubFV_unbindT y y' (FV y'') t'

{-@ lem_weaken_tv_wf_wfexis :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> ProofOf(WFFE (concatF (erase_env g) (erase_env g'))) -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && isWFExis p_t_wf }
            -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> k_a:Kind
            -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a k_a g) g') t k) } / [wftypSize p_t_wf, 0] @-}
lem_weaken_tv_wf_wfexis :: Env -> Env -> WFFE -> Type -> Kind -> WFType -> Vname -> Kind -> WFType 
lem_weaken_tv_wf_wfexis g g' p_env_wf t k p_t_wf@(WFExis env y t_y k_y p_ty_wf t' k' y' p_y'_t'_wf) a k_a
  = WFExis (concatE (ConsT a k_a g) g') y
             t_y k_y (lem_weaken_tv_wf g g' p_env_wf t_y k_y p_ty_wf a k_a) 
             t' k' (y'' ? lem_free_bound_in_env (concatE g g') t k p_t_wf y'')
             (lem_weaken_tv_wf g (Cons y'' t_y g') p_y''env_wf (unbindT y y'' t') k' p_y''_t'_wf a k_a)
        where
          y''_        = fresh_var(concatE (ConsT a k_a g) g')
          y''         = y''_  ? lem_in_env_concat g g' y''_
                              ? lem_in_env_concat (ConsT a k_a g) g' y''_
          p_er_ty_wf  = lem_erase_wftype env t_y k_y p_ty_wf ? lem_erase_concat g g'
          p_y'env_wf  = WFFBind (erase_env env) p_env_wf y'  (erase t_y) k_y p_er_ty_wf
          p_y''env_wf = WFFBind (erase_env env) p_env_wf y'' (erase t_y) k_y p_er_ty_wf
          p_y''_t'_wf = lem_change_var_wf (concatE g g') y' t_y Empty p_y'env_wf
                             (unbindT y y' t') k' p_y'_t'_wf y''
                             ? lem_tsubFV_unbindT y y' (FV y'') t'

{-@ lem_weaken_tv_wf_wfpoly :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> ProofOf(WFFE (concatF (erase_env g) (erase_env g'))) -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && isWFPoly p_t_wf }
            -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> k_a:Kind
            -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a k_a g) g') t k) } / [wftypSize p_t_wf, 0] @-}
lem_weaken_tv_wf_wfpoly :: Env -> Env -> WFFE -> Type -> Kind -> WFType -> Vname -> Kind -> WFType 
lem_weaken_tv_wf_wfpoly g g' p_env_wf t k p_t_wf@(WFPoly gg a1 k1 t1 k_t1 a1' p_a1'_t1) a k_a
  = WFPoly (concatE (ConsT a k_a g) g') a1 k1 t1 k_t1 a1'' p_a1''env'_t1
      where
        a1''_         = fresh_var (concatE (ConsT a k_a g) g')
        a1''          = a1''_ ? lem_in_env_concat g g' a1''_
                              ? lem_in_env_concat (ConsT a k_a g) g' a1''_
                              ? lem_free_bound_in_env (concatE g g') t k p_t_wf a1''_
        p_a1'env_wf   = WFFBindT (erase_env gg) (p_env_wf ? lem_erase_concat g g') a1'  k1
        p_a1''env_wf  = WFFBindT (erase_env gg) (p_env_wf ? lem_erase_concat g g') a1'' k1
        p_a1''env_t1  = lem_change_tvar_wf (concatE g g') a1' k1 Empty p_a1'env_wf
                            (unbind_tvT a1 a1' t1) k_t1 p_a1'_t1 a1''
                            ? lem_tchgFTV_unbind_tvT a1 a1' a1'' (t1
                                  ? lem_free_bound_in_env (concatE g g') t k p_t_wf a1')
        p_a1''env'_t1 = lem_weaken_tv_wf g (ConsT a1'' k1 g') p_a1''env_wf (unbind_tvT a1 a1'' t1)
                                      k_t1 p_a1''env_t1 a k_a

{-@ lem_weaken_tv_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> ProofOf(WFFE (concatF (erase_env g) (erase_env g'))) -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k }
            -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> k_a:Kind
            -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a k_a g) g') t k) } / [wftypSize p_t_wf, 1] @-}
lem_weaken_tv_wf :: Env -> Env -> WFFE -> Type -> Kind -> WFType -> Vname -> Kind -> WFType 
lem_weaken_tv_wf g g' p_env_wf t k p_t_wf@(WFBase env b tt) a k_a
    = WFBase (concatE (ConsT a k_a g) g') b tt
lem_weaken_tv_wf g g' p_env_wf t k p_t_wf@(WFRefn {}) a k_a
    = lem_weaken_tv_wf_wfrefn g g' p_env_wf t k p_t_wf a k_a
lem_weaken_tv_wf g g' p_env_wf t k p_t_wf@(WFVar1 {}) a k_a
    = lem_weaken_tv_wf_wfvar1 g g' p_env_wf t k p_t_wf a k_a
lem_weaken_tv_wf g g' p_env_wf t k p_t_wf@(WFVar2 {}) a k_a
    = lem_weaken_tv_wf_wfvar2 g g' p_env_wf t k p_t_wf a k_a
lem_weaken_tv_wf g g' p_env_wf t k p_t_wf@(WFVar3 {}) a k_a
    = lem_weaken_tv_wf_wfvar3 g g' p_env_wf t k p_t_wf a k_a
lem_weaken_tv_wf g g' p_env_wf t k p_t_wf@(WFFunc {}) a k_a
    = lem_weaken_tv_wf_wffunc g g' p_env_wf t k p_t_wf a k_a
lem_weaken_tv_wf g g' p_env_wf t k p_t_wf@(WFExis {}) a k_a
    = lem_weaken_tv_wf_wfexis g g' p_env_wf t k p_t_wf a k_a
lem_weaken_tv_wf g g' p_env_wf t k p_t_wf@(WFPoly {}) a k_a
    = lem_weaken_tv_wf_wfpoly g g' p_env_wf t k p_t_wf a k_a
lem_weaken_tv_wf g g' p_env_wf t k p_t_wf@(WFKind _ _t pf_env_t_b) a k_a
    = WFKind (concatE (ConsT a k_a g) g') t pf_env'_t_b
        where
          pf_env'_t_b = lem_weaken_tv_wf g g' p_env_wf t Base pf_env_t_b a k_a

{-@ lem_weaken_tv_wf' :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> ProofOf(WFEnv (concatE g g')) -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k }
            -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> k_a:Kind
            -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a k_a g) g') t k) } / [wftypSize p_t_wf, 2] @-}
lem_weaken_tv_wf' :: Env -> Env -> WFEnv -> Type -> Kind -> WFType -> Vname -> Kind -> WFType 
lem_weaken_tv_wf' g g' p_env_wf t k p_t_wf a k_a 
    = lem_weaken_tv_wf g g' p_er_env_wf t k p_t_wf a k_a
        where
          p_er_env_wf = lem_erase_env_wfenv (concatE g g') p_env_wf ? lem_erase_concat g g'

{-@ lem_weaken_many_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFFE (concatF (erase_env g) (erase_env g'))) -> t:Type -> k:Kind 
      -> ProofOf(WFType g t k) -> ProofOf(WFType (concatE g g') t k) @-}
lem_weaken_many_wf :: Env -> Env -> WFFE -> Type -> Kind -> WFType -> WFType
lem_weaken_many_wf g Empty            p_env_wf t k p_g_t = p_g_t 
lem_weaken_many_wf g (Cons x t_x g')  p_env_wf t k p_g_t 
  = lem_weaken_wf    (concatE g g') Empty p_env'_wf t k p_gg'_t x t_x
     where
       (WFFBind  env' p_env'_wf _ _ _ _) = p_env_wf
       p_gg'_t   = lem_weaken_many_wf g g' p_env'_wf t k p_g_t ? lem_erase_concat g g'
lem_weaken_many_wf g (ConsT a k_a g') p_env_wf t k p_g_t 
  = lem_weaken_tv_wf (concatE g g') Empty p_env'_wf t k p_gg'_t a k_a
     where
       (WFFBindT env' p_env'_wf _ _)     = p_env_wf
       p_gg'_t   = lem_weaken_many_wf g g' p_env'_wf t k p_g_t ? lem_erase_concat g g'

{-@ lem_weaken_many_wf' :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE g g')) -> t:Type -> k:Kind -> ProofOf(WFType g t k) 
      -> ProofOf(WFType (concatE g g') t k) @-}
lem_weaken_many_wf' :: Env -> Env -> WFEnv -> Type -> Kind -> WFType -> WFType
lem_weaken_many_wf' g g' p_env_wf t k p_g_t = lem_weaken_many_wf g g' p_er_env_wf t k p_g_t
  where
    p_er_env_wf = lem_erase_env_wfenv (concatE g g') p_env_wf ? lem_erase_concat g g'
