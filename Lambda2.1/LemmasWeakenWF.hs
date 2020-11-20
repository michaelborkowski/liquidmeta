{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasWeakenWF where

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
import SystemFAlphaEquivalence
import BasicPropsCSubst
import BasicPropsDenotes
import Entailments
import LemmasChangeVarWF

{-@ reflect foo38 @-}
foo38 x = Just x
foo38 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------

--                             wftypSize pf == wftypSize p_t_wf } / [wftypSize p_t_wf] @-}
{-@ lem_weaken_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> ProofOf(WFFE (concatF (erase_env g) (erase_env g'))) -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k }
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> t_x:Type 
            -> { pf:WFType | propOf pf == (WFType (concatE (Cons x t_x g) g') t k) } / [wftypSize p_t_wf] @-}
lem_weaken_wf :: Env -> Env -> WFFE -> Type -> Kind -> WFType -> Vname -> Type -> WFType 
lem_weaken_wf g g' p_env_wf t k p_t_wf@(WFBase env b) x t_x
    = WFBase (concatE (Cons x t_x g) g') b
lem_weaken_wf g g' p_env_wf t k p_t_wf@(WFRefn env y b pf_env_b p y' pf_p_bl) x t_x 
    = undefined {- TODO TODO update me for WFFE
    = WFRefn (concatE (Cons x t_x g) g') y b pf_env'_b p y''
          (lem_weaken_ftyp (erase_env g) (FCons y'' (FTBasic b) (erase_env g'))
               ({-lem_erase_env_wfenv (concatE g (Cons y'' (TRefn b 1 (Bc True)) g'))-} pf_y''env_wf
                    ? lem_erase_concat g (Cons y'' (TRefn b 1 (Bc True)) g'))
               (unbind y y'' p) (FTBasic TBool) 
               (pf_y''_p_bl `withProof` lem_subFV_unbind y y' (FV y'') p 
                    ? lem_erase_concat g (Cons y'' (TRefn b 1 (Bc True)) g'))
                           x (erase t_x) ? lem_erase_concat (Cons x t_x g) g')
        where
          y''_         = fresh_var (concatE (Cons x t_x g) g')
          y''          = y''_ `withProof` lem_in_env_concat g g' y''_
                              `withProof` lem_in_env_concat (Cons x t_x g) g' y''_
                              `withProof` lem_free_bound_in_env (concatE g g') t k p_t_wf y''_
          pf_y'env_wf  = WFFBind env p_env_wf y'  (TRefn b 1 (Bc True)) Base pf_env_b
          pf_y''env_wf = WFFBind env p_env_wf y'' (TRefn b 1 (Bc True)) Base pf_env_b
          pf_y''_p_bl  = lem_change_var_ftyp (erase_env (concatE g g')) y' (FTBasic b) FEmpty
                             ({-lem_erase_env_wfenv (concatE g (Cons y' (TRefn b 1 (Bc True)) g'))-}
                                                  pf_y'env_wf)
                             (unbind y y' p) (FTBasic TBool) pf_p_bl y''
          pf_env'_b    = lem_weaken_wf g g' p_env_wf (TRefn b 1 (Bc True)) Base pf_env_b x t_x
-}
lem_weaken_wf g g' p_env_wf t k p_t_wf@(WFVar1 {}) x t_x
    = undefined
lem_weaken_wf g g' p_env_wf t k p_t_wf@(WFVar2 {}) x t_x 
    = undefined
lem_weaken_wf g g' p_env_wf t k p_t_wf@(WFVar3 {}) x t_x
    = undefined
lem_weaken_wf g g' p_env_wf t k p_t_wf@(WFFunc env y t_y k_y p_ty_wf t' k' y' p_y'_t'_wf) x t_x 
    = undefined {- TODO TODO update me for WFFE
    = WFFunc (concatE (Cons x t_x g) g') y
             t_y k_y (lem_weaken_wf g g' p_env_wf t_y k_y p_ty_wf x t_x ) 
             t' k' (y'' `withProof` lem_free_bound_in_env (concatE g g') t k p_t_wf y'')
             (lem_weaken_wf g (Cons y'' t_y g') p_y''env_wf (unbindT y y'' t') k'
                         (p_y''_t'_wf `withProof` lem_tsubFV_unbindT y y' (FV y'') t')
                         x t_x) 
        where
          y''_        = fresh_var(concatE (Cons x t_x g) g')
          y''         = y''_  `withProof` lem_in_env_concat g g' y''_
                              `withProof` lem_in_env_concat (Cons x t_x g) g' y''_
          p_y'env_wf  = WFEBind env p_env_wf y'  t_y k_y p_ty_wf
          p_y''env_wf = WFEBind env p_env_wf y'' t_y k_y p_ty_wf
          p_y''_t'_wf = lem_change_var_wf (concatE g g') y' t_y Empty p_y'env_wf
                             (unbindT y y' t') k' p_y'_t'_wf y''
-}
lem_weaken_wf g g' p_env_wf t k p_t_wf@(WFExis env y t_y k_y p_ty_wf t' k' y' p_y'_t'_wf) x t_x 
    = undefined {- TODO TODO update me for WFFE
    = WFExis (concatE (Cons x t_x g) g') y 
             t_y k_y (lem_weaken_wf g g' p_env_wf t_y k_y p_ty_wf x t_x) 
             t' k' (y'' `withProof` lem_free_bound_in_env (concatE g g') t k p_t_wf y'')
             (lem_weaken_wf g (Cons y'' t_y g') p_y''env_wf (unbindT y y'' t') k'
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
-}
lem_weaken_wf g g' p_env_wf t k p_t_wf@(WFPoly {}) x t_x
    = undefined
lem_weaken_wf g g' p_env_wf t k p_t_wf@(WFKind env _t pf_env_t_base) x t_x
    = WFKind (concatE (Cons x t_x g) g') t 
             (lem_weaken_wf g g' p_env_wf t Base pf_env_t_base x t_x)

{-@ lem_weaken_wf' :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> ProofOf(WFEnv (concatE g g')) -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k }
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> t_x:Type 
            -> { pf:WFType | propOf pf == (WFType (concatE (Cons x t_x g) g') t k) } / [wftypSize p_t_wf] @-}
lem_weaken_wf' :: Env -> Env -> WFEnv -> Type -> Kind -> WFType -> Vname -> Type -> WFType 
lem_weaken_wf' g g' p_env_wf t k p_t_wf x t_x = undefined

{-@ lem_weaken_tv_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> ProofOf(WFFE (concatF (erase_env g) (erase_env g'))) -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k }
            -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> k_a:Kind
            -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a k_a g) g') t k) &&
                             wftypSize pf == wftypSize p_t_wf } / [wftypSize p_t_wf] @-}
lem_weaken_tv_wf :: Env -> Env -> WFFE -> Type -> Kind -> WFType -> Vname -> Kind -> WFType 
lem_weaken_tv_wf g g' p_env_wf t k p_t_wf@(WFBase env b) a k_a
    = WFBase (concatE (ConsT a k_a g) g') b
lem_weaken_tv_wf g g' p_env_wf t k p_t_wf@(WFRefn {}) a k_a
    = undefined
lem_weaken_tv_wf g g' p_env_wf t k p_t_wf@(WFVar1 {}) a k_a
    = undefined
lem_weaken_tv_wf g g' p_env_wf t k p_t_wf@(WFVar2 {}) a k_a
    = undefined
lem_weaken_tv_wf g g' p_env_wf t k p_t_wf@(WFVar3 {}) a k_a
    = undefined
lem_weaken_tv_wf g g' p_env_wf t k p_t_wf@(WFFunc {}) a k_a
    = undefined
lem_weaken_tv_wf g g' p_env_wf t k p_t_wf@(WFExis {}) a k_a
    = undefined
lem_weaken_tv_wf g g' p_env_wf t k p_t_wf@(WFPoly {}) a k_a
    = undefined
lem_weaken_tv_wf g g' p_env_wf t k p_t_wf@(WFKind {}) a k_a
    = undefined

{-@ lem_weaken_tv_wf' :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> ProofOf(WFEnv (concatE g g')) -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k }
            -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> k_a:Kind
            -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a k_a g) g') t k) &&
                             wftypSize pf == wftypSize p_t_wf } / [wftypSize p_t_wf] @-}
lem_weaken_tv_wf' :: Env -> Env -> WFEnv -> Type -> Kind -> WFType -> Vname -> Kind -> WFType 
lem_weaken_tv_wf' = undefined

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
lem_weaken_many_wf' = undefined
