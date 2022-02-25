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
import BasicPropsEnvironments
import SystemFLemmasWeaken
import LemmasWeakenWF

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------

{-@ lem_weaken_tv_wf_wfrefn :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> t:Type -> k:Kind
        -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && isWFRefn p_t_wf }
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> k_a:Kind
        -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a k_a g) g') t k) } 
         / [tsize t, envsize g', ksize k, 0] @-}
lem_weaken_tv_wf_wfrefn :: Env -> Env -> Type -> Kind -> WFType -> Vname -> Kind -> WFType 
lem_weaken_tv_wf_wfrefn g g' t k p_t_wf@(WFRefn env b pf_env_b ps nms mk_pf_ps_bl) a k_a
    = WFRefn (concatE (ConsT a k_a g) g') b pf_env'_b ps nms' mk_pf'_ps_bl
        where
          pf_env'_b    = lem_weaken_tv_wf g g' (TRefn b PEmpty) Base pf_env_b a k_a
          {-@ mk_pf'_ps_bl :: { y:Vname | NotElem y nms' }
                 -> ProofOf(PHasFType (FCons y (FTBasic b) (erase_env (concatE (ConsT a k_a g) g')))
                                      (unbindP y ps)) @-}
          mk_pf'_ps_bl y = lem_weaken_tv_pftyp (erase_env g) (FCons y (FTBasic b) (erase_env g'))
                                           (unbindP y ps) (mk_pf_ps_bl y ? lem_erase_concat g g')
                                           a k_a ? lem_erase_concat (ConsT a k_a g) g'
          nms'         = a:(unionEnv nms (concatE g g'))

{-@ lem_weaken_tv_wf_wfvar1 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && isWFVar1 p_t_wf }
            -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> k_a:Kind
            -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a k_a g) g') t k) } 
             / [tsize t, envsize g', ksize k, 0] @-}
lem_weaken_tv_wf_wfvar1 :: Env -> Env  -> Type -> Kind -> WFType -> Vname -> Kind -> WFType 
lem_weaken_tv_wf_wfvar1 g g'  t k p_t_wf@(WFVar1 env a' k') a k_a  = case g' of
  Empty               -> WFVar3 (concatE g g') a' k' p_t_wf a k_a
  (ConsT _a' _k' g'') -> WFVar1 (concatE (ConsT a k_a g) g'') a' k'

{-@ lem_weaken_tv_wf_wfvar2 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && isWFVar2 p_t_wf }
            -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> k_a:Kind
            -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a k_a g) g') t k) } 
             / [tsize t, envsize g', ksize k, 0] @-}
lem_weaken_tv_wf_wfvar2 :: Env -> Env -> Type -> Kind -> WFType -> Vname -> Kind -> WFType 
lem_weaken_tv_wf_wfvar2 g g'  t k p_t_wf@(WFVar2 env a'_ k' p_env_a' z t_z) a k_a = case g' of
  Empty             -> WFVar3 (concatE g g') a'_ k' p_t_wf a k_a 
  (Cons _z _tz g'') -> WFVar2 (concatE (ConsT a k_a g) g'') a' k' p_env'_a' z t_z
    where
      a'        = a'_ ? lem_in_env_concat g g'' a'_
      p_env'_a' = lem_weaken_tv_wf g g'' t k p_env_a' a k_a

{-@ lem_weaken_tv_wf_wfvar3 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && isWFVar3 p_t_wf }
            -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> k_a:Kind
            -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a k_a g) g') t k) } 
             / [tsize t, envsize g', ksize k, 0] @-}
lem_weaken_tv_wf_wfvar3 :: Env -> Env -> Type -> Kind -> WFType -> Vname -> Kind -> WFType 
lem_weaken_tv_wf_wfvar3 g g' t k p_t_wf@(WFVar3 env a'_ k' p_env_a' a1 k1) a k_a = case g' of
  Empty               -> WFVar3 (concatE g g') a'_ k' p_t_wf a k_a
  (ConsT _a1 _k1 g'') -> WFVar3 (concatE (ConsT a k_a g) g'') a' k' p_env'_a' a1 k1
    where
      a'        = a'_ ? lem_in_env_concat g g'' a'_
      p_env'_a' = lem_weaken_tv_wf g g'' t k p_env_a' a k_a

{-@ lem_weaken_tv_wf_wffunc :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && isWFFunc p_t_wf  }
            -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> k_a:Kind
            -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a k_a g) g') t k) } 
             / [tsize t, envsize g', ksize k, 0] @-}
lem_weaken_tv_wf_wffunc :: Env -> Env -> Type -> Kind -> WFType -> Vname -> Kind -> WFType 
lem_weaken_tv_wf_wffunc g g' t k p_t_wf@(WFFunc env t_y k_y p_ty_wf t' k' nms mk_p_y_t'_wf) a k_a
    = WFFunc (concatE (ConsT a k_a g) g') t_y k_y (lem_weaken_tv_wf g g' t_y k_y p_ty_wf a k_a )
             t' k' nms' mk_p'_y_t'_wf
        where
          {-@ mk_p'_y_t'_wf :: { y:Vname | NotElem y nms' }
                -> ProofOf(WFType (Cons y t_y (concatE (ConsT a k_a g) g')) (unbindT y t') k') @-}
          mk_p'_y_t'_wf y = lem_weaken_tv_wf g (Cons y t_y g')
                                             (unbindT y t') k' (mk_p_y_t'_wf y) a k_a
          nms'            = a:(unionEnv nms (concatE g g'))

{-@ lem_weaken_tv_wf_wfexis :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && isWFExis p_t_wf }
            -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> k_a:Kind
            -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a k_a g) g') t k) } 
             / [tsize t, envsize g', ksize k, 0] @-}
lem_weaken_tv_wf_wfexis :: Env -> Env -> Type -> Kind -> WFType -> Vname -> Kind -> WFType 
lem_weaken_tv_wf_wfexis g g' t k p_t_wf@(WFExis env t_y k_y p_ty_wf t' k' nms mk_p_y_t'_wf) a k_a
    = WFExis (concatE (ConsT a k_a g) g') t_y k_y (lem_weaken_tv_wf g g' t_y k_y p_ty_wf a k_a )
             t' k' nms' mk_p'_y_t'_wf
        where
          {-@ mk_p'_y_t'_wf :: { y:Vname | NotElem y nms' }
                -> ProofOf(WFType (Cons y t_y (concatE (ConsT a k_a g) g')) (unbindT y t') k') @-}
          mk_p'_y_t'_wf y = lem_weaken_tv_wf g (Cons y t_y g')
                                             (unbindT y t') k' (mk_p_y_t'_wf y) a k_a
          nms'            = a:(unionEnv nms (concatE g g'))

{-@ lem_weaken_tv_wf_wfpoly :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && isWFPoly p_t_wf }
            -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> k_a:Kind
            -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a k_a g) g') t k) } 
             / [tsize t, envsize g', ksize k, 0] @-}
lem_weaken_tv_wf_wfpoly :: Env -> Env -> Type -> Kind -> WFType -> Vname -> Kind -> WFType 
lem_weaken_tv_wf_wfpoly g g'  t k p_t_wf@(WFPoly gg k1 t1 k_t1 nms mk_p_a1_t1) a k_a
    = WFPoly (concatE (ConsT a k_a g) g') k1 t1 k_t1 nms' mk_p_a1env'_t1
        where
          {-@ mk_p_a1env'_t1 :: { a1:Vname | NotElem a1 nms' }
                -> ProofOf(WFType (ConsT a1 k1 (concatE (ConsT a k_a g) g')) (unbind_tvT a1 t1) k_t1) @-}
          mk_p_a1env'_t1 a1 = lem_weaken_tv_wf g (ConsT a1 k1 g')
                                               (unbind_tvT a1 t1) k_t1 (mk_p_a1_t1 a1) a k_a
          nms'            = a:(unionEnv nms (concatE g g'))

{-@ lem_weaken_tv_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k }
            -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> k_a:Kind
            -> { pf:WFType | propOf pf == (WFType (concatE (ConsT a k_a g) g') t k) } 
             / [tsize t, envsize g', ksize k, 1] @-}
lem_weaken_tv_wf :: Env -> Env -> Type -> Kind -> WFType -> Vname -> Kind -> WFType 
lem_weaken_tv_wf g g' t k p_t_wf@(WFBase env b) a k_a
    = WFBase (concatE (ConsT a k_a g) g') b 
lem_weaken_tv_wf g g' t k p_t_wf@(WFRefn {}) a k_a
    = lem_weaken_tv_wf_wfrefn g g'  t k p_t_wf a k_a
lem_weaken_tv_wf g g' t k p_t_wf@(WFVar1 {}) a k_a
    = lem_weaken_tv_wf_wfvar1 g g'  t k p_t_wf a k_a
lem_weaken_tv_wf g g' t k p_t_wf@(WFVar2 {}) a k_a
    = lem_weaken_tv_wf_wfvar2 g g'  t k p_t_wf a k_a
lem_weaken_tv_wf g g' t k p_t_wf@(WFVar3 {}) a k_a
    = lem_weaken_tv_wf_wfvar3 g g'  t k p_t_wf a k_a
lem_weaken_tv_wf g g' t k p_t_wf@(WFFunc {}) a k_a
    = lem_weaken_tv_wf_wffunc g g'  t k p_t_wf a k_a
lem_weaken_tv_wf g g' t k p_t_wf@(WFExis {}) a k_a
    = lem_weaken_tv_wf_wfexis g g'  t k p_t_wf a k_a
lem_weaken_tv_wf g g' t k p_t_wf@(WFPoly {}) a k_a
    = lem_weaken_tv_wf_wfpoly g g'  t k p_t_wf a k_a
lem_weaken_tv_wf g g' t k p_t_wf@(WFKind _ _t pf_env_t_b) a k_a
    = WFKind (concatE (ConsT a k_a g) g') t pf_env'_t_b
        where
          pf_env'_t_b = lem_weaken_tv_wf g g' t Base pf_env_t_b a k_a

{-@ lem_weaken_many_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> t:Type -> k:Kind 
      -> ProofOf(WFType g t k) -> ProofOf(WFType (concatE g g') t k) @-}
lem_weaken_many_wf :: Env -> Env -> Type -> Kind -> WFType -> WFType
lem_weaken_many_wf g Empty            t k p_g_t = p_g_t 
lem_weaken_many_wf g (Cons x t_x g')  t k p_g_t 
  = lem_weaken_wf    (concatE g g') Empty t k p_gg'_t x t_x
     where
       p_gg'_t   = lem_weaken_many_wf g g' t k p_g_t ? lem_erase_concat g g'
lem_weaken_many_wf g (ConsT a k_a g') t k p_g_t 
  = lem_weaken_tv_wf (concatE g g') Empty t k p_gg'_t a k_a
     where
       p_gg'_t   = lem_weaken_many_wf g g' t k p_g_t ? lem_erase_concat g g'
