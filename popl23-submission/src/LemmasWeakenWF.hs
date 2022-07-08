{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasWeakenWF where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof,(?))
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import BasicPropsEnvironments
import SystemFLemmasWeaken

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------

{-@ lem_weaken_wf_wfrefn :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && isWFRefn p_t_wf }
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> t_x:Type 
            -> { pf:WFType | propOf pf == (WFType (concatE (Cons x t_x g) g') t k) } 
             / [tsize t, envsize g', ksize k, 0] @-}
lem_weaken_wf_wfrefn :: Env -> Env -> Type -> Kind -> WFType -> Vname -> Type -> WFType 
lem_weaken_wf_wfrefn g g' t k p_t_wf@(WFRefn env b pf_env_b ps nms mk_pf_ps_bl) x t_x 
    = WFRefn (concatE (Cons x t_x g) g') b pf_env'_b ps nms' mk_pf'_ps_bl
        where
          pf_env'_b    = lem_weaken_wf g g' (TRefn b PEmpty) Base pf_env_b x t_x
          {-@ mk_pf'_ps_bl :: { y:Vname | NotElem y nms' }
                -> ProofOf(PHasFType (FCons y (FTBasic b) (erase_env (concatE (Cons x t_x g) g')))
                                     (unbindP y ps)) @-}
          mk_pf'_ps_bl y = lem_weaken_pftyp (erase_env g) (FCons y (FTBasic b) (erase_env g')) 
                                            (unbindP y ps) (mk_pf_ps_bl y ? lem_erase_concat g g')
                                            x (erase t_x) ? lem_erase_concat (Cons x t_x g) g'
          nms'         = x:(unionEnv nms (concatE g g'))        

{-@ lem_weaken_wf_wfvar1 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && isWFVar1 p_t_wf }
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> t_x:Type 
            -> { pf:WFType | propOf pf == (WFType (concatE (Cons x t_x g) g') t k) } 
             / [tsize t, envsize g', ksize k, 0] @-} 
lem_weaken_wf_wfvar1 :: Env -> Env -> Type -> Kind -> WFType -> Vname -> Type -> WFType 
lem_weaken_wf_wfvar1 g g' t k p_t_wf@(WFVar1 env a' k') x t_x  = case g' of
  Empty               -> WFVar2 (concatE g g') a' k' p_t_wf x t_x
  (ConsT _a' _k' g'') -> WFVar1 (concatE (Cons x t_x g) g'') a' k'

{-@ lem_weaken_wf_wfvar2 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && isWFVar2 p_t_wf }
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> t_x:Type 
            -> { pf:WFType | propOf pf == (WFType (concatE (Cons x t_x g) g') t k) } 
             / [tsize t, envsize g', ksize k, 0] @-}
lem_weaken_wf_wfvar2 :: Env -> Env  -> Type -> Kind -> WFType -> Vname -> Type -> WFType 
lem_weaken_wf_wfvar2 g g'  t k p_t_wf@(WFVar2 env a'_ k' p_env_a' z t_z) x t_x = case g' of
  Empty             -> WFVar2 (concatE g g') a'_ k' p_t_wf x t_x 
  (Cons _z _tz g'') -> WFVar2 (concatE (Cons x t_x g) g'') a' k' p_env'_a' z t_z
    where
      a'        = a'_ ? lem_in_env_concat g g'' a'_
      p_env'_a' = lem_weaken_wf g g'' t k p_env_a' x t_x

{-@ lem_weaken_wf_wfvar3 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && isWFVar3 p_t_wf }
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> t_x:Type 
            -> { pf:WFType | propOf pf == (WFType (concatE (Cons x t_x g) g') t k) } 
             / [tsize t, envsize g', ksize k, 0] @-}
lem_weaken_wf_wfvar3 :: Env -> Env  -> Type -> Kind -> WFType -> Vname -> Type -> WFType 
lem_weaken_wf_wfvar3 g g'  t k p_t_wf@(WFVar3 env a'_ k' p_env_a' a1 k1) x t_x = case g' of
  Empty               -> WFVar2 (concatE g g') a'_ k' p_t_wf x t_x
  (ConsT _a1 _k1 g'') -> WFVar3 (concatE (Cons x t_x g) g'') a' k' p_env'_a' a1 k1
    where
      a'        = a'_ ? lem_in_env_concat g g'' a'_
      p_env'_a' = lem_weaken_wf g g'' t k p_env_a' x t_x

{-@ lem_weaken_wf_wffunc :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && isWFFunc p_t_wf }
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> t_x:Type 
            -> { pf:WFType | propOf pf == (WFType (concatE (Cons x t_x g) g') t k) } 
             / [tsize t, envsize g', ksize k, 0] @-}
lem_weaken_wf_wffunc :: Env -> Env  -> Type -> Kind -> WFType -> Vname -> Type -> WFType 
lem_weaken_wf_wffunc g g'  t k p_t_wf@(WFFunc env t_y k_y p_ty_wf t' k' nms mk_p_y_t'_wf) x t_x 
    = WFFunc (concatE (Cons x t_x g) g') t_y k_y (lem_weaken_wf g g' t_y k_y p_ty_wf x t_x ) 
             t' k' nms' mk_p'_y_t'_wf 
        where
          {-@ mk_p'_y_t'_wf :: { y:Vname | NotElem y nms' }
                -> ProofOf(WFType (Cons y t_y (concatE (Cons x t_x g) g')) (unbindT y t') k') @-}
          mk_p'_y_t'_wf y = lem_weaken_wf g (Cons y t_y g')
                                          (unbindT y t') k' (mk_p_y_t'_wf y) x t_x
          nms'            = x:(unionEnv nms (concatE g g'))

{-@ lem_weaken_wf_wfexis :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && isWFExis p_t_wf }
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> t_x:Type 
            -> { pf:WFType | propOf pf == (WFType (concatE (Cons x t_x g) g') t k) } 
             / [tsize t, envsize g', ksize k, 0] @-}
lem_weaken_wf_wfexis :: Env -> Env  -> Type -> Kind -> WFType -> Vname -> Type -> WFType 
lem_weaken_wf_wfexis g g'  t k p_t_wf@(WFExis env t_y k_y p_ty_wf t' k' nms mk_p_y_t'_wf) x t_x 
    = WFExis (concatE (Cons x t_x g) g') t_y k_y (lem_weaken_wf g g'  t_y k_y p_ty_wf x t_x ) 
             t' k' nms' mk_p'_y_t'_wf 
        where
          {-@ mk_p'_y_t'_wf :: { y:Vname | NotElem y nms' }
                -> ProofOf(WFType (Cons y t_y (concatE (Cons x t_x g) g')) (unbindT y t') k') @-}
          mk_p'_y_t'_wf y = lem_weaken_wf g (Cons y t_y g') 
                                          (unbindT y t') k' (mk_p_y_t'_wf y) x t_x
          nms'            = x:(unionEnv nms (concatE g g'))

{-@ lem_weaken_wf_wfpoly :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k && isWFPoly p_t_wf }
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> t_x:Type 
            -> { pf:WFType | propOf pf == (WFType (concatE (Cons x t_x g) g') t k) } 
             / [tsize t, envsize g', ksize k, 0] @-}
lem_weaken_wf_wfpoly :: Env -> Env  -> Type -> Kind -> WFType -> Vname -> Type -> WFType 
lem_weaken_wf_wfpoly g g'  t k p_t_wf@(WFPoly gg k1 t1 k_t1 nms mk_p_a1_t1) x t_x
  = WFPoly (concatE (Cons x t_x g) g') k1 t1 k_t1 nms' mk_p_a1env'_t1
      where
        {-@ mk_p_a1env'_t1 :: { a1:Vname | NotElem a1 nms' }
              -> ProofOf(WFType (ConsT a1 k1 (concatE (Cons x t_x g) g')) (unbind_tvT a1 t1) k_t1) @-}
          mk_p_a1env'_t1 a1 = lem_weaken_wf g (ConsT a1 k1 g') 
                                            (unbind_tvT a1 t1) k_t1 (mk_p_a1_t1 a1) x t_x
          nms'            = x:(unionEnv nms (concatE g g'))

{-@ lem_weaken_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> t:Type -> k:Kind
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t k }
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> t_x:Type 
            -> { pf:WFType | propOf pf == (WFType (concatE (Cons x t_x g) g') t k) } 
             / [tsize t, envsize g', ksize k, 1] @-}
lem_weaken_wf :: Env -> Env  -> Type -> Kind -> WFType -> Vname -> Type -> WFType 
lem_weaken_wf g g'  t k p_t_wf@(WFBase env b) x t_x
    = WFBase (concatE (Cons x t_x g) g') b 
lem_weaken_wf g g'  t k p_t_wf@(WFRefn {}) x t_x 
    = lem_weaken_wf_wfrefn g g' t k p_t_wf x t_x
lem_weaken_wf g g'  t k p_t_wf@(WFVar1 {}) x t_x
    = lem_weaken_wf_wfvar1 g g' t k p_t_wf x t_x
lem_weaken_wf g g'  t k p_t_wf@(WFVar2 {}) x t_x 
    = lem_weaken_wf_wfvar2 g g' t k p_t_wf x t_x
lem_weaken_wf g g'  t k p_t_wf@(WFVar3 {}) x t_x
    = lem_weaken_wf_wfvar3 g g' t k p_t_wf x t_x
lem_weaken_wf g g'  t k p_t_wf@(WFFunc {}) x t_x 
    = lem_weaken_wf_wffunc g g' t k p_t_wf x t_x
lem_weaken_wf g g'  t k p_t_wf@(WFExis {}) x t_x 
    = lem_weaken_wf_wfexis g g' t k p_t_wf x t_x
lem_weaken_wf g g'  t k p_t_wf@(WFPoly {}) x t_x
    = lem_weaken_wf_wfpoly g g' t k p_t_wf x t_x
lem_weaken_wf g g'  t k p_t_wf@(WFKind env _t pf_env_t_base) x t_x
    = WFKind (concatE (Cons x t_x g) g') t (lem_weaken_wf g g' t Base pf_env_t_base x t_x)
