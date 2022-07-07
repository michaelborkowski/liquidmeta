{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesWFType where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof,(?))
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness            --(WFFT(..),isWFFT)
import SystemFTyping                    --(HasFType(..),firstBV,inType,ty',refn_pred,ty,erase_ty,
import BasicPropsEnvironments
import WellFormedness                   --(WFType(..),noDefnsInRefns,isWellFormed,makeWFType)
import PrimitivesFTyping                --(isEql)
import Typing

-----------------------------------------------------------------------------
-- | All of our assumptions about BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

-- Constant and Primitive Typing Lemmas
-- Lemma. Well-Formedness of Constant Types
{-@ lem_wf_tybc :: g:Env -> b:Bool -> ProofOf(WFType g (tybc b) Base) @-}
lem_wf_tybc :: Env -> Bool -> WFType
lem_wf_tybc g b = undefined --makeWFType g (tybc b) Base

{-@ lem_wf_tyic :: g:Env -> n:Int -> ProofOf(WFType g (tyic n) Base) @-}
lem_wf_tyic :: Env -> Int -> WFType
lem_wf_tyic g n = undefined --makeWFType g (tyic n) Base

{-@ lem_wf_ty :: c:Prim -> ProofOf(WFType Empty (ty c) Star) @-}
lem_wf_ty :: Prim -> WFType
lem_wf_ty c        = undefined

{-@ lem_wf_intype :: { c:Prim | not (isPoly c) } -> ProofOf(WFType Empty (inType c) Base) @-}
lem_wf_intype :: Prim -> WFType
lem_wf_intype c    = undefined 

{-@ lem_wf_ty' :: { c:Prim | not (isPoly c) } -> y:Vname
        -> ProofOf(WFType (Cons y (inType c) Empty) (unbindT y (ty' c)) Star) @-}
lem_wf_ty' :: Prim -> Int -> WFType
lem_wf_ty' c y   = undefined

-- Lemma. Constants Have Exact Types
{-@ lem_tybc_exact :: g:Env -> b:Bool 
        -> { pf:Subtype | propOf pf == Subtype g (tybc b) (self (tybc b) (Bc b) Base) } @-}
lem_tybc_exact :: Env -> Bool -> Subtype
lem_tybc_exact g b = undefined

{-@ lem_tyic_exact :: g:Env -> n:Int
        -> { pf:Subtype | propOf pf == Subtype g (tyic n) (self (tyic n) (Ic n) Base) } @-}
lem_tyic_exact :: Env -> Int -> Subtype
lem_tyic_exact g n = undefined

-- Lemma. Typing of \delta(c,v) and \delta_T(c,t)
{-@ lem_delta_ty'c :: { c:Prim | not (isPoly c) } -> v:Value -> ProofOf(HasType Empty v (inType c))
        -> ProofOf(HasType Empty (delta c v) (tsubBV v (ty' c))) @-}
lem_delta_ty'c :: Prim -> Expr -> HasType -> HasType
lem_delta_ty'c c v p_v_tx = undefined -- this part we leave as an assumption

{-@ lem_deltaT_ty'c :: { c:Prim | isPoly c } -> t:UserType -> ProofOf(WFType Empty t Base)
        -> ProofOf(HasType Empty (deltaT c t)
                           (tsubBTV t (TFunc (inType c) (ty' c)))) @-}
lem_deltaT_ty'c :: Prim -> Type -> WFType -> HasType
lem_deltaT_ty'c c t p_emp_t = undefined -- this part we leave as an assumption
