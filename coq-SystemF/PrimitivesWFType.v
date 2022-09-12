{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module primitivesWFtype where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness            --(WFFT(..),isWFFT)
import SystemFTyping                    --(HasFtype(..),firstBV,intype,ty',refn_pred,ty,erase_ty,
import BasicPropsEnvironments
import WellFormedness                   --(WFtype(..),noDefnsInRefns,isWellFormed,makeWFtype)
import primitivesFTyping                --(isEql)
import Typing

-----------------------------------------------------------------------------
-- | All of our assumptions about BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

-- Constant and primitive Typing Lemmas
-- Lemma. Well-Formedness of Constant types
{-@ lem_wf_tybc :: g:env -> b:Bool -> ProofOf(WFtype g (tybc b) Base) @-}
lem_wf_tybc :: env -> Bool -> WFtype
lem_wf_tybc g b = undefined --makeWFtype g (tybc b) Base

{-@ lem_wf_tyic :: g:env -> n:Int -> ProofOf(WFtype g (tyic n) Base) @-}
lem_wf_tyic :: env -> Int -> WFtype
lem_wf_tyic g n = undefined --makeWFtype g (tyic n) Base

{-@ lem_wf_ty :: c:Prim -> ProofOf(WFtype Empty (ty c) Star) @-}
lem_wf_ty :: Prim -> WFtype
lem_wf_ty c        = undefined

{-@ lem_wf_intype :: { c:Prim | not (isPoly c) } -> ProofOf(WFtype Empty (intype c) Base) @-}
lem_wf_intype :: Prim -> WFtype
lem_wf_intype c    = undefined 

{-@ lem_wf_ty' :: { c:Prim | not (isPoly c) } -> y:vname
        -> ProofOf(WFtype (Cons y (intype c) Empty) (unbindT y (ty' c)) Star) @-}
lem_wf_ty' :: Prim -> Int -> WFtype
lem_wf_ty' c y   = undefined

-- Lemma. Constants Have Exact types
{-@ lem_tybc_exact :: g:env -> b:Bool 
        -> { pf:Subtype | propOf pf == Subtype g (tybc b) (self (tybc b) (Bc b) Base) &&
                          sizeOf pf == 0 } @-}
lem_tybc_exact :: env -> Bool -> Subtype
lem_tybc_exact g b = undefined

{-@ lem_tyic_exact :: g:env -> n:Int
        -> { pf:Subtype | propOf pf == Subtype g (tyic n) (self (tyic n) (Ic n) Base) &&
                          sizeOf pf == 0 } @-}
lem_tyic_exact :: env -> Int -> Subtype
lem_tyic_exact g n = undefined

-- Lemma. Typing of \delta(c,v) and \delta_T(c,t)
{-@ lem_delta_ty'c :: { c:Prim | not (isPoly c) } -> v:Value -> ProofOf(Hastype Empty v (intype c))
        -> ProofOf(Hastype Empty (delta c v) (tsubBV v (ty' c))) @-}
lem_delta_ty'c :: Prim -> expr -> Hastype -> Hastype
lem_delta_ty'c c v p_v_tx = undefined -- this part we leave as an assumption

{-@ lem_deltaT_ty'c :: { c:Prim | isPoly c } -> t:Usertype -> ProofOf(WFtype Empty t Base)
        -> ProofOf(Hastype Empty (deltaT c t)
                           (tsubBTV t (TFunc (intype c) (ty' c)))) @-}
lem_deltaT_ty'c :: Prim -> type -> WFtype -> Hastype
lem_deltaT_ty'c c t p_emp_t = undefined -- this part we leave as an assumption
