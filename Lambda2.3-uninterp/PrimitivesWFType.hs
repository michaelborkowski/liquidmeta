{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesWFType where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness            --(WFFT(..),isWFFT)
import SystemFTyping                    --(HasFType(..),firstBV,inType,ty',refn_pred,ty,erase_ty,
import BasicPropsEnvironments
import WellFormedness                   --(WFType(..),noDefnsInRefns,isWellFormed,makeWFType)
import PrimitivesFTyping                --(isEql)
import Typing

{-@ reflect foo19 @-}
foo19 :: a -> Maybe a
foo19 x = Just x

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

-- Lemma. Constants Have Exact Types
{-@ lem_tybc_exact :: g:Env -> b:Bool 
        -> { pf:Subtype | propOf pf == Subtype g (tybc b) (self (tybc b) (Bc b) Base) &&
                          sizeOf pf == 0 } @-}
lem_tybc_exact :: Env -> Bool -> Subtype
lem_tybc_exact g b = undefined

{-@ lem_tyic_exact :: g:Env -> n:Int
        -> { pf:Subtype | propOf pf == Subtype g (tyic n) (self (tyic n) (Ic n) Base) &&
                          sizeOf pf == 0 } @-}
lem_tyic_exact :: Env -> Int -> Subtype
lem_tyic_exact g n = undefined

