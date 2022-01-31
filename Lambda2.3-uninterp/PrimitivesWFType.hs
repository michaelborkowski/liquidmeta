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
import WellFormedness                   --(WFType(..),noDefnsInRefns,isWellFormed,makeWFType)
import PrimitivesFTyping                --(isEql)

{-@ reflect foo19 @-}
foo19 :: a -> Maybe a
foo19 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
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
