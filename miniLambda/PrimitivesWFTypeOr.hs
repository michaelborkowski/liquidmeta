{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesWFTypeOr where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFTyping
import WellFormedness

{-@ reflect foo10 @-}
foo10 :: a -> Maybe a
foo10 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

{-@ lem_wf_intype_or :: () -> { pf:_ | noDefnsInRefns Empty (inType Or) && isWellFormed Empty (inType Or) } @-}
lem_wf_intype_or :: () -> Proof
lem_wf_intype_or _ = ()

{-@ lem_wf_ty'_or :: y:Int -> { pf:_ | noDefnsInRefns (Cons y (inType Or) Empty) 
                                              (unbindT (firstBV Or) y (ty' Or))
                                 && isWellFormed (Cons y (inType Or) Empty) 
                                                 (unbindT (firstBV Or) y (ty' Or)) } @-}
lem_wf_ty'_or :: Int -> Proof
lem_wf_ty'_or y = ()

{-@ lem_wf_ty_or :: () -> { pf:_ | noDefnsInRefns Empty (ty Or) && isWellFormed Empty (ty Or) } @-}
lem_wf_ty_or :: () -> Proof
lem_wf_ty_or _ = () ? lem_wf_intype_or () ? lem_wf_ty'_or (firstBV Or)
