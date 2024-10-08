{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesWFTypeLeq where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFTyping
import WellFormedness

{-@ reflect foo13 @-}
foo13 :: a -> Maybe a
foo13 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

{-@ lem_wf_intype_leq :: () -> { pf:_ | noDefnsInRefns Empty (inType Leq) 
                                          && isWellFormed Empty (inType Leq) } @-}
lem_wf_intype_leq :: () -> Proof
lem_wf_intype_leq _ = ()

{-@ lem_wf_ty'_leq :: y:Int -> { pf:_ | noDefnsInRefns (Cons y (inType Leq) Empty) 
                                              (unbindT (firstBV Leq) y (ty' Leq))
                                 && isWellFormed (Cons y (inType Leq) Empty) 
                                                 (unbindT (firstBV Leq) y (ty' Leq)) } @-}
lem_wf_ty'_leq :: Int -> Proof
lem_wf_ty'_leq y = ()

{-@ lem_wf_ty_leq :: () -> { pf:_ | noDefnsInRefns Empty (ty Leq) && isWellFormed Empty (ty Leq) } @-}
lem_wf_ty_leq :: () -> Proof
lem_wf_ty_leq _ = () ? lem_wf_intype_leq () ? lem_wf_ty'_leq (firstBV Leq)
