{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesWFTypeNot where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness

{-@ reflect foo09 @-}
foo09 :: a -> Maybe a
foo09 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

{-@ lem_wf_intype_not :: () -> { pf:_ | noDefnsInRefns Empty (inType Not) && isWellFormed Empty (inType Not) Base } @-}
lem_wf_intype_not :: () -> Proof
lem_wf_intype_not _ = ()

{-@ lem_wf_ty'_not :: () -> { pf:_ | noDefnsInRefns (Cons (firstBV Not) (inType Not) Empty) 
                                              (unbindT (firstBV Not) (firstBV Not) (ty' Not))
                                 && isWellFormed (Cons (firstBV Not) (inType Not) Empty) 
                                                 (unbindT (firstBV Not) (firstBV Not) (ty' Not)) Star } @-}
lem_wf_ty'_not :: () -> Proof
lem_wf_ty'_not _ = ()

{-@ lem_wf_ty_not :: () -> { pf:_ | noDefnsInRefns Empty (ty Not) && isWellFormed Empty (ty Not) Star } @-}
lem_wf_ty_not :: () -> Proof
lem_wf_ty_not _ = () ? lem_wf_intype_not () ? lem_wf_ty'_not ()

