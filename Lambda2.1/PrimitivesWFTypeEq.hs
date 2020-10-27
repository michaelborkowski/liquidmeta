{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesWFTypeEq where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness

{-@ reflect foo13 @-}
foo13 :: a -> Maybe a
foo13 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

{-@ lem_wf_intype_eq :: () -> { pf:_ | noDefnsInRefns Empty (inType Eq) 
                                         && isWellFormed Empty (inType Eq) Base } @-}
lem_wf_intype_eq :: () -> Proof
lem_wf_intype_eq _ = ()

{-@ lem_wf_ty'_eq :: y:Int -> { pf:_ | noDefnsInRefns (Cons y (inType Eq) Empty) 
                                              (unbindT (firstBV Eq) y (ty' Eq))
                                 && isWellFormed (Cons y (inType Eq) Empty) 
                                                 (unbindT (firstBV Eq) y (ty' Eq)) Star } @-}
lem_wf_ty'_eq :: Int -> Proof
lem_wf_ty'_eq y = ()

{-@ lem_wf_ty_eq :: () -> { pf:_ | noDefnsInRefns Empty (ty Eq) && isWellFormed Empty (ty Eq) Star } @-}
lem_wf_ty_eq :: () -> Proof
lem_wf_ty_eq _ = () ? lem_wf_intype_eq () ? lem_wf_ty'_eq (firstBV Eq)

