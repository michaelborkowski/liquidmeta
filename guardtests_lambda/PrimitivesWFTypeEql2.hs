{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesWFTypeEql where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
--import Data.Maybe
import qualified Data.Set as S

import Basics
--import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness

{-@ ignore foo18 @-}
{-@ reflect foo18 @-}
foo18 :: Int -> Maybe Int
foo18 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

{-@ lem_wf_ty_eql :: () -> { pf:_ | isWellFormed Empty (ty Eql) Star } @-}
{-      -> { pf:_ | noDefnsInRefns Empty (ty Eql) && isWellFormed Empty (ty Eql) Star } @-}
lem_wf_ty_eql :: () -> Proof
lem_wf_ty_eql _ = () -- ? lem_wf_ty_inside_eql (fresh_var Empty)
