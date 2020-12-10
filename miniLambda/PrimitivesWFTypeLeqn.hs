{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesWFTypeLeqn where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFTyping
import WellFormedness

{-@ reflect foo14 @-}
foo14 :: a -> Maybe a
foo14 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

{-@ lem_wf_intype_leqn :: n:Int -> { pf:_ | noDefnsInRefns Empty (inType (Leqn n)) 
                                              && isWellFormed Empty (inType (Leqn n)) } @-}
lem_wf_intype_leqn :: Int -> Proof
lem_wf_intype_leqn n = ()

{-@ lem_wf_ty'_leqn :: n:Int -> y:Int -> { pf:_ | noDefnsInRefns (Cons y (inType (Leqn n)) Empty) 
                                           (unbindT (firstBV (Leqn n)) y (ty' (Leqn n)))
                                 && isWellFormed (Cons y (inType (Leqn n)) Empty) 
                                      (unbindT (firstBV (Leqn n)) y (ty' (Leqn n))) } @-}
lem_wf_ty'_leqn :: Int -> Int -> Proof
lem_wf_ty'_leqn n y = ()

{-@ lem_wf_ty_leqn :: n:Int -> { pf:_ | noDefnsInRefns Empty (ty (Leqn n)) 
                                          && isWellFormed Empty (ty (Leqn n)) } @-}
lem_wf_ty_leqn :: Int -> Proof
lem_wf_ty_leqn n = () ? lem_wf_intype_leqn n ? lem_wf_ty'_leqn n (firstBV (Leqn n))
