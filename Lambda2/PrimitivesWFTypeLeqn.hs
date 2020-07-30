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

{-@ reflect foo11 @-}
foo11 :: a -> Maybe a
foo11 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

{-@ lem_wf_intype_leqn :: n:Int -> { pf:_ | noDefnsInRefns Empty (inType (Leqn n)) 
                                              && isWellFormed Empty (inType (Leqn n)) Base } @-}
lem_wf_intype_leqn :: Int -> Proof
lem_wf_intype_leqn n = ()

{-@ lem_wf_ty'_leqn :: n:Int -> { pf:_ | noDefnsInRefns (Cons (firstBV (Leqn n)) (inType (Leqn n)) Empty) 
                                           (unbindT (firstBV (Leqn n)) (firstBV (Leqn n)) (ty' (Leqn n)))
                                 && isWellFormed (Cons (firstBV (Leqn n)) (inType (Leqn n)) Empty) 
                                      (unbindT (firstBV (Leqn n)) (firstBV (Leqn n)) (ty' (Leqn n))) Star } @-}
lem_wf_ty'_leqn :: Int -> Proof
lem_wf_ty'_leqn n = ()

{-@ lem_wf_ty_leqn :: n:Int -> { pf:_ | noDefnsInRefns Empty (ty (Leqn n)) 
                                          && isWellFormed Empty (ty (Leqn n)) Star } @-}
lem_wf_ty_leqn :: Int -> Proof
lem_wf_ty_leqn n = () ? lem_wf_intype_leqn n ? lem_wf_ty'_leqn n

