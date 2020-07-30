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

--semantics = (\e e' -> Step e e', \e e' -> EvalsTo e e', \e e' -> AppReduced e e')
--typing = (TBool, TInt, \g e t -> HasFType g e t, \g t -> WFType g t, \g -> WFEnv g)

{-@ reflect foo07 @-}
foo07 :: a -> Maybe a
foo07 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

{-@ lem_wf_intype_or :: () -> { pf:_ | noDefnsInRefns Empty (inType Or) && isWellFormed Empty (inType Or) Base } @-}
lem_wf_intype_or :: () -> Proof
lem_wf_intype_or _ = ()

{-@ lem_wf_ty'_or :: () -> { pf:_ | noDefnsInRefns (Cons (firstBV Or) (inType Or) Empty) 
                                              (unbindT (firstBV Or) (firstBV Or) (ty' Or))
                                 && isWellFormed (Cons (firstBV Or) (inType Or) Empty) 
                                                 (unbindT (firstBV Or) (firstBV Or) (ty' Or)) Star } @-}
lem_wf_ty'_or :: () -> Proof
lem_wf_ty'_or _ = ()

{-@ lem_wf_ty_or :: () -> { pf:_ | noDefnsInRefns Empty (ty Or) && isWellFormed Empty (ty Or) Star } @-}
lem_wf_ty_or :: () -> Proof
lem_wf_ty_or _ = () ? lem_wf_intype_or () ? lem_wf_ty'_or ()

