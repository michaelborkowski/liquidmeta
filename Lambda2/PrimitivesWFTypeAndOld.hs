{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-} 
{- @ LIQUID "--no-totality" @-} 
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesWFTypeAndOld where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFTyping
import WellFormedness

semantics = (\e e' -> Step e e', \e e' -> EvalsTo e e', \e e' -> AppReduced e e')
typing = (TBool, TInt, \g e t -> HasFType g e t, \g t -> WFType g t, \g -> WFEnv g)
--semantics = (Step, EvalsTo, AppReduced)
--typing = (TBool, TInt, HasFType, WFType, WFEnv)

{-@ reflect foo06 @-}
foo06 :: a -> Maybe a
foo06 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

{-@ lem_wf_intype_and :: { pf:_ | noDefnsInRefns Empty (inType And) && isWellFormed Empty (inType And) Base } @-}
lem_wf_intype_and :: Proof
lem_wf_intype_and = ()

{-@ lem_wf_ty'_and :: { pf:_ | noDefnsInRefns (Cons (firstBV And) (inType And) Empty) 
                                              (unbindT (firstBV And) (firstBV And) (ty' And))
                                 && isWellFormed (Cons (firstBV And) (inType And) Empty) 
                                                 (unbindT (firstBV And) (firstBV And) (ty' And)) Star } @-}
lem_wf_ty'_and :: Proof
lem_wf_ty'_and = ()

{-@ lem_wf_ty_and :: { pf:_ | noDefnsInRefns Empty (ty And) && isWellFormed Empty (ty And) Star } @-}
lem_wf_ty_and :: Proof
lem_wf_ty_and = () ? lem_wf_intype_and ? lem_wf_ty'_and 

