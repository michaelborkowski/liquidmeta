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

semantics = (\e e' -> Step e e', \e e' -> EvalsTo e e', \e e' -> AppReduced e e')
typing = (TBool, TInt, \g e t -> HasFType g e t, \g t -> WFType g t, \g -> WFEnv g)

{-@ reflect foo10 @-}
foo10 :: a -> Maybe a
foo10 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

{-@ lem_wf_intype_leq :: { pf:_ | noDefnsInRefns Empty (inType Leq) && isWellFormed Empty (inType Leq) Base } @-}
lem_wf_intype_leq :: Proof
lem_wf_intype_leq = ()

{-@ lem_wf_ty'_leq :: { pf:_ | noDefnsInRefns (Cons (firstBV Leq) (inType Leq) Empty) 
                                              (unbindT (firstBV Leq) (firstBV Leq) (ty' Leq))
                                 && isWellFormed (Cons (firstBV Leq) (inType Leq) Empty) 
                                                 (unbindT (firstBV Leq) (firstBV Leq) (ty' Leq)) Star } @-}
lem_wf_ty'_leq :: Proof
lem_wf_ty'_leq = ()

{-@ lem_wf_ty_leq :: { pf:_ | noDefnsInRefns Empty (ty Leq) && isWellFormed Empty (ty Leq) Star } @-}
lem_wf_ty_leq :: Proof
lem_wf_ty_leq = () ? lem_wf_intype_leq ? lem_wf_ty'_leq

