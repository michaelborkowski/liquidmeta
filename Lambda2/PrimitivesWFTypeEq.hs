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
import SystemFTyping
import WellFormedness

semantics = (\e e' -> Step e e', \e e' -> EvalsTo e e', \e e' -> AppReduced e e')
typing = (TBool, TInt, \g e t -> HasFType g e t, \g t -> WFType g t, \g -> WFEnv g)

{-@ reflect foo12 @-}
foo12 :: a -> Maybe a
foo12 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

{-@ lem_wf_intype_eq :: { pf:_ | noDefnsInRefns Empty (inType Eq) && isWellFormed Empty (inType Eq) Base } @-}
lem_wf_intype_eq :: Proof
lem_wf_intype_eq = ()

{-@ lem_wf_ty'_eq :: { pf:_ | noDefnsInRefns (Cons (firstBV Eq) (inType Eq) Empty) 
                                              (unbindT (firstBV Eq) (firstBV Eq) (ty' Eq))
                                 && isWellFormed (Cons (firstBV Eq) (inType Eq) Empty) 
                                                 (unbindT (firstBV Eq) (firstBV Eq) (ty' Eq)) Star } @-}
lem_wf_ty'_eq :: Proof
lem_wf_ty'_eq = ()

{-@ lem_wf_ty_eq :: { pf:_ | noDefnsInRefns Empty (ty Eq) && isWellFormed Empty (ty Eq) Star } @-}
lem_wf_ty_eq :: Proof
lem_wf_ty_eq = () ? lem_wf_intype_eq ? lem_wf_ty'_eq

