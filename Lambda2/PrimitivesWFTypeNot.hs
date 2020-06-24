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
import SystemFTyping
import WellFormedness

semantics = (\e e' -> Step e e', \e e' -> EvalsTo e e', \e e' -> AppReduced e e')
typing = (TBool, TInt, \g e t -> HasFType g e t, \g t -> WFType g t, \g -> WFEnv g)

{-@ reflect foo08 @-}
foo08 :: a -> Maybe a
foo08 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

{-@ lem_wf_intype_not :: { pf:_ | noDefnsInRefns Empty (inType Not) && isWellFormed Empty (inType Not) Base } @-}
lem_wf_intype_not :: Proof
lem_wf_intype_not = ()

{-@ lem_wf_ty'_not :: { pf:_ | noDefnsInRefns (Cons (firstBV Not) (inType Not) Empty) 
                                              (unbindT (firstBV Not) (firstBV Not) (ty' Not))
                                 && isWellFormed (Cons (firstBV Not) (inType Not) Empty) 
                                                 (unbindT (firstBV Not) (firstBV Not) (ty' Not)) Star } @-}
lem_wf_ty'_not :: Proof
lem_wf_ty'_not = ()

{-@ lem_wf_ty_not :: { pf:_ | noDefnsInRefns Empty (ty Not) && isWellFormed Empty (ty Not) Star } @-}
lem_wf_ty_not :: Proof
lem_wf_ty_not = () ? lem_wf_intype_not ? lem_wf_ty'_not

