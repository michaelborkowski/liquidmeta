{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesWFTypeAnd where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import SystemFWellFormedness            (WFFT(..))
import SystemFTyping                    (HasFType(..),firstBV,inType,ty',refn_pred,ty,erase_ty,
                                          noDefnsBaseAppT,checkType,synthType)
import WellFormedness                   (WFType(..),noDefnsInRefns,isWellFormed)

{-@ reflect foo09 @-}
foo09 :: a -> Maybe a
foo09 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

{-@ lem_wf_intype_and :: () -> { pf:_ | noDefnsInRefns Empty (inType And) && isWellFormed Empty (inType And) Base } @-}
lem_wf_intype_and :: () -> Proof
lem_wf_intype_and _ = ()

{-@ lem_wf_ty'_and :: y:Int -> { pf:_ | noDefnsInRefns (Cons y (inType And) Empty) 
                                              (unbindT (firstBV And) y (ty' And))
                                 && isWellFormed (Cons y (inType And) Empty) 
                                                 (unbindT (firstBV And) y (ty' And)) Star } @-}
lem_wf_ty'_and :: Int -> Proof
lem_wf_ty'_and y = ()

{-@ lem_wf_ty_and :: () -> { pf:_ | noDefnsInRefns Empty (ty And) && isWellFormed Empty (ty And) Star } @-}
lem_wf_ty_and :: () -> Proof
lem_wf_ty_and _ = () -- ? lem_wf_intype_and () ? lem_wf_ty'_and (firstBV And)
