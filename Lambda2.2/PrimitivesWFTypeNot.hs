{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesWFTypeNot where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import SystemFWellFormedness            (WFFT(..))
import SystemFTyping                    (HasFType(..),firstBV,inType,ty',refn_pred,ty,erase_ty,
                                          noDefnsBaseAppT,checkType,synthType)
import WellFormedness                   (WFType(..),noDefnsInRefns,isWellFormed)

{-@ reflect foo11 @-}
foo11 :: a -> Maybe a
foo11 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

{-@ lem_wf_intype_not :: () -> { pf:_ | noDefnsInRefns Empty (inType Not) && isWellFormed Empty (inType Not) Base } @-}
lem_wf_intype_not :: () -> Proof
lem_wf_intype_not _ = ()

{-@ lem_wf_ty'_not :: y:Int -> { pf:_ | noDefnsInRefns (Cons y (inType Not) Empty) 
                                              (unbindT (firstBV Not) y (ty' Not))
                                 && isWellFormed (Cons y (inType Not) Empty) 
                                                 (unbindT (firstBV Not) y (ty' Not)) Star } @-}
lem_wf_ty'_not :: Int -> Proof
lem_wf_ty'_not y = ()

{-@ lem_wf_ty_not :: () -> { pf:_ | noDefnsInRefns Empty (ty Not) && isWellFormed Empty (ty Not) Star } @-}
lem_wf_ty_not :: () -> Proof
lem_wf_ty_not _ = () -- ? lem_wf_intype_not () ? lem_wf_ty'_not (firstBV Not)
