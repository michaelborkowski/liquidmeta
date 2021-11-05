{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesWFTypeEqv where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import SystemFWellFormedness            (WFFT(..))
import SystemFTyping                    (HasFType(..),firstBV,inType,ty',refn_pred,ty,erase_ty,
                                          noDefnsBaseAppT,checkType,synthType)
import WellFormedness                   (WFType(..),noDefnsInRefns,isWellFormed)

{-@ reflect foo12 @-}
foo12 :: a -> Maybe a
foo12 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

{-@ lem_wf_intype_eqv :: () -> { pf:_ | noDefnsInRefns Empty (inType Eqv) && isWellFormed Empty (inType Eqv) Base } @-}
lem_wf_intype_eqv :: () -> Proof
lem_wf_intype_eqv _ = () 

{-@ lem_wf_ty'_eqv :: y:Int -> { pf:_ | noDefnsInRefns (Cons y (inType Eqv) Empty) 
                                              (unbindT (firstBV Eqv) y (ty' Eqv))
                                 && isWellFormed (Cons y (inType Eqv) Empty) 
                                                 (unbindT (firstBV Eqv) y (ty' Eqv)) Star } @-}
lem_wf_ty'_eqv :: Int -> Proof
lem_wf_ty'_eqv y = ()

{-@ lem_wf_ty_eqv :: () -> { pf:_ | noDefnsInRefns Empty (ty Eqv) && isWellFormed Empty (ty Eqv) Star } @-}
lem_wf_ty_eqv :: () -> Proof
lem_wf_ty_eqv _ = () -- ? lem_wf_intype_eqv () ? lem_wf_ty'_eqv (firstBV Eqv)
