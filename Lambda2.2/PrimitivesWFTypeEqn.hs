{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesWFTypeEqn where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import SystemFWellFormedness            (WFFT(..))
import SystemFTyping                    (HasFType(..),firstBV,inType,ty',refn_pred,ty,erase_ty,
                                          noDefnsBaseAppT,checkType,synthType)
import WellFormedness                   (WFType(..),noDefnsInRefns,isWellFormed)

{-@ reflect foo16 @-}
foo16 :: a -> Maybe a
foo16 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

{-@ lem_wf_intype_eqn :: n:Int -> { pf:_ | noDefnsInRefns Empty (inType (Eqn n)) 
                                              && isWellFormed Empty (inType (Eqn n)) Base } @-}
lem_wf_intype_eqn :: Int -> Proof
lem_wf_intype_eqn n = ()

{-@ lem_wf_ty'_eqn :: n:Int -> y:Int -> { pf:_ | noDefnsInRefns (Cons y (inType (Eqn n)) Empty) 
                                           (unbindT (firstBV (Eqn n)) y (ty' (Eqn n)))
                                 && isWellFormed (Cons y (inType (Eqn n)) Empty) 
                                      (unbindT (firstBV (Eqn n)) y (ty' (Eqn n))) Star } @-}
lem_wf_ty'_eqn :: Int -> Int -> Proof
lem_wf_ty'_eqn n y = ()

{-@ lem_wf_ty_eqn :: n:Int -> { pf:_ | noDefnsInRefns Empty (ty (Eqn n)) 
                                          && isWellFormed Empty (ty (Eqn n)) Star } @-}
lem_wf_ty_eqn :: Int -> Proof
lem_wf_ty_eqn n = () -- ? lem_wf_intype_eqn n ? lem_wf_ty'_eqn n (firstBV (Eqn n))
