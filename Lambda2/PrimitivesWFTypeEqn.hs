{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesWFTypeEqn where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFTyping
import WellFormedness

semantics = (\e e' -> Step e e', \e e' -> EvalsTo e e', \e e' -> AppReduced e e')
typing = (TBool, TInt, \g e t -> HasFType g e t, \g t -> WFType g t, \g -> WFEnv g)

{-@ reflect foo13 @-}
foo13 :: a -> Maybe a
foo13 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

{-@ lem_wf_intype_eqn :: n:Int -> { pf:_ | noDefnsInRefns Empty (inType (Eqn n)) 
                                              && isWellFormed Empty (inType (Eqn n)) Base } @-}
lem_wf_intype_eqn :: Int -> Proof
lem_wf_intype_eqn n = ()

{-@ lem_wf_ty'_eqn :: n:Int -> { pf:_ | noDefnsInRefns (Cons (firstBV (Eqn n)) (inType (Eqn n)) Empty) 
                                           (unbindT (firstBV (Eqn n)) (firstBV (Eqn n)) (ty' (Eqn n)))
                                 && isWellFormed (Cons (firstBV (Eqn n)) (inType (Eqn n)) Empty) 
                                      (unbindT (firstBV (Eqn n)) (firstBV (Eqn n)) (ty' (Eqn n))) Star } @-}
lem_wf_ty'_eqn :: Int -> Proof
lem_wf_ty'_eqn n = ()

{-@ lem_wf_ty_eqn :: n:Int -> { pf:_ | noDefnsInRefns Empty (ty (Eqn n)) 
                                          && isWellFormed Empty (ty (Eqn n)) Star } @-}
lem_wf_ty_eqn :: Int -> Proof
lem_wf_ty_eqn n = () ? lem_wf_intype_eqn n ? lem_wf_ty'_eqn n

