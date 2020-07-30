{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesWFTypeEqv where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFTyping
import WellFormedness

{-semantics = (\e e' -> Step e e', \e e' -> EvalsTo e e', \e e' -> AppReduced e e')
typing = (TBool, TInt, \g e t -> HasFType g e t, \g t -> WFType g t, \g -> WFEnv g) -}

{-@ reflect foo09 @-}
foo09 :: a -> Maybe a
foo09 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

{-@ lem_wf_intype_eqv :: () -> { pf:_ | noDefnsInRefns Empty (inType Eqv) && isWellFormed Empty (inType Eqv) Base } @-}
lem_wf_intype_eqv :: () -> Proof
lem_wf_intype_eqv _ = () {-noDefnsInRefns Empty (inType Eqv)
                  === noDefnsInRefns Empty (TRefn TBool 1 (Bc True))
                  === noDefns (unbind 1 (fresh_var Empty) (Bc True))
--                  ? toProof (isValue (FV (fresh_var Empty)) === True)
                  === noDefns (subBV 1 (FV (fresh_var Empty) ? toProof (isValue (FV (fresh_var Empty)))) (Bc True))
                  === noDefns (Bc True)
                  === True *** QED -}


{-@ lem_wf_ty'_eqv :: () -> { pf:_ | noDefnsInRefns (Cons (firstBV Eqv) (inType Eqv) Empty) 
                                              (unbindT (firstBV Eqv) (firstBV Eqv) (ty' Eqv))
                                 && isWellFormed (Cons (firstBV Eqv) (inType Eqv) Empty) 
                                                 (unbindT (firstBV Eqv) (firstBV Eqv) (ty' Eqv)) Star } @-}
lem_wf_ty'_eqv :: () -> Proof
lem_wf_ty'_eqv _ = ()


{-@ lem_wf_ty_eqv :: () -> { pf:_ | noDefnsInRefns Empty (ty Eqv) && isWellFormed Empty (ty Eqv) Star } @-}
lem_wf_ty_eqv :: () -> Proof
lem_wf_ty_eqv _ = () ? lem_wf_intype_eqv () ? lem_wf_ty'_eqv ()

