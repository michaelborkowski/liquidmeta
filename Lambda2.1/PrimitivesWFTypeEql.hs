{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesWFTypeEql where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness

{-@ reflect foo16 @-}
foo16 :: a -> Maybe a
foo16 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

{-@ lem_wf_intype_eql :: () 
      -> { pf:_ | noDefnsInRefns (ConsT 4 Base Empty) (unbind_tvT 1 4 (inType Eql)) 
               && isWellFormed (ConsT 4 Base Empty) (unbind_tvT 1 4 (inType Eql)) Base } @-}
lem_wf_intype_eql :: () -> Proof
lem_wf_intype_eql _ = ()

{-@ lem_wf_ty'_eql :: ()
      -> { pf:_ | noDefnsInRefns (Cons (firstBV Eql) (unbind_tvT 1 4 (inType Eql)) (ConsT 4 Base Empty))
                      (unbindT (firstBV Eql) (firstBV Eql) (unbind_tvT 1 4 (ty' Eql))) 
               && isWellFormed (Cons (firstBV Eql) (unbind_tvT 1 4 (inType Eql)) (ConsT 4 Base Empty))
                      (unbindT (firstBV Eql) (firstBV Eql) (unbind_tvT 1 4 (ty' Eql))) Star } @-}
lem_wf_ty'_eql :: () -> Proof
lem_wf_ty'_eql _ = () ? lem_wf_intype_eql ()

{-@ lem_wf_ty_inside_eql :: () 
      -> { pf:_ | noDefnsInRefns (ConsT 4 Base Empty) 
                      (TFunc (firstBV Eql) (unbind_tvT 1 4 (inType Eql)) (unbind_tvT 1 4 (ty' Eql))) 
               && isWellFormed (ConsT 4 Base Empty) 
                      (TFunc (firstBV Eql) (unbind_tvT 1 4 (inType Eql)) 
                             (unbind_tvT 1 4 (ty' Eql))) Star } @-}
lem_wf_ty_inside_eql :: () -> Proof
lem_wf_ty_inside_eql _ = () ? lem_wf_intype_eql () ? lem_wf_ty'_eql ()

{-@ lem_wf_ty_eql :: ()
      -> { pf:_ | noDefnsInRefns Empty (ty Eql) && isWellFormed Empty (ty Eql) Star } @-}
lem_wf_ty_eql :: () -> Proof
lem_wf_ty_eql _ = () ? lem_wf_ty_inside_eql ()
