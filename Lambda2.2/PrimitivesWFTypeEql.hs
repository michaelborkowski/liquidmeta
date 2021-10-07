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

{-@ reflect foo18 @-}
foo18 :: a -> Maybe a
foo18 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

{-@ lem_wf_intype_eql :: a':Vname
      -> { pf:_ | noDefnsInRefns (ConsT a' Base Empty) (unbind_tvT 1 a' (inType Eql)) 
               && isWellFormed (ConsT a' Base Empty) (unbind_tvT 1 a' (inType Eql)) Base } @-}
lem_wf_intype_eql :: Vname  -> Proof
lem_wf_intype_eql a' = ()

{-@ lem_wf_ty'_eql :: a':Vname
      -> { pf:_ | noDefnsInRefns (Cons (fresh_var (ConsT a' Base Empty)) (unbind_tvT 1 a' (inType Eql)) 
                                       (ConsT a' Base Empty))
                      (unbindT (firstBV Eql) (fresh_var (ConsT a' Base Empty)) (unbind_tvT 1 a' (ty' Eql))) 
               && isWellFormed (Cons (fresh_var (ConsT a' Base Empty)) (unbind_tvT 1 a' (inType Eql)) 
                                     (ConsT a' Base Empty))
                      (unbindT (firstBV Eql) (fresh_var (ConsT a' Base Empty)) (unbind_tvT 1 a' (ty' Eql))) Star } @-}
lem_wf_ty'_eql :: Vname -> Proof
lem_wf_ty'_eql a' = () ? lem_wf_intype_eql a'
  where 
    y = fresh_var (ConsT a' Base Empty)

{-@ lem_wf_ty_inside_eql :: a':Vname  
      -> { pf:_ | noDefnsInRefns (ConsT a' Base Empty) 
                      (TFunc (firstBV Eql) (unbind_tvT 1 a' (inType Eql)) (unbind_tvT 1 a' (ty' Eql))) 
               && isWellFormed (ConsT a' Base Empty) 
                      (TFunc (firstBV Eql) (unbind_tvT 1 a' (inType Eql)) 
                             (unbind_tvT 1 a' (ty' Eql))) Star } @-}
lem_wf_ty_inside_eql :: Vname -> Proof
lem_wf_ty_inside_eql a' = () ? lem_wf_intype_eql a' ? lem_wf_ty'_eql a'

{-@ lem_wf_ty_eql :: ()
      -> { pf:_ | noDefnsInRefns Empty (ty Eql) && isWellFormed Empty (ty Eql) Star } @-}
lem_wf_ty_eql :: () -> Proof
lem_wf_ty_eql _ = () ? lem_wf_ty_inside_eql (fresh_var Empty)
