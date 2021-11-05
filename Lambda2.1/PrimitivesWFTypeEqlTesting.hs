{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{- @ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesWFTypeEqlTesting where

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

{-@ lem_unbind_tv_eql :: a':Vname 
      -> { pf:_ | unbind_tvT 1 a' (inType Eql) == TRefn (FTV a') Z (Bc True) } @-}
lem_unbind_tv_eql :: Vname  -> Proof
lem_unbind_tv_eql a' = () ? ( unbind_tvT 1 a' (inType Eql) 
                          === unbind_tvT 1 a' (TRefn (BTV 1) Z (Bc True))  -- by unfolding inType
                          === TRefn (FTV a') Z (unbind_tv 1 a' (Bc True))  -- by unfolding unbind_tvT
                          === TRefn (FTV a') Z (Bc True) )                 -- by unfolding unbind_tv

{-@ lem_tv_bound_in :: a':Vname -> { pf:_ | tv_bound_in a' Base (ConsT a' Base Empty) } @-}
lem_tv_bound_in :: Vname -> Proof
lem_tv_bound_in a' = () ? ( tv_bound_in a' Base (ConsT a' Base (Empty 
                                                ? (in_env a' Empty === S.member a' (binds Empty))))   
                        === (Base == Base)                              -- by undfolding tv_bound_in
                        === True )

{-@ lem_wf_intype_eql :: a':Vname
      -> { pf:_ | noDefnsInRefns (ConsT a' Base Empty) (unbind_tvT 1 a' (inType Eql)) 
               && isWellFormed (ConsT a' Base Empty) (unbind_tvT 1 a' (inType Eql)) Base } @-}
lem_wf_intype_eql :: Vname  -> Proof
lem_wf_intype_eql a' = () ? ( in_env a' Empty === S.member a' (binds Empty) )
                          ? ( isValue (FV (fresh_var (ConsT a' Base Empty))) )
                          ? ( isTerm  (FV (fresh_var (ConsT a' Base Empty))) )
  ? ( in_envF (fresh_var (ConsT a' Base Empty)) (erase_env (ConsT a' Base Empty))
  === S.member (fresh_var (ConsT a' Base Empty)) (bindsF (erase_env (ConsT a' Base Empty)))
  === S.member (fresh_var (ConsT a' Base Empty)) (binds (ConsT a' Base Empty))
  === in_env (fresh_var (ConsT a' Base Empty)) (ConsT a' Base Empty)
  === False )
  ? ( noDefnsInRefns (ConsT a' Base Empty) (unbind_tvT 1 a' (inType Eql))         ? lem_unbind_tv_eql a'
  === noDefnsInRefns (ConsT a' Base Empty) (TRefn (FTV a') Z (Bc True))          -- by reducing unbind_tvT
  === noDefnsBaseAppT (unbind 0 (fresh_var (ConsT a' Base Empty)) (Bc True))     -- by unfolding noDefnsInRefns
  === noDefnsBaseAppT (subBV 0 (FV (fresh_var (ConsT a' Base Empty))) (Bc True)) -- by unfolding unbind
  === noDefnsBaseAppT (Bc True)                                                  -- by unfolding subBV
  === True )                                                                     -- by unfolding noDefnsBaseAppT
  ? ( isWellFormed (ConsT a' Base Empty) (unbind_tvT 1 a' (inType Eql)) Base     -- ? lem_unbind_tv_eql a'
  === isWellFormed (ConsT a' Base Empty) (TRefn (FTV a') Z (Bc True)) Base       -- by reducing unbind_tvT
        {- evaluate guard: tv_bound_in a' Base (ConsT a' Base Empty) =>* True -}  ? lem_tv_bound_in a'
  === checkType (FCons (fresh_var (ConsT a' Base Empty)) (FTBasic (FTV a')) (erase_env (ConsT a' Base Empty)))
                (unbind 0 (fresh_var (ConsT a' Base Empty)) (Bc True))
                (FTBasic TBool)                                                  -- by unfolding isWellFormed
  === checkType (FCons (fresh_var (ConsT a' Base Empty)) (FTBasic (FTV a')) (erase_env (ConsT a' Base Empty)))
                (subBV 0 (FV (fresh_var (ConsT a' Base Empty))) (Bc True))
                (FTBasic TBool)                                                  -- by unfolding unbind
  === checkType (FCons (fresh_var (ConsT a' Base Empty)) (FTBasic (FTV a')) (erase_env (ConsT a' Base Empty)))
                (Bc True) (FTBasic TBool)                                        -- by unfolding subBV
  === (FTBasic TBool == FTBasic TBool)                                           -- by unfolding checkType
  === True )

