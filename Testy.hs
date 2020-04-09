{- # LANGUAGE GADTs #-}

--{-@ LIQUID "--higherorder" @-}
{- @ LIQUID "--diff"        @-}
{- @ LIQUID "--no-termination" @-}
{- @ LIQUID "--no-totality" @-}
{- @ LIQUID "--reflection"  @-}
{- @ LIQUID "--ple"         @-}
{- @ LIQUID "--short-names" @-}

module Testy where

--import Control.Exception (assert)
import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)

{-@ lem_bad :: v:Int -> { w:Int | v > 1 } @-}
lem_bad :: Int -> Int
lem_bad y = _y
--  where
--    y = z
      
