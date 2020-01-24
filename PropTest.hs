{-# LANGUAGE GADTs #-}

module STLC where

import Language.Haskell.Liquid.ProofCombinators 

data Expr = N Int                -- 0, 1, 2, ...
          | Add Expr Expr        -- e1 + e2
  deriving (Eq, Show) 

data Value = VNum Int            -- 
  deriving (Eq, Show)

data BStepP where
    BStep :: Expr -> Value -> BStepP

data BStep where
    ENum :: Int -> BStep
    EAdd :: Expr -> Int -> BStep -> Expr -> Int -> BStep -> Int -> BStep

{-@ data BStep where 
    ENum :: v:Int -> Prop(BStep (N v) (VNum v))
 |  EAdd :: e1:Expr -> v1:Int -> Prop(BStep e1 (VNum v1))
              -> e2:Expr -> v2:Int -> Prop(BStep e2 (VNum v2))
              -> { v:Int | v == v1 + v2 } -> Prop(BStep (Add e1 e2) (VNum v)) @-}
