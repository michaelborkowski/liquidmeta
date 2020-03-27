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
    ENum :: w:Int -> Prop(BStep (N w) (VNum w))
 |  EAdd :: e1:Expr -> v1:Int -> Prop(BStep e1 (VNum v1))
              -> e2:Expr -> v2:Int -> Prop(BStep e2 (VNum v2))
              -> { w:Int | w == v1 + v2 } -> Prop(BStep (Add e1 e2) (VNum w)) @-}

{-@ lem_unpack1 :: m:Int -> n:Int 
        -> ( q'::{ q:Int | q == m + n }, { pf:BStep | prop pf == BStep (Add (N m) (N n)) (VNum q')})
        -> { r:Int | r == m + n } @-}
lem_unpack1 :: Int -> Int -> (Int, BStep) -> Int
lem_unpack1 m n (q, step) = q

{-@ lem_unpack2 :: m:Int -> n:Int 
        -> tup:( q'::{ q:Int | q == m + n }, { pf:BStep | prop pf == BStep (Add (N m) (N n)) (VNum q')})
        -> { outpf:BStep | prop outpf == BStep (Add (N m) (N n)) (VNum (fst tup))}  @-}
lem_unpack2 :: Int -> Int -> (Int, BStep) -> BStep
lem_unpack2 m n (q, step) = step
