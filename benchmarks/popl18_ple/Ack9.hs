
-- | Proving ackermann properties from
-- | http://www.cs.yorku.ca/~gt/papers/Ackermann-function.pdf

{- @ LIQUID "--higherorder"     @-}
{-@ LIQUID "--ple" @-}


module Ackermann where

--import Language.Haskell.Liquid.ProofCombinators

-- | First ackermann definition

{-@ axiomatize ack @-}
{-@ ack :: n:Nat -> x:Nat -> Nat / [n, x] @-}
ack :: Int -> Int -> Int
ack n x     | n == 0        = x + 2
            | x == 0        = 2
            | otherwise     = ack (n-1) (ack n (x-1))

{-@ lemma9_helper  :: x:Nat -> { l:Int | l < x + 2 }
            -> { pf:_ | x + l < ack 1 x } @-}
lemma9_helper :: Int -> Int -> () -- Proof
lemma9_helper x l  | x == 0   = () --ack 1 0 === 2 *** QED
                   | x > 0    = lemma9_helper (x-1) (l-1)   -- FAIL with interpreter

