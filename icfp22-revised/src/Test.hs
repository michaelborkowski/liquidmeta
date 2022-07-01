{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Test where

data TTa = Ta0 | Ta1 Int
{-@ data TTa where
        Ta0 :: TTa
        Ta1 :: n:Int -> { v:TTa | n == 2 } @-}

    

{-@ t0 :: { v:TTa | 1 == 2 } @-}
t0 :: TTa
t0 = Ta1 1 
