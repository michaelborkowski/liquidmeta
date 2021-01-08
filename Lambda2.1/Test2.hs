{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Test2 where

import Test 

{-@ lem_rvname_equal ::  t:Type  ->  t':Type -> { t'':Type | t'' == t' } @-}
lem_rvname_equal :: Type -> Type -> Type
lem_rvname_equal (TRefn b x p) (TRefn b' y q) = TRefn b' x q
lem_rvname_equal t             t'             = t'  

{-@ lem_rvname_equal' :: { t:Type | isTRefn t} -> { t':Type | isTRefn t' }
        -> { t'':Type | t'' == t' } @-}
lem_rvname_equal' :: Type -> Type -> Type
lem_rvname_equal' (TRefn b x p) (TRefn b' y q) = TRefn b' x q

