{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesRefinements where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import Entailments
import LemmasChangeVarWF
import LemmasWeakenWF
import LemmasWellFormedness
import LemmasTyping
import LemmasSubtyping
import LemmasChangeVarTyp
import LemmasWeakenTyp

{-@ reflect foo60 @-}
foo60 x = Just x
foo60 :: a -> Maybe a

{-@ lem_sub_refn_pred_and :: b:Bool -> { pf:_ | subBV 1 (Bc b) (refn_pred And)
                             == App (App (Prim Eqv) (BV 3)) (App (App (Prim And) (Bc b)) (BV 2)) } @-}
lem_sub_refn_pred_and :: Bool -> Proof
lem_sub_refn_pred_and b = ()

{-@ lem_sub_refn_pred_or :: b:Bool -> { pf:_ | subBV 1 (Bc b) (refn_pred Or)
                             == App (App (Prim Eqv) (BV 3)) (App (App (Prim Or) (Bc b)) (BV 2)) } @-}
lem_sub_refn_pred_or :: Bool -> Proof
lem_sub_refn_pred_or b = ()

{-@ lem_sub_refn_pred_not :: b:Bool -> { pf:_ | subBV 2 (Bc b) (refn_pred Not)
                             == App (App (Prim Eqv) (BV 3)) (App (Prim Not) (Bc b)) } @-}
lem_sub_refn_pred_not :: Bool -> Proof
lem_sub_refn_pred_not b = ()

{-@ lem_sub_refn_pred_eqv :: b:Bool -> { pf:_ | subBV 1 (Bc b) (refn_pred Eqv)
                             == App (App (Prim Eqv) (BV 3)) (App (App (Prim Or) 
                                    (App (App (Prim And) (Bc b)) (BV 2)))              
                                    (App (App (Prim And) (App (Prim Not) (Bc b))) (App (Prim Not) (BV 2)))) } @-}
lem_sub_refn_pred_eqv :: Bool -> Proof
lem_sub_refn_pred_eqv b = ()

{-@ lem_sub_refn_pred_leq :: n:Int -> { pf:_ | subBV 1 (Ic n) (refn_pred Leq)
                             == App (App (Prim Eqv) (BV 3)) (App (App (Prim Leq) (Ic n)) (BV 2)) } @-}
lem_sub_refn_pred_leq :: Int -> Proof
lem_sub_refn_pred_leq n = ()

{-@ lem_sub_refn_pred_leqn :: n:Int -> m:Int -> { pf:_ | subBV 2 (Ic m) (refn_pred (Leqn n))
                             == App (App (Prim Eqv) (BV 3)) (App (App (Prim Leq) (Ic n)) (Ic m)) } @-}
lem_sub_refn_pred_leqn :: Int -> Int -> Proof
lem_sub_refn_pred_leqn n m = ()

{-@ lem_sub_refn_pred_eq :: n:Int -> { pf:_ | subBV 1 (Ic n) (refn_pred Eq)
                             == App (App (Prim Eqv) (BV 3)) (App (App (Prim Eq) (Ic n)) (BV 2)) } @-}
lem_sub_refn_pred_eq :: Int -> Proof
lem_sub_refn_pred_eq n = ()

{-@ lem_sub_refn_pred_eqn :: n:Int -> m:Int -> { pf:_ | subBV 2 (Ic m) (refn_pred (Eqn n))
                             == App (App (Prim Eqv) (BV 3)) (App (App (Prim Eq) (Ic n)) (Ic m)) } @-}
lem_sub_refn_pred_eqn :: Int -> Int -> Proof
lem_sub_refn_pred_eqn n m = ()

{-@ lem_sub_refn_pred_eql :: { b:Basic | b == TBool || b == TInt } -> p:Pred
        -> { pf:_ | subBTV 1 (TRefn b 1 p) (refn_pred Eql)
                    == App (App (Prim Eqv) (BV 3)) (App (App (AppT (Prim Eql) (TRefn b 1 p)) (BV 1)) (BV 2)) } @-}
lem_sub_refn_pred_eql :: Basic -> Pred -> Proof
lem_sub_refn_pred_eql b p = ()
