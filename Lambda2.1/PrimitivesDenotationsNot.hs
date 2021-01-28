{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesDenotationsNot where

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
import SystemFLemmasWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import PrimitivesSemantics

{-@ reflect foo53 @-}
foo53 x = Just x
foo53 :: a -> Maybe a

{-@ lem_den_not :: () -> ProofOf(Denotes (ty Not) (Prim Not)) @-}
lem_den_not :: () -> Denotes
lem_den_not _ = DFunc 2 (TRefn TBool Z (Bc True)) (ty' Not) (Prim Not) (FTPrm FEmpty Not) val_den_func

{-@ val_den_func :: v_x:Value -> ProofOf(Denotes (TRefn TBool Z (Bc True)) v_x)
                              -> ProofOf(ValueDenoted (App (Prim Not) v_x) (tsubBV 2 v_x (ty' Not))) @-}
val_den_func :: Expr -> Denotes -> ValueDenoted
val_den_func v_x den_tx_vx = case v_x of 
    (Bc True)  -> ValDen (App (Prim Not) (Bc True)) (tsubBV 2 (Bc True) t') (Bc False) 
                         (lem_step_evals (App (Prim Not) (Bc True)) (Bc False) 
                                         (EPrim Not (Bc True))) den_t't
    (Bc False) -> ValDen (App (Prim Not) (Bc False)) (tsubBV 2 (Bc False) t') (Bc True) 
                         (lem_step_evals (App (Prim Not) (Bc False)) (Bc True) 
                                         (EPrim Not (Bc False))) den_t'f
    _     -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool Z (Bc True)) den_tx_vx)
  where
    t'  = ty' Not
    {- @ den_t't :: ProofOf(Denotes (tsubBV 2 (Bc True) (ty' Not)) (Bc False)) @-}
    den_t't = DRefn TBool Z p't (Bc False) (FTBC FEmpty False) ev_prt't
    {-@ ev_prt't :: ProofOf(EvalsTo (subBV 0 (Bc False) p't) (Bc True)) @-}
    ev_prt't = reduce_not_tt True 
    p't = subBV 2 (Bc True)  (refn_pred Not)
    {- @ den_t'f :: ProofOf(Denotes (tsubBV 2 (Bc False) (ty' Not)) (Bc True)) @-}
    den_t'f = DRefn TBool Z p'f (Bc True) (FTBC FEmpty True) ev_prt'f
    {-@ ev_prt'f :: ProofOf(EvalsTo (subBV 0 (Bc True)  p'f) (Bc True)) @-}
    ev_prt'f = reduce_not_tt False
    p'f = subBV 2 (Bc False) (refn_pred Not)
{-{-@ den_t't :: ProofOf(Denotes (tsubBV 2 (Bc True) (ty' Not)) (Bc False)) @-}
den_t't :: Denotes
den_t't = DRefn TBool Z p't (Bc False) (FTBC FEmpty False) ev_prt't
  where
    {-@ ev_prt't :: ProofOf(EvalsTo (subBV 0 (Bc False) p't) (Bc True)) @-}
    ev_prt't = reduce_not_tt True 
    p't = subBV 2 (Bc True)  (refn_pred Not)
    
{-@ den_t'f :: ProofOf(Denotes (tsubBV 2 (Bc False) (ty' Not)) (Bc True)) @-}
den_t'f :: Denotes
den_t'f = DRefn TBool Z p'f (Bc True) (FTBC FEmpty True) ev_prt'f
  where
    {-@ ev_prt'f :: ProofOf(EvalsTo (subBV 0 (Bc True)  p'f) (Bc True)) @-}
    ev_prt'f = reduce_not_tt False
    p'f = subBV 2 (Bc False) (refn_pred Not)-}
