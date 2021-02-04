{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple-local"   @-}
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
lem_den_not _ = DFunc 2 (TRefn TBool Z (Bc True)) (ty' Not) (Prim Not ? val_not) 
                      (FTPrm FEmpty Not ? er_not) val_den_func ? ty_not
  where
    er_not    = toProof ( erase_ty Not === erase (ty Not) ? ty_not
                                       === erase (TFunc 2   (TRefn TBool   Z (Bc True))  (ty' Not)) )
    ty_not    = toProof ( ty Not === TFunc (firstBV Not)      (inType Not)  (ty' Not)
                                 === TFunc 2   (TRefn TBool   Z (Bc True))  (ty' Not) )
    val_not   = toProof ( isValue (Prim Not) === True ) ? toProof ( isTerm (Prim Not) === True )

{-@ val_den_func :: v_x:Value -> ProofOf(Denotes (TRefn TBool Z (Bc True)) v_x)
                              -> ProofOf(ValueDenoted (App (Prim Not) v_x) (tsubBV 2 v_x (ty' Not))) @-}
val_den_func :: Expr -> Denotes -> ValueDenoted
val_den_func v_x den_tx_vx = case v_x of 
    (Bc True)  -> ValDen (App (Prim Not) (Bc True)) (tsubBV 2 (Bc True) t') (Bc False ? val_f) 
                         (lem_step_evals (App (Prim Not) (Bc True)) (Bc False ? val_f) 
                                         (EPrim Not (Bc True ? comp_t) ? del_t )) den_t't
    (Bc False) -> ValDen (App (Prim Not) (Bc False)) (tsubBV 2 (Bc False) t') (Bc True ? val_t) 
                         (lem_step_evals (App (Prim Not) (Bc False)) (Bc True) 
                                         (EPrim Not (Bc False ? comp_f) ? del_f )) den_t'f
    _     -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool Z (Bc True) ? er_bool) den_tx_vx)
  where
    t'  = ty' Not
    {- @ den_t't :: ProofOf(Denotes (tsubBV 2 (Bc True) (ty' Not)) (Bc False)) @-}
    den_t't = DRefn TBool Z p't (Bc False) (FTBC FEmpty False) ev_prt't
    p't = subBV 2 (Bc True ? val_t)  (refn_pred Not)
    {- @ den_t'f :: ProofOf(Denotes (tsubBV 2 (Bc False) (ty' Not)) (Bc True)) @-}
    den_t'f = DRefn TBool Z p'f (Bc True ? val_t) (FTBC FEmpty True) ev_prt'f
    p'f = subBV 2 (Bc False ? val_f) (refn_pred Not)

    comp_f    = toProof ( isCompat Not (Bc False) === True )
    comp_t    = toProof ( isCompat Not (Bc True)  === True )
    del_f     = toProof ( delta Not (Bc False ? comp_f) === Bc True )
    del_t     = toProof ( delta Not (Bc True  ? comp_t)  === Bc False )
    val_f     = toProof ( isValue (Bc False) === True ) ? toProof ( isTerm (Bc False) === True )
    val_t     = toProof ( isValue (Bc True)  === True ) ? toProof ( isTerm (Bc True)  === True )
    er_bool   = toProof ( erase (TRefn TBool Z (Bc True)) === FTBasic TBool )

{-@ ple ev_prt't @-}
{-@ ev_prt't :: ProofOf(EvalsTo (subBV 0 (Bc False) (subBV 2 (Bc True) (refn_pred Not))) (Bc True)) @-}
ev_prt't :: EvalsTo
ev_prt't = reduce_not_tt True 
  
{-@ ple ev_prt'f @-}  
{-@ ev_prt'f :: ProofOf(EvalsTo (subBV 0 (Bc True) (subBV 2 (Bc False) (refn_pred Not))) (Bc True)) @-}
ev_prt'f :: EvalsTo
ev_prt'f = reduce_not_tt False
