{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesDenotationsOr where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import SameBinders
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import PrimitivesFTyping
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasSubstitution
import Typing
import SystemFAlphaEquivalence
import Entailments
import BasicPropsCSubst
import BasicPropsDenotes
import PrimitivesSemantics

{-@ reflect foo52 @-}
foo52 x = Just x
foo52 :: a -> Maybe a

{-@ lem_den_or :: ProofOf(Denotes (ty Or) (Prim Or)) @-}
lem_den_or :: Denotes
lem_den_or = simpleDFunc 1 (TRefn TBool 1 (Bc True)) t' (Prim Or) (FTPrm FEmpty Or) val_den_func
  where
    val_den_func :: Expr -> Denotes -> ValueDenoted
    val_den_func v_x den_tx_vx = case v_x of 
      (Bc True)  -> ValDen (App (Prim Or) (Bc True)) (tsubBV 1 (Bc True) t') (Lambda 1 (Bc True)) 
                      (lem_step_evals (App (Prim Or) (Bc True)) (Lambda 1 (Bc True)) 
                                      (EPrim Or (Bc True))) den_t't_lamtt -- den_t'f_lamff
      (Bc False) -> ValDen (App (Prim Or) (Bc False)) (tsubBV 1 (Bc False) t') (Lambda 1 (BV 1)) 
                      (lem_step_evals (App (Prim Or) (Bc False)) (Lambda 1 (BV 1)) 
                                      (EPrim Or (Bc False))) den_t'f_id
      _     -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool 1 (Bc True)) den_tx_vx)
    t' = TFunc 2 (TRefn TBool 2 (Bc True)) (TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                                                               (App (App (Prim Or) (BV 1)) (BV 2)) ))

    t't = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Or) (Bc True)) (BV 2)) )
    den_t't_lamtt = simpleDFunc 2 (TRefn TBool 2 (Bc True)) t't (Lambda 1 (Bc True))
                          (FTAbs FEmpty 1 (FTBasic TBool) Base (WFFTBasic FEmpty TBool) (Bc True)
                                 (FTBasic TBool) 1 (FTBC (FCons 1 (FTBasic TBool) FEmpty) True))
                          val_den_func3
    val_den_func3 :: Expr -> Denotes -> ValueDenoted
    val_den_func3 v_x den_tx_vx = case v_x of
      (Bc True)  -> ValDen (App (Lambda 1 (Bc True)) (Bc True)) (tsubBV 2 (Bc True) t't) (Bc True)
                      (lem_step_evals (App (Lambda 1 (Bc True)) (Bc True)) (Bc True) 
                                      (EAppAbs 1 (Bc True) (Bc True))) den_t'''t_tt
      (Bc False) -> ValDen (App (Lambda 1 (Bc True)) (Bc False)) (tsubBV 2 (Bc False) t't) (Bc True)
                      (lem_step_evals (App (Lambda 1 (Bc True)) (Bc False)) (Bc True) 
                                      (EAppAbs 1 (Bc True) (Bc False))) den_t'''f_tt
      _          -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool 2 (Bc True)) den_tx_vx)
    t'''t = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Or) (Bc True)) (Bc True)) )
    t'''f = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Or) (Bc True)) (Bc False)) )
    den_t'''t_tt = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Or) (Bc True)) (Bc True)) )
                        (Bc True) (FTBC FEmpty True) or_ev_prt'''t_tt
    {-@ or_ev_prt'''t_tt :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc True)) (App (App (Prim Or) (Bc True)) (Bc True))) (Bc True)) @-}
    or_ev_prt'''t_tt = reduce_or_tt True True
    den_t'''f_tt = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Or) (Bc True)) (Bc False)) )
                        (Bc True) (FTBC FEmpty True) or_ev_prt'''f_tt
    {-@ or_ev_prt'''f_tt :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc True)) (App (App (Prim Or) (Bc True)) (Bc False))) (Bc True)) @-}
    or_ev_prt'''f_tt = reduce_or_tt True False

    t'f = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Or) (Bc False)) (BV 2)) )
    den_t'f_id = simpleDFunc 2 (TRefn TBool 2 (Bc True)) t'f (Lambda 1 (BV 1)) 
                       (FTAbs FEmpty 1 (FTBasic TBool) Base (WFFTBasic FEmpty TBool) (BV 1) 
                              (FTBasic TBool) 1 (FTVar1 FEmpty 1 (FTBasic TBool)))
                       val_den_func2
    val_den_func2 :: Expr -> Denotes -> ValueDenoted
    val_den_func2 v_x den_tx_vx = case v_x of 
      (Bc True)  -> ValDen (App (Lambda 1 (BV 1)) (Bc True)) (tsubBV 2 (Bc True) t'f) (Bc True)
                      (lem_step_evals (App (Lambda 1 (BV 1)) (Bc True)) (Bc True) 
                      (EAppAbs 1 (BV 1) (Bc True))) den_t''t_tt
      (Bc False) -> ValDen (App (Lambda 1 (BV 1)) (Bc False)) (tsubBV 2 (Bc False) t'f) (Bc False)
                      (lem_step_evals (App (Lambda 1 (BV 1)) (Bc False)) (Bc False) 
                      (EAppAbs 1 (BV 1) (Bc False))) den_t''f_ff
      _          -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool 2 (Bc True)) den_tx_vx)
    t''t = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Or) (Bc False)) (Bc True)) )
    t''f = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Or) (Bc False)) (Bc False)) )
    den_t''t_tt = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Or) (Bc False)) (Bc True)) )
                        (Bc True) (FTBC FEmpty True) or_ev_prt''t_tt
    {-@ or_ev_prt''t_tt :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc True)) (App (App (Prim Or) (Bc False)) (Bc True))) (Bc True)) @-}
    or_ev_prt''t_tt = reduce_or_tt False True
    den_t''f_ff = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Or) (Bc False)) (Bc False)) )
                        (Bc False) (FTBC FEmpty False) or_ev_prt''f_ff
    {-@ or_ev_prt''f_ff :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc False)) (App (App (Prim Or) (Bc False)) (Bc False))) (Bc True)) @-}
    or_ev_prt''f_ff = reduce_or_tt False False

{-@ lem_den_not :: ProofOf(Denotes (ty Not) (Prim Not)) @-}
lem_den_not :: Denotes
lem_den_not = simpleDFunc 2 (TRefn TBool 2 (Bc True)) t'
                    (Prim Not) (FTPrm FEmpty Not) val_den_func
  where
    val_den_func :: Expr -> Denotes -> ValueDenoted
    val_den_func v_x den_tx_vx = case v_x of 
      (Bc True)  -> ValDen (App (Prim Not) (Bc True)) (tsubBV 2 (Bc True) t') (Bc False) 
                      (lem_step_evals (App (Prim Not) (Bc True)) (Bc False) (EPrim Not (Bc True))) den_t't
      (Bc False) -> ValDen (App (Prim Not) (Bc False)) (tsubBV 2 (Bc False) t') (Bc True) 
                      (lem_step_evals (App (Prim Not) (Bc False)) (Bc True) (EPrim Not (Bc False))) den_t'f
      _     -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool 2 (Bc True)) den_tx_vx)
    t'  = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (Prim Not) (BV 2)))
    t't = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (Prim Not) (Bc True)) )
    t'f = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (Prim Not) (Bc False)) )
    den_t't = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (Prim Not) (Bc True)) )
                        (Bc False) (FTBC FEmpty False) ev_prt't
    {-@ ev_prt't :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc False)) (App (Prim Not) (Bc True)) ) (Bc True)) @-}
    ev_prt't = reduce_not_tt True 
    den_t'f = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (Prim Not) (Bc False)) )
                        (Bc True) (FTBC FEmpty True) ev_prt'f 
    {-@ ev_prt'f :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc True)) (App (Prim Not) (Bc False)) ) (Bc True)) @-}
    ev_prt'f = reduce_not_tt False
