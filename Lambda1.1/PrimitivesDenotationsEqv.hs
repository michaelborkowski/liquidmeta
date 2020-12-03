{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesDenotationsEqv where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFTyping
import WellFormedness
import PrimitivesFTyping
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import Entailments
import PrimitivesSemantics

{-@ reflect foo53 @-}
foo53 x = Just x
foo53 :: a -> Maybe a
  
{-@ lem_den_eqv :: ProofOf(Denotes (ty Eqv) (Prim Eqv)) @-}
lem_den_eqv :: Denotes
lem_den_eqv = DFunc 1 (TRefn TBool 1 (Bc True)) t'
                    (Prim Eqv) (FTPrm FEmpty Eqv) val_den_func 
  where
    val_den_func :: Expr -> Denotes -> ValueDenoted
    val_den_func v_x den_tx_vx = case v_x of 
      (Bc True)  -> ValDen (App (Prim Eqv) (Bc True)) (tsubBV 1 (Bc True) t') (Lambda 1 (BV 1)) 
                      (lem_step_evals (App (Prim Eqv) (Bc True)) (Lambda 1 (BV 1)) 
                      (EPrim Eqv (Bc True))) den_t't_id
      (Bc False) -> ValDen (App (Prim Eqv) (Bc False)) (tsubBV 1 (Bc False) t') (Lambda 1 (App (Prim Not) (BV 1))) 
                      (lem_step_evals (App (Prim Eqv) (Bc False)) (Lambda 1 (App (Prim Not) (BV 1))) 
                      (EPrim Eqv (Bc False))) den_t'f_nt
      _     -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool 1 (Bc True)) den_tx_vx)
    t' = TFunc 2 (TRefn TBool 2 (Bc True)) (TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                   (App (App (Prim Or) (App (App (Prim And) (BV 1)) (BV 2)) )
                        (App (App (Prim And) (App (Prim Not) (BV 1))) (App (Prim Not) (BV 2))))))
    t't = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                   (App (App (Prim Or) (App (App (Prim And) (Bc True)) (BV 2)) )
                        (App (App (Prim And) (App (Prim Not) (Bc True))) (App (Prim Not) (BV 2)))))
    den_t't_id = DFunc 2 (TRefn TBool 2 (Bc True)) t't (Lambda 1 (BV 1)) 
                       (FTAbs FEmpty 1 (FTBasic TBool) (BV 1) 
                              (FTBasic TBool) 1 (FTVar1 FEmpty 1 (FTBasic TBool))) val_den_func2
    val_den_func2 :: Expr -> Denotes -> ValueDenoted
    val_den_func2 v_x den_tx_vx = case v_x of 
      (Bc True)  -> ValDen (App (Lambda 1 (BV 1)) (Bc True)) (tsubBV 2 (Bc True) t't) (Bc True)
                      (lem_step_evals (App (Lambda 1 (BV 1)) (Bc True)) (Bc True) 
                      (EAppAbs 1 (BV 1) (Bc True))) den_t''t_tt
      (Bc False) -> ValDen (App (Lambda 1 (BV 1)) (Bc False)) (tsubBV 2 (Bc False) t't) (Bc False)
                      (lem_step_evals (App (Lambda 1 (BV 1)) (Bc False)) (Bc False) 
                      (EAppAbs 1 (BV 1) (Bc False))) den_t''f_ff
      _          -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool 2 (Bc True)) den_tx_vx)
    t''t = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                   (App (App (Prim Or) (App (App (Prim And) (Bc True)) (Bc True)) )
                        (App (App (Prim And) (App (Prim Not) (Bc True))) (App (Prim Not) (Bc True)))))
    t''f = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                   (App (App (Prim Or) (App (App (Prim And) (Bc True)) (Bc False)) )
                        (App (App (Prim And) (App (Prim Not) (Bc True))) (App (Prim Not) (Bc False)))))
    den_t''t_tt = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                   (App (App (Prim Or) (App (App (Prim And) (Bc True)) (Bc True)) )
                        (App (App (Prim And) (App (Prim Not) (Bc True))) (App (Prim Not) (Bc True)))))
                        (Bc True) (FTBC FEmpty True) eqv_ev_prt''t_tt
    {-@ eqv_ev_prt''t_tt :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc True)) (App (App (Prim Or) (App (App (Prim And) (Bc True)) (Bc True)) ) (App (App (Prim And) (App (Prim Not) (Bc True))) (App (Prim Not) (Bc True))))) (Bc True)) @-}
    eqv_ev_prt''t_tt = reduce_eqv_tt True True
    den_t''f_ff = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                   (App (App (Prim Or) (App (App (Prim And) (Bc True)) (Bc False)) )
                        (App (App (Prim And) (App (Prim Not) (Bc True))) (App (Prim Not) (Bc False)))))
                        (Bc False) (FTBC FEmpty False) eqv_ev_prt''f_ff
    {-@ eqv_ev_prt''f_ff :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc False)) (App (App (Prim Or) (App (App (Prim And) (Bc True)) (Bc False)) ) (App (App (Prim And) (App (Prim Not) (Bc True))) (App (Prim Not) (Bc False))))) (Bc True)) @-}
    eqv_ev_prt''f_ff = reduce_eqv_tt True False

    t'f = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                   (App (App (Prim Or) (App (App (Prim And) (Bc False)) (BV 2)) )
                        (App (App (Prim And) (App (Prim Not) (Bc False))) (App (Prim Not) (BV 2)))))
    den_t'f_nt = DFunc 2 (TRefn TBool 2 (Bc True)) t'f (Lambda 1 (App (Prim Not) (BV 1)))
                       (FTAbs FEmpty 1 (FTBasic TBool)  
                              (App (Prim Not) (BV 1)) (FTBasic TBool) 1 
                              (FTApp (FCons 1 (FTBasic TBool) FEmpty) (Prim Not) (FTBasic TBool)
                                     (FTBasic TBool) (FTPrm (FCons 1 (FTBasic TBool) FEmpty) Not)
                                     (FV 1) (FTVar1 FEmpty 1 (FTBasic TBool))))  val_den_func3
    val_den_func3 :: Expr -> Denotes -> ValueDenoted
    val_den_func3 v_x den_tx_vx = case v_x of 
      (Bc True)  -> ValDen (App (Lambda 1 (App (Prim Not) (BV 1))) (Bc True)) (tsubBV 2 (Bc True) t'f) 
                      (Bc False) (AddStep (App (Lambda 1 (App (Prim Not) (BV 1))) (Bc True)) 
                                          (App (Prim Not) (Bc True)) 
                                          (EAppAbs 1 (App (Prim Not) (BV 1)) (Bc True))
                                          (Bc False) (lem_step_evals (App (Prim Not) (Bc True))
                                                                     (Bc False) (EPrim Not (Bc True))) )
                                          den_t'''t_ff
      (Bc False) -> ValDen (App (Lambda 1 (App (Prim Not) (BV 1))) (Bc False)) (tsubBV 2 (Bc False) t'f) 
                      (Bc True) (AddStep (App (Lambda 1 (App (Prim Not) (BV 1))) (Bc False)) 
                                          (App (Prim Not) (Bc False)) 
                                          (EAppAbs 1 (App (Prim Not) (BV 1)) (Bc False))
                                          (Bc True) (lem_step_evals (App (Prim Not) (Bc False)) 
                                                                    (Bc True) (EPrim Not (Bc False))) )
                                          den_t'''f_tt
      _          -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool 2 (Bc True)) den_tx_vx)
    t'''t = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                   (App (App (Prim Or) (App (App (Prim And) (Bc False)) (Bc True)) )
                        (App (App (Prim And) (App (Prim Not) (Bc False))) (App (Prim Not) (Bc True)))))
    t'''f = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                   (App (App (Prim Or) (App (App (Prim And) (Bc False)) (Bc False)) )
                        (App (App (Prim And) (App (Prim Not) (Bc False))) (App (Prim Not) (Bc False)))))
    den_t'''t_ff = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                   (App (App (Prim Or) (App (App (Prim And) (Bc False)) (Bc True)) )
                        (App (App (Prim And) (App (Prim Not) (Bc False))) (App (Prim Not) (Bc True)))))
                        (Bc False) (FTBC FEmpty False) eqv_ev_prt'''t_ff
    {-@ eqv_ev_prt'''t_ff :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc False)) (App (App (Prim Or) (App (App (Prim And) (Bc False)) (Bc True)) ) (App (App (Prim And) (App (Prim Not) (Bc False))) (App (Prim Not) (Bc True))))) (Bc True)) @-}
    eqv_ev_prt'''t_ff = reduce_eqv_tt False True
    den_t'''f_tt = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                   (App (App (Prim Or) (App (App (Prim And) (Bc False)) (Bc False)) )
                        (App (App (Prim And) (App (Prim Not) (Bc False))) (App (Prim Not) (Bc False)))))
                        (Bc True) (FTBC FEmpty True) eqv_ev_prt'''f_tt
    {-@ eqv_ev_prt'''f_tt :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc True)) (App (App (Prim Or) (App (App (Prim And) (Bc False)) (Bc False)) ) (App (App (Prim And) (App (Prim Not) (Bc False))) (App (Prim Not) (Bc False))))) (Bc True)) @-}
    eqv_ev_prt'''f_tt = reduce_eqv_tt False False
