{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--fuel=8"      @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesDenotationsOr where

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

{-@ reflect foo52 @-}
foo52 x = Just x
foo52 :: a -> Maybe a

--{-@ reflect (ty' Or) @-}
--(ty' Or) :: Type
--(ty' Or) = TFunc 2 (TRefn TBool Z (Bc True)) (TRefn TBool Z (App (App (Prim Eqv) (BV 0))
--                                                         (App (App (Prim Or) (BV 1)) (BV 2)) ))
--
--{-@ reflect t'orb @-}
--t'orb :: Bool -> Type
--t'orb b = TRefn TBool Z (App (App (Prim Eqv) (BV 0)) (App (App (Prim Or) (Bc b)) (BV 2)) )

{-@ lem_den_or :: ProofOf(Denotes (ty Or) (Prim Or)) @-}
lem_den_or :: Denotes
lem_den_or = DFunc 1 (TRefn TBool Z (Bc True)) (ty' Or) (Prim Or ? val_or) 
                   (FTPrm FEmpty Or) val_den_func_or
  where
    val_or  = isValue (Prim Or) ? isTerm (Prim Or)  

{-@ val_den_func_or :: v_x:Value -> ProofOf(Denotes (TRefn TBool Z (Bc True)) v_x)
                                 -> ProofOf(ValueDenoted (App (Prim Or) v_x) (tsubBV 1 v_x (ty' Or))) @-}
val_den_func_or :: Expr -> Denotes -> ValueDenoted
val_den_func_or v_x den_tx_vx = case v_x of 
      (Bc True)  -> ValDen (App (Prim Or) (Bc True)) (tsubBV 1 (Bc True) (ty' Or)) (Lambda 1 (Bc True)) 
                      (lem_step_evals (App (Prim Or) (Bc True)) (Lambda 1 (Bc True)) 
                                      (EPrim Or (Bc True))) den_t'ort_lamtt 
      (Bc False) -> ValDen (App (Prim Or) (Bc False)) (tsubBV 1 (Bc False) (ty' Or)) (Lambda 1 (BV 1)) 
                      (lem_step_evals (App (Prim Or) (Bc False)) (Lambda 1 (BV 1)) 
                                      (EPrim Or (Bc False))) den_t'orf_id
      _     -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool Z (Bc True)) den_tx_vx)

{-@ den_t'ort_lamtt :: ProofOf(Denotes (tsubBV 1 (Bc True) (ty' Or)) (Lambda 1 (Bc True))) @-}
den_t'ort_lamtt :: Denotes
den_t'ort_lamtt = DFunc 2 (TRefn TBool Z (Bc True)) t'or_t (Lambda 1 (Bc True))
                      (FTAbs FEmpty 1 (FTBasic TBool) Base (WFFTBasic FEmpty TBool) (Bc True)
                             (FTBasic TBool) 1 (FTBC (FCons 1 (FTBasic TBool) FEmpty) True))
                      val_den_func_or3
  where
    t'or_t    = tsubBV 1 (Bc True) (TRefn TBool Z (refn_pred Or))

{-@ val_den_func_or3 :: v_x:Value -> ProofOf(Denotes (TRefn TBool Z (Bc True)) v_x)
      -> ProofOf(ValueDenoted (App (Lambda 1 (Bc True)) v_x) 
                              (tsubBV 2 v_x (tsubBV 1 (Bc True) (TRefn TBool Z (refn_pred Or))))) @-}
val_den_func_or3 :: Expr -> Denotes -> ValueDenoted
val_den_func_or3 v_x den_tx_vx = case v_x of
      (Bc True)  -> ValDen (App (Lambda 1 (Bc True)) (Bc True)) (tsubBV 2 (Bc True) t'or_t) (Bc True ? val_t)
                      (lem_step_evals (App (Lambda 1 (Bc True)) (Bc True)) (Bc True) 
                                      (EAppAbs 1 (Bc True) (Bc True))) den_t'''t_tt
      (Bc False) -> ValDen (App (Lambda 1 (Bc True)) (Bc False)) (tsubBV 2 (Bc False) t'or_t) (Bc True ? val_t)
                      (lem_step_evals (App (Lambda 1 (Bc True)) (Bc False)) (Bc True) 
                                      (EAppAbs 1 (Bc True) (Bc False))) den_t'''f_tt
      _          -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool Z (Bc True)) den_tx_vx) 
  where
    t'or_t       = tsubBV 1 (Bc True) (TRefn TBool Z (refn_pred Or))
    den_t'''t_tt = DRefn TBool Z p'''t (Bc True) (FTBC FEmpty True) or_ev_prt'''t_tt
    p'''t        = subBV 2 (Bc True ? val_t)  (subBV 1 (Bc True ? val_t) (refn_pred Or))
    den_t'''f_tt = DRefn TBool Z p'''f (Bc True) (FTBC FEmpty True) or_ev_prt'''f_tt
    p'''f        = subBV 2 (Bc False ? val_f) (subBV 1 (Bc True ? val_f) (refn_pred Or))
    val_t        = isValue (Bc True)   ? isTerm (Bc True)
    val_f       = isValue (Bc False)  ? isTerm (Bc False)

{-@ or_ev_prt'''t_tt :: ProofOf(EvalsTo (subBV 0 (Bc True) (subBV 2 (Bc True)  (subBV 1 (Bc True) (refn_pred Or)))) (Bc True)) @-}
or_ev_prt'''t_tt :: EvalsTo
or_ev_prt'''t_tt = reduce_or_tt True True ? blOr True True

{-@ or_ev_prt'''f_tt :: ProofOf(EvalsTo (subBV 0 (Bc True) (subBV 2 (Bc False) (subBV 1 (Bc True) (refn_pred Or)))) (Bc True)) @-}
or_ev_prt'''f_tt :: EvalsTo    
or_ev_prt'''f_tt = reduce_or_tt True False ? blOr True False

{-@ den_t'orf_id :: ProofOf(Denotes (tsubBV 1 (Bc False) (ty' Or)) (Lambda 1 (BV 1))) @-}
den_t'orf_id :: Denotes
den_t'orf_id = DFunc 2 (TRefn TBool Z (Bc True)) t'or_f (Lambda 1 (BV 1)) 
                   (FTAbs FEmpty 1 (FTBasic TBool) Base (WFFTBasic FEmpty TBool) (BV 1) 
                          (FTBasic TBool) 1 (FTVar1 FEmpty 1 (FTBasic TBool))) val_den_func_or2
  where
    t'or_f       = tsubBV 1 (Bc False) (TRefn TBool Z (refn_pred Or))

{-@ val_den_func_or2 :: v_x:Value -> ProofOf(Denotes (TRefn TBool Z (Bc True)) v_x)
      -> ProofOf(ValueDenoted (App (Lambda 1 (BV 1)) v_x) 
                              (tsubBV 2 v_x (tsubBV 1 (Bc False) (TRefn TBool Z (refn_pred Or))))) @-}
val_den_func_or2 :: Expr -> Denotes -> ValueDenoted
val_den_func_or2 v_x den_tx_vx = case v_x of 
      (Bc True)  -> ValDen (App (Lambda 1 (BV 1)) (Bc True)) (tsubBV 2 (Bc True) t'or_f) (Bc True ? val_t)
                      (lem_step_evals (App (Lambda 1 (BV 1)) (Bc True)) (Bc True) 
                      (EAppAbs 1 (BV 1) (Bc True))) den_t''t_tt
      (Bc False) -> ValDen (App (Lambda 1 (BV 1)) (Bc False)) (tsubBV 2 (Bc False) t'or_f) (Bc False ? val_f)
                      (lem_step_evals (App (Lambda 1 (BV 1)) (Bc False)) (Bc False) 
                      (EAppAbs 1 (BV 1) (Bc False))) den_t''f_ff
      _          -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool Z (Bc True)) den_tx_vx)
  where
    t'or_f      = tsubBV 1 (Bc False) (TRefn TBool Z (refn_pred Or))
    den_t''t_tt = DRefn TBool Z p''t (Bc True) (FTBC FEmpty True) (reduce_or_tt False True ? blOr False True)
    p''t        = subBV 2 (Bc True ? val_t)  (subBV 1 (Bc False ? val_f) (refn_pred Or))
    den_t''f_ff = DRefn TBool Z p''f (Bc False) (FTBC FEmpty False) or_ev_prt''f_ff
    p''f        = subBV 2 (Bc False ? val_f) (subBV 1 (Bc False ? val_f) (refn_pred Or))
    val_f       = isValue (Bc False)  ? isTerm (Bc False)
    val_t       = isValue (Bc True)   ? isTerm (Bc True)
 
{-@ or_ev_prt''f_ff :: ProofOf(EvalsTo (subBV 0 (Bc False) (subBV 2 (Bc False) (subBV 1 (Bc False) (refn_pred Or)))) (Bc True)) @-}
or_ev_prt''f_ff :: EvalsTo
or_ev_prt''f_ff = reduce_or_tt False False ? blOr False False
