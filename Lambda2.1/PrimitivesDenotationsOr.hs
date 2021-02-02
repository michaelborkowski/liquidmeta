{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--fuel=1"      @-}
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

{-@ reflect t'_or @-}
t'_or :: Type
t'_or = TFunc 2 (TRefn TBool Z (Bc True)) (TRefn TBool Z (App (App (Prim Eqv) (BV 0))
                                                         (App (App (Prim Or) (BV 1)) (BV 2)) ))

{-@ reflect t'orb @-}
t'orb :: Bool -> Type
t'orb b = TRefn TBool Z (App (App (Prim Eqv) (BV 0)) (App (App (Prim Or) (Bc b)) (BV 2)) )

{-@ lem_den_or :: ProofOf(Denotes (ty Or) (Prim Or)) @-}
lem_den_or :: Denotes
lem_den_or = DFunc 1 (TRefn TBool Z (Bc True)) t'_or (Prim Or) (FTPrm FEmpty Or) val_den_func_or
  
{-@ val_den_func_or :: v_x:Value -> ProofOf(Denotes (TRefn TBool Z (Bc True)) v_x)
                                 -> ProofOf(ValueDenoted (App (Prim Or) v_x) (tsubBV 1 v_x t'_or)) @-}
val_den_func_or :: Expr -> Denotes -> ValueDenoted
val_den_func_or v_x den_tx_vx = case v_x of 
      (Bc True)  -> ValDen (App (Prim Or) (Bc True)) (tsubBV 1 (Bc True) t'_or) (Lambda 1 (Bc True)) 
                      (lem_step_evals (App (Prim Or) (Bc True)) (Lambda 1 (Bc True)) 
                                      (EPrim Or (Bc True))) den_t'ort_lamtt 
      (Bc False) -> ValDen (App (Prim Or) (Bc False)) (tsubBV 1 (Bc False) t'_or) (Lambda 1 (BV 1)) 
                      (lem_step_evals (App (Prim Or) (Bc False)) (Lambda 1 (BV 1)) 
                                      (EPrim Or (Bc False))) den_t'orf_id
      _     -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool Z (Bc True)) den_tx_vx)

{-@ den_t'ort_lamtt :: ProofOf(Denotes (tsubBV 1 (Bc True) t'_or) (Lambda 1 (Bc True))) @-}
den_t'ort_lamtt :: Denotes
den_t'ort_lamtt = DFunc 2 (TRefn TBool Z (Bc True)) (t'orb True) (Lambda 1 (Bc True))
                      (FTAbs FEmpty 1 (FTBasic TBool) Base (WFFTBasic FEmpty TBool) (Bc True)
                             (FTBasic TBool) 1 (FTBC (FCons 1 (FTBasic TBool) FEmpty) True))
                      val_den_func_or3

{-@ val_den_func_or3 :: v_x:Value -> ProofOf(Denotes (TRefn TBool Z (Bc True)) v_x)
                          -> ProofOf(ValueDenoted (App (Lambda 1 (Bc True)) v_x) (tsubBV 2 v_x (t'orb True))) @-}
val_den_func_or3 :: Expr -> Denotes -> ValueDenoted
val_den_func_or3 v_x den_tx_vx = case v_x of
      (Bc True)  -> ValDen (App (Lambda 1 (Bc True)) (Bc True)) (tsubBV 2 (Bc True) (t'orb True)) (Bc True)
                      (lem_step_evals (App (Lambda 1 (Bc True)) (Bc True)) (Bc True) 
                                      (EAppAbs 1 (Bc True) (Bc True))) den_t'''t_tt
      (Bc False) -> ValDen (App (Lambda 1 (Bc True)) (Bc False)) (tsubBV 2 (Bc False) (t'orb True)) (Bc True)
                      (lem_step_evals (App (Lambda 1 (Bc True)) (Bc False)) (Bc True) 
                                      (EAppAbs 1 (Bc True) (Bc False))) den_t'''f_tt
      _          -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool Z (Bc True)) den_tx_vx) 

{-@ den_t'''t_tt :: ProofOf(Denotes (tsubBV 2 (Bc True) (t'orb True)) (Bc True)) @-}
den_t'''t_tt :: Denotes    
den_t'''t_tt = DRefn TBool Z p'''t (Bc True) (FTBC FEmpty True) or_ev_prt'''t_tt
  where
    or_ev_prt'''t_tt = reduce_or_tt True True
    {-@ p'''t :: { p:Pred | p == subBV 2 (Bc True) (subBV 1 (Bc True) (refn_pred Or)) } @-}
    p'''t = App (App (Prim Eqv) (BV 0)) (App (App (Prim Or) (Bc True)) (Bc True))

{-@ den_t'''f_tt :: ProofOf(Denotes (tsubBV 2 (Bc False) (t'orb True)) (Bc True)) @-}
den_t'''f_tt :: Denotes
den_t'''f_tt = DRefn TBool Z p'''f (Bc True) (FTBC FEmpty True) or_ev_prt'''f_tt
  where
    or_ev_prt'''f_tt = reduce_or_tt True False
    {-@ p'''f :: { p:Pred | p == subBV 2 (Bc False) (subBV 1 (Bc True) (refn_pred Or)) } @-}
    p'''f = App (App (Prim Eqv) (BV 0)) (App (App (Prim Or) (Bc True)) (Bc False))

{-@ den_t'orf_id :: ProofOf(Denotes (tsubBV 1 (Bc False) t'_or) (Lambda 1 (BV 1))) @-}
den_t'orf_id :: Denotes
den_t'orf_id = DFunc 2 (TRefn TBool Z (Bc True)) (t'orb False) (Lambda 1 (BV 1)) 
                   (FTAbs FEmpty 1 (FTBasic TBool) Base (WFFTBasic FEmpty TBool) (BV 1) 
                          (FTBasic TBool) 1 (FTVar1 FEmpty 1 (FTBasic TBool))) val_den_func_or2

{-@ val_den_func_or2 :: v_x:Value -> ProofOf(Denotes (TRefn TBool Z (Bc True)) v_x)
                          -> ProofOf(ValueDenoted (App (Lambda 1 (BV 1)) v_x) (tsubBV 2 v_x (t'orb False))) @-}
val_den_func_or2 :: Expr -> Denotes -> ValueDenoted
val_den_func_or2 v_x den_tx_vx = case v_x of 
      (Bc True)  -> ValDen (App (Lambda 1 (BV 1)) (Bc True)) (tsubBV 2 (Bc True) (t'orb False)) (Bc True)
                      (lem_step_evals (App (Lambda 1 (BV 1)) (Bc True)) (Bc True) 
                      (EAppAbs 1 (BV 1) (Bc True))) den_t''t_tt
      (Bc False) -> ValDen (App (Lambda 1 (BV 1)) (Bc False)) (tsubBV 2 (Bc False) (t'orb False)) (Bc False)
                      (lem_step_evals (App (Lambda 1 (BV 1)) (Bc False)) (Bc False) 
                      (EAppAbs 1 (BV 1) (Bc False))) den_t''f_ff
      _          -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool Z (Bc True)) den_tx_vx)
 
{-@ den_t''t_tt :: ProofOf(Denotes (tsubBV 2 (Bc True) (t'orb False)) (Bc True)) @-}
den_t''t_tt :: Denotes
den_t''t_tt = DRefn TBool Z p''t (Bc True) (FTBC FEmpty True) (reduce_or_tt False True)
  where
    {-@ p''t :: { p:Pred | p == subBV 2 (Bc True) (subBV 1 (Bc False) (refn_pred Or)) } @-}
    p''t = App (App (Prim Eqv) (BV 0)) (App (App (Prim Or) (Bc False))  (Bc True))

{-@ den_t''f_ff :: ProofOf(Denotes (tsubBV 2 (Bc False) (t'orb False)) (Bc False)) @-}
den_t''f_ff :: Denotes
den_t''f_ff = DRefn TBool Z p''f (Bc False) (FTBC FEmpty False) or_ev_prt''f_ff
  where
    or_ev_prt''f_ff = reduce_or_tt False False
    {-@ p''f :: { p:Pred | p == subBV 2 (Bc False) (subBV 1 (Bc False) (refn_pred Or)) } @-}
    p''f = App (App (Prim Eqv) (BV 0)) (App (App (Prim Or) (Bc False)) (Bc False))
