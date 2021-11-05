{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple-local"   @-}
{-@ LIQUID "--fuel=4"      @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesDenotationsAnd where

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

{-@ reflect foo51 @-}
foo51 x = Just x
foo51 :: a -> Maybe a

{-@ lem_den_and :: ProofOf(Denotes (ty And) (Prim And)) @-}
lem_den_and :: Denotes
lem_den_and = DFunc 1 (TRefn TBool Z (Bc True)) (ty' And) (Prim And ? val_and) 
                    (FTPrm FEmpty And ? er_and) val_den_func_and ? ty_and
  where
    er_and    = erase_ty And === erase (ty And) ? ty_and
    ty_and    = ty And === TFunc (firstBV And)      (inType And)  (ty' And)
    val_and   = isValue (Prim And) ? isTerm (Prim And)

{-@ val_den_func_and :: v_x:Value -> ProofOf(Denotes (TRefn TBool Z (Bc True)) v_x) 
                                  -> ProofOf(ValueDenoted (App (Prim And) v_x) (tsubBV 1 v_x (ty' And))) @-}
val_den_func_and :: Expr -> Denotes -> ValueDenoted
val_den_func_and v_x den_tx_vx = case v_x of 
      (Bc True)  -> ValDen (App (Prim And) (Bc True)) (tsubBV 1 (Bc True) (ty' And)) (Lambda 1 (BV 1) ? val_id) 
                      (lem_step_evals (App (Prim And) (Bc True)) (Lambda 1 (BV 1)) 
                                      (EPrim And (Bc True ? comp_t) ? del_t )) den_t'andt_id
      (Bc False) -> ValDen (App (Prim And) (Bc False)) (tsubBV 1 (Bc False) (ty' And)) (Lambda 1 (Bc False) ? val_ff) 
                      (lem_step_evals (App (Prim And) (Bc False)) (Lambda 1 (Bc False)) 
                                      (EPrim And (Bc False ? comp_f) ? del_f )) den_t'andf_lamff
      _     -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool Z (Bc True) ? er_bool ) den_tx_vx)
  where
    comp_f    = isCompat And (Bc False)
    comp_t    = isCompat And (Bc True)
    del_f     = delta And (Bc False ? comp_f ? val_f)
    del_t     = delta And (Bc True  ? comp_t ? val_t)
    val_f     = isValue (Bc False)  ? isTerm (Bc False)
    val_t     = isValue (Bc True)   ? isTerm (Bc True)
    val_ff    = isValue (Lambda 1 (Bc False)) ? isTerm (Lambda 1 (Bc False))
    val_id    = isValue (Lambda 1 (BV 1))     ? isTerm (Lambda 1 (BV 1))
    er_bool   = erase (TRefn TBool Z (Bc True)) 

{-@ ple den_t'andt_id @-}
{-@ den_t'andt_id :: ProofOf(Denotes (tsubBV 1 (Bc True) (ty' And)) (Lambda 1 (BV 1))) @-}
den_t'andt_id :: Denotes
den_t'andt_id = DFunc 2 (TRefn TBool Z (Bc True)) t'and_t (Lambda 1 (BV 1) ? val_id) 
                  (FTAbs FEmpty 1 (FTBasic TBool) Base (WFFTBasic FEmpty TBool) (BV 1) 
                    (FTBasic TBool) (1 ? ftv1 ? femp) (FTVar1 FEmpty 1 (FTBasic TBool) ? un1) ? er_func) 
                  val_den_func_and2
      ? ( tsubBV 1 (Bc True ? val_t) (ty' And) ? lem_tsubBV_notin 1 (Bc True ? val_t) (TRefn TBool Z (Bc True))
      === TFunc 2 (TRefn TBool Z (Bc True)) (tsubBV 1 (Bc True) (TRefn TBool Z (refn_pred And))) )
  where
    t'and_t   = tsubBV 1 (Bc True ? val_t) (TRefn TBool Z (refn_pred And))
    femp      = not (in_envF 1 FEmpty) === not (S.member 1 (bindsF FEmpty))
    ftv1      = fv (BV 1) ? ftv (BV 1)
    un1       = unbind 1 1 (BV 1) === subBV 1 (FV 1 ? val1) (BV 1) ? lem_subBV_id 1 (FV 1 ? val1)
    val_id    = isValue (Lambda 1 (BV 1))    ? (isTerm (Lambda 1 (BV 1)) === isTerm (BV 1))
    val_t     = isValue (Bc True) ? isTerm (Bc True)
    val1      = isValue (FV 1) ? isTerm (FV 1)
    er_func   = ( erase (TFunc 2 (TRefn TBool Z (Bc True)) 
                                 (tsubBV 1 (Bc True ? val_t) (TRefn TBool Z (refn_pred And))))
              === FTFunc (erase (TRefn TBool Z (Bc True)))
                         (erase (tsubBV 1 (Bc True ? val_t) (TRefn TBool Z (refn_pred And))))
                ? lem_erase_tsubBV 1 (Bc True ? val_t) (TRefn TBool Z (refn_pred And))
              === FTFunc (FTBasic TBool) (erase (TRefn TBool Z (refn_pred And))) )

{-@ ple val_den_func_and2 @-}
{-@ val_den_func_and2 :: v_x:Value -> ProofOf(Denotes (TRefn TBool Z (Bc True)) v_x)
      -> ProofOf(ValueDenoted (App (Lambda 1 (BV 1)) v_x) 
                              (tsubBV 2 v_x (tsubBV 1 (Bc True) (TRefn TBool Z (refn_pred And))))) @-}
val_den_func_and2 :: Expr -> Denotes -> ValueDenoted
val_den_func_and2 v_x den_tx_vx = case v_x of 
      (Bc True)  -> ValDen (App (Lambda 1 (BV 1)) (Bc True)) (tsubBV 2 (Bc True) (t'and_t)) (Bc True ? val_t)
                      (lem_step_evals (App (Lambda 1 (BV 1)) (Bc True)) (Bc True ? subtt) 
                                      (EAppAbs 1 (BV 1) (Bc True)  {-? subtt-} )) den_t''t_tt 
      (Bc False) -> ValDen (App (Lambda 1 (BV 1)) (Bc False)) (tsubBV 2 (Bc False) (t'and_t)) (Bc False )
                      (lem_step_evals (App (Lambda 1 (BV 1)) (Bc False)) (Bc False ? subft) 
                                      (EAppAbs 1 (BV 1) (Bc False) {-? subft-} )) den_t''f_ff 
      _          -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool Z (Bc True) ? er_bool) den_tx_vx)
  where
    t'and_t     = tsubBV 1 (Bc True) (TRefn TBool Z (refn_pred And))
    den_t''t_tt = DRefn TBool Z p''t (Bc True) (FTBC FEmpty True) ev_prt''t_tt
    p''t        = subBV 2 (Bc True ? val_t)  (subBV 1 (Bc True ? val_t) (refn_pred And))
    den_t''f_ff = DRefn TBool Z p''f (Bc False) (FTBC FEmpty False) ev_prt''f_ff
    p''f        = subBV 2 (Bc False ? val_f) (subBV 1 (Bc True ? val_t) (refn_pred And))
    subtt       = subBV 1 (Bc True) (BV 1)  ?  lem_subBV_id 1 (Bc True)  
                                           === Bc True  ? lem_value_pred (Bc True)
    subft       = subBV 1 (Bc False) (BV 1) ?  lem_subBV_id 1 (Bc False) 
                                           === Bc False ? lem_value_pred (Bc False)
    val1        = isValue (BV 1) ? isTerm (BV 1)
    val_f       = isValue (Bc False)  ? isTerm (Bc False)
    val_t       = isValue (Bc True)   ? isTerm (Bc True)
    er_bool     = erase (TRefn TBool Z (Bc True)) 

{-@ ev_prt''t_tt :: ProofOf(EvalsTo (subBV 0 (Bc True) (subBV 2 (Bc True)  (subBV 1 (Bc True) (refn_pred And)))) 
                                    (Bc True)) @-}
ev_prt''t_tt :: EvalsTo
ev_prt''t_tt = reduce_and_tt True True ? blAnd True True

{-@ ev_prt''f_ff :: ProofOf(EvalsTo (subBV 0 (Bc False) (subBV 2 (Bc False) (subBV 1 (Bc True) (refn_pred And)))) 
                                    (Bc True)) @-}
ev_prt''f_ff :: EvalsTo
ev_prt''f_ff = reduce_and_tt True False ? blAnd True False

{-@ den_t'andf_lamff :: ProofOf(Denotes (tsubBV 1 (Bc False) (ty' And)) (Lambda 1 (Bc False))) @-}
den_t'andf_lamff :: Denotes
den_t'andf_lamff = DFunc 2 (TRefn TBool Z (Bc True)) t'and_f (Lambda 1 (Bc False) ? val_ff)
                      (FTAbs FEmpty 1 (FTBasic TBool) Base (WFFTBasic FEmpty TBool) (Bc False) 
                             (FTBasic TBool) (1 ? ftv1) (FTBC (FCons 1 (FTBasic TBool) (FEmpty ? femp)) False ? un1)
                             ? er_func ) val_den_func_and3
                      ? ( tsubBV 1 (Bc False ? val_f) (ty' And) 
                        ? lem_tsubBV_notin 1 (Bc False ? val_f) (TRefn TBool Z (Bc True))
                      === TFunc 2 (TRefn TBool Z (Bc True)) (tsubBV 1 (Bc False) (TRefn TBool Z (refn_pred And))) )
  where
    t'and_f   = tsubBV 1 (Bc False ? val_f) (TRefn TBool Z (refn_pred And))
    femp      = not (in_envF 1 FEmpty) === not (S.member 1 (bindsF FEmpty))
    ftv1      = fv (Bc False) ? ftv (Bc False)
    un1       = unbind 1 1 (Bc False) === subBV 1 (FV 1 ? val1) (Bc False)
    val1      = isValue (FV 1) ? isTerm (FV 1)
    val_f     = isValue (Bc False)  ? isTerm (Bc False)
    val_t     = isValue (Bc True)   ? isTerm (Bc True)
    val_ff    = isValue (Lambda 1 (Bc False))   ? (isTerm (Lambda 1 (Bc False)) === isTerm (Bc False))
    er_func   = ( erase (TFunc 2 (TRefn TBool Z (Bc True)) 
                                 (tsubBV 1 (Bc False ? val_f) (TRefn TBool Z (refn_pred And))))
              === FTFunc (erase (TRefn TBool Z (Bc True)))
                         (erase (tsubBV 1 (Bc False ? val_f) (TRefn TBool Z (refn_pred And))))
                ? lem_erase_tsubBV 1 (Bc False ? val_f) (TRefn TBool Z (refn_pred And))
              === FTFunc (FTBasic TBool) (erase (TRefn TBool Z (refn_pred And))) )

{-@ val_den_func_and3 :: v_x:Value -> ProofOf(Denotes (TRefn TBool Z (Bc True)) v_x)
      -> ProofOf(ValueDenoted (App (Lambda 1 (Bc False)) v_x) 
                                   (tsubBV 2 v_x (tsubBV 1 (Bc False) (TRefn TBool Z (refn_pred And))))) @-}
val_den_func_and3 :: Expr -> Denotes -> ValueDenoted
val_den_func_and3 v_x den_tx_vx = case v_x of
      (Bc True)  -> ValDen (App (Lambda 1 (Bc False)) (Bc True)) (tsubBV 2 (Bc True) t'and_f) (Bc False ? val_f)
                      (lem_step_evals (App (Lambda 1 (Bc False)) (Bc True)) (Bc False ? val_f) 
                                      (EAppAbs 1 (Bc False) (Bc True) ? subtf)) den_t'''t_ff
      (Bc False) -> ValDen (App (Lambda 1 (Bc False)) (Bc False)) (tsubBV 2 (Bc False) t'and_f) (Bc False ? val_f)
                      (lem_step_evals (App (Lambda 1 (Bc False)) (Bc False)) (Bc False ? val_f) 
                                      (EAppAbs 1 (Bc False) (Bc False) ? subff)) den_t'''f_ff
      _          -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool Z (Bc True) ? er_bool) den_tx_vx)
  where
    t'and_f   = tsubBV 1 (Bc False) (TRefn TBool Z (refn_pred And))
    den_t'''t_ff = DRefn TBool Z p'''t (Bc False) (FTBC FEmpty False) ev_prt'''t_ff
    p'''t = subBV 2 (Bc True ? val_t)  (subBV 1 (Bc False ? val_f) (refn_pred And))
    den_t'''f_ff = DRefn TBool Z p'''f (Bc False) (FTBC FEmpty False) ev_prt'''f_ff
    p'''f = subBV 2 (Bc False ? val_f) (subBV 1 (Bc False ? val_t) (refn_pred And))
    subtf       = subBV 1 (Bc True  ? val_t) (Bc False)
    subff       = subBV 1 (Bc False ? val_f) (Bc False)
    val_f       = isValue (Bc False)  ? isTerm (Bc False)
    val_t       = isValue (Bc True)   ? isTerm (Bc True)
    er_bool     = erase (TRefn TBool Z (Bc True)) 

{-@ ev_prt'''t_ff :: ProofOf(EvalsTo (subBV 0 (Bc False) (subBV 2 (Bc True)  (subBV 1 (Bc False) (refn_pred And))))
                                     (Bc True)) @-}
ev_prt'''t_ff :: EvalsTo
ev_prt'''t_ff = reduce_and_tt False True ? blAnd False True

{-@ ev_prt'''f_ff :: ProofOf(EvalsTo (subBV 0 (Bc False) (subBV 2 (Bc False) (subBV 1 (Bc False) (refn_pred And))))
                                     (Bc True)) @-}
ev_prt'''f_ff :: EvalsTo
ev_prt'''f_ff = reduce_and_tt False False ? blAnd False False
