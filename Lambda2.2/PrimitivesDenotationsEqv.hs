{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--fuel=6"      @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesDenotationsEqv where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
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
import BasicPropsCSubst
import BasicPropsDenotes
import Typing
import PrimitivesSemantics

{-@ reflect foo53 @-}
foo53 x = Just x
foo53 :: a -> Maybe a

{-@ lem_den_eqv :: ProofOf(Denotes (ty Eqv) (Prim Eqv)) @-}
lem_den_eqv :: Denotes
lem_den_eqv = DFunc 1 (TRefn TBool Z (Bc True)) (ty' Eqv) (Prim Eqv ? val_eqv) 
                    (FTPrm FEmpty Eqv ? er_eqv) val_den_func_eqv  
                    ? (ty Eqv === TFunc (firstBV Eqv) (inType Eqv) (ty' Eqv))
  where
    er_eqv      = erase (TFunc 1 (TRefn TBool Z (Bc True)) (ty' Eqv))
    val_eqv     = isValue (Prim Eqv) ? isTerm (Prim Eqv)
 
{-@ lem_den_eqv_p :: { p:Pred | Set_emp (tfreeBV (TRefn TBool Z p)) }
        -> ProofOf(Denotes (TFunc 1 (TRefn TBool Z p) 
                                  (TFunc 2 (TRefn TBool Z p) (TRefn TBool Z (refn_pred Eqv)))) (Prim Eqv)) @-}
lem_den_eqv_p :: Expr -> Denotes
lem_den_eqv_p p = lem_drefn_in_dfunc_twice 1 2 TBool Z (TRefn TBool Z (refn_pred Eqv))
                                           (Prim Eqv) lem_den_eqv p

{-@ val_den_func_eqv :: v_x:Value -> ProofOf(Denotes (TRefn TBool Z (Bc True)) v_x)
                                  -> ProofOf(ValueDenoted (App (Prim Eqv) v_x) (tsubBV 1 v_x (ty' Eqv))) @-}
val_den_func_eqv :: Expr -> Denotes -> ValueDenoted
val_den_func_eqv v_x den_tx_vx = case v_x of 
    (Bc True)  -> ValDen (App (Prim Eqv) (Bc True)) (tsubBV 1 (Bc True) (ty' Eqv)) (Lambda 1 (BV 1)) 
                    (lem_step_evals (App (Prim Eqv) (Bc True)) (Lambda 1 (BV 1)) 
                    (EPrim Eqv (Bc True ? comp_t)  ? delta Eqv (Bc True ? comp_t))) den_t'eqvt_id
    (Bc False) -> ValDen (App (Prim Eqv) (Bc False)) (tsubBV 1 (Bc False) (ty' Eqv)) (Lambda 1 (App (Prim Not) (BV 1))) 
                    (lem_step_evals (App (Prim Eqv) (Bc False)) (Lambda 1 (App (Prim Not) (BV 1))) 
                    (EPrim Eqv (Bc False ? comp_f) ? delta Eqv (Bc False ? comp_f))) den_t'eqvf_nt
    _     -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool Z (Bc True) ? er_bool) den_tx_vx)
  where
    comp_f    = isCompat Eqv (Bc False)
    comp_t    = isCompat Eqv (Bc True) 
    er_bool   = erase (TRefn TBool Z (Bc True))

{-@ den_t'eqvt_id :: ProofOf(Denotes (tsubBV 1 (Bc True) (ty' Eqv)) (Lambda 1 (BV 1))) @-}
den_t'eqvt_id :: Denotes
den_t'eqvt_id = DFunc 2 (TRefn TBool Z (Bc True)) t't (Lambda 1 (BV 1) ? val_id) 
                      (FTAbs FEmpty 1 (FTBasic TBool) Base (WFFTBasic FEmpty TBool) (BV 1) 
                        (FTBasic TBool) (1 ? ftv1) (FTVar1 FEmpty (1 ? femp) (FTBasic TBool) ? un1)) val_den_func_eqv2
    ? ( tsubBV 1 (Bc True ? val_t) (ty' Eqv) ? lem_tsubBV_notin 1 (Bc True ? val_t) (TRefn TBool Z (Bc True))
    === TFunc 2 (TRefn TBool Z (Bc True)) (tsubBV 1 (Bc True) (TRefn TBool Z (refn_pred Eqv))) )
  where
    t't         = tsubBV 1 (Bc True ? val_t) (TRefn TBool Z (refn_pred Eqv))
    femp        = not (in_envF 1 FEmpty) === not (S.member 1 (bindsF FEmpty))
    ftv1        = fv (BV 1) ? ftv (BV 1)
    un1         = unbind 1 1 (BV 1) === subBV 1 (FV 1 ? val1) (BV 1) ? lem_subBV_id 1 (FV 1 ? val1)
    val1        = isValue (FV 1) ? isTerm (FV 1)
    val_id      = isValue (Lambda 1 (BV 1))    ? (isTerm (Lambda 1 (BV 1)) === isTerm (BV 1))
    val_f       = isValue (Bc False) ? isTerm (Bc False)
    val_t       = isValue (Bc True)  ? isTerm (Bc True)

{-@ val_den_func_eqv2 :: v_x:Value -> ProofOf(Denotes (TRefn TBool Z (Bc True)) v_x)
       -> ProofOf(ValueDenoted (App (Lambda 1 (BV 1)) v_x) 
                               (tsubBV 2 v_x ( tsubBV 1 (Bc True) (TRefn TBool Z (refn_pred Eqv)) ))) @-}
val_den_func_eqv2 :: Expr -> Denotes -> ValueDenoted
val_den_func_eqv2 v_x den_tx_vx = case v_x of 
      (Bc True)  -> ValDen (App (Lambda 1 (BV 1)) (Bc True)) (tsubBV 2 (Bc True) t't) (Bc True ? val_t)
                      (lem_step_evals (App (Lambda 1 (BV 1)) (Bc True)) (Bc True) 
                      (EAppAbs 1 (BV 1) (Bc True) ? subtt)) den_t''t_tt
      (Bc False) -> ValDen (App (Lambda 1 (BV 1)) (Bc False)) (tsubBV 2 (Bc False) t't) (Bc False ? val_f)
                      (lem_step_evals (App (Lambda 1 (BV 1)) (Bc False)) (Bc False) 
                      (EAppAbs 1 (BV 1) (Bc False) ? subff)) den_t''f_ff
      _          -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool Z (Bc True) ? er_bool) den_tx_vx)
  where
    t't         = tsubBV 1 (Bc True) (TRefn TBool Z (refn_pred Eqv))
    den_t''t_tt = DRefn TBool Z p''t (Bc True) (FTBC FEmpty True) eqv_ev_prt''t_tt
    p''t        = subBV 2 (Bc True ? val_t)  (subBV 1 (Bc True ? val_t) (refn_pred Eqv))
    den_t''f_ff = DRefn TBool Z p''f (Bc False) (FTBC FEmpty False) eqv_ev_prt''f_ff
    p''f        = subBV 2 (Bc False ? val_f)  (subBV 1 (Bc True ? val_t) (refn_pred Eqv))

    er_bool     = erase (TRefn TBool Z (Bc True))
    subtt       = subBV 1 (Bc True  ? val_t) (BV 1) ?  lem_subBV_id 1 (Bc True)
                                                   === Bc True ? lem_value_pred (Bc True)
    subff       = subBV 1 (Bc False ? val_f) (BV 1) ?  lem_subBV_id 1 (Bc False)
                                                   === Bc False ? lem_value_pred (Bc False)
    val_f       = isValue (Bc False)  ? isTerm (Bc False)
    val_t       = isValue (Bc True)   ? isTerm (Bc True)

{-@ eqv_ev_prt''t_tt :: ProofOf(EvalsTo (subBV 0 (Bc True) (subBV 2 (Bc True) (subBV 1 (Bc True) (refn_pred Eqv)))) (Bc True)) @-}
eqv_ev_prt''t_tt :: EvalsTo
eqv_ev_prt''t_tt = reduce_eqv_tt True True  ? blIff True True

{-@ eqv_ev_prt''f_ff :: ProofOf(EvalsTo (subBV 0 (Bc False) (subBV 2 (Bc False) (subBV 1 (Bc True) (refn_pred Eqv)))) (Bc True)) @-}
eqv_ev_prt''f_ff :: EvalsTo
eqv_ev_prt''f_ff = reduce_eqv_tt True False ? blIff True False

{-@ den_t'eqvf_nt :: ProofOf(Denotes (tsubBV 1 (Bc False) (ty' Eqv)) (Lambda 1 (App (Prim Not) (BV 1)))) @-}
den_t'eqvf_nt :: Denotes
den_t'eqvf_nt = DFunc 2 (TRefn TBool Z (Bc True)) t'f (Lambda 1 (App (Prim Not) (BV 1)) ? val_lam)
                   (FTAbs FEmpty 1 (FTBasic TBool) Base (WFFTBasic FEmpty TBool) 
                          (App (Prim Not) (BV 1)) (FTBasic TBool) (1 ? ftv1)
                          (FTApp (FCons 1 (FTBasic TBool) (FEmpty ? femp)) (Prim Not) (FTBasic TBool)
                                 (FTBasic TBool) (FTPrm (FCons 1 (FTBasic TBool) FEmpty) Not ? erase_ty Not)
                                 (FV 1) (FTVar1 FEmpty (1 ? femp) (FTBasic TBool) ? un1)) ? er_pf) val_den_func_eqv3
    ? ( tsubBV 1 (Bc False ? val_f) (ty' Eqv) ? lem_tsubBV_notin 1 (Bc False ? val_f) (TRefn TBool Z (Bc True))
    === TFunc 2 (TRefn TBool Z (Bc True)) (tsubBV 1 (Bc False) (TRefn TBool Z (refn_pred Eqv))) )
  where
    t'f     = tsubBV 1 (Bc False) (TRefn TBool Z (refn_pred Eqv))
    er_pf   =   erase (TFunc 2 (TRefn TBool Z (Bc True)) (tsubBV 1 (Bc False) (TRefn TBool Z (refn_pred Eqv))))
            === FTFunc (erase (TRefn TBool Z (Bc True))) (erase (tsubBV 1 (Bc False) (TRefn TBool Z (refn_pred Eqv))))
              ? lem_erase_tsubBV 1 (Bc False) (TRefn TBool Z (refn_pred Eqv))
            === FTFunc (FTBasic TBool) (erase (TRefn TBool Z (refn_pred Eqv)))
    femp    = not (in_envF 1 FEmpty) === not (S.member 1 (bindsF FEmpty))
    ftv1    = ( fv  (App (Prim Not) (BV 1)) === S.union (fv  (Prim Not)) (fv  (BV 1)) )
            ? ( ftv (App (Prim Not) (BV 1)) === S.union (ftv (Prim Not)) (ftv (BV 1)) )
    un1     =   unbind 1 1 (App (Prim Not) (BV 1))
            === subBV 1 (FV 1 ? val1) (App (Prim Not) (BV 1))
            === App (subBV 1 (FV 1 ? val1) (Prim Not)) (subBV 1 (FV 1 ? val1) (BV 1)) ? lem_subBV_id 1 (FV 1 ? val1)
    val1    = isValue (FV 1) ? isTerm (FV 1)
    val_lam = isValue (Lambda 1 (App (Prim Not) (BV 1))) 
            ? ( isTerm (Lambda 1 (App (Prim Not) (BV 1))) === isTerm (App (Prim Not) (BV 1))
            === (isTerm (Prim Not) && isTerm (BV 1)) )
    val_f   = isValue (Bc False)  ? isTerm (Bc False)

{-@ val_den_func_eqv3 :: v_x:Value -> ProofOf(Denotes (TRefn TBool Z (Bc True)) v_x)
         -> ProofOf(ValueDenoted (App (Lambda 1 (App (Prim Not) (BV 1))) v_x)
                                 (tsubBV 2 v_x (tsubBV 1 (Bc False) (TRefn TBool Z (refn_pred Eqv))))) @-}
val_den_func_eqv3 :: Expr -> Denotes -> ValueDenoted
val_den_func_eqv3 v_x den_tx_vx = case v_x of 
      (Bc True)  -> ValDen (App (Lambda 1 (App (Prim Not) (BV 1))) (Bc True)) (tsubBV 2 (Bc True) t'f) 
                      (Bc False ? val_f) (AddStep (App (Lambda 1 (App (Prim Not) (BV 1))) (Bc True)) 
                                          (App (Prim Not) (Bc True)) 
                                          (EAppAbs 1 (App (Prim Not) (BV 1)) (Bc True) ? sub_tt)
                                          (Bc False) (lem_step_evals (App (Prim Not) (Bc True))
                                            (Bc False) (EPrim Not (Bc True ? comp_t) ? delta Not (Bc True ? comp_t))) )
                                          den_t'''t_ff
      (Bc False) -> ValDen (App (Lambda 1 (App (Prim Not) (BV 1))) (Bc False)) (tsubBV 2 (Bc False) t'f) 
                      (Bc True ? val_t) (AddStep (App (Lambda 1 (App (Prim Not) (BV 1))) (Bc False)) 
                                          (App (Prim Not) (Bc False)) 
                                          (EAppAbs 1 (App (Prim Not) (BV 1)) (Bc False) ? sub_ff)
                                          (Bc True) (lem_step_evals (App (Prim Not) (Bc False)) 
                                            (Bc True) (EPrim Not (Bc False ? comp_f) ? delta Not (Bc False ? comp_f))) )
                                          den_t'''f_tt
      _          -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool Z (Bc True) ? er_bool) den_tx_vx)
  where
    t'f          = tsubBV 1 (Bc False) (TRefn TBool Z (refn_pred Eqv))
    den_t'''t_ff = DRefn TBool Z p'''t (Bc False) (FTBC FEmpty False) eqv_ev_prt'''t_ff
    p'''t        = subBV 2 (Bc True  ? val_t) (subBV 1 (Bc False ? val_f) (refn_pred Eqv))
    den_t'''f_tt = DRefn TBool Z p'''f (Bc True) (FTBC FEmpty True) eqv_ev_prt'''f_tt
    p'''f        = subBV 2 (Bc False ? val_f) (subBV 1 (Bc False ? val_f) (refn_pred Eqv))

    comp_f       = isCompat Not (Bc False)
    comp_t       = isCompat Not (Bc True)
    er_bool      = erase (TRefn TBool Z (Bc True))
    sub_tt       = subBV 1 (Bc True  ? val_t) (App (Prim Not) (BV 1)) 
               === App (subBV 1 (Bc True) (Prim Not)) (subBV 1 (Bc True) (BV 1))
               === App (Prim Not) (subBV 1 (Bc True) (BV 1)) ?  lem_subBV_id 1 (Bc True)
                                                            === App (Prim Not) (Bc True ? lem_value_pred (Bc True))
    sub_ff       = subBV 1 (Bc False ? val_f) (App (Prim Not) (BV 1))
               === App (subBV 1 (Bc False) (Prim Not)) (subBV 1 (Bc False) (BV 1))
               === App (Prim Not) (subBV 1 (Bc False) (BV 1)) ? lem_subBV_id 1 (Bc False)               
                                                            === App (Prim Not) (Bc False ? lem_value_pred (Bc False))
    val_f       = isValue (Bc False)  ? isTerm (Bc False)
    val_t       = isValue (Bc True)   ? isTerm (Bc True)

{-@ eqv_ev_prt'''t_ff :: ProofOf(EvalsTo (subBV 0 (Bc False) (subBV 2 (Bc True) (subBV 1 (Bc False) (refn_pred Eqv)))) (Bc True)) @-}
eqv_ev_prt'''t_ff :: EvalsTo
eqv_ev_prt'''t_ff = reduce_eqv_tt False True  ? blIff False True

{-@ eqv_ev_prt'''f_tt :: ProofOf(EvalsTo (subBV 0 (Bc True) (subBV 2 (Bc False) (subBV 1 (Bc False) (refn_pred Eqv)))) (Bc True)) @-}
eqv_ev_prt'''f_tt :: EvalsTo
eqv_ev_prt'''f_tt = reduce_eqv_tt False False ? blIff False False
