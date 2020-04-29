{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-}
{- @ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Primitives2b where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import BasicProps
import Typing
import Primitives

-- force these into scope
semantics = (Step, EvalsTo)
typing = (HasBType, HasType, WFType, WFEnv, Subtype)
denotations = (Entails, Denotes, DenotesEnv, ValueDenoted)

{-@ reflect foo6 @-}
foo6 x = Just x
foo6 :: a -> Maybe a


{-@ reduce_or_tt :: b:Bool -> b':Bool -> { pf:_ | propOf pf == 
      EvalsTo (subBV 3 (Bc (blOr b b')) (subBV 2 (Bc b') (subBV 1 (Bc b) (refn_pred Or)))) (Bc True) } @-}
reduce_or_tt :: Bool -> Bool -> EvalsTo
reduce_or_tt b b' = final_step
  where
    st_eqv_3   = EPrim Eqv (Bc (b || b')) 
    step_one   = EApp1 (App (Prim Eqv) (Bc (b || b'))) (delta Eqv (Bc (b || b'))) st_eqv_3
                       (App (App (Prim Or) (Bc b)) (Bc b')) 
    st_and_1   = EPrim Or (Bc b) -----
    st_and_12  = EApp1 (App (Prim Or) (Bc b)) (delta Or (Bc b)) st_and_1 (Bc b')
    {-@ st_and_2 :: ProofOf(Step (App (delta Or (Bc b)) (Bc b')) (Bc (blOr b b')))  @-}
    st_and_2   = if b then (EAppAbs 1 (Bc True) (Bc b')) else (EAppAbs 1 (BV 1) (Bc b'))
    base_st    = Refl (Bc (b || b'))
    ev_and_12  = AddStep (App (App (Prim Or) (Bc b)) (Bc b')) (App (delta Or (Bc b)) (Bc b'))
                         st_and_12 (Bc (b || b')) (AddStep (App (delta Or (Bc b)) (Bc b')) (Bc (b || b'))
                                                          st_and_2 (Bc (b || b')) base_st)
    eval_two   = if (b || b') then (lemma_app_many2 (delta Eqv (Bc True)) 
                                         (App (App (Prim Or) (Bc b)) (Bc b')) (Bc (b || b')) ev_and_12)
                              else (lemma_app_many2 (delta Eqv (Bc False )) 
                                         (App (App (Prim Or) (Bc b)) (Bc b')) (Bc (b || b')) ev_and_12)
    eval_12    = AddStep (App (App (Prim Eqv) (Bc (b || b'))) (App (App (Prim Or) (Bc b)) (Bc b'))) 
                         (App (delta Eqv (Bc (b || b')))      (App (App (Prim Or) (Bc b)) (Bc b')))
                         step_one (App (delta Eqv (Bc (b || b'))) (Bc (b || b'))) eval_two
    eval_three = reduce_eqv (b || b') (b || b')
    final_step = lemma_evals_trans (App (App (Prim Eqv) (Bc (b || b'))) (App (App (Prim Or) (Bc b)) (Bc b')))
                                   (App (delta Eqv (Bc (b || b'))) (Bc (b || b'))) (Bc True)
                                   eval_12 eval_three

{-@ reduce_not_tt :: b:Bool -> { pf:_ | propOf pf ==
      EvalsTo (subBV 3 (Bc (blNot b)) (subBV 2 (Bc b) (refn_pred Not))) (Bc True) } @-}
reduce_not_tt :: Bool -> EvalsTo
reduce_not_tt b = final_step
  where
    st_eqv_3   = EPrim Eqv (Bc (not b))
    step_one   = EApp1 (App (Prim Eqv) (Bc (not b))) (delta Eqv (Bc (not b))) st_eqv_3
                       (App (Prim Not) (Bc b))
    step_not   = EPrim Not (Bc b) -- Not b ==> delta Not b == not b 
    step_two   = EApp2 (App (Prim Not) (Bc b)) (Bc (not b)) step_not (delta Eqv (Bc (not b)))
    eval_three = reduce_eqv (not b) (not b)
    final_step = AddStep (App (App (Prim Eqv) (Bc (not b))) (App (Prim Not) (Bc b)))
                         (App (delta Eqv (Bc (not b))) (App (Prim Not) (Bc b))) step_one
                         (Bc True) (AddStep (App (delta Eqv (Bc (not b))) (App (Prim Not) (Bc b)))
                                            (App (delta Eqv (Bc (not b))) (Bc (not b))) step_two
                                            (Bc True) eval_three) 
  

{-@ lem_den_or :: ProofOf(Denotes (ty Or) (Prim Or)) @-}
lem_den_or :: Denotes
lem_den_or = DFunc 1 (TRefn TBool 4 (Bc True)) t' (Prim Or) (BTPrm BEmpty Or) val_den_func
  where
    val_den_func :: Expr -> Denotes -> ValueDenoted
    val_den_func v_x den_tx_vx = case v_x of 
      (Bc True)  -> ValDen (App (Prim Or) (Bc True)) (tsubBV 1 (Bc True) t') (Lambda 1 (Bc True)) 
                      (lem_step_evals (App (Prim Or) (Bc True)) (Lambda 1 (Bc True)) 
                                      (EPrim Or (Bc True))) den_t't_lamtt -- den_t'f_lamff
      (Bc False) -> ValDen (App (Prim Or) (Bc False)) (tsubBV 1 (Bc False) t') (Lambda 1 (BV 1)) 
                      (lem_step_evals (App (Prim Or) (Bc False)) (Lambda 1 (BV 1)) 
                                      (EPrim Or (Bc False))) den_t'f_id
      _     -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool 4 (Bc True)) den_tx_vx)
    t' = TFunc 2 (TRefn TBool 5 (Bc True)) (TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                                                               (App (App (Prim Or) (BV 1)) (BV 2)) ))

    t't = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Or) (Bc True)) (BV 2)) )
    den_t't_lamtt = DFunc 2 (TRefn TBool 5 (Bc True)) t't (Lambda 1 (Bc True))
                          (BTAbs BEmpty 1 (BTBase TBool) (Bc True) (BTBase TBool) 1 
                                 (BTBC (BCons 1 (BTBase TBool) BEmpty) True))
                          val_den_func3
    val_den_func3 :: Expr -> Denotes -> ValueDenoted
    val_den_func3 v_x den_tx_vx = case v_x of
      (Bc True)  -> ValDen (App (Lambda 1 (Bc True)) (Bc True)) (tsubBV 2 (Bc True) t't) (Bc True)
                      (lem_step_evals (App (Lambda 1 (Bc True)) (Bc True)) (Bc True) 
                                      (EAppAbs 1 (Bc True) (Bc True))) den_t'''t_tt
      (Bc False) -> ValDen (App (Lambda 1 (Bc True)) (Bc False)) (tsubBV 2 (Bc False) t't) (Bc True)
                      (lem_step_evals (App (Lambda 1 (Bc True)) (Bc False)) (Bc True) 
                                      (EAppAbs 1 (Bc True) (Bc False))) den_t'''f_tt
      _          -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool 5 (Bc True)) den_tx_vx)
    t'''t = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Or) (Bc True)) (Bc True)) )
    t'''f = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Or) (Bc True)) (Bc False)) )
    den_t'''t_tt = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Or) (Bc True)) (Bc True)) )
                        (Bc True) (BTBC BEmpty True) or_ev_prt'''t_tt
    {-@ or_ev_prt'''t_tt :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc True)) (App (App (Prim Or) (Bc True)) (Bc True))) (Bc True)) @-}
    or_ev_prt'''t_tt = reduce_or_tt True True
    den_t'''f_tt = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Or) (Bc True)) (Bc False)) )
                        (Bc True) (BTBC BEmpty True) or_ev_prt'''f_tt
    {-@ or_ev_prt'''f_tt :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc True)) (App (App (Prim Or) (Bc True)) (Bc False))) (Bc True)) @-}
    or_ev_prt'''f_tt = reduce_or_tt True False

    t'f = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Or) (Bc False)) (BV 2)) )
    den_t'f_id = DFunc 2 (TRefn TBool 5 (Bc True)) t'f (Lambda 1 (BV 1)) 
                       (BTAbs BEmpty 1 (BTBase TBool) (BV 1) (BTBase TBool) 1 (BTVar1 BEmpty 1 (BTBase TBool)))
                       val_den_func2
    val_den_func2 :: Expr -> Denotes -> ValueDenoted
    val_den_func2 v_x den_tx_vx = case v_x of 
      (Bc True)  -> ValDen (App (Lambda 1 (BV 1)) (Bc True)) (tsubBV 2 (Bc True) t'f) (Bc True)
                      (lem_step_evals (App (Lambda 1 (BV 1)) (Bc True)) (Bc True) 
                      (EAppAbs 1 (BV 1) (Bc True))) den_t''t_tt
      (Bc False) -> ValDen (App (Lambda 1 (BV 1)) (Bc False)) (tsubBV 2 (Bc False) t'f) (Bc False)
                      (lem_step_evals (App (Lambda 1 (BV 1)) (Bc False)) (Bc False) 
                      (EAppAbs 1 (BV 1) (Bc False))) den_t''f_ff
      _          -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool 5 (Bc True)) den_tx_vx)
    t''t = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Or) (Bc False)) (Bc True)) )
    t''f = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Or) (Bc False)) (Bc False)) )
    den_t''t_tt = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Or) (Bc False)) (Bc True)) )
                        (Bc True) (BTBC BEmpty True) or_ev_prt''t_tt
    {-@ or_ev_prt''t_tt :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc True)) (App (App (Prim Or) (Bc False)) (Bc True))) (Bc True)) @-}
    or_ev_prt''t_tt = reduce_or_tt False True
    den_t''f_ff = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Or) (Bc False)) (Bc False)) )
                        (Bc False) (BTBC BEmpty False) or_ev_prt''f_ff
    {-@ or_ev_prt''f_ff :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc False)) (App (App (Prim Or) (Bc False)) (Bc False))) (Bc True)) @-}
    or_ev_prt''f_ff = reduce_or_tt False False


{-@ lem_den_not :: ProofOf(Denotes (ty Not) (Prim Not)) @-}
lem_den_not :: Denotes
lem_den_not = DFunc 2 (TRefn TBool 5 (Bc True)) t'
                    (Prim Not) (BTPrm BEmpty Not) val_den_func
  where
    val_den_func :: Expr -> Denotes -> ValueDenoted
    val_den_func v_x den_tx_vx = case v_x of 
      (Bc True)  -> ValDen (App (Prim Not) (Bc True)) (tsubBV 2 (Bc True) t') (Bc False) 
                      (lem_step_evals (App (Prim Not) (Bc True)) (Bc False) (EPrim Not (Bc True))) den_t't
      (Bc False) -> ValDen (App (Prim Not) (Bc False)) (tsubBV 2 (Bc False) t') (Bc True) 
                      (lem_step_evals (App (Prim Not) (Bc False)) (Bc True) (EPrim Not (Bc False))) den_t'f
      _     -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool 5 (Bc True)) den_tx_vx)
    t'  = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (Prim Not) (BV 2)))
    t't = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (Prim Not) (Bc True)) )
    t'f = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (Prim Not) (Bc False)) )
    den_t't = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (Prim Not) (Bc True)) )
                        (Bc False) (BTBC BEmpty False) ev_prt't
    {-@ ev_prt't :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc False)) (App (Prim Not) (Bc True)) ) (Bc True)) @-}
    ev_prt't = reduce_not_tt True 
    den_t'f = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (Prim Not) (Bc False)) )
                        (Bc True) (BTBC BEmpty True) ev_prt'f 
    {-@ ev_prt'f :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc True)) (App (Prim Not) (Bc False)) ) (Bc True)) @-}
    ev_prt'f = reduce_not_tt False

