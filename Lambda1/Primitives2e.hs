{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-}
{- @ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Primitives2e where

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

{-@ reflect foo9 @-}
foo9 x = Just x
foo9 :: a -> Maybe a


{-@ reduce_eq_tt :: n:Int -> m:Int -> { pf:_ | propOf pf == 
      EvalsTo (subBV 3 (Bc (intEq n m)) (subBV 2 (Ic m) (subBV 1 (Ic n) (refn_pred Eq)))) (Bc True) } @-}
reduce_eq_tt :: Int -> Int -> EvalsTo
reduce_eq_tt n m = final_step
  where
    st_eqv_3   = EPrim Eqv (Bc (n == m)) 
    step_one   = EApp1 (App (Prim Eqv) (Bc (n == m))) (delta Eqv (Bc (n == m))) st_eqv_3
                       (App (App (Prim Eq) (Ic n)) (Ic m)) 
    st_leq_1   = EPrim Eq (Ic n)
    st_leq_12  = EApp1 (App (Prim Eq) (Ic n)) (delta Eq (Ic n)) st_leq_1 (Ic m)
    {-@ st_leq_2 :: ProofOf(Step (App (delta Eq (Ic n)) (Ic m)) (Bc (intEq n m)))  @-}
    st_leq_2   = EPrim (Eqn n) (Ic m) 
    base_st    = Refl (Bc (n == m))
    ev_and_12  = AddStep (App (App (Prim Eq) (Ic n)) (Ic m)) (App (delta Eq (Ic n)) (Ic m))
                         st_leq_12 (Bc (n == m)) (AddStep (App (delta Eq (Ic n)) (Ic m)) (Bc (n == m))
                                                          st_leq_2 (Bc (n == m)) base_st)
    eval_two   = if ( n == m ) then (lemma_app_many2 (delta Eqv (Bc True)) 
                                       (App (App (Prim Eq) (Ic n)) (Ic m)) (Bc (n == m)) ev_and_12)
                               else (lemma_app_many2 (delta Eqv (Bc False)) 
                                       (App (App (Prim Eq) (Ic n)) (Ic m)) (Bc (n == m)) ev_and_12)
    eval_12    = AddStep (App (App (Prim Eqv) (Bc (n == m))) (App (App (Prim Eq) (Ic n)) (Ic m))) 
                         (App (delta Eqv (Bc (n == m)))      (App (App (Prim Eq) (Ic n)) (Ic m)))
                         step_one (App (delta Eqv (Bc (n == m))) (Bc (n == m))) eval_two

    eval_three = reduce_eqv (n == m) (n == m)
    final_step = lemma_evals_trans (App (App (Prim Eqv) (Bc (n == m))) (App (App (Prim Eq) (Ic n)) (Ic m)))
                                   (App (delta Eqv (Bc (n == m))) (Bc (n == m))) (Bc True)
                                   eval_12 eval_three

{-@ reduce_eqn_tt :: n:Int -> m:Int -> { pf:_ | propOf pf ==
      EvalsTo (subBV 3 (Bc (intEq n m)) (subBV 2 (Ic m) (refn_pred (Eqn n)))) (Bc True) } @-}
reduce_eqn_tt :: Int -> Int -> EvalsTo
reduce_eqn_tt n m = reduce_eq_tt n m




{-@ lem_den_eq :: ProofOf(Denotes (ty Eq) (Prim Eq)) @-}
lem_den_eq :: Denotes
lem_den_eq = DFunc 1 (TRefn TInt 4 (Bc True)) t' (Prim Eq) (BTPrm BEmpty Eq) val_den_func
  where
    t' = TFunc 2 (TRefn TInt 5 (Bc True)) (TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                                                         (App (App (Prim Eq) (BV 1)) (BV 2)) ))
    {-@ val_den_func :: v_x:Value -> ProofOf(Denotes (TRefn TInt 4 (Bc True)) v_x)
                                  -> ProofOf(ValueDenoted (App (Prim Eq) v_x) (tsubBV 1 v_x t')) @-}
    val_den_func :: Expr -> Denotes -> ValueDenoted
    val_den_func v_x den_tx_vx = case v_x of 
      (Ic n) -> ValDen (App (Prim Eq) (Ic n)) (tsubBV 1 (Ic n) t') (Prim (Eqn n))
                       (lem_step_evals (App (Prim Eq) (Ic n)) (Prim (Eqn n)) 
                       (EPrim Eq (Ic n))) den_t'n_eqn
        where
          t'n = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Eq) (Ic n)) (BV 2)) )
          den_t'n_eqn = DFunc 2 (TRefn TInt 5 (Bc True)) t'n (Prim (Eqn n)) 
                              (BTPrm BEmpty (Eqn n)) val_den_func2
          {-@ val_den_func2 :: v_x:Value -> ProofOf(Denotes (TRefn TInt 5 (Bc True)) v_x)
                                  -> ProofOf(ValueDenoted (App (Prim (Eqn n)) v_x) (tsubBV 2 v_x t'n)) @-}
          val_den_func2 :: Expr -> Denotes -> ValueDenoted
          val_den_func2 v_x den_tx_vx = case v_x of 
            (Ic m) -> ValDen (App (Prim (Eqn n)) (Ic m)) (tsubBV 2 (Ic m) t'n) (Bc (n == m))
                             (lem_step_evals (App (Prim (Eqn n)) (Ic m)) (Bc (n == m)) 
                             (EPrim (Eqn n) (Ic m))) den_t'nm_eq
              where
                t'nm = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Eq) (Ic n)) (Ic m)) )
                den_t'nm_eq = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Eq) (Ic n)) (Ic m)))
                                    (Bc (n == m)) (BTBC BEmpty (n == m)) ev_prt'nm_eq
                {- @ ev_prt'nm_eq :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc (intEq n m))) 
                                              (App (App (Prim Eq) (Ic n)) (Ic m))) (Bc True)) @-}
                ev_prt'nm_eq = reduce_eq_tt n m
            _      -> impossible ("by lemma" ? lem_den_ints v_x (TRefn TInt 5 (Bc True)) den_tx_vx)
      _      -> impossible ("by lemma" ? lem_den_ints v_x (TRefn TInt 4 (Bc True)) den_tx_vx)

{-@ lem_den_eqn :: n:Int -> ProofOf(Denotes (ty (Eqn n)) (Prim (Eqn n))) @-}
lem_den_eqn :: Int -> Denotes
lem_den_eqn n = DFunc 2 (TRefn TInt 5 (Bc True)) t'n (Prim (Eqn n)) (BTPrm BEmpty (Eqn n)) val_den_func
  where
    t'n = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Eq) (Ic n)) (BV 2)) )
    {-@ val_den_func :: v_x:Value -> ProofOf(Denotes (TRefn TInt 5 (Bc True)) v_x)
                                  -> ProofOf(ValueDenoted (App (Prim (Eqn n)) v_x) (tsubBV 2 v_x t'n)) @-}
    val_den_func :: Expr -> Denotes -> ValueDenoted
    val_den_func v_x den_tx_vx = case v_x of 
      (Ic m) -> ValDen (App (Prim (Eqn n)) (Ic m)) (tsubBV 2 (Ic m) t'n) (Bc (n == m))
                       (lem_step_evals (App (Prim (Eqn n)) (Ic m)) (Bc (n == m)) (EPrim (Eqn n) (Ic m)))
                       den_t'nm_eq
        where
          t'nm = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Eq) (Ic n)) (Ic m)) )
          den_t'nm_eq = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Eq) (Ic n)) (Ic m)) )
                              (Bc (n == m)) (BTBC BEmpty (n == m)) ev_prt'nm_neq
          {- @ ev_prt'nm_neq :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc (intEq n m))) 
                                                    (App (App (Prim Eq) (Ic n)) (Ic m))) (Bc True)) @-}
          ev_prt'nm_neq = reduce_eqn_tt n m
      _      -> impossible ("by lemma" ? lem_den_ints v_x (TRefn TInt 5 (Bc True)) den_tx_vx)


