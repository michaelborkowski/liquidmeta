{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-}
{- @ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Primitives2d where

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

{-@ reflect foo8 @-}
foo8 x = Just x
foo8 :: a -> Maybe a



{-@ reduce_leq_tt :: n:Int -> m:Int -> { pf:_ | propOf pf == 
      EvalsTo (subBV 3 (Bc (intLeq n m)) (subBV 2 (Ic m) (subBV 1 (Ic n) (refn_pred Leq)))) (Bc True) } @-}
reduce_leq_tt :: Int -> Int -> EvalsTo
reduce_leq_tt n m = final_step
  where
    st_eqv_3   = EPrim Eqv (Bc (n <= m)) 
    step_one   = EApp1 (App (Prim Eqv) (Bc (n <= m))) (delta Eqv (Bc (n <= m))) st_eqv_3
                       (App (App (Prim Leq) (Ic n)) (Ic m)) 
    st_leq_1   = EPrim Leq (Ic n)
    st_leq_12  = EApp1 (App (Prim Leq) (Ic n)) (delta Leq (Ic n)) st_leq_1 (Ic m)
    {-@ st_leq_2 :: ProofOf(Step (App (delta Leq (Ic n)) (Ic m)) (Bc (intLeq n m)))  @-}
    st_leq_2   = EPrim (Leqn n) (Ic m) 
    base_st    = Refl (Bc (n <= m))
    ev_and_12  = AddStep (App (App (Prim Leq) (Ic n)) (Ic m)) (App (delta Leq (Ic n)) (Ic m))
                         st_leq_12 (Bc (n <= m)) (AddStep (App (delta Leq (Ic n)) (Ic m)) (Bc (n <= m))
                                                          st_leq_2 (Bc (n <= m)) base_st)
    eval_two   = if ( n <= m ) then (lemma_app_many2 (delta Eqv (Bc True)) 
                                       (App (App (Prim Leq) (Ic n)) (Ic m)) (Bc (n <= m)) ev_and_12)
                               else (lemma_app_many2 (delta Eqv (Bc False)) 
                                       (App (App (Prim Leq) (Ic n)) (Ic m)) (Bc (n <= m)) ev_and_12)
    eval_12    = AddStep (App (App (Prim Eqv) (Bc (n <= m))) (App (App (Prim Leq) (Ic n)) (Ic m))) 
                         (App (delta Eqv (Bc (n <= m)))      (App (App (Prim Leq) (Ic n)) (Ic m)))
                         step_one (App (delta Eqv (Bc (n <= m))) (Bc (n <= m))) eval_two

    eval_three = reduce_eqv (n <= m) (n <= m)
    final_step = lemma_evals_trans (App (App (Prim Eqv) (Bc (n <= m))) (App (App (Prim Leq) (Ic n)) (Ic m)))
                                   (App (delta Eqv (Bc (n <= m))) (Bc (n <= m))) (Bc True)
                                   eval_12 eval_three


{-@ reduce_leqn_tt :: n:Int -> m:Int -> { pf:_ | propOf pf ==
      EvalsTo (subBV 3 (Bc (intLeq n m)) (subBV 2 (Ic m) (refn_pred (Leqn n)))) (Bc True) } @-}
reduce_leqn_tt :: Int -> Int -> EvalsTo
reduce_leqn_tt n m = reduce_leq_tt n m


 
{-@ lem_den_leq :: ProofOf(Denotes (ty Leq) (Prim Leq)) @-}
lem_den_leq :: Denotes
lem_den_leq = DFunc 1 (TRefn TInt 4 (Bc True)) t' (Prim Leq) (BTPrm BEmpty Leq) val_den_func
  where
    t' = TFunc 2 (TRefn TInt 5 (Bc True)) (TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                                                              (App (App (Prim Leq) (BV 1)) (BV 2)) ))
    {-@ val_den_func :: v_x:Value -> ProofOf(Denotes (TRefn TInt 4 (Bc True)) v_x)
                                  -> ProofOf(ValueDenoted (App (Prim Leq) v_x) (tsubBV 1 v_x t')) @-}
    val_den_func :: Expr -> Denotes -> ValueDenoted
    val_den_func v_x den_tx_vx = case v_x of 
      (Ic n) -> ValDen (App (Prim Leq) (Ic n)) (tsubBV 1 (Ic n) t') (Prim (Leqn n))
                       (lem_step_evals (App (Prim Leq) (Ic n)) (Prim (Leqn n)) 
                       (EPrim Leq (Ic n))) den_t'n_leqn
        where
          t'n = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Leq) (Ic n)) (BV 2)) )
          den_t'n_leqn = DFunc 2 (TRefn TInt 5 (Bc True)) t'n (Prim (Leqn n)) 
                               (BTPrm BEmpty (Leqn n)) val_den_func2
          {-@ val_den_func2 :: v_x:Value -> ProofOf(Denotes (TRefn TInt 5 (Bc True)) v_x)
                                  -> ProofOf(ValueDenoted (App (Prim (Leqn n)) v_x) (tsubBV 2 v_x t'n)) @-}
          val_den_func2 :: Expr -> Denotes -> ValueDenoted
          val_den_func2 v_x den_tx_vx = case v_x of 
            (Ic m) -> ValDen (App (Prim (Leqn n)) (Ic m)) (tsubBV 2 (Ic m) t'n) (Bc (n <= m))
                         (lem_step_evals (App (Prim (Leqn n)) (Ic m)) (Bc (n <= m)) (EPrim (Leqn n) (Ic m)))
                         den_t'nm_lte
              where
                t'nm = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Leq) (Ic n)) (Ic m)) )
                den_t'nm_lte = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Leq) (Ic n)) (Ic m)))
                                     (Bc (n <= m)) (BTBC BEmpty (n <= m)) ev_prt'nm_lte
                {- @ ev_prt'nm_lte :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc (intLeq n m))) 
                                               (App (App (Prim Leq) (Ic n)) (Ic m))) (Bc True)) @-}
                ev_prt'nm_lte = reduce_leq_tt n m
            _      -> impossible ("by lemma" ? lem_den_ints v_x (TRefn TInt 5 (Bc True)) den_tx_vx)
      _      -> impossible ("by lemma" ? lem_den_ints v_x (TRefn TInt 4 (Bc True)) den_tx_vx)


{-@ lem_den_leqn :: n:Int -> ProofOf(Denotes (ty (Leqn n)) (Prim (Leqn n))) @-}
lem_den_leqn :: Int -> Denotes
lem_den_leqn n = DFunc 2 (TRefn TInt 5 (Bc True)) t'n (Prim (Leqn n)) (BTPrm BEmpty (Leqn n)) val_den_func
  where
    t'n = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Leq) (Ic n)) (BV 2)) )
    {-@ val_den_func :: v_x:Value -> ProofOf(Denotes (TRefn TInt 5 (Bc True)) v_x)
                                  -> ProofOf(ValueDenoted (App (Prim (Leqn n)) v_x) (tsubBV 2 v_x t'n)) @-}
    val_den_func :: Expr -> Denotes -> ValueDenoted
    val_den_func v_x den_tx_vx = case v_x of 
      (Ic m) -> ValDen (App (Prim (Leqn n)) (Ic m)) (tsubBV 2 (Ic m) t'n) (Bc (n <= m))
                       (lem_step_evals (App (Prim (Leqn n)) (Ic m)) (Bc (n <= m)) (EPrim (Leqn n) (Ic m)))
                       den_t'nm_lte
        where
          t'nm = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Leq) (Ic n)) (Ic m)) )
          den_t'nm_lte = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Leq) (Ic n)) (Ic m)))
                               (Bc (n <= m)) (BTBC BEmpty (n <= m)) ev_prt'nm_nlte
          {- @ ev_prt'nm_nlte :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc (intLeq n m))) 
                                                (App (App (Prim Leq) (Ic n)) (Ic m))) (Bc True)) @-}
          ev_prt'nm_nlte = reduce_leqn_tt n m
      _      -> impossible ("by lemma" ? lem_den_ints v_x (TRefn TInt 5 (Bc True)) den_tx_vx)

