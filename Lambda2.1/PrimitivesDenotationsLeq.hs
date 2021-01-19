{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesDenotationsLeq where

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
import Entailments
import PrimitivesSemantics

{-@ reflect foo54 @-}
foo54 x = Just x
foo54 :: a -> Maybe a

{-@ lem_den_leq :: ProofOf(Denotes (ty Leq) (Prim Leq)) @-}
lem_den_leq :: Denotes
lem_den_leq = DFunc 1 (TRefn TInt Z (Bc True)) t' (Prim Leq) (FTPrm FEmpty Leq) val_den_func
  where
    t' = TFunc 2 (TRefn TInt Z (Bc True)) (TRefn TBool Z (App (App (Prim Eqv) (BV 0)) 
                                                              (App (App (Prim Leq) (BV 1)) (BV 2)) ))
    {-@ val_den_func :: v_x:Value -> ProofOf(Denotes (TRefn TInt Z (Bc True)) v_x)
                                  -> ProofOf(ValueDenoted (App (Prim Leq) v_x) (tsubBV 1 v_x t')) @-}
    val_den_func :: Expr -> Denotes -> ValueDenoted
    val_den_func v_x den_tx_vx = case v_x of 
      (Ic n) -> ValDen (App (Prim Leq) (Ic n)) (tsubBV 1 (Ic n) t') (Prim (Leqn n))
                       (lem_step_evals (App (Prim Leq) (Ic n)) (Prim (Leqn n)) 
                       (EPrim Leq (Ic n))) den_t'n_leqn
        where
          t'n = TRefn TBool Z (App (App (Prim Eqv) (BV 0)) (App (App (Prim Leq) (Ic n)) (BV 2)) )
          den_t'n_leqn = DFunc 2 (TRefn TInt Z (Bc True)) t'n (Prim (Leqn n)) 
                               (FTPrm FEmpty (Leqn n)) val_den_func2
          {-@ val_den_func2 :: v_x:Value -> ProofOf(Denotes (TRefn TInt Z (Bc True)) v_x)
                                  -> ProofOf(ValueDenoted (App (Prim (Leqn n)) v_x) (tsubBV 2 v_x t'n)) @-}
          val_den_func2 :: Expr -> Denotes -> ValueDenoted
          val_den_func2 v_x den_tx_vx = case v_x of 
            (Ic m) -> ValDen (App (Prim (Leqn n)) (Ic m)) (tsubBV 2 (Ic m) t'n) (Bc (n <= m))
                         (lem_step_evals (App (Prim (Leqn n)) (Ic m)) (Bc (n <= m)) (EPrim (Leqn n) (Ic m)))
                         den_t'nm_lte
              where
                t'nm = TRefn TBool Z (App (App (Prim Eqv) (BV 0)) (App (App (Prim Leq) (Ic n)) (Ic m)) )
                den_t'nm_lte = DRefn TBool Z (App (App (Prim Eqv) (BV 0)) (App (App (Prim Leq) (Ic n)) (Ic m)))
                                     (Bc (n <= m)) (FTBC FEmpty (n <= m)) ev_prt'nm_lte
                {- @ ev_prt'nm_lte :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc (intLeq n m))) 
                                               (App (App (Prim Leq) (Ic n)) (Ic m))) (Bc True)) @-}
                ev_prt'nm_lte = reduce_leq_tt n m
            _      -> impossible ("by lemma" ? lem_den_ints v_x (TRefn TInt Z (Bc True)) den_tx_vx)
      _      -> impossible ("by lemma" ? lem_den_ints v_x (TRefn TInt Z (Bc True)) den_tx_vx)

{-@ lem_den_leqn :: n:Int -> ProofOf(Denotes (ty (Leqn n)) (Prim (Leqn n))) @-}
lem_den_leqn :: Int -> Denotes
lem_den_leqn n = DFunc 2 (TRefn TInt Z (Bc True)) t'n (Prim (Leqn n)) (FTPrm FEmpty (Leqn n)) val_den_func
  where
    t'n = TRefn TBool Z (App (App (Prim Eqv) (BV 0)) (App (App (Prim Leq) (Ic n)) (BV 2)) )
    {-@ val_den_func :: v_x:Value -> ProofOf(Denotes (TRefn TInt Z (Bc True)) v_x)
                                  -> ProofOf(ValueDenoted (App (Prim (Leqn n)) v_x) (tsubBV 2 v_x t'n)) @-}
    val_den_func :: Expr -> Denotes -> ValueDenoted
    val_den_func v_x den_tx_vx = case v_x of 
      (Ic m) -> ValDen (App (Prim (Leqn n)) (Ic m)) (tsubBV 2 (Ic m) t'n) (Bc (n <= m))
                       (lem_step_evals (App (Prim (Leqn n)) (Ic m)) (Bc (n <= m)) (EPrim (Leqn n) (Ic m)))
                       den_t'nm_lte
        where
          t'nm = TRefn TBool Z (App (App (Prim Eqv) (BV 0)) (App (App (Prim Leq) (Ic n)) (Ic m)) )
          den_t'nm_lte = DRefn TBool Z (App (App (Prim Eqv) (BV 0)) (App (App (Prim Leq) (Ic n)) (Ic m)))
                               (Bc (n <= m)) (FTBC FEmpty (n <= m)) ev_prt'nm_nlte
          {- @ ev_prt'nm_nlte :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc (intLeq n m))) 
                                                (App (App (Prim Leq) (Ic n)) (Ic m))) (Bc True)) @-}
          ev_prt'nm_nlte = reduce_leqn_tt n m
      _      -> impossible ("by lemma" ? lem_den_ints v_x (TRefn TInt Z (Bc True)) den_tx_vx)
