{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesDenotationsEq where

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

{-@ reflect foo47 @-}
foo47 x = Just x
foo47 :: a -> Maybe a

{-@ lem_den_eq :: ProofOf(Denotes (ty Eq) (Prim Eq)) @-}
lem_den_eq :: Denotes
lem_den_eq = DFunc 1 (TRefn TInt 1 (Bc True)) t' (Prim Eq) (FTPrm FEmpty Eq) val_den_func
  where
    t' = TFunc 2 (TRefn TInt 2 (Bc True)) (TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                                                         (App (App (Prim Eq) (BV 1)) (BV 2)) ))
    {-@ val_den_func :: v_x:Value -> ProofOf(Denotes (TRefn TInt 1 (Bc True)) v_x)
                                  -> ProofOf(ValueDenoted (App (Prim Eq) v_x) (tsubBV 1 v_x t')) @-}
    val_den_func :: Expr -> Denotes -> ValueDenoted
    val_den_func v_x den_tx_vx = case v_x of 
      (Ic n) -> ValDen (App (Prim Eq) (Ic n)) (tsubBV 1 (Ic n) t') (Prim (Eqn n))
                       (lem_step_evals (App (Prim Eq) (Ic n)) (Prim (Eqn n)) 
                       (EPrim Eq (Ic n))) den_t'n_eqn
        where
          t'n = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Eq) (Ic n)) (BV 2)) )
          den_t'n_eqn = DFunc 2 (TRefn TInt 2 (Bc True)) t'n (Prim (Eqn n)) 
                              (FTPrm FEmpty (Eqn n)) val_den_func2
          {-@ val_den_func2 :: v_x:Value -> ProofOf(Denotes (TRefn TInt 2 (Bc True)) v_x)
                                  -> ProofOf(ValueDenoted (App (Prim (Eqn n)) v_x) (tsubBV 2 v_x t'n)) @-}
          val_den_func2 :: Expr -> Denotes -> ValueDenoted
          val_den_func2 v_x den_tx_vx = case v_x of 
            (Ic m) -> ValDen (App (Prim (Eqn n)) (Ic m)) (tsubBV 2 (Ic m) t'n) (Bc (n == m))
                             (lem_step_evals (App (Prim (Eqn n)) (Ic m)) (Bc (n == m)) 
                             (EPrim (Eqn n) (Ic m))) den_t'nm_eq
              where
                t'nm = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Eq) (Ic n)) (Ic m)) )
                den_t'nm_eq = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Eq) (Ic n)) (Ic m)))
                                    (Bc (n == m)) (FTBC FEmpty (n == m)) ev_prt'nm_eq
                {- @ ev_prt'nm_eq :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc (intEq n m))) 
                                              (App (App (Prim Eq) (Ic n)) (Ic m))) (Bc True)) @-}
                ev_prt'nm_eq = reduce_eq_tt n m
            _      -> impossible ("by lemma" ? lem_den_ints v_x (TRefn TInt 2 (Bc True)) den_tx_vx)
      _      -> impossible ("by lemma" ? lem_den_ints v_x (TRefn TInt 1 (Bc True)) den_tx_vx)

{-@ lem_den_eqn :: n:Int -> ProofOf(Denotes (ty (Eqn n)) (Prim (Eqn n))) @-}
lem_den_eqn :: Int -> Denotes
lem_den_eqn n = DFunc 2 (TRefn TInt 2 (Bc True)) t'n (Prim (Eqn n)) (FTPrm FEmpty (Eqn n)) val_den_func
  where
    t'n = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Eq) (Ic n)) (BV 2)) )
    {-@ val_den_func :: v_x:Value -> ProofOf(Denotes (TRefn TInt 2 (Bc True)) v_x)
                                  -> ProofOf(ValueDenoted (App (Prim (Eqn n)) v_x) (tsubBV 2 v_x t'n)) @-}
    val_den_func :: Expr -> Denotes -> ValueDenoted
    val_den_func v_x den_tx_vx = case v_x of 
      (Ic m) -> ValDen (App (Prim (Eqn n)) (Ic m)) (tsubBV 2 (Ic m) t'n) (Bc (n == m))
                       (lem_step_evals (App (Prim (Eqn n)) (Ic m)) (Bc (n == m)) (EPrim (Eqn n) (Ic m)))
                       den_t'nm_eq
        where
          t'nm = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Eq) (Ic n)) (Ic m)) )
          den_t'nm_eq = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim Eq) (Ic n)) (Ic m)) )
                              (Bc (n == m)) (FTBC FEmpty (n == m)) ev_prt'nm_neq
          {- @ ev_prt'nm_neq :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc (intEq n m))) 
                                                    (App (App (Prim Eq) (Ic n)) (Ic m))) (Bc True)) @-}
          ev_prt'nm_neq = reduce_eqn_tt n m
      _      -> impossible ("by lemma" ? lem_den_ints v_x (TRefn TInt 2 (Bc True)) den_tx_vx)
