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
import PrimitivesSemantics

{-@ reflect foo56 @-}
foo56 x = Just x
foo56 :: a -> Maybe a

{-@ reflect t'_eq @-}
t'_eq :: Type
t'_eq = TFunc 2 (TRefn TInt Z (Bc True)) (TRefn TBool Z (App (App (Prim Eqv) (BV 0))
                                                         (App (App (Prim Eq) (BV 1)) (BV 2)) ))
{-@ reflect t'eqn @-}
t'eqn :: Int -> Type
t'eqn n = TRefn TBool Z (App (App (Prim Eqv) (BV 0)) (App (App (Prim Eq) (Ic n)) (BV 2)) )

{-@ lem_den_eq :: ProofOf(Denotes (ty Eq) (Prim Eq)) @-}
lem_den_eq :: Denotes
lem_den_eq = DFunc 1 (TRefn TInt Z (Bc True)) t'_eq (Prim Eq) (FTPrm FEmpty Eq) val_den_func_eq

{-@ val_den_func_eq :: v_x:Value -> ProofOf(Denotes (TRefn TInt Z (Bc True)) v_x)
                                 -> ProofOf(ValueDenoted (App (Prim Eq) v_x) (tsubBV 1 v_x t'_eq)) @-}
val_den_func_eq :: Expr -> Denotes -> ValueDenoted
val_den_func_eq v_x den_tx_vx = case v_x of 
  (Ic n) -> ValDen (App (Prim Eq) (Ic n)) (tsubBV 1 (Ic n) t'_eq) (Prim (Eqn n))
                       (lem_step_evals (App (Prim Eq) (Ic n)) (Prim (Eqn n)) 
                       (EPrim Eq (Ic n))) (den_t'eqn_eq n)
  _      -> impossible ("by lemma" ? lem_den_ints v_x (TRefn TInt Z (Bc True)) den_tx_vx)
   
{-@ den_t'eqn_eq :: n:Int -> ProofOf(Denotes (tsubBV 1 (Ic n) t'_eq) (Prim (Eqn n))) @-}
den_t'eqn_eq :: Int -> Denotes 
den_t'eqn_eq n = DFunc 2 (TRefn TInt Z (Bc True)) (t'eqn n) (Prim (Eqn n)) 
                       (FTPrm FEmpty (Eqn n)) (val_den_func_eq2 n)
      
{-@ val_den_func_eq2 :: n:Int -> v_x:Value -> ProofOf(Denotes (TRefn TInt Z (Bc True)) v_x)
                              -> ProofOf(ValueDenoted (App (Prim (Eqn n)) v_x) (tsubBV 2 v_x (t'eqn n))) @-}
val_den_func_eq2 :: Int -> Expr -> Denotes -> ValueDenoted
val_den_func_eq2 n v_x den_tx_vx = case v_x of 
    (Ic m) -> ValDen (App (Prim (Eqn n)) (Ic m)) (tsubBV 2 (Ic m) (t'eqn n)) (Bc (n == m))
                     (lem_step_evals (App (Prim (Eqn n)) (Ic m)) (Bc (n == m)) 
                     (EPrim (Eqn n) (Ic m))) den_t'eqnm_eq
      where
        t'eqnm = TRefn TBool Z (App (App (Prim Eqv) (BV 0)) (App (App (Prim Eq) (Ic n)) (Ic m)) )
        den_t'eqnm_eq = DRefn TBool Z (App (App (Prim Eqv) (BV 0)) (App (App (Prim Eq) (Ic n)) (Ic m)))
                            (Bc (n == m)) (FTBC FEmpty (n == m)) ev_prt'eqnm_eq
        {- @ ev_prt'eqnm_eq :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc (intEq n m))) 
                                      (App (App (Prim Eq) (Ic n)) (Ic m))) (Bc True)) @-}
        ev_prt'eqnm_eq = reduce_eq_tt n m
    _      -> impossible ("by lemma" ? lem_den_ints v_x (TRefn TInt Z (Bc True)) den_tx_vx)

{-@ lem_den_eqn :: n:Int -> ProofOf(Denotes (ty (Eqn n)) (Prim (Eqn n))) @-}
lem_den_eqn :: Int -> Denotes
lem_den_eqn n = DFunc 2 (TRefn TInt Z (Bc True)) (t'eqn n) (Prim (Eqn n)) (FTPrm FEmpty (Eqn n)) 
                      (val_den_func_eqn n)
  
{-@ val_den_func_eqn :: n:Int -> v_x:Value -> ProofOf(Denotes (TRefn TInt Z (Bc True)) v_x)
                              -> ProofOf(ValueDenoted (App (Prim (Eqn n)) v_x) (tsubBV 2 v_x (t'eqn n))) @-}
val_den_func_eqn :: Int -> Expr -> Denotes -> ValueDenoted
val_den_func_eqn n v_x den_tx_vx = case v_x of 
  (Ic m) -> ValDen (App (Prim (Eqn n)) (Ic m)) (tsubBV 2 (Ic m) (t'eqn n)) (Bc (n == m))
                   (lem_step_evals (App (Prim (Eqn n)) (Ic m)) (Bc (n == m)) (EPrim (Eqn n) (Ic m)))
                   den_t'eqnm_eq
    where
      t'eqnm = TRefn TBool Z (App (App (Prim Eqv) (BV 0)) (App (App (Prim Eq) (Ic n)) (Ic m)) )
      den_t'eqnm_eq = DRefn TBool Z (App (App (Prim Eqv) (BV 0)) (App (App (Prim Eq) (Ic n)) (Ic m)) )
                            (Bc (n == m)) (FTBC FEmpty (n == m)) ev_prt'eqnm_neq
      {- @ ev_prt'eqnm_neq :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc (intEq n m))) 
                                              (App (App (Prim Eq) (Ic n)) (Ic m))) (Bc True)) @-}
      ev_prt'eqnm_neq = reduce_eqn_tt n m
  _      -> impossible ("by lemma" ? lem_den_ints v_x (TRefn TInt Z (Bc True)) den_tx_vx)
