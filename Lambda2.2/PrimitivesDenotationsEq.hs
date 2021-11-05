{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--fuel=4"      @-}
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

{-@ lem_den_eq :: ProofOf(Denotes (ty Eq) (Prim Eq)) @-}
lem_den_eq :: Denotes
lem_den_eq = DFunc 1 (TRefn TInt Z (Bc True)) (ty' Eq) (Prim Eq ? val_eq) 
                   (FTPrm FEmpty Eq) val_den_func_eq
  where
    val_eq = isValue (Prim Eq) ? isTerm (Prim Eq)

{-@ lem_den_eq_p :: { p:Pred | Set_emp (tfreeBV (TRefn TInt Z p)) }
        -> ProofOf(Denotes (TFunc 1 (TRefn TInt Z p)           
                                  (TFunc 2 (TRefn TInt Z p) (TRefn TBool Z (refn_pred Eq)))) (Prim Eq)) @-}
lem_den_eq_p :: Expr -> Denotes
lem_den_eq_p p = lem_drefn_in_dfunc_twice 1 2 TInt Z (TRefn TBool Z (refn_pred Eq))
                                           (Prim Eq) lem_den_eq p

{-@ val_den_func_eq :: v_x:Value -> ProofOf(Denotes (TRefn TInt Z (Bc True)) v_x)
                                 -> ProofOf(ValueDenoted (App (Prim Eq) v_x) (tsubBV 1 v_x (ty' Eq))) @-}
val_den_func_eq :: Expr -> Denotes -> ValueDenoted
val_den_func_eq v_x den_tx_vx = case v_x of 
  (Ic n) -> ValDen (App (Prim Eq) (Ic n)) (tsubBV 1 (Ic n) (ty' Eq)) (Prim (Eqn n))
                       (lem_step_evals (App (Prim Eq) (Ic n)) (Prim (Eqn n)) 
                       (EPrim Eq (Ic n))) (den_t'eqn_eq n)
  _      -> impossible ("by lemma" ? lem_den_ints v_x (TRefn TInt Z (Bc True)) den_tx_vx)
   
{-@ den_t'eqn_eq :: n:Int -> ProofOf(Denotes (tsubBV 1 (Ic n) (ty' Eq)) (Prim (Eqn n))) @-}
den_t'eqn_eq :: Int -> Denotes 
den_t'eqn_eq n = DFunc 2 (TRefn TInt Z (Bc True)) t'eqn_n (Prim (Eqn n) ? val_eqn) 
                       (FTPrm FEmpty (Eqn n)) (val_den_func_eq2 n)
    ? ( tsubBV 1 (Ic n ? term_n) (ty' Eq) ? lem_tsubBV_notin 1 (Ic n ? term_n) (TRefn TInt Z (Bc True))
    === TFunc 2 (TRefn TInt Z (Bc True)) (tsubBV 1 (Ic n ? term_n) (TRefn TBool Z (refn_pred Eq))) )
  where
    t'eqn_n = tsubBV 1 (Ic n ? term_n) (TRefn TBool Z (refn_pred Eq))
    term_n  = isTerm (Ic n)
    val_eqn = isValue (Prim (Eqn n)) ? isTerm (Prim (Eqn n))
      
{-@ val_den_func_eq2 :: n:Int -> v_x:Value -> ProofOf(Denotes (TRefn TInt Z (Bc True)) v_x)
      -> ProofOf(ValueDenoted (App (Prim (Eqn n)) v_x) 
                              (tsubBV 2 v_x (tsubBV 1 (Ic n) (TRefn TBool Z (refn_pred Eq))))) @-}
val_den_func_eq2 :: Int -> Expr -> Denotes -> ValueDenoted
val_den_func_eq2 n v_x den_tx_vx = case v_x of 
    (Ic m) -> ValDen (App (Prim (Eqn n)) (Ic m)) (tsubBV 2 (Ic m) t'eqn_n) (Bc (n == m) ? tm_nm)
                     (lem_step_evals (App (Prim (Eqn n)) (Ic m)) (Bc (n == m)) 
                     (EPrim (Eqn n) (Ic m))) den_t'eqnm_eq
      where
        t'eqn_n = tsubBV 1 (Ic n ? term_n) (TRefn TBool Z (refn_pred Eq))
        den_t'eqnm_eq = DRefn TBool Z p_nm (Bc (n == m) ? tm_nm) (FTBC FEmpty (n == m)) ev_prt'eqnm_eq
        p_nm    = subBV 2 (Ic m) (subBV 1 (Ic n ? term_n) (refn_pred Eq))
        {-@ ev_prt'eqnm_eq :: ProofOf(EvalsTo (subBV 0 (Bc (intEq n m)) (subBV 2 (Ic m) (subBV 1 (Ic n) (refn_pred Eq)))) (Bc True)) @-}
        ev_prt'eqnm_eq = reduce_eq_tt n m ? intEq n m
        term_n  = isTerm (Ic n)
        tm_nm   = isTerm (Bc (n == m))           
    _      -> impossible ("by lemma" ? lem_den_ints v_x (TRefn TInt Z (Bc True)) den_tx_vx)

{-@ lem_den_eqn :: n:Int -> ProofOf(Denotes (ty (Eqn n)) (Prim (Eqn n))) @-}
lem_den_eqn :: Int -> Denotes
lem_den_eqn n = DFunc 2 (TRefn TInt Z (Bc True)) (ty' (Eqn n)) (Prim (Eqn n) ? val_eqn) 
                      (FTPrm FEmpty (Eqn n)) (val_den_func_eqn n)
  where
    val_eqn = isValue (Prim (Eqn n)) ? isTerm (Prim (Eqn n))
  
{-@ val_den_func_eqn :: n:Int -> v_x:Value -> ProofOf(Denotes (TRefn TInt Z (Bc True)) v_x)
                     -> ProofOf(ValueDenoted (App (Prim (Eqn n)) v_x) (tsubBV 2 v_x (ty' (Eqn n)))) @-}
val_den_func_eqn :: Int -> Expr -> Denotes -> ValueDenoted
val_den_func_eqn n v_x den_tx_vx = case v_x of 
  (Ic m) -> ValDen (App (Prim (Eqn n)) (Ic m)) (tsubBV 2 (Ic m) (ty' (Eqn n))) (Bc (n == m) ? tm_nm)
                   (lem_step_evals (App (Prim (Eqn n)) (Ic m)) (Bc (n == m)) (EPrim (Eqn n) (Ic m)))
                   den_t'eqnm_eq
    where
      den_t'eqnm_eq = DRefn TBool Z p_nm (Bc (n == m) ? tm_nm) (FTBC FEmpty (n == m)) ev_prt'eqnm_neq
      p_nm          = subBV 2 (Ic m) (refn_pred (Eqn n))
      ev_prt'eqnm_neq = reduce_eqn_tt n m ? intEq n m
      tm_nm         = isTerm (Bc (n == m))
  _      -> impossible ("by lemma" ? lem_den_ints v_x (TRefn TInt Z (Bc True)) den_tx_vx)
