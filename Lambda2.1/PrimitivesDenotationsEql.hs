{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesDenotationsEql where

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
import PrimitivesDenotationsEqv
import PrimitivesDenotationsEq

{-@ reflect foo34 @-}
foo34 x = Just x
foo34 :: a -> Maybe a

{-@ lem_den_eqv' :: ProofOf(Denotes (

{-@ lem_den_eql :: ProofOf(Denotes (ty Eql) (Prim Eql)) @-}
lem_den_eql :: Denotes
lem_den_eql = DPoly 1 Base t'{-(TFunc (firstBV Eql) (inType Eql) (ty' Eql))-} (Prim Eql)
                    (FTPrm FEmpty Eql) val_den_func
  where
    t' = (TFunc (firstBV Eql) (inType Eql) (ty' Eql))
    {-@ val_den_func :: t_a:Type -> ProofOf(WFType Empty t_a Base)
                            -> ProofOf(ValueDenoted (AppT (Prim Eql) t_a) (tsubBTV 1 t_a t')) @-}
    val_den_func :: Type -> WFType -> ValueDenoted
    val_den_func t_a pf_emp_ta = case (erase t_a) of
      (FTBasic TBool) -> ValDen (AppT (Prim Eql) t_a) (tsubBTV 1 t_a t') (Prim Eqv)
                                (lem_step_evals (AppT (Prim Eql) t_a) (Prim Eqv) (EPrimT Eql t_a)) 
                                lem_den_eqv
      (FTBasic TInt)  -> ValDen (AppT (Prim Eql) t_a) (tsubBTV 1 t_a t') (Prim Eq)
                                (lem_step_evals (AppT (Prim Eql) t_a) (Prim Eq)  (EPrimT Eql t_a)) 
                                lem_den_eq
      {-(TExists x t_x ta') -> ValDen (AppT (Prim Eql) t_a) (tsubBTV a t_a t') 
        where
          (WFExis _ _ _ _ _ _ _ y pf_y_ta') = pf_emp_ta
          (ValDen _ _ v ev_e_v den_ta'_v) = val_den_func ta' -}
      _               -> impossible ("by lemma" ? lem_base_types (erase t_a)
                                             (lem_erase_wftype Empty t_a Base pf_emp_ta))
{-
DFunc 1 (TRefn TInt 1 (Bc True)) t' (Prim Eq) (FTPrm FEmpty Eq) val_den_func
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
-}
