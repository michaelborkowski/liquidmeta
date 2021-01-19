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
import Entailments
import PrimitivesSemantics
import PrimitivesDenotationsEqv
import PrimitivesDenotationsEq

{-@ reflect foo57 @-}
foo57 x = Just x
foo57 :: a -> Maybe a

-- {-@ lem_den_eqv' :: ProofOf(Denotes (

{-@ lem_den_eql :: () -> ProofOf(Denotes (ty Eql) (Prim Eql)) @-}
lem_den_eql :: () -> Denotes
lem_den_eql () = DPoly 1 Base t'{-(TFunc (firstBV Eql) (inType Eql) (ty' Eql))-} (Prim Eql)
                    (FTPrm FEmpty Eql) val_den_func 
  where
    {-@ val_den_func :: t_a:Type -> ProofOf(WFType Empty t_a Base)
                            -> ProofOf(ValueDenoted (AppT (Prim Eql) t_a) (tsubBTV 1 t_a t')) @-}
    val_den_func :: Type -> WFType -> ValueDenoted
    val_den_func t_a pf_emp_ta = case (erase t_a) of
      (FTBasic TBool) -> undefined {- ValDen (AppT (Prim Eql) t_a) (tsubBTV 1 t_a t') (Prim Eqv)
                                (lem_step_evals (AppT (Prim Eql) t_a) (Prim Eqv) (EPrimT Eql t_a)) 
                                lem_den_eqv -}
      (FTBasic TInt)  -> undefined {- ValDen (AppT (Prim Eql) t_a) (tsubBTV 1 t_a t') (Prim Eq)
                                (lem_step_evals (AppT (Prim Eql) t_a) (Prim Eq)  (EPrimT Eql t_a)) 
                                lem_den_eq -}
      _               -> impossible ("by lemma" ? lem_base_types (erase t_a)
                                             (lem_erase_wftype Empty t_a Base pf_emp_ta))
    t' = (TFunc (firstBV Eql) (inType Eql) (ty' Eql))
