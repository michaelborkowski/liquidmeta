{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module DenotationsSelfify where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFTyping
import WellFormedness
import PrimitivesFTyping
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasFTyping
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import PrimitivesSemantics 
import LemmasWeakenWF
import SubstitutionLemmaWF

{-@ reflect foo50 @-}
foo50 x = Just x
foo50 :: a -> Maybe a

{-@ lem_equals_evals :: e:Expr -> v:Value -> ProofOf(EvalsTo e v) -> b:Basic 
        -> ProofOf(HasFType FEmpty v (FTBasic b))
        -> ProofOf(EvalsTo (App (App (equals b) v) e) (Bc True)) @-}
lem_equals_evals :: Expr -> Expr -> EvalsTo -> Basic -> HasFType -> EvalsTo
lem_equals_evals e v ev_e_v TBool p_v_b = case v of
  (Bc w)  -> ev_eqv_tt
    where
      ev_eqv_tt  = lemma_eqv_semantics v w (Refl v) e w ev_e_v
  _       -> impossible ("by lemma" ? lem_bool_values v p_v_b)
lem_equals_evals e v ev_e_v TInt  p_v_b = case v of
  (Ic n)  -> ev_eq_tt
    where
      ev_eq_tt   = lemma_eq_semantics v n (Refl v) e n ev_e_v
  _       -> impossible ("by lemma" ? lem_int_values v p_v_b)

--- Lemma 7 in the paper version
{-@ lem_denotations_selfify :: t:Type 
        -> { e:Expr | Set_emp (freeBV e) } -> v:Value -> ProofOf(EvalsTo e v) -> ProofOf(Denotes t v)
        -> ProofOf(Denotes (self t e) v) @-}
lem_denotations_selfify :: Type {-> WFType-} -> Expr -> Expr -> EvalsTo -> Denotes -> Denotes
lem_denotations_selfify (TRefn b z p)      {-p_emp_t-} e v ev_e_v den_t_v = case den_t_v of
  (DRefn _b _z _p _v p_v_b ev_pv_tt) -> DRefn b z (selfify p b z e) v p_v_b ev_selfpv_tt
      where           -- (subBV x v p) ~>* tt          -- (subBV x v (selfify p b z e)) ~>* tt
        ev_rhs_tt    = lem_equals_evals e v ev_e_v b p_v_b 
        ev_selfpv_tt = lemma_and_semantics (subBV z v p) True ev_pv_tt 
                           (subBV z v (App (App (equals b) (BV z)) e) ? lem_subBV_notin z v (equals b)
                                                                      ? lem_subBV_notin z v e) 
                           True ev_rhs_tt
lem_denotations_selfify (TFunc z t_z t')   {-p_emp_t-} e v ev_e_v den_t_v = den_t_v
lem_denotations_selfify (TExists z t_z t') {-p_emp_t-} e v ev_e_v den_t_v = case den_t_v of
  (DExis _z _tz _t' _v p_v_tzt' v_z den_tz_vz den_t'vz_v) 
    -> DExis z t_z (self t' e) v  p_v_tzt' v_z den_tz_vz den_selft'vz_v
         where 
           den_selft'vz_v = lem_denotations_selfify (tsubBV z v_z t') {-p_emp_t'vz -}
                                                    e v ev_e_v den_t'vz_v
               ? lem_tsubBV_self z v_z t' e
