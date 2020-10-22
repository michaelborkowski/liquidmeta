{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-}  
{- @ LIQUID "--no-totality" @-}  
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module DenotationsSelfify where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import Entailments
import LemmasChangeVarWF
import LemmasWeakenWF
import LemmasWellFormedness
import LemmasTyping
import LemmasSubtyping
import LemmasChangeVarTyp
import LemmasWeakenTyp
--import SubstitutionLemmaWF

{-@ reflect foo40 @-}
foo40 x = Just x
foo40 :: a -> Maybe a

--- Lemma 7 in the paper version
{-@ lem_denotations_selfify :: t:Type -> k:Kind -> ProofOf(WFType Empty t k) 
        -> e:Expr -> v:Value -> ProofOf(EvalsTo e v) -> ProofOf(Denotes t v)
        -> ProofOf(Denotes (self t e) v) @-}
lem_denotations_selfify :: Type -> Kind -> WFType -> Expr -> Expr
                                -> EvalsTo -> Denotes -> Denotes
lem_denotations_selfify (TRefn b z p)      k p_emp_t e v ev_e_v den_t_v = case den_t_v of
  (DRefn _b _z _p _v p_v_b ev_pv_tt) -> DRefn b z (selfify p b z e) v p_v_b ev_selfpv_tt
      where
        ev_selfpv_tt = undefined
lem_denotations_selfify (TFunc z t_z t')   k p_emp_t e v ev_e_v den_t_v = den_t_v
lem_denotations_selfify (TExists z t_z t') k p_emp_t e v ev_e_v den_t_v = case den_t_v of
  (DExis _z _tz _t' _v p_v_ert' v_z den_tz_vz den_t'vz_v) -> undefined
lem_denotations_selfify (TPoly a k_a t')   k p_emp_t e v ev_e_v den_t_v = den_t_v
