{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasExactness where

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
import DenotationsSelfify
import DenotationsSoundnessSub
import PrimitivesSemantics
import PrimitivesDenotations
import DenotationsSoundnessTyp

{-@ reflect foo52 @-}
foo52 x = Just x
foo52 :: a -> Maybe a

{-@ lem_self_idempotent_upper :: g:Env -> t:Type -> k:Kind -> e:Expr -> ProofOf(WFType g t k)
        -> ProofOf(WFEnv g) -> ProofOf(Subtype g (self t e) (self (self t e) e)) @-}
lem_self_idempotent_upper :: Env -> Type -> Kind -> Expr -> WFType -> WFEnv -> Subtype
lem_self_idempotent_upper = undefined

{-@ lem_self_idempotent_lower :: g:Env -> t:Type -> k:Kind -> e:Expr -> ProofOf(WFType g t k)
        -> ProofOf(WFEnv g) -> ProofOf(Subtype g (self (self t e) e) (self t e)) @-}
lem_self_idempotent_lower :: Env -> Type -> Kind -> Expr -> WFType -> WFEnv -> Subtype
lem_self_idempotent_lower g (TRefn b z p) k e p_g_t p_g_wf 
  = undefined
lem_self_idempotent_lower g t@(TFunc z t_z t') k e p_g_t p_g_wf 
  = lem_sub_refl g t k p_g_t p_g_wf
lem_self_idempotent_lower g (TExists z t_z t') k e p_g_t p_g_wf 
  = undefined
lem_self_idempotent_lower g t@(TPoly a k_a t') k e p_g_t p_g_wf 
  = lem_sub_refl g t k p_g_t p_g_wf

{-@ lem_exact_subtype :: g:Env -> s:Type -> t:Type -> ProofOf(Subtype g s t)
        -> e:Expr -> t_e:Type -> ProofOf(HasType g e t_e) 
        -> ProofOf(Subtype g (self s e) (self t e)) @-}
lem_exact_subtype :: Env -> Type -> Type -> Subtype -> Expr -> Type -> HasType -> Subtype
lem_exact_subtype g s t (SBase {}) e t_e p_e_te = undefined
lem_exact_subtype g s t (SFunc {}) e t_e p_e_te = undefined
lem_exact_subtype g s t (SWitn {}) e t_e p_e_te = undefined
lem_exact_subtype g s t (SBind {}) e t_e p_e_te = undefined
lem_exact_subtype g s t (SPoly {}) e t_e p_e_te = undefined

{-@ lem_exact_type :: g:Env -> v:Value -> t:Type -> ProofOf(HasType g v t)
        -> ProofOf(HasType g v (self t v)) @-}
lem_exact_type :: Env -> Expr -> Type -> HasType -> HasType
lem_exact_type g e t (TBC {}) = undefined
lem_exact_type g e t (TIC {}) = undefined
lem_exact_type g e t (TVar1 {}) = undefined
lem_exact_type g e t (TVar2 {}) = undefined
lem_exact_type g e t (TVar3 {}) = undefined
lem_exact_type g e t (TPrm {}) = undefined
lem_exact_type g e t (TAbs {}) = undefined
lem_exact_type g e t (TApp {}) = undefined
lem_exact_type g e t (TAbsT {}) = undefined
lem_exact_type g e t (TAppT {}) = undefined
lem_exact_type g e t (TLet {}) = undefined
lem_exact_type g e t (TAnn {}) = undefined
lem_exact_type g e t (TSub {}) = undefined
