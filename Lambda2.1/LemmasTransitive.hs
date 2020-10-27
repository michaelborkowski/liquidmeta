{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasTransitive where

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
import SubstitutionLemmaWF
import DenotationsSelfify
import DenotationsSoundnessSub
import PrimitivesSemantics
import PrimitivesDenotations
import DenotationsSoundnessTyp
import LemmasExactness
import SubstitutionLemmaEnt
import SubstitutionLemmaTyp
import LemmasNarrowingEnt
import LemmasNarrowingTyp

{-@ reflect foo57 @-}
foo57 x = Just x
foo57 :: a -> Maybe a

{-@ lem_sub_trans :: g:Env -> t:Type -> t':Type -> t'':Type 
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t' }
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' }
            -> ProofOf(Subtype g t t'') / [subtypSize p_t_t', subtypSize p_t'_t''] @-}
lem_sub_trans :: Env -> Type -> Type -> Type -> Subtype -> Subtype -> Subtype
lem_sub_trans g t t' t'' p_t_t' p_t'_t'' = undefined
-- case analysis:
-- SBase SBase		TRefn TRefn TRefn
-- SFunc SFunc		TFunc TFunc TFunc
-- SPoly SPoly 		TPoly TPoly TPoly -- all other cases must have TExists
-- SWitn SWitn		any   TExis TExis
-- SWitn SBind		any   TExis any
--
-- SBind SBase		TExis TRefn TRefn
-- SBind SFunc		TExis TFunc TFunc
-- SBind SWitn		TExis any   TExis
-- SBind SBind		TExis TExis any
-- SBind SPoly		TExis TPoly TPoly
