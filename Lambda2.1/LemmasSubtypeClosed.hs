{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasSubtypeClosed where

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
import LemmasTransitive

{-@ reflect foo58 @-}
foo58 x = Just x
foo58 :: a -> Maybe a

data SubtypeStarP where
    SubtypeStar :: Env -> Type -> Type -> SubtypeStarP

data SubtypeStar where
    SubRefl :: Env -> Type -> Kind -> WFType -> WFEnv -> SubtypeStar
    SubStep :: Env -> Type -> Type -> Type -> Subtype -> SubtypeStar -> SubtypeStar
{-@ data SubtypeStar where
        SubRefl :: g:Env -> t:Type -> k:Kind -> ProofOf(WFType g t k)
                         -> ProofOf(WFEnv g) -> ProofOf(SubtypeStar g t t)
      | SubStep :: g:Env -> t:Type -> t':Type -> t'':Type -> ProofOf(Subtype g t t')
                         -> ProofOf(SubtypeStar g t' t'') -> ProofOf(SubtypeStar g t t'') @-}

{-@ lem_subtype_closed :: g:Env -> s:Type -> t:Type -> ProofOf(SubtypeStar g s t) 
                                -> ProofOf(Subtype g s t) @-}
lem_subtype_closed :: Env -> Type -> Type -> SubtypeStar -> Subtype
lem_subtype_closed g _ t (SubRefl _g _t k p_g_t p_g_wf)
  = lem_sub_refl g t k p_g_t p_g_wf
lem_subtype_closed g s t (SubStep _g _s s' _t p_s_s' seq_s'_t)
  = lem_sub_trans g s s' t p_s_s' p_s'_t
      where
        p_s'_t = lem_subtype_closed g s' t seq_s'_t

-- If G |- e : t0 and the last rule used was TSub then there exists a type t1 such that
--     G |- t1 <: t0 and G |- e : t1 and typSize(G |- e : t1) < typSize(G |- e : t0). If the
--     last rule used was also TSub then there exists a t2 such that t2 <: t1 and so on. Clearly
--     this process can't continue forever; the next lemma proves that there exists some lower
--     bound to this sequence ... t2 <: t1 <:0: there exists some t' such that 
--     G |- e : t' and G |- t' <:* t. By the lemma above we also have G |- t' <: t

data LowerBoundTypeP where
    LowerBoundType :: Env -> Expr -> Type -> LowerBoundTypeP

data LowerBoundType where
      LBForType :: Env -> Expr -> Type -> Type -> Subtype -> HasType -> LowerBoundType
{-@ data LowerBoundType where
      LBForType :: g:Env -> e:Expr -> t:Type -> t':Type -> ProofOf(Subtype g t' t) 
                     -> { p_e_t':HasType | propOf p_e_t' == HasType g e t' && not (isTSub p_e_t') } 
                     -> ProofOf(LowerBoundType g e t) @-}

{-@ lem_typ_lower_bound :: g:Env -> e:Expr -> t:Type -> ProofOf(WFEnv g)
        -> { p_e_t:HasType | propOf p_e_t == HasType g e t } -> ProofOf(LowerBoundType g e t) @-}
lem_typ_lower_bound g e t p_wf_g (TSub _g _e s p_e_s _t k p_t_k p_s_t)
  = LBForType g e t t' p_t'_t p_e_t'
      where
        (LBForType _g _e _s t' p_t'_s p_e_t') = lem_typ_lower_bound g e s p_wf_g p_e_s
        p_t'_t = lem_sub_trans g t' s t p_t'_s p_s_t
lem_typ_lower_bound g e t p_wf_g p_e_t = LBForType g e t t p_t_t p_e_t
  where
    p_t_t = lem_sub_refl  g t Star p_g_t p_wf_g
    p_g_t = lem_typing_wf g e t p_e_t p_wf_g
