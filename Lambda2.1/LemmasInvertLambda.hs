{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasInvertLambda where

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
import LemmasSubtypeClosed

{-@ reflect foo59 @-}
foo59 x = Just x
foo59 :: a -> Maybe a

-- A collection of Lemmas about inverting typing judgements for abstraction types. In our
--   system this is not trivial because TSub could be used finitely many times to produce
--   the judgment. Lemma 16 is lem_invert_tabs.

{-@ lem_invert_tabs :: g:Env -> w:Vname -> e:Expr -> x:Vname -> t_x:Type -> t:Type 
        -> ProofOf(HasType g (Lambda w e) (TFunc x t_x t)) -> ProofOf(WFEnv g)
        -> (Vname,HasType)<{\y pf -> not (in_env y g) && 
               not (Set_mem y (fv e)) && not (Set_mem y (ftv e)) &&
               not (Set_mem y (free t)) && not (Set_mem y (freeTV t)) &&
               propOf pf == HasType (Cons y t_x g) (unbind w y e) (unbindT x y t)}> @-}
lem_invert_tabs :: Env -> Vname -> Expr -> Vname -> Type -> Type -> HasType 
                       -> WFEnv -> (Vname, HasType)
lem_invert_tabs g x e t_x t p_xe_txt p_wf_g 
  = undefined {-case (lem_typ_lower_bound g (Lambda x e) (TFunc x t_x t) p_wf_g p_xe_txt) of
      (LBForType _g _xe _txt s p_s_txt 
      (TAbs _g _x _tx k_x p_g_tx _e _t y p_yg_e_t)  -> p_yg_e_t-}

{-@ lem_invert_tabst :: g:Env -> a1:Vname -> k1:Kind -> e1:Expr -> a:Vname -> k:Kind -> t:Type 
        -> ProofOf(HasType g (LambdaT a1 k1 e1) (TPoly a k t)) -> ProofOf(WFEnv g)
        -> (Vname, HasType)<{\a' pf -> k == k1 && not (in_env a' g) &&
               not (Set_mem a' (fv e1)) && not (Set_mem a' (ftv e1)) &&
               not (Set_mem a' (free t)) && not (Set_mem a' (freeTV t)) &&
               propOf pf == HasType (ConsT a' k g) (unbind_tv a1 a' e1) (unbind_tvT a a' t)}> @-}
lem_invert_tabst :: Env -> Vname -> Kind -> Expr -> Vname -> Kind -> Type -> HasType 
                        -> WFEnv -> (Vname, HasType)
lem_invert_tabst g a k e t p_ae_at p_wf_g = undefined {-
  = case (lem_typ_lower_bound g (LambdaT a k e) (TPoly a k t) p_wf_g p_ae_at) of
      (TAbsT _g _a _k _e _t k_t a' p_ag_e_t p_ag_t) -> p_ag_e_t -}

-- Given G |-w \exists x:t_x. t : k, we can produce a proof tree ending in WFExis
{-@ lem_wfexis_for_wf_texists' :: g:Env -> x:Vname -> t_x:Type -> t:Type -> k:Kind
        -> { p_g_ex_t : WFType | propOf p_g_ex_t  == WFType g (TExists x t_x t) k }
        -> (Kind,WFType)<{\k0 pf -> propOf pf == WFType g (TExists x t_x t) k0 && isWFExis pf }> @-}
lem_wfexis_for_wf_texists' :: Env -> Vname -> Type -> Type -> Kind -> WFType -> (Kind,WFType)
lem_wfexis_for_wf_texists' g x t_x t k p_g_ex_t@(WFExis {})           = (k,  p_g_ex_t)
lem_wfexis_for_wf_texists' g x t_x t k (WFKind _g _ext p_g_ex_t_base) = (k0, p_g_ex_t')
  where
    (k0, p_g_ex_t') = lem_wfexis_for_wf_texists' g x t_x t Base p_g_ex_t_base

-- Given G |-w \exists x:t_x. t : k, we can produce a proof tree ending in WFExis
{-@ lem_wfexis_for_wf_texists :: g:Env -> x:Vname -> t_x:Type -> t:Type -> k:Kind
        -> { p_g_ex_t : WFType | propOf p_g_ex_t  == WFType g (TExists x t_x t) k }
        -> { p_g_ex_t': WFType | propOf p_g_ex_t' == WFType g (TExists x t_x t) k && isWFExis p_g_ex_t' } @-}
lem_wfexis_for_wf_texists :: Env -> Vname -> Type -> Type -> Kind -> WFType -> WFType
lem_wfexis_for_wf_texists g x t_x t k p_g_ex_t@(WFExis {})           = p_g_ex_t
lem_wfexis_for_wf_texists g x t_x t k (WFKind _g _ext p_g_ex_t_base) = undefined {-(k0, p_g_ex_t')
  where
    (k0, p_g_ex_t') = lem_wfexis_for_wf_texists' g x t_x t Base p_g_ex_t_base-}
