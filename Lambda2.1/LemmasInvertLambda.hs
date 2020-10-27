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

{-@ lem_invert_tabs :: g:Env -> x:Vname -> e:Expr -> t_x:Type -> t:Type 
        -> ProofOf(HasType g (Lambda x e) (TFunc x t_x t)) -> ProofOf(WFEnv g)
        -> (Vname,HasType)<{\y pf -> not (in_env y g) && 
               not (Set_mem y (fv e)) && not (Set_mem y (ftv e)) &&
               not (Set_mem y (free t)) && not (Set_mem y (freeTV t)) &&
               propOf pf == HasType (Cons y t_x g) (unbind x y e) (unbindT x y t)}> @-}
lem_invert_tabs :: Env -> Vname -> Expr -> Type -> Type -> HasType -> WFEnv -> (Vname, HasType)
lem_invert_tabs g x e t_x t p_xe_txt p_wf_g 
  = undefined {-case (lem_typ_lower_bound g (Lambda x e) (TFunc x t_x t) p_wf_g p_xe_txt) of
      (LBForType _g _xe _txt s p_s_txt 
      (TAbs _g _x _tx k_x p_g_tx _e _t y p_yg_e_t)  -> p_yg_e_t-}

--               not (Set_mem a' (free t)) && not (Set_mem a' (freeTV t)) &&
{-@ lem_invert_tabst :: g:Env -> a:Vname -> k:Kind -> e:Expr -> t:Type 
        -> ProofOf(HasType g (LambdaT a k e) (TPoly a k t)) -> ProofOf(WFEnv g)
        -> (Vname, HasType)<{\a' pf -> not (in_env a' g) &&
               not (Set_mem a' (fv e)) && not (Set_mem a' (ftv e)) &&
               propOf pf == HasType (ConsT a' k g) (unbind_tv a a' e) (unbind_tvT a a' t)}> @-}
lem_invert_tabst :: Env -> Vname -> Kind -> Expr -> Type -> HasType -> WFEnv -> (Vname, HasType)
lem_invert_tabst g a k e t p_ae_at p_wf_g = undefined {-
  = case (lem_typ_lower_bound g (LambdaT a k e) (TPoly a k t) p_wf_g p_ae_at) of
      (TAbsT _g _a _k _e _t k_t a' p_ag_e_t p_ag_t) -> p_ag_e_t -}
