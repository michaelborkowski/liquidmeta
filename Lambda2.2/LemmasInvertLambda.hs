{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasInvertLambda where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
--import {--} Semantics
import SystemFWellFormedness            (WFFT(..))
import SystemFTyping                    (erase_ty,ty,tyic,tybc)
import WellFormedness                   (WFType(..),WFEnv(..),isWFFunc,isWFPoly)
import BasicPropsSubstitution
import BasicPropsEnvironments           (concatE,esubFV,echgFTV)
import BasicPropsWellFormedness         (lem_wffunc_for_wf_tfunc,lem_wfpoly_for_wf_tpoly)
--import {--} SystemFLemmasFTyping
--import {--} SystemFLemmasSubstitution
import Typing                           (HasType(..),Subtype(..),isTAbs,isTAbsT,isTSub,self)
--import {--} BasicPropsCSubst
--import {--} BasicPropsDenotes
--import {--} Entailments
import LemmasChangeVarWF                (lem_change_var_wf',lem_change_tvar_wf')
--import {--} LemmasWeakenWF
--import {--} LemmasWellFormedness             
import LemmasTyping                     (lem_typing_wf,lem_fv_bound_in_env)
--import {--} LemmasSubtyping
import LemmasChangeVarTyp               (lem_change_var_typ,lem_change_tvar_typ)
--import {--} LemmasWeakenTyp
--import {--} SubstitutionLemmaWF
--import {--} DenotationsSelfify
--import {--} PrimitivesSemantics
--import {--} PrimitivesDenotations
--import {--} DenotationsSoundness
--import {--} LemmasExactness
--import {--} SubstitutionLemmaEnt
--import {--} SubstitutionLemmaTyp
--import {--} LemmasNarrowingEnt
import LemmasNarrowingTyp               (lem_narrow_typ)
--import {--} LemmasTransitive
import LemmasSubtypeClosed              (LowerBoundType(..),lem_typ_lower_bound)

{-@ reflect foo73 @-}
foo73 x = Just x
foo73 :: a -> Maybe a

-- A collection of Lemmas about inverting typing judgements for abstraction types. In our
--   system this is not trivial because TSub could be used finitely many times to produce
--   the judgment. Lemma 16 is lem_invert_tabs.

{-@ lem_typeof_lambda_nosub :: g:Env -> w:Vname -> e:Expr -> s:Type
       -> { p_we_s : HasType | propOf p_we_s == HasType g (Lambda w e) s && not (isTSub p_we_s) }
       -> { pf:_ | isTFunc s && isTAbs p_we_s } @-}
lem_typeof_lambda_nosub :: Env -> Vname -> Expr -> Type -> HasType -> Proof
lem_typeof_lambda_nosub g w e s p_we_s = case p_we_s of
  (TAbs {}) -> ()

{-@ lem_invert_tabs :: g:Env -> w:Vname -> e:Expr -> x:Vname -> t_x:Type -> t:Type 
        -> ProofOf(HasType g (Lambda w e) (TFunc x t_x t)) -> ProofOf(WFEnv g)
        -> (Vname,HasType)<{\y pf -> not (in_env y g) && 
               not (Set_mem y (fv e)) && not (Set_mem y (ftv e)) &&
               not (Set_mem y (free t)) && not (Set_mem y (freeTV t)) &&
               propOf pf == HasType (Cons y t_x g) (unbind w y e) (unbindT x y t)}> @-}
lem_invert_tabs :: Env -> Vname -> Expr -> Vname -> Type -> Type -> HasType 
                       -> WFEnv -> (Vname, HasType)
lem_invert_tabs g w e x t_x t' p_we_txt' p_g_wf = (y, p_yg_e_t') 
                ? lem_fv_bound_in_env g (Lambda w e) (TFunc x t_x t') p_we_txt' p_g_wf y
  where
    (LBForType _g _we _txt s p_s_txt' p_we_s) = lem_typ_lower_bound g (Lambda w e)
                                                   (TFunc x t_x t') p_g_wf p_we_txt' 
    (SFunc _ _ _ _ _ p_tx_sx0 _s' _t' y p_yg_s'_t')  = p_s_txt'  -- yg the tx env
           ? lem_typeof_lambda_nosub g w e s p_we_s
    (TAbs _ x0 s_x0 k_x0 p_g_sx0 _ s' y' p_y'g_e_s') = p_we_s    -- y'g the sx0 env  w == x0
    p_g_txt'    = lem_wffunc_for_wf_tfunc g x t_x t' Star (lem_typing_wf g (Lambda w e) (TFunc x t_x t')
                                                               p_we_txt' p_g_wf)
    (WFFunc _ _ _tx k_x p_g_tx _t'_ k' z p_zg_t') = p_g_txt'
    p_zg_wf     = WFEBind g p_g_wf z t_x k_x p_g_tx
    p_yg_t'     = lem_change_var_wf' g z t_x Empty p_zg_wf (unbindT x z t') k' p_zg_t' y
                                     ? lem_tsubFV_unbindT x z (FV y) t'
    p_y'sxg_wf  = WFEBind g p_g_wf y' s_x0 k_x0 p_g_sx0
    p_y'txg_wf  = WFEBind g p_g_wf y' t_x  k_x   p_g_tx
    p_y'g_e_s'_ = lem_narrow_typ g Empty y' t_x k_x p_g_tx s_x0 p_tx_sx0 p_y'sxg_wf
                                 (unbind w y' e) (unbindT x0 y' s') p_y'g_e_s'
    p_yg_e_s'   = lem_change_var_typ g y' t_x Empty p_y'txg_wf (unbind w y' e)
                                  (unbindT x0 y' s') p_y'g_e_s'_ y
                                  ? lem_subFV_unbind   w  y' (FV y) e
                                  ? lem_tsubFV_unbindT x0 y' (FV y) s'
    p_yg_e_t'   = TSub (Cons y t_x g) (unbind w y e) (unbindT x0 y s') p_yg_e_s' 
                       (unbindT x y t') k' p_yg_t' p_yg_s'_t'

{-@ lem_typeof_lambdaT_nosub :: g:Env -> a:Vname -> k:Kind -> e:Expr -> s:Type
       -> { p_ae_s : HasType | propOf p_ae_s == HasType g (LambdaT a k e) s && not (isTSub p_ae_s) }
       -> { pf:_ | isTPoly s && isTAbsT p_ae_s } @-}
lem_typeof_lambdaT_nosub :: Env -> Vname -> Kind -> Expr -> Type -> HasType -> Proof
lem_typeof_lambdaT_nosub g a k e s p_ae_s = case p_ae_s of
  (TAbsT {}) -> ()
--                                        removed k == k1
{-@ lem_invert_tabst :: g:Env -> a1:Vname -> k1:Kind -> e1:Expr -> a:Vname -> k:Kind -> t:Type 
        -> ProofOf(HasType g (LambdaT a1 k1 e1) (TPoly a k t)) -> ProofOf(WFEnv g)
        -> (Vname, HasType)<{\a' pf -> not (in_env a' g) &&
               not (Set_mem a' (fv e1)) && not (Set_mem a' (ftv e1)) &&
               not (Set_mem a' (free t)) && not (Set_mem a' (freeTV t)) &&
               propOf pf == HasType (ConsT a' k g) (unbind_tv a1 a' e1) (unbind_tvT a a' t)}> @-}
lem_invert_tabst :: Env -> Vname -> Kind -> Expr -> Vname -> Kind -> Type -> HasType 
                        -> WFEnv -> (Vname, HasType)
lem_invert_tabst g a1 k1 e1 a k t p_a1e1_at p_wf_g = (a', p_a'g_e1_t) 
                 ? lem_fv_bound_in_env g (LambdaT a1 k1 e1) (TPoly a k t) p_a1e1_at p_wf_g a'
  where
    (LBForType _g _a1e1 _at a0s p_a0s_at p_a1e1_a0s) = lem_typ_lower_bound g (LambdaT a1 k1 e1)
                                                           (TPoly a k t) p_wf_g p_a1e1_at
    (SPoly _ a0 k0 s _ _ a' p_a'g_s_t) = p_a0s_at ? lem_typeof_lambdaT_nosub g a1 k1 e1 a0s p_a1e1_a0s
    (TAbsT _ _ _ _ _s k_s a'' p_a''g_e1_s p_a''g_s) = p_a1e1_a0s
    p_g_at       = lem_wfpoly_for_wf_tpoly g a k t (lem_typing_wf g (LambdaT a1 k1 e1) (TPoly a k t)
                                                        p_a1e1_at p_wf_g)
    (WFPoly _ _ _ _t k_t aa p_aag_t) = p_g_at 
    p_wf_aag     = WFEBindT g p_wf_g aa k
    p_a'g_t      = lem_change_tvar_wf' g aa k Empty p_wf_aag (unbind_tvT a aa t) k_t p_aag_t a'
                                       ? lem_tchgFTV_unbind_tvT a aa a' t
    p_wf_a''g    = WFEBindT g p_wf_g a'' k
    p_a'g_e1_s   = lem_change_tvar_typ g a'' k Empty p_wf_a''g (unbind_tv a1 a'' e1)
                                       (unbind_tvT a0 a'' s) p_a''g_e1_s a'
                                       ? lem_chgFTV_unbind_tv   a1 a'' a' e1
                                       ? lem_tchgFTV_unbind_tvT a0 a'' a' s
    p_a'g_e1_t   = TSub (ConsT a' k g) (unbind_tv a1 a' e1) (unbind_tvT a0 a' s) p_a'g_e1_s
                        (unbind_tvT a a' t) k_t p_a'g_t p_a'g_s_t
