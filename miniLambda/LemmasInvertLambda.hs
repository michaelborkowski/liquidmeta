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
import DenotationsSoundness
import PrimitivesSemantics
import PrimitivesDenotations
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

{-@ lem_typeof_lambda_nosub :: g:Env -> w:Vname -> e:Expr -> s:Type
       -> { p_we_s : HasType | propOf p_we_s == HasType g (Lambda w e) s && not (isTSub p_we_s) }
       -> { pf:_ | isTFunc s && isTAbs p_we_s } @-}
lem_typeof_lambda_nosub :: Env -> Vname -> Expr -> Type -> HasType -> Proof
lem_typeof_lambda_nosub g w e s p_we_s = case p_we_s of
  (TAbs {}) -> ()

{-@ lem_invert_tabs :: g:Env -> w:Vname -> e:Expr -> x:Vname -> t_x:Type -> t:Type 
        -> ProofOf(HasType g (Lambda w e) (TFunc x t_x t)) -> ProofOf(WFEnv g)
        -> (Vname,HasType)<{\y pf -> not (in_env y g) && 
               not (Set_mem y (fv e)) && not (Set_mem y (free t)) && 
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
    (TAbs _ x0 s_x0 p_g_sx0 _ s' y' p_y'g_e_s') = p_we_s    -- y'g the sx0 env  w == x0
    p_g_txt'    = lem_typing_wf g (Lambda w e) (TFunc x t_x t') p_we_txt' p_g_wf
    (WFFunc _ _ _tx p_g_tx _t'_ z p_zg_t') = p_g_txt'
    p_yg_t'     = lem_change_var_wf g z t_x Empty (unbindT x z t') p_zg_t' y
                     ? lem_tsubFV_unbindT x z (FV y) t'
    p_y'sxg_wf  = WFEBind g p_g_wf y' s_x0 p_g_sx0
    p_y'g_e_s'_ = lem_narrow_typ g Empty y' t_x p_g_tx s_x0 p_tx_sx0 p_y'sxg_wf 
                                 (unbind w y' e) (unbindT x0 y' s') p_y'g_e_s'
    p_y'txg_wf  = WFEBind g p_g_wf y' t_x p_g_tx
    p_yg_e_s'   = lem_change_var_typ g y' t_x Empty p_y'txg_wf (unbind w y' e)
                                  (unbindT x0 y' s') p_y'g_e_s'_ y
                                  ? lem_subFV_unbind   w  y' (FV y) e
                                  ? lem_tsubFV_unbindT x0 y' (FV y) s'
    p_yg_e_t'   = TSub (Cons y t_x g) (unbind w y e) (unbindT x0 y s') p_yg_e_s' 
                       (unbindT x y t') p_yg_t' p_yg_s'_t'
