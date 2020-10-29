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

{-@ lem_typeof_lambda_nosub :: g:Env -> w:Vname -> e:Expr -> s:Type
       -> { p_we_s : HasType | propOf p_we_s == HasType g (Lambda w e) s && not (isTSub p_we_s) }
       -> { pf:_ | isTFunc s } @-}
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
                ? lem_fv_bound_in_env g (Lambda w e) (TFunc x t_x t') p_we_txt' y
  where
    (LBForType _g _we _txt s p_s_txt' p_we_s) = lem_typ_lower_bound g (Lambda w e)
                                                   (TFunc x t_x t') p_g_wf p_we_txt' 
    (SFunc _ _ _ _ _ p_tx_sx0 _s' _t' y p_yg_s'_t')  = p_s_txt'  -- yg the tx env
           ? lem_typeof_lambda_nosub g w e s p_we_s
    (TAbs _ x0 s_x0 k_x0 p_g_sx0 _ s' y' p_y'g_e_s') = p_we_s    -- y'g the sx0 env  w == x0
    p_g_txt'    = lem_wffunc_for_wf_tfunc g x t_x t' (lem_typing_wf g (Lambda w e) (TFunc x t_x t')
                                                         p_we_txt' p_g_wf)
    (WFFunc _ _ _tx k_x p_g_tx _t'_ k' z p_zg_t') = p_g_txt'
    p_zg_wf     = WFEBind g p_g_wf z t_x k_x p_g_tx
    p_yg_t'     = lem_change_var_wf g z t_x Empty p_zg_wf (unbindT x z t') k' p_zg_t' y
                     ? lem_tsubFV_unbindT x z (FV y) t'
    p_y'g_e_s'_ = lem_narrow_typ g Empty y' t_x s_x0 p_tx_sx0 (unbind w y' e)  
                                 (unbindT x0 y' s') p_y'g_e_s'
    p_y'txg_wf  = WFEBind g p_g_wf y' t_x k_x p_g_tx
    p_yg_e_s'   = lem_change_var_typ g y' t_x Empty p_y'txg_wf (unbind w y' e)
                                  (unbindT x0 y' s') p_y'g_e_s'_ y
                                  ? lem_subFV_unbind   w  y' (FV y) e
                                  ? lem_tsubFV_unbindT x0 y' (FV y) s'
    p_yg_e_t'   = TSub (Cons y t_x g) (unbind w y e) (unbindT x0 y s') p_yg_e_s' 
                       (unbindT x y t') k' p_yg_t' p_yg_s'_t'

{-@ lem_typeof_lambdaT_nosub :: g:Env -> a:Vname -> k:Kind -> e:Expr -> s:Type
       -> { p_ae_s : HasType | propOf p_ae_s == HasType g (LambdaT a k e) s && not (isTSub p_ae_s) }
       -> { pf:_ | isTPoly s } @-}
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
                 ? lem_fv_bound_in_env g (LambdaT a1 k1 e1) (TPoly a k t) p_a1e1_at a'
  where
    (LBForType _g _a1e1 _at a0s p_a0s_at p_a1e1_a0s) = lem_typ_lower_bound g (LambdaT a1 k1 e1)
                                                           (TPoly a k t) p_wf_g p_a1e1_at
    (SPoly _ a0 k0 s _ _ a' p_a'g_s_t) = p_a0s_at ? lem_typeof_lambdaT_nosub g a1 k1 e1 a0s p_a1e1_a0s
    (TAbsT _ _ _ _ _s k_s a'' p_a''g_e1_s p_a''g_s) = p_a1e1_a0s
    p_g_at       = lem_wfpoly_for_wf_tpoly g a k t (lem_typing_wf g (LambdaT a1 k1 e1) (TPoly a k t)
                                                        p_a1e1_at p_wf_g)
    (WFPoly _ _ _ _t k_t aa p_aag_t) = p_g_at 
    p_wf_aag     = WFEBindT g p_wf_g aa k
    p_a'g_t      = lem_change_tvar_wf g aa k Empty p_wf_aag (unbind_tvT a aa t) k_t p_aag_t a'
                                      ? lem_tchgFTV_unbind_tvT a aa a' t
    p_wf_a''g    = WFEBindT g p_wf_g a'' k
    p_a'g_e1_s   = lem_change_tvar_typ g a'' k Empty p_wf_a''g (unbind_tv a1 a'' e1)
                                       (unbind_tvT a0 a'' s) p_a''g_e1_s a'
                                       ? lem_chgFTV_unbind_tv   a1 a'' a' e1
                                       ? lem_tchgFTV_unbind_tvT a0 a'' a' s
    p_a'g_e1_t   = TSub (ConsT a' k g) (unbind_tv a1 a' e1) (unbind_tvT a0 a' s) p_a'g_e1_s
                        (unbind_tvT a a' t) k_t p_a'g_t p_a'g_s_t


-- These lemmas allow us to directly invert the Well Formedness Judgments of certain types 
--     by allowing us to bypass the possibility of WFKind
{-@ lem_wffunc_for_wf_tfunc :: g:Env -> x:Vname -> t_x:Type -> t:Type 
        -> { p_g_txt : WFType | propOf p_g_txt  == WFType g (TFunc x t_x t) Star }
        -> { p_g_txt': WFType | propOf p_g_txt' == WFType g (TFunc x t_x t) Star && isWFFunc p_g_txt' } @-}
lem_wffunc_for_wf_tfunc :: Env -> Vname -> Type -> Type -> WFType -> WFType
lem_wffunc_for_wf_tfunc g x t_x t p_g_txt@(WFFunc {})           = p_g_txt
lem_wffunc_for_wf_tfunc g x t_x t (WFKind _g _ext p_g_txt_base) 
  = impossible ("by lemma" ? lem_wf_tfunc_star g x t_x t p_g_txt_base)

{-@ lem_wf_tfunc_star :: g:Env -> x:Vname -> t_x:Type -> t:Type
        -> ProofOf(WFType g (TFunc x t_x t) Base) -> { pf:_ | false } @-}
lem_wf_tfunc_star :: Env -> Vname -> Type -> Type -> WFType -> Proof
lem_wf_tfunc_star g x t_x t (WFBase {}) = ()
lem_wf_tfunc_star g x t_x t (WFRefn {}) = ()
lem_wf_tfunc_star g x t_x t (WFVar1 {}) = ()
lem_wf_tfunc_star g x t_x t (WFVar2 {}) = ()
lem_wf_tfunc_star g x t_x t (WFVar3 {}) = ()
lem_wf_tfunc_star g x t_x t (WFFunc {}) = ()
lem_wf_tfunc_star g x t_x t (WFExis {}) = ()
lem_wf_tfunc_star g x t_x t (WFPoly {}) = ()
lem_wf_tfunc_star g x t_x t (WFKind _g txt p_g_txt_base) = ()

-- Given G |-w \exists x:t_x. t : k, we can produce a proof tree ending in WFExis
{-@ lem_wfexis_for_wf_texists :: g:Env -> x:Vname -> t_x:Type -> t:Type -> k:Kind
        -> { p_g_ex_t : WFType | propOf p_g_ex_t  == WFType g (TExists x t_x t) k }
        -> { p_g_ex_t': WFType | propOf p_g_ex_t' == WFType g (TExists x t_x t) k && isWFExis p_g_ex_t' } @-}
lem_wfexis_for_wf_texists :: Env -> Vname -> Type -> Type -> Kind -> WFType -> WFType
lem_wfexis_for_wf_texists g x t_x t k p_g_ex_t@(WFExis {})           = p_g_ex_t
lem_wfexis_for_wf_texists g x t_x t k (WFKind _g _ext p_g_ex_t_base) = p_g_ex_t_star
  where
    (WFExis _ _ _ k_x p_g_tx _ k_t y p_yg_t_kt) = p_g_ex_t_base
    {-@ p_yg_t_star :: { pf:WFType | propOf pf == WFType (Cons y t_x g) (unbindT x y t) Star } @-}
    p_yg_t_star = case k_t of 
      Base -> WFKind (Cons y t_x g) (unbindT x y t) p_yg_t_kt
      Star -> p_yg_t_kt
    p_g_ex_t_star = WFExis g x t_x k_x p_g_tx t Star y p_yg_t_star

{-@ lem_wfpoly_for_wf_tpoly :: g:Env -> a:Vname -> k:Kind -> t:Type 
        -> { p_g_at : WFType | propOf p_g_at  == WFType g (TPoly a k t) Star }
        -> { p_g_at': WFType | propOf p_g_at' == WFType g (TPoly a k t) Star && isWFPoly p_g_at' } @-}
lem_wfpoly_for_wf_tpoly :: Env -> Vname -> Kind -> Type -> WFType -> WFType
lem_wfpoly_for_wf_tpoly g a k t p_g_at@(WFPoly {})           = p_g_at
lem_wfpoly_for_wf_tpoly g a k t (WFKind _g _at p_g_at_base) 
  = impossible ("by lemma" ? lem_wf_tpoly_star g a k t p_g_at_base)

{-@ lem_wf_tpoly_star :: g:Env -> a:Vname -> k:Kind -> t:Type
        -> ProofOf(WFType g (TPoly a k t) Base) -> { pf:_ | false } @-}
lem_wf_tpoly_star :: Env -> Vname -> Kind -> Type -> WFType -> Proof
lem_wf_tpoly_star g a k t (WFBase {}) = ()
lem_wf_tpoly_star g a k t (WFRefn {}) = ()
lem_wf_tpoly_star g a k t (WFVar1 {}) = ()
lem_wf_tpoly_star g a k t (WFVar2 {}) = ()
lem_wf_tpoly_star g a k t (WFVar3 {}) = ()
lem_wf_tpoly_star g a k t (WFFunc {}) = ()
lem_wf_tpoly_star g a k t (WFExis {}) = ()
lem_wf_tpoly_star g a k t (WFPoly {}) = ()
lem_wf_tpoly_star g a k t (WFKind {}) = ()

