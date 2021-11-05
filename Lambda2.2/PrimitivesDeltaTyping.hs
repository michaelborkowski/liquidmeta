{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--fuel=6"      @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesDeltaTyping where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics                        (delta,deltaT,isCompat,isCompatT)
--import SystemFWellFormedness
import SystemFTyping                    (HasFType(..),firstBV,inType,ty',ty,tybc,tyic,erase_ty,refn_pred)
import WellFormedness
import PrimitivesFTyping                
import PrimitivesWFType                 ----(lem_wf_inside_ty)
import BasicPropsSubstitution
import BasicPropsEnvironments           (esubFV,echgFTV,esubFTV,concatE,lem_empty_concatE)
import BasicPropsWellFormedness         (lem_wffunc_for_wf_tfunc,lem_wfpoly_for_wf_tpoly)
--import SystemFLemmasFTyping
--import SystemFLemmasSubstitution
import Typing
--import BasicPropsCSubst
--import BasicPropsDenotes
--import Entailments
import LemmasChangeVarWF
--import LemmasWeakenWF
import LemmasWellFormedness             (lem_subtype_in_env_wf)
import LemmasTyping                     (lem_typing_hasftype,lem_typing_wf)
--import LemmasSubtyping
--import LemmasChangeVarTyp
--import LemmasWeakenTyp
import SubstitutionWFAgain
--import DenotationsSelfify
--import PrimitivesSemantics
--import PrimitivesDenotations
--import DenotationsSoundness
--import LemmasExactness
--import SubstitutionLemmaEnt
import SubstitutionLemmaTyp             (lem_subst_sub)
import SubstitutionLemmaTypTV           (lem_subst_tv_sub)
import LemmasSubtypeClosed
--import LemmasInvertLambda
--import PrimitivesRefinements

{-@ reflect foo72 @-}
foo72 x = Just x
foo72 :: a -> Maybe a

{-@ lem_prim_compat_in_tapp :: p:Prim -> v:Value -> t:Type
        -> ProofOf(HasType Empty (App (Prim p) v) t)
        -> { pf:_ | isCompat p v } @-}
lem_prim_compat_in_tapp :: Prim -> Expr -> Type -> HasType -> Proof
lem_prim_compat_in_tapp c v t p_cv_t
  | c == And      = () ? lem_bool_values v p_v_er_sx
  | c == Or       = () ? lem_bool_values v p_v_er_sx
  | c == Not      = () ? lem_bool_values v p_v_er_sx
  | c == Eqv      = () ? lem_bool_values v p_v_er_sx
  | c == Leq      = () ? lem_int_values v p_v_er_sx
  | c == (Leqn _) = () ? lem_int_values v p_v_er_sx
  | c == Eq       = () ? lem_int_values v p_v_er_sx
  | c == (Eqn _)  = () ? lem_int_values v p_v_er_sx
    where
      (LBForType _ _ _ s p_s_t p_cv_s)   = lem_typ_lower_bound Empty (App (Prim c) v) t
                                                               WFEEmpty p_cv_t
      (TApp _ _ x s_x s' p_c_sxs' _ p_v_sx) = p_cv_s
      (FTPrm {})                         = lem_typing_hasftype Empty (Prim c) (TFunc x s_x s')
                                                               p_c_sxs' WFEEmpty
      p_v_er_sx                          = lem_typing_hasftype Empty v s_x p_v_sx WFEEmpty

{-@ lem_prim_compatT_in_tappT :: c:Prim -> t_a:UserType -> t:Type
        -> ProofOf(HasType Empty (AppT (Prim c) t_a) t) -> { pf:_ | isCompatT c t_a } @-}
lem_prim_compatT_in_tappT :: Prim -> Type -> Type -> HasType -> Proof
lem_prim_compatT_in_tappT c t_a t p_cta_t 
  = lem_prim_compatT_in_ftappt c t_a (erase t) p_er_cta_t
      where
        p_er_cta_t = lem_typing_hasftype Empty (AppT (Prim c) t_a) t p_cta_t WFEEmpty

{-@ lem_delta_ty'c :: { c:Prim | c != Eql } -> v:Value -> ProofOf(HasType Empty v (inType c))
        -> ProofOf(HasType Empty (delta c v) (tsubBV (firstBV c) v (ty' c))) @-}
lem_delta_ty'c :: Prim -> Expr -> HasType -> HasType
lem_delta_ty'c c v p_v_tx = undefined -- this part we leave as an assumption

{-@ lem_delta_typ :: c:Prim -> v:Value -> x:Vname -> t_x:Type -> t':Type
        -> ProofOf(HasType Empty (Prim c) (TFunc x t_x t')) -> ProofOf(HasType Empty v t_x)
        -> { pf:_ | propOf pf == HasType Empty (delta c v) (tsubBV x v t') } @-} 
lem_delta_typ :: Prim -> Expr -> Vname -> Type -> Type 
                     -> HasType -> HasType -> HasType
lem_delta_typ c v x t_x t' p_c_txt' p_v_tx  
  = case (lem_typ_lower_bound Empty (Prim c) (TFunc x t_x t') WFEEmpty p_c_txt') of 
      (LBForType _ _ _ s p_s_t p_c_s) -> case p_c_s of -- s === ty c
          (TPrm Empty _c) -> TSub Empty (delta c (v ? compat)) ty'cv p_cv_ty'cv 
                                  (tsubBV x v t') k' p_emp_t'v p_ty'cv_t'v
            where
              compat      = lem_prim_compat_in_tapp c v (TExists x t_x t')
                                (TApp Empty (Prim c) x t_x t' p_c_txt' v p_v_tx)
              ty'cv       = tsubBV (firstBV c) v (ty' c)
              (WFFunc _ _ _ _ _ _ k' y p_y_t') 
                          = lem_wffunc_for_wf_tfunc Empty x t_x t' Star
                                (lem_typing_wf Empty (Prim c) (TFunc x t_x t') p_c_txt' WFEEmpty)
              p_emp_tx    = lem_typing_wf Empty v t_x p_v_tx WFEEmpty
              p_y_wf      = WFEBind Empty WFEEmpty y t_x Star p_emp_tx 
              p_emp_t'v   = lem_subst_wf' Empty Empty y v t_x p_v_tx p_y_wf (unbindT x y t') k' p_y_t'
                                          ? lem_tsubFV_unbindT x y v t'
              (SFunc _ _ _ _ _ p_tx_in _ _ z p_z_ty'c_t') = p_s_t
              p_v_in      = TSub Empty v t_x p_v_tx (inType c) Base (lem_wf_intype c) p_tx_in
              p_cv_ty'cv  = lem_delta_ty'c c v p_v_in
              p_z_wf      = WFEBind Empty WFEEmpty z t_x Star p_emp_tx 
              p_z_t'      = lem_change_var_wf' Empty y t_x Empty p_y_wf (unbindT x y t') k' p_y_t' z
                                               ? lem_tsubFV_unbindT x y (FV z) t'
              p_zin_ty'c  = lem_wf_ty' c z
              p_ztx_ty'c  = lem_subtype_in_env_wf Empty Empty z t_x (inType c) p_tx_in 
                                                  (unbindT (firstBV c) z (ty' c)) Star p_zin_ty'c
              p_ty'cv_t'v = lem_subst_sub Empty Empty z v t_x p_v_tx p_z_wf 
                                          (unbindT (firstBV c) z (ty' c)) Star p_ztx_ty'c 
                                          (unbindT x z t') k' p_z_t'  p_z_ty'c_t' 
                                 ? esubFV z v Empty
                                 ? lem_empty_concatE Empty
                                 ? lem_tsubFV_unbindT (firstBV c) z v (ty' c)
                                 ? lem_tsubFV_unbindT x           z v t'

{-@ lem_deltaT_ty'c :: t:UserType -> ProofOf(WFType Empty t Base)
        -> ProofOf(HasType Empty (deltaT Eql t) 
                           (tsubBTV 1 t (TFunc (firstBV Eql) (inType Eql) (ty' Eql)))) @-}
lem_deltaT_ty'c :: Type -> WFType -> HasType
lem_deltaT_ty'c t p_emp_t = undefined -- this part we leave as an assumption

{-@ lem_tyeql_forallbase :: c:Prim -> a:Vname -> k:Kind -> s:Type 
        -> ProofOf(Subtype Empty (ty c) (TPoly a k s)) -> { pf:_ | k == Base } @-}
lem_tyeql_forallbase :: Prim -> Vname -> Kind -> Type -> Subtype -> Proof
lem_tyeql_forallbase c a k s p_ty_aks = case p_ty_aks of
  (SPoly {}) -> ()

{-@ lem_deltaT_typ :: c:Prim -> a:Vname -> k:Kind -> s:Type
        -> ProofOf(HasType Empty (Prim c) (TPoly a k s)) -> t:UserType -> ProofOf(WFType Empty t k)
        -> ProofOf(HasType Empty (deltaT c t) (tsubBTV a t s)) @-}
lem_deltaT_typ :: Prim -> Vname -> Kind -> Type -> HasType -> Type -> WFType -> HasType
lem_deltaT_typ c   a k s p_c_aks t p_emp_t  
  = case (lem_typ_lower_bound Empty (Prim c) (TPoly a k s) WFEEmpty p_c_aks) of 
      (LBForType _ _ _ as' p_as'_as p_c_as') -> case p_c_as' of -- as' = ty Eql here
        (TPrm Empty _c) -> TSub Empty deltaT_c_t tyct p_ct_tyct (tsubBTV a t s) k_s
                                p_emp_st p_tyct_st
          where
            deltaT_c_t  = deltaT c (t ? lem_prim_compatT_in_tappT c t (tsubBTV a t s)
                                            (TAppT Empty (Prim c) a k s p_c_aks t p_emp_t))
            tyct        = tsubBTV 1 t (TFunc (firstBV Eql) (inType Eql) (ty' Eql))
            p_emp_as    = lem_typing_wf Empty (Prim c) (TPoly a k s) p_c_aks WFEEmpty
            (WFPoly _ _ _ _ k_s a' p_a'_s) = lem_wfpoly_for_wf_tpoly Empty a k s p_emp_as  
            p_a'_wf     = WFEBindT Empty WFEEmpty a' k -- ? lem_empty_concatE (ConsT 
            p_emp_st    = lem_subst_tv_wf' Empty Empty a' t k p_emp_t p_a'_wf 
                                           (unbind_tvT a a' s) k_s p_a'_s 
                                           ? lem_tsubFTV_unbind_tvT a a' t s 
            (SPoly _ _ _base _ _a _s a'' p_a''_tyc_s) = p_as'_as
            p_ct_tyct   = lem_deltaT_ty'c t (p_emp_t ? lem_tyeql_forallbase c a k s p_as'_as)
            p_a''_wf    = WFEBindT Empty WFEEmpty a'' k 
            p_a''_s     = lem_change_tvar_wf' Empty a' k Empty p_a'_wf (unbind_tvT a a' s)
                                              k_s p_a'_s a'' ? lem_tchgFTV_unbind_tvT a a' a'' s
            p_a''_tyc   = lem_wf_inside_ty a''
            p_tyct_st   = lem_subst_tv_sub Empty Empty a'' t k p_emp_t p_a''_wf 
                              (unbind_tvT 1 a'' (TFunc (firstBV Eql) (inType Eql) (ty' Eql)))
                              Star p_a''_tyc (unbind_tvT a a'' s) k_s p_a''_s p_a''_tyc_s
                              ? esubFTV a'' t Empty  ? lem_empty_concatE Empty
                              ? lem_tsubFTV_unbind_tvT 1 a'' t (TFunc (firstBV Eql) (inType Eql) (ty' Eql))
                              ? lem_tsubFTV_unbind_tvT a a'' t s
