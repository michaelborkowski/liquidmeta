{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesDeltaTyping where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof,(?))
import qualified Data.Set as S

import Basics
import Semantics                        --(delta,deltaT,isCompat,isCompatT)
import SystemFWellFormedness
import SystemFTyping                    --(HasFType(..),firstBV,inType,ty',ty,tybc,tyic,erase_ty,refn_pred)
import BasicPropsSubstitution
import BasicPropsEnvironments           --(esubFV,echgFTV,esubFTV,concatE,lem_empty_concatE)
import WellFormedness
import PrimitivesFTyping                
import PrimitivesWFType                 ----(lem_wf_inside_ty)
import BasicPropsWellFormedness         --(lem_wffunc_for_wf_tfunc,lem_wfpoly_for_wf_tpoly)
import Typing
import LemmasWellFormedness             --(lem_subtype_in_env_wf)
import SubstitutionLemmaWF
import SubstitutionLemmaWFTV
import LemmasTyping                     --(lem_typing_hasftype,lem_typing_wf)
import LemmasSubtyping
import SubstitutionLemmaTyp             --(lem_subst_sub)
import SubstitutionLemmaTypTV           --(lem_subst_tv_sub)
import LemmasTransitive
import LemmasInversion

{-@ lem_prim_compat_in_tapp :: p:Prim -> v:Value -> t:Type
        -> ProofOf(HasType Empty (App (Prim p) v) t)
        -> { pf:_ | isCompat p v } @-}
lem_prim_compat_in_tapp :: Prim -> Expr -> Type -> HasType -> Proof
lem_prim_compat_in_tapp c v t p_cv_t
    = lem_prim_compat_in_ftapp c v (erase t) (p_cv_er_t)
        where
          p_cv_er_t    = lem_typing_hasftype Empty (App (Prim c) v) t p_cv_t WFEEmpty

{-@ lem_prim_compatT_in_tappT :: c:Prim -> t_a:UserType -> t:Type
        -> ProofOf(HasType Empty (AppT (Prim c) t_a) t) -> { pf:_ | isCompatT c t_a } @-}
lem_prim_compatT_in_tappT :: Prim -> Type -> Type -> HasType -> Proof
lem_prim_compatT_in_tappT c t_a t p_cta_t 
  = lem_prim_compatT_in_ftappt c t_a (erase t) p_er_cta_t
      where
        p_er_cta_t = lem_typing_hasftype Empty (AppT (Prim c) t_a) t p_cta_t WFEEmpty

{-@ lem_delta_typ ::  c:Prim  -> v:Value  -> t_x:Type -> t':Type
        -> ProofOf(HasType Empty (Prim c) (TFunc t_x t')) -> ProofOf(HasType Empty v t_x)
        -> { pf:_ | propOf pf == HasType Empty (delta c v) (TExists t_x t') } @-} 
lem_delta_typ :: Prim -> Expr ->  Type -> Type -> HasType -> HasType -> HasType
lem_delta_typ c v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (TPrm _ _) -> TSub n Empty (delta c v ? compat) (tsubBV v (ty' c)) p_cv_ty'cv
                     (TExists (inType c) (ty' c)) Star p_emp_exty' p_ty'cv_exty'
    where
      p_cv_ty'cv    = lem_delta_ty'c c v p_v_tx
      p_emp_exty'   = WFExis Empty t_x Base (lem_wf_intype c) (ty' c) Star [] (lem_wf_ty' c)
      p_ty'cv_exty' = lem_witness_sub Empty v t_x p_v_tx (ty' c) Star p_emp_exty' WFEEmpty
      n             = max (typSize p_cv_ty'cv) (subtypSize  p_ty'cv_exty')
  (TSub {})  
    -> let (TSub _ _ _ s p_c_s _ k_t p_g_txt' p_s_t) 
               = lem_collapse_sub Empty (Prim c) (TFunc t_x t') WFEEmpty p_c_txt'
         in case p_s_t of
              (SFunc n _ _ _ p_tx_in _ _ nms mk_p_ty'c_t') -> case p_c_s of
                (TPrm Empty _c) 
                      -> TSub n''' Empty (delta c (v ? compat)) ty'cv p_cv_ty'cv
                              (TExists t_x t') Star p_emp_extxt' p_ty'cv_extxt'
                    where
                      {-@ mk_wf_ty' :: y:Vname  
                            -> ProofOf(WFType (Cons y t_x Empty) (unbindT y (ty' c)) Star) @-}
                      mk_wf_ty' y = lem_narrow_wf Empty Empty y t_x (inType c) p_tx_in
                                                  (unbindT y (ty' c)) Star (lem_wf_ty' c y)                
                      p_g_tx         = lem_typing_wf Empty v t_x p_v_tx WFEEmpty
                      ty'cv          = tsubBV v (ty' c)
                      p_v_in         = TSub n'' Empty v t_x p_v_tx (inType c) Base (lem_wf_intype c) p_tx_in
                      p_cv_ty'cv     = lem_delta_ty'c c v p_v_in
                      p_emp_extxt'   = lem_typing_wf Empty (App (Prim c) v) (TExists t_x t')
                                                     p_cv_extxt' WFEEmpty
                      p_emp_exty'    = WFExis Empty t_x Star p_g_tx (ty' c) Star [] mk_wf_ty' --(lem_wf_ty' c)
                      p_ty'cv_txty'  = lem_witness_sub Empty v t_x p_v_tx (ty' c) Star p_emp_exty'
                                                       WFEEmpty
                      p_txty'_extxt' = lem_subtype_in_exists n Empty t_x (ty' c) 
                                                     (t' ? lem_wftype_islct Empty (TExists t_x t') 
                                                                            Star p_emp_extxt')
                                                     Star p_g_tx nms mk_p_ty'c_t'
                      p_emp_ty'cv    = lem_typing_wf Empty (delta c v ? compat) (tsubBV v (ty' c)) 
                                                     p_cv_ty'cv WFEEmpty
                      p_ty'cv_extxt' = lem_sub_trans Empty WFEEmpty (tsubBV v (ty' c)) Star p_emp_ty'cv
                                                     (TExists t_x (ty' c)) (TExists t_x t') Star
                                                     p_emp_extxt' p_ty'cv_txty' p_txty'_extxt' 
                      n''         = max (typSize p_v_tx)     (subtypSize p_tx_in)
                      n'''        = max (typSize p_cv_ty'cv) (subtypSize p_ty'cv_extxt')     
              (SBind {}) -> case p_c_s of
                (TPrm {}) -> impossible "s == tyc must be TFunc"
 where
     p_cv_extxt'    = TApp n' Empty (Prim c) t_x t' p_c_txt' v p_v_tx
     compat         = lem_prim_compat_in_tapp c v (TExists t_x t') p_cv_extxt'
     n'          = max (typSize p_c_txt')   (typSize p_v_tx)

{-@ lem_tyeql_forallbase :: c:Prim  -> k:Kind -> s:Type 
        -> ProofOf(Subtype Empty (ty c) (TPoly k s)) -> { pf:_ | k == Base } @-}
lem_tyeql_forallbase :: Prim -> Kind -> Type -> Subtype -> Proof
lem_tyeql_forallbase c k s p_ty_aks = case p_ty_aks of
  (SPoly {}) -> ()

{-@ lem_deltaT_typ ::  c:Prim  -> k:Kind -> s:Type
        -> ProofOf(HasType Empty (Prim c) (TPoly k s)) -> t:UserType -> ProofOf(WFType Empty t k)
        -> ProofOf(HasType Empty (deltaT c t) (tsubBTV t s)) @-}
lem_deltaT_typ :: Prim -> Kind -> Type -> HasType -> Type -> WFType -> HasType
lem_deltaT_typ c k u' p_c_ku' t p_emp_t  = case p_c_ku' of
  (TPrm _ _) -> lem_deltaT_ty'c c t p_emp_t 
  (TSub {})
    -> let (TSub _ _ _ tyc p_c_tyc _ k_u p_emp_ku' p_tyc_u)
               = lem_collapse_sub Empty (Prim c) (TPoly k u') WFEEmpty p_c_ku'
         in case p_tyc_u of
              (SPoly n _ _ tyc' _ nms mk_p_tyc'_u') -> case p_c_tyc of 
                (TPrm Empty _c) 
                      -> TSub n'' Empty deltaT_c_t tyct p_ct_tyct (tsubBTV t u') Star
                              p_emp_u't p_tyct_u't
                    where
                      p_ct_u't    = TAppT n' Empty (Prim c) k u' p_c_ku' t p_emp_t
                      deltaT_c_t  = deltaT c (t ? lem_prim_compatT_in_tappT c t (tsubBTV t u') p_ct_u't)
                      tyct        = tsubBTV t (TFunc  (inType c) (ty' c))
                      p_ct_tyct   = lem_deltaT_ty'c c t (p_emp_t ? lem_tyeql_forallbase c k u' p_tyc_u)
                      a           = fresh nms --_var {-(union-} nms {-nms')-} Empty
                      p_emp_u't   = lem_typing_wf Empty (AppT (Prim c) t) (tsubBTV t u') p_ct_u't 
                                                  WFEEmpty
                      p_tyct_u't  = lem_subst_tv_sub Empty Empty a t k p_emp_t WFEEmpty
                                      (unbind_tvT a (TFunc (inType c) (ty' c)))
                                      (unbind_tvT a u') (mk_p_tyc'_u' a)
                                  ? toProof ( esubFTV a t Empty === Empty )
                                  ? lem_empty_concatE Empty
                                  ? lem_tsubFTV_unbind_tvT a t (TFunc (inType c) (ty' c)
                                          ? lem_free_bound_in_env Empty (ty c) Star (lem_wf_ty c) a)
                                  ? lem_tsubFTV_unbind_tvT a t 
                                          (u' ? lem_free_bound_in_env Empty (TPoly k u') k_u p_emp_ku' a)
                      n'          = typSize p_c_ku'
                      n''         = max (typSize p_ct_tyct) (subtypSize p_tyct_u't)
              (SBind {}) -> case p_c_tyc of
                (TAbsT {}) -> impossible "ty(c) must be TPoly"
