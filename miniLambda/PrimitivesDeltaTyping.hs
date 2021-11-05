{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesDeltaTyping where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFTyping
import WellFormedness
import PrimitivesFTyping
import PrimitivesWFType
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
import LemmasSubtypeClosed
import LemmasInvertLambda
import PrimitivesRefinements

{-@ reflect foo61 @-}
foo61 x = Just x
foo61 :: a -> Maybe a

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

{-@ lem_delta_ty'c :: c:Prim  -> v:Value -> ProofOf(HasType Empty v (inType c))
        -> ProofOf(HasType Empty (delta c v) (tsubBV (firstBV c) v (ty' c))) @-}
lem_delta_ty'c :: Prim -> Expr -> HasType -> HasType
lem_delta_ty'c c v p_v_tx = undefined -- this part we assume

{-@ lem_delta_typ :: c:Prim -> v:Value -> x:Vname -> t_x:Type -> t':Type
        -> ProofOf(HasType Empty (Prim c) (TFunc x t_x t')) -> ProofOf(HasType Empty v t_x)
        -> { pf:_ | propOf pf == HasType Empty (delta c v) (tsubBV x v t') } @-} 
lem_delta_typ :: Prim -> Expr -> Vname -> Type -> Type 
                     -> HasType -> HasType -> HasType
lem_delta_typ c v x t_x t' p_c_txt' p_v_tx  
  = case (lem_typ_lower_bound Empty (Prim c) (TFunc x t_x t') WFEEmpty p_c_txt') of 
      (LBForType _ _ _ s p_s_t p_c_s) -> case p_c_s of -- s === ty c
          (TPrm Empty _c) -> TSub Empty (delta_c_v) ty'cv p_cv_ty'cv 
                                  (tsubBV x v t') p_emp_t'v p_ty'cv_t'v
            where
              delta_c_v   = delta c (v ? lem_prim_compat_in_tapp c v (TExists x t_x t')
                                            (TApp Empty (Prim c) x t_x t' p_c_txt' v p_v_tx))
              ty'cv       = tsubBV (firstBV c) v (ty' c)
              (WFFunc _ _ _ _ _ y p_y_t') = lem_typing_wf Empty (Prim c) (TFunc x t_x t') 
                                                               p_c_txt' WFEEmpty
              p_emp_tx    = lem_typing_wf Empty v t_x p_v_tx WFEEmpty
              p_y_wf      = WFEBind Empty WFEEmpty y t_x p_emp_tx 
              p_emp_t'v   = lem_subst_wf' Empty Empty y v t_x p_v_tx p_y_wf (unbindT x y t') p_y_t'
                                ? lem_tsubFV_unbindT x y v t'
              (SFunc _ _ _ _ _ p_tx_in _ _ z p_z_ty'c_t') = p_s_t
              p_v_in      = TSub Empty v t_x p_v_tx (inType c) (lem_wf_intype c) p_tx_in
              p_cv_ty'cv  = lem_delta_ty'c c v p_v_in
              p_z_wf      = WFEBind Empty WFEEmpty z t_x p_emp_tx 
              p_z_t'      = lem_change_var_wf Empty y t_x Empty (unbindT x y t') p_y_t' z
                                ? lem_tsubFV_unbindT x y (FV z) t'
              p_zin_ty'c  = lem_wf_ty' c z
              p_ztx_ty'c  = lem_subtype_in_env_wf Empty Empty z t_x (inType c) p_tx_in 
                                                  (unbindT (firstBV c) z (ty' c)) p_zin_ty'c
              p_ty'cv_t'v = lem_subst_sub Empty Empty z v t_x p_v_tx p_z_wf 
                                          (unbindT (firstBV c) z (ty' c)) p_ztx_ty'c 
                                          (unbindT x z t') p_z_t'
                                          p_z_ty'c_t' 
                                ? lem_tsubFV_unbindT (firstBV c) z v (ty' c)
                                ? lem_tsubFV_unbindT x           z v t'
