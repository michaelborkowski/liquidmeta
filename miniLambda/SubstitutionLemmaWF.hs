{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SubstitutionLemmaWF where

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

{-@ reflect foo48 @-}
foo48 x = Just x
foo48 :: a -> Maybe a

-- -- -- -- -- -- -- -- -- -- -- ---
-- Part of the Substitution Lemma --
-- -- -- -- -- -- -- -- -- -- -- ---

{-@ lem_subst_wf_wfrefn :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
          -> t_x:Type -> ProofOf(HasFType (erase_env g) v_x (erase t_x))
          -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> t:Type 
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (Cons x t_x g) g') t && isWFRefn p_env_t}
          -> ProofOf(WFType (concatE g (esubFV x v_x g')) (tsubFV x v_x t)) / [wftypSize p_env_t, 0] @-}
lem_subst_wf_wfrefn :: Env -> Env -> Vname -> Expr -> Type -> HasFType -> WFEnv 
                    -> Type -> WFType -> WFType
lem_subst_wf_wfrefn g g' x v_x t_x p_vx_er_tx p_env_wf t (WFRefn env z b p y_ p_env'_p_bl)
  = WFRefn (concatE g (esubFV x v_x g')) z b (subFV x v_x p) y -- _env = g'; x:tx; g
           p_ygg'_pvx_bl 
      where
        y             = y_ ? lem_in_env_esub g' x v_x y_
                           ? lem_in_env_concat g  g' y_
                           ? lem_in_env_concat (Cons x t_x g) g' y_
                           ? lem_fv_bound_in_fenv (erase_env g) v_x (erase t_x) p_vx_er_tx y_
        p_ygg'_pvx_bl = lem_subst_ftyp (erase_env g) (FCons y (FTBasic b) (erase_env g')) 
                           (x ? lem_in_env_concatF (erase_env g) (erase_env g') x
                              ? lem_in_env_concatF (erase_env g) (FCons y (FTBasic b) (erase_env g')) x)
                           v_x (erase t_x)  p_vx_er_tx (unbind z y p) (FTBasic TBool) 
                           (p_env'_p_bl ? lem_erase_concat (Cons x t_x g) g')
                           ? lem_commute_subFV_subBV1 z (FV y) x 
                               (v_x ? lem_freeBV_emptyB (erase_env g) v_x (erase t_x) p_vx_er_tx) p
                           ? lem_erase_concat g (esubFV x v_x g')
                           ? lem_erase_esubFV x v_x g'

{-@ lem_subst_wf_wffunc :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
          -> t_x:Type -> ProofOf(HasFType (erase_env g) v_x (erase t_x)) 
          -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> t:Type 
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (Cons x t_x g) g') t && isWFFunc p_env_t}
          -> ProofOf(WFType (concatE g (esubFV x v_x g')) (tsubFV x v_x t)) / [wftypSize p_env_t, 0] @-}
lem_subst_wf_wffunc :: Env -> Env -> Vname -> Expr -> Type -> HasFType -> WFEnv 
                           -> Type -> WFType -> WFType
lem_subst_wf_wffunc g g' x v_x t_x p_vx_er_tx p_env_wf t (WFFunc _env z t_z p_env_tz t' y_ p_yenv_t')
  = WFFunc (concatE g (esubFV x v_x g')) z (tsubFV x v_x t_z) p_g'g_tzvx 
           (tsubFV x v_x t') y p_yg'g_t'vx
      where
        y           = y_ ? lem_in_env_esub g' x v_x y_ 
                         ? lem_in_env_concat g  g' y_ 
                         ? lem_in_env_concat (Cons x t_x g) g' y_
                         ? lem_fv_bound_in_fenv (erase_env g) v_x (erase t_x) p_vx_er_tx y_
        p_yenv_wf   = WFEBind (concatE (Cons x t_x g) g') p_env_wf y t_z p_env_tz
        p_g'g_tzvx  = lem_subst_wf g g'              x v_x t_x p_vx_er_tx p_env_wf  t_z p_env_tz
        p_yg'g_t'vx = lem_subst_wf g (Cons y t_z g') x v_x t_x p_vx_er_tx p_yenv_wf (unbindT z y t') 
                         (p_yenv_t' {-? lem_erase_concat (Cons x t_x g) g'-})
                         ? lem_commute_tsubFV_tsubBV1 z (FV y) x 
                               (v_x ? lem_freeBV_emptyB (erase_env g) v_x (erase t_x) p_vx_er_tx) t'

{-@ lem_subst_wf_wfexis :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
          -> t_x:Type -> ProofOf(HasFType (erase_env g) v_x (erase t_x)) 
          -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> t:Type 
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (Cons x t_x g) g') t && isWFExis p_env_t}
          -> ProofOf(WFType (concatE g (esubFV x v_x g')) (tsubFV x v_x t)) / [wftypSize p_env_t, 0] @-}
lem_subst_wf_wfexis :: Env -> Env -> Vname -> Expr -> Type -> HasFType -> WFEnv 
                           -> Type -> WFType -> WFType
lem_subst_wf_wfexis g g' x v_x t_x p_vx_er_tx p_env_wf t (WFExis _env z t_z p_env_tz t' y_ p_yenv_t')
  = WFExis (concatE g (esubFV x v_x g')) z (tsubFV x v_x t_z) p_g'g_tzvx 
           (tsubFV x v_x t') y p_yg'g_t'vx
      where
        y           = y_ ? lem_in_env_esub g' x v_x y_ 
                         ? lem_in_env_concat g  g' y_ 
                         ? lem_in_env_concat (Cons x t_x g) g' y_
                         ? lem_fv_bound_in_fenv (erase_env g) v_x (erase t_x) p_vx_er_tx y_
        p_yenv_wf   = WFEBind (concatE (Cons x t_x g) g') p_env_wf y t_z p_env_tz
        p_g'g_tzvx  = lem_subst_wf g g'              x v_x t_x p_vx_er_tx p_env_wf t_z p_env_tz
        p_yg'g_t'vx = lem_subst_wf g (Cons y t_z g') x v_x t_x p_vx_er_tx p_yenv_wf (unbindT z y t') 
                         (p_yenv_t' {-? lem_erase_concat (Cons x t_x g) g'-})
                         ? lem_commute_tsubFV_tsubBV1 z (FV y) x 
                               (v_x ? lem_freeBV_emptyB (erase_env g) v_x (erase t_x) p_vx_er_tx) t'

{-@ lem_subst_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
          -> t_x:Type -> ProofOf(HasFType (erase_env g) v_x (erase t_x))
          -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> t:Type 
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (Cons x t_x g) g') t }
          -> ProofOf(WFType (concatE g (esubFV x v_x g')) (tsubFV x v_x t)) / [wftypSize p_env_t, 1] @-}
lem_subst_wf :: Env -> Env -> Vname -> Expr -> Type -> HasFType -> WFEnv 
                    -> Type -> WFType -> WFType
lem_subst_wf g g' x v_x t_x p_vx_tx p_env_wf t p_env_t@(WFRefn env z b p y_ p_env'_p_bl)  
  = lem_subst_wf_wfrefn g g' x v_x t_x p_vx_tx p_env_wf t p_env_t 
lem_subst_wf g g' x v_x t_x p_vx_tx p_env_wf t p_env_t@(WFFunc _env z t_z p_env_tz t' y_ p_yenv_t')
  = lem_subst_wf_wffunc g g' x v_x t_x p_vx_tx p_env_wf t p_env_t
lem_subst_wf g g' x v_x t_x p_vx_tx p_env_wf t p_env_t@(WFExis _env z t_z p_env_tz t' y_ p_yenv_t')
  = lem_subst_wf_wfexis g g' x v_x t_x p_vx_tx p_env_wf t p_env_t

-- this version takes a regular typing judgment
{-@ lem_subst_wf' :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
          -> t_x:Type -> ProofOf(HasType g v_x t_x) 
          -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> t:Type 
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (Cons x t_x g) g') t }
          -> ProofOf(WFType (concatE g (esubFV x v_x g')) (tsubFV x v_x t)) @-} 
lem_subst_wf' :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv 
                     -> Type -> WFType -> WFType
lem_subst_wf' g g' x v_x t_x p_vx_tx p_env_wf t p_env_t
  = lem_subst_wf g g' x v_x t_x p_vx_er_tx p_env_wf t p_env_t 
      where
        p_xg_wf     = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _) = p_xg_wf
        p_vx_er_tx = lem_typing_hasftype g v_x t_x p_vx_tx p_g_wf

-------------------------------------------------------------
------- | METATHEORY Development: Some technical Lemmas
-------------------------------------------------------------

{-@ lem_witness_sub :: g:Env -> v_x:Value -> t_x:Type -> ProofOf(HasType g v_x t_x)
        -> ProofOf(WFEnv g) -> x:Vname -> t':Type 
        -> { y:Vname | not (in_env y g) && not (Set_mem y (free t')) }
        -> ProofOf(WFType (Cons y t_x g) (unbindT x y t'))
        -> ProofOf(Subtype g (tsubBV x v_x t') (TExists x t_x t')) @-}
lem_witness_sub :: Env -> Expr -> Type -> HasType -> WFEnv -> Vname -> Type
                       -> Vname -> WFType -> Subtype
lem_witness_sub g v_x t_x p_vx_tx p_g_wf x t' y p_yg_t'
  = SWitn g v_x t_x p_vx_tx (tsubBV x v_x t') x t' p_t'vx_t'vx
      where
        p_g_tx      = lem_typing_wf g v_x t_x p_vx_tx p_g_wf
        p_yg_wf     = WFEBind g p_g_wf y t_x p_g_tx
        p_g_t'vx    = lem_subst_wf' g Empty y v_x t_x p_vx_tx p_yg_wf (unbindT x y t') p_yg_t'
                                    ? lem_tsubFV_unbindT x y v_x t'
        p_t'vx_t'vx = lem_sub_refl g (tsubBV x v_x t') p_g_t'vx p_g_wf
