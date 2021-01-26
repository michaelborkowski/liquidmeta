{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SubstitutionLemmaWFEnv where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Strengthenings
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import PrimitivesFTyping
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasFTyping2
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import BasicPropsEraseTyping
import PrimitivesSemantics -- this module has moved "up" in the order
import LemmasWeakenWF
import LemmasWeakenWFTV
import LemmasWellFormedness
import SubstitutionLemmaWF
import SubstitutionLemmaWFTV
import SubstitutionWFAgain

{-@ reflect foo51 @-}
foo51 :: a -> Maybe a
foo51 x = Just x

{-@ lem_subst_wfenv :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> ProofOf(HasType g v_x t_x)
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') )
        -> ProofOf(WFEnv (concatE g (esubFV x v_x g')) ) / [envsize g'] @-}
lem_subst_wfenv :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv -> WFEnv
lem_subst_wfenv g Empty           x v_x t_x p_vx_tx p_xg_wf  = case p_xg_wf of
  (WFEBind  _g p_g_wf _x _tx _ _) -> p_g_wf
  (WFEBindT _g p_g_wf _  _)       -> p_g_wf
lem_subst_wfenv g (Cons z t_z g') x v_x t_x p_vx_tx p_env_wf = case p_env_wf of
  (WFEBind env' p_env'_wf _z _tz k_z p_env'_tz) 
    -> WFEBind env'' p_env''_wf z (tsubFV x v_x t_z) k_z p_env''_tzvx
      where
        env''        = concatE g (esubFV x v_x g')
        p_env''_wf   = lem_subst_wfenv g g' x v_x t_x p_vx_tx p_env'_wf
        p_env''_tzvx = lem_subst_wf' g g' x v_x t_x p_vx_tx p_env'_wf t_z k_z p_env'_tz
lem_subst_wfenv g (ConsT a k_a g') x v_x t_x p_vx_tx p_env_wf = case p_env_wf of
  (WFEBindT env' p_env'_wf _a _ka)           -> WFEBindT env'' p_env''_wf a k_a
    where
      env''      = concatE g (esubFV x v_x g')
      p_env''_wf = lem_subst_wfenv g g' x v_x t_x p_vx_tx p_env'_wf

{-@ lem_subst_tv_wfenv :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') )
        -> ProofOf(WFEnv (concatE g (esubFTV a t_a g')) ) / [envsize g'] @-}
lem_subst_tv_wfenv :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv -> WFEnv
lem_subst_tv_wfenv g Empty           a t_a k_a p_g_ta p_xg_wf  = case p_xg_wf of
  (WFEBind  _g p_g_wf _ _ _ _) -> p_g_wf
  (WFEBindT _g p_g_wf _ _)     -> p_g_wf
lem_subst_tv_wfenv g (Cons z t_z g') a t_a k_a p_g_ta p_env_wf = case p_env_wf of
  (WFEBind env' p_env'_wf _z _tz k_z p_env'_tz) 
    -> WFEBind env'' p_env''_wf z (tsubFTV a t_a t_z) k_z p_env''_tzta
      where
        env''        = concatE g (esubFTV a t_a g')
        p_env''_wf   = lem_subst_tv_wfenv g g' a t_a k_a p_g_ta p_env'_wf
        p_env''_tzta = lem_subst_tv_wf'   g g' a t_a k_a p_g_ta p_env'_wf t_z k_z p_env'_tz
lem_subst_tv_wfenv g (ConsT a1 k1 g') a t_a k_a p_g_ta p_env_wf = case p_env_wf of
  (WFEBindT env' p_env'_wf _a1 _k1)          -> WFEBindT env'' p_env''_wf a1 k1
    where
      env''      = concatE g (esubFTV a t_a g')
      p_env''_wf = lem_subst_tv_wfenv g g' a t_a k_a p_g_ta p_env'_wf


{-@ lem_csubst_wfenv :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> th:CSub -> ProofOf(DenotesEnv g th) -> ProofOf(WFEnv (concatE g g'))
        -> ProofOf(WFEnv (csubst_env th g')) @-}
lem_csubst_wfenv :: Env -> Env -> CSub -> DenotesEnv -> WFEnv -> WFEnv
lem_csubst_wfenv Empty           g'  th   den_g_th p_g'_wf = p_g'_wf ? lem_empty_concatE g' 
                                                                     ? lem_csubst_env_empty th
lem_csubst_wfenv (Cons x t_x g)  g' xth den_xg_xth p_g'xg_wf = case den_xg_xth of
  (DExt _g th_ den_g_th _x _tx v_x den_thtx_vx) -> p_g'_wf
    where
      th         = th_ ? lem_binds_env_th g th_ den_g_th
      p_emp_vx_thtx  = get_ftyp_from_den (ctsubst th t_x) v_x den_thtx_vx ? lem_erase_ctsubst th t_x
      p_g'x_wf   = lem_csubst_wfenv g (concatE (Cons x t_x Empty) g') th den_g_th 
                                    (p_g'xg_wf ? lem_concat_shift g x t_x g')
                                    ? lem_csubst_env_concat th (Cons x t_x Empty) g'
                                    ? lem_csubst_cons_env th x t_x Empty
                                    ? lem_csubst_env_empty th
      p_g'_wf    = lem_subst_wfenv Empty (csubst_env th g') x v_x (ctsubst th t_x) p_emp_vx_thtx
                                   p_g'_wf ? lem_empty_concatE (esubFV x v_x (csubst_env th g'))
                                           ? lem_unroll_csubst_env_left th x v_x g'
lem_csubst_wfenv (ConsT a k_a g) g' ath den_ag_ath p_g'ag_wf = case den_ag_ath of 
  (DExtT _g th_ den_g_th _a _ka t_a p_emp_ta) -> p_g'_wf
    where
      th         = th_ ? lem_binds_env_th g th_ den_g_th
      p_ag_wf    = lem_truncate_wfenv (ConsT a k_a g)  g' p_g'ag_wf
      (WFEBindT _ p_g_wf _ _) = p_ag_wf
      p_g_ta     = lem_weaken_many_wf' Empty g (p_g_wf ? lem_empty_concatE g) t_a k_a p_emp_ta
      p_g'g_wf   = lem_subst_tv_wfenv g g' a t_a k_a p_g_ta p_g'ag_wf
      p_g'_wf    = lem_csubst_wfenv g (esubFTV a t_a g') th den_g_th p_g'g_wf

{-@ lem_ctsubst_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> t:Type -> k:Kind -> ProofOf(WFType (concatE g g') t k) -> ProofOf (WFEnv (concatE g g')) 
        -> th:CSub -> ProofOf(DenotesEnv g th)  
        -> ProofOf(WFType (csusbt_env th g') (ctsubst th t) k) @-}
lem_ctsubst_wf :: Env -> Env -> Type -> Kind -> WFType -> WFEnv -> CSub -> DenotesEnv -> WFType
lem_ctsubst_wf Empty           g' t k p_env_t p_env_wf th den_g_th = case den_g_th of
  (DEmp)                                           -> p_env_t ? lem_binds_env_th Empty th den_g_th
lem_ctsubst_wf (Cons x t_x g)  g' t k p_env_t p_env_wf xth den_xg_xth = case den_xg_xth of
  (DExt _g th_ den_g_th _x _tx v_x den_thtx_vx) -> p_g'_xtht
    where
      th             = th_ ? lem_binds_env_th g th_ den_g_th
      p_emp_vx_thtx  = get_ftyp_from_den (ctsubst th t_x) v_x den_thtx_vx ? lem_erase_ctsubst th t_x
      p_xg_wf        = lem_truncate_wfenv (Cons x t_x g)  g' p_env_wf
      (WFEBind _ p_g_wf _ _ k_x p_g_tx) = p_xg_wf
      p_er_g_wf      = lem_erase_env_wfenv g p_g_wf
      p_g'x_wf       = lem_csubst_wfenv g (concatE (Cons x t_x Empty) g') th den_g_th
                                        (p_env_wf ? lem_concat_shift g x t_x g')
      p_g'x_tht      = lem_ctsubst_wf g (concatE (Cons x t_x Empty) g') t k 
                                      (p_env_t ? lem_concat_shift g x t_x g') 
                                      (p_env_wf ? lem_concat_shift g x t_x g')
                                      th den_g_th ? lem_csubst_env_concat th (Cons x t_x Empty) g'
                                                  ? lem_csubst_cons_env th x t_x Empty
                                                  ? lem_csubst_env_empty th
      p_g'_xtht      = lem_subst_wf Empty (csubst_env th g') x v_x (ctsubst th t_x) p_emp_vx_thtx     
                                    p_g'x_wf (ctsubst th t) k p_g'x_tht
                                    ? lem_empty_concatE (esubFV x v_x (csubst_env th g'))
                                    ? lem_unroll_csubst_env_left th x v_x g'
                                    ? lem_unroll_ctsubst_left th x v_x t
lem_ctsubst_wf (ConsT a k_a g) g' t k p_env_t p_env_wf ath den_ag_ath = case den_ag_ath of
  (DExtT _g th_ den_g_th _a _ka t_a p_emp_ta) -> p_g'_atht
    where
      th         = th_ ? lem_binds_env_th g th_ den_g_th
      p_ag_wf    = lem_truncate_wfenv (ConsT a k_a g)  g' p_env_wf
      (WFEBindT _ p_g_wf _ _) = p_ag_wf
      p_g_ta     = lem_weaken_many_wf' Empty g (p_g_wf ? lem_empty_concatE g) t_a k_a p_emp_ta
      p_g'g_at   = lem_subst_tv_wf' g g' a t_a k_a p_g_ta p_env_wf t k p_env_t 
      p_g'g_wf   = lem_subst_tv_wfenv g g' a t_a k_a p_g_ta p_env_wf
      p_g'_atht  = lem_ctsubst_wf g (esubFTV a t_a g') (tsubFTV a t_a t) k p_g'g_at p_g'g_wf th den_g_th
