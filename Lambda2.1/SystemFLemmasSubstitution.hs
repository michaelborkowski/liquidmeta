{-# LANGUAGE GADTs #-}

{-@ LIQUID "--no-termination" @-}  -- TODO: assume
{-@ LIQUID "--no-totality" @-}     -- TODO: assume
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SystemFLemmasSubstitution where

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
import SystemFWellFormedness
import SystemFLemmasWellFormedness
import SystemFLemmasFTyping

{-@ reflect foo22 @-}
foo22 x = Just x
foo22 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development for the Underlying System F Calculus
------------------------------------------------------------------------------

-- -- -- -- -- -- -- -- ---
-- THE SUBSTITUTION LEMMA -
-- -- -- -- -- -- -- -- ---

{-@ lem_subst_ftyp :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> { x:Vname | (not (in_envF x g)) && not (in_envF x g') } -> v_x:Value
        -> t_x:FType -> ProofOf(HasFType g v_x t_x) 
        -> ProofOf(WFFE (concatF (FCons x t_x g) g')) -> e:Expr -> t:FType
        -> ProofOf(HasFType (concatF (FCons x t_x g) g') e t)
        -> ProofOf(HasFType (concatF g g') (subFV x v_x e) t) @-}
lem_subst_ftyp :: FEnv -> FEnv -> Vname -> Expr -> FType -> HasFType -> WFFE
        -> Expr -> FType -> HasFType -> HasFType
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t (FTBC _env b) = FTBC (concatF g g') b
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t (FTIC _env n) = FTIC (concatF g g') n
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t (FTVar1 _env z _t)
  = undefined --assume
{-  = case g' of
      (FEmpty)         -> p_vx_tx   
      (FCons _z _ g'') -> FTVar1 (concatF g g'') (z ? lem_in_env_concatF (FCons x t_x g) g'' z
                                                    ? lem_in_env_concatF g g'' z) t-}
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t (FTVar2 _env z _t p_z_t w t_w)
  = undefined -- assume
{-
  = case g' of
      (FEmpty)           -> case ( x == z ) of
                    (True)  -> impossible "it is"
                    (False) -> p_z_t -- ? toProof ( e === (FV z) )
      (FCons _w _tw g'') -> case ( x == z ) of
                    (True)  -> lem_weaken_ftyp (concatF g g'') FEmpty v_x t p_gg''_vx_tx w t_w 
                                               ? toProof ( e === FV x )
                                 where
                                   p_gg''_vx_tx = lem_subst_ftyp g g'' x v_x t_x p_vx_tx e t p_z_t
                    (False) -> FTVar2 (concatF g g'') (z ? lem_in_env_concatF (FCons x t_x g) g'' z
                                                        ? lem_in_env_concatF g g'' z)
                                      t p_z_tvx (w ? lem_fv_bound_in_fenv g v_x t_x p_vx_tx w
                                                   ? lem_in_env_concatF (FCons x t_x g) g'' w   
                                                   ? lem_in_env_concatF g g'' w) t_w
                                 where
                                   p_z_tvx = lem_subst_ftyp g g'' x v_x t_x p_vx_tx e t p_z_t-}
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t (FTVar3 _env z _t p_z_t a k)
  = undefined -- assume
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t (FTPrm _env c) = FTPrm (concatF g g') c
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t (FTAbs env_ z t_z e' t' _ _ y_ p_yenv_e'_t')
  = undefined -- assume
{-  = FTAbs (concatF g g') z t_z (subFV x v_x e') t' y p_yg'g_e'vx_t'
      where
        y              = y_ ? lem_in_env_concatF g g' y_
                            ? lem_in_env_concatF (FCons x t_x g) g' y_
                            ? lem_fv_bound_in_fenv g v_x t_x p_vx_tx y_
        p_yg'g_e'vx_t' = lem_subst_ftyp g (FCons y t_z g') x v_x t_x p_vx_tx (unbind z y e')
                                        t' p_yenv_e'_t' ? lem_commute_subFV_subBV1 z (FV y) x v_x e'-}
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t (FTApp env_ e' t_z t' p_env_e'_tzt' e_z p_env_ez_tz)
  = undefined -- assume
{-  = FTApp (concatF g g') (subFV x v_x e') t_z t' p_g'g_e'vx_tzt' (subFV x v_x e_z) p_g'g_ezvx_tz
      where
        p_g'g_e'vx_tzt' = lem_subst_ftyp g g' x v_x t_x p_vx_tx e' (FTFunc t_z t') p_env_e'_tzt'
        p_g'g_ezvx_tz   = lem_subst_ftyp g g' x v_x t_x p_vx_tx e_z t_z p_env_ez_tz-}
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t (FTAbsT env_ a k e' t' a' p_a'env_e'_t')
  = undefined -- assume
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t (FTAppT env_ e' a k t' p_env_e'_at' liqt p_env_er_liqt)
  = undefined -- assume
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t (FTLet env_ e_z t_z p_env_ez_tz z e' t_ y_ p_yenv_e'_t)
  = undefined -- assume
{-  = FTLet (concatF g g') (subFV x v_x e_z) t_z p_g'g_ezvx_tz z (subFV x v_x e') t y p_yg'g_e'vx_t
      where
        y              = y_ ? lem_in_env_concatF g g' y_
                            ? lem_in_env_concatF (FCons x t_x g) g' y_
                            ? lem_fv_bound_in_fenv g v_x t_x p_vx_tx y_
        p_g'g_ezvx_tz  = lem_subst_ftyp g g' x v_x t_x p_vx_tx e_z t_z p_env_ez_tz
        p_yg'g_e'vx_t  = lem_subst_ftyp g (FCons y t_z g') x v_x t_x p_vx_tx (unbind z y e')
                                        t p_yenv_e'_t ? lem_commute_subFV_subBV1 z (FV y) x v_x e'-}
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t (FTAnn env_ e' t_ liqt p_env_e'_t)
  = undefined -- assume
{-  = FTAnn (concatF g g') (subFV x v_x e') t 
          (tsubFV x (v_x ? lem_fv_subset_bindsF g v_x t_x p_vx_tx )
                  liqt ? lem_erase_tsubFV x v_x liqt
                       ? lem_binds_cons_concatF g g' x t_x ) p_g'g_e'_t
      where
        p_g'g_e'_t = lem_subst_ftyp g g' x v_x t_x p_vx_tx e' t p_env_e'_t
-}

{-@ lem_subst_tv_ftyp :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> { a:Vname | (not (in_envF a g)) && not (in_envF a g') } -> t_a:Type -> k_a:Kind
        -> ProofOf(WFFT g (erase t_a) k_a) -> ProofOf(WFFE (concatF (FConsT a k_a g) g')) 
        -> e:Expr -> t:FType -> ProofOf(HasFType (concatF (FConsT a k_a g) g') e t)
        -> ProofOf(HasFType (concatF g (fesubFV a (erase t_a) g')) 
                            (subFTV a t_a e) (ftsubFV a (erase t_a) t)) @-}
lem_subst_tv_ftyp :: FEnv -> FEnv -> Vname -> Type -> Kind -> WFFT -> WFFE
        -> Expr -> FType -> HasFType -> HasFType
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta pf_wf_env e t (FTBC _env b) 
  = FTBC (concatF g (fesubFV a (erase t_a) g')) b ? lem_in_fenv_fesub g' a (erase t_a) a
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta pf_wf_env e t (FTIC _env n)
  = FTIC (concatF g (fesubFV a (erase t_a) g')) n ? lem_in_fenv_fesub g' a (erase t_a) a
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta pf_wf_env e t (FTVar1 _env z _t)
  = undefined -- assume
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta pf_wf_env e t (FTVar2 _env z _t p_z_t w t_w)
  = undefined -- assume
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta pf_wf_env e t (FTVar3 _env z _t p_z_t a' k')
  = undefined -- assume
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta pf_wf_env e t (FTPrm _env c) 
  = undefined -- assume
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta pf_wf_env e t (FTAbs env_ z t_z e' t' _ _ y_ p_yenv_e'_t')
  = undefined -- assume
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta pf_wf_env e t (FTApp env_ e' t_z t' p_env_e'_tzt' e_z p_env_ez_tz)
  = undefined -- assume
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta pf_wf_env e t (FTAbsT env_ a' k e' t' a'' p_a''env_e'_t')
  = undefined -- assume
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta pf_wf_env e t (FTAppT env_ e' a' k' t' p_env_e'_a't' liqt p_env_er_liqt)
  = undefined -- assume
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta pf_wf_env e t (FTLet env_ e_z t_z p_env_ez_tz z e' t_ y_ p_yenv_e'_t)
  = undefined -- assume
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta pf_wf_env e t (FTAnn env_ e' t_ liqt p_env_e'_t)
  = undefined -- assume
