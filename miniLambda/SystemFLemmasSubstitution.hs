{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SystemFLemmasSubstitution where

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

{-@ reflect foo24 @-}
foo24 x = Just x
foo24 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development for the Underlying System F Calculus
------------------------------------------------------------------------------

-- -- -- -- -- -- -- -- ---
-- THE SUBSTITUTION LEMMA -
-- -- -- -- -- -- -- -- ---

{-@ lem_subst_ftyp_ftvar :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
      -> { x:Vname | (not (in_envF x g)) && not (in_envF x g') } -> v_x:Value
      -> t_x:FType -> ProofOf(HasFType g v_x t_x) -> e:Expr -> t:FType
      -> {p_e_t:HasFType | propOf p_e_t == HasFType (concatF (FCons x t_x g) g') e t && isFTVar p_e_t}
      -> ProofOf(HasFType (concatF g g') (subFV x v_x e) t) / [ftypSize p_e_t, 0] @-}
lem_subst_ftyp_ftvar :: FEnv -> FEnv -> Vname -> Expr -> FType -> HasFType 
        -> Expr -> FType -> HasFType -> HasFType
lem_subst_ftyp_ftvar g g' x v_x t_x p_vx_tx e t (FTVar1 _env z _t)
  = case g' of
      (FEmpty)         -> p_vx_tx   
      (FCons _z _ g'') -> FTVar1 (concatF g g'') (z ? lem_in_env_concatF (FCons x t_x g) g'' z
                                                    ? lem_in_env_concatF g g'' z) t
lem_subst_ftyp_ftvar g g' x v_x t_x p_vx_tx e t (FTVar2 _env z _t p_z_t w t_w)
  = case g' of
      (FEmpty)           -> case ( x == z ) of
        (True)  -> impossible "it is"
        (False) -> p_z_t -- ? toProof ( e === (FV z) )
      (FCons _w _tw g'') -> case ( x == z ) of
        (True)  -> lem_weaken_ftyp (concatF g g'') FEmpty v_x t p_gg''_vx_tx w t_w 
          where
            p_gg''_vx_tx = lem_subst_ftyp g g'' x v_x t_x p_vx_tx e t p_z_t
        (False) -> FTVar2 (concatF g g'') (z ? lem_in_env_concatF (FCons x t_x g) g'' z
                                             ? lem_in_env_concatF g g'' z)
                          t p_z_tvx (w ? lem_fv_bound_in_fenv g v_x t_x p_vx_tx w
                                       ? lem_in_env_concatF (FCons x t_x g) g'' w   
                                       ? lem_in_env_concatF g g'' w) t_w
          where
            p_z_tvx = lem_subst_ftyp g g'' x v_x t_x p_vx_tx e t p_z_t

{-@ lem_subst_ftyp :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> { x:Vname | (not (in_envF x g)) && not (in_envF x g') } -> v_x:Value
        -> t_x:FType -> ProofOf(HasFType g v_x t_x) -> e:Expr -> t:FType
        -> { p_e_t:HasFType | propOf p_e_t == HasFType (concatF (FCons x t_x g) g') e t }
        -> ProofOf(HasFType (concatF g g') (subFV x v_x e) t) / [ftypSize p_e_t, 1] @-}
lem_subst_ftyp :: FEnv -> FEnv -> Vname -> Expr -> FType -> HasFType
        -> Expr -> FType -> HasFType -> HasFType
lem_subst_ftyp g g' x v_x t_x p_vx_tx e t (FTBC _env b) = FTBC (concatF g g') b
lem_subst_ftyp g g' x v_x t_x p_vx_tx e t (FTIC _env n) = FTIC (concatF g g') n
lem_subst_ftyp g g' x v_x t_x p_vx_tx e t p_e_t@(FTVar1 _env z _t)
  = lem_subst_ftyp_ftvar g g' x v_x t_x p_vx_tx e t p_e_t
lem_subst_ftyp g g' x v_x t_x p_vx_tx e t p_e_t@(FTVar2 _env z _t p_z_t w t_w)
  = lem_subst_ftyp_ftvar g g' x v_x t_x p_vx_tx e t p_e_t
lem_subst_ftyp g g' x v_x t_x p_vx_tx e t (FTPrm _env c) = FTPrm (concatF g g') c
lem_subst_ftyp g g' x v_x t_x p_vx_tx e t (FTAbs env_ z t_z e' t' y_ p_yenv_e'_t')
  = FTAbs (concatF g g') z t_z (subFV x v_x e') t' y p_yg'g_e'vx_t'
      where
        y              = y_ ? lem_in_env_concatF g g' y_
                            ? lem_in_env_concatF (FCons x t_x g) g' y_
                            ? lem_fv_bound_in_fenv g v_x t_x p_vx_tx y_
        p_yg'g_e'vx_t' = lem_subst_ftyp g (FCons y t_z g') x v_x t_x p_vx_tx 
                                        (unbind z y e') t' p_yenv_e'_t' 
                                        ? lem_commute_subFV_subBV1 z (FV y) x 
                                            (v_x ? lem_freeBV_emptyB g v_x t_x p_vx_tx) e'
lem_subst_ftyp g g' x v_x t_x p_vx_tx e t (FTApp env_ e' t_z t' p_env_e'_tzt' e_z p_env_ez_tz)
  = FTApp (concatF g g') (subFV x v_x e') t_z t' p_g'g_e'vx_tzt' (subFV x v_x e_z) p_g'g_ezvx_tz
      where
        p_g'g_e'vx_tzt' = lem_subst_ftyp g g' x v_x t_x p_vx_tx e' (FTFunc t_z t') p_env_e'_tzt'
        p_g'g_ezvx_tz   = lem_subst_ftyp g g' x v_x t_x p_vx_tx e_z t_z p_env_ez_tz
