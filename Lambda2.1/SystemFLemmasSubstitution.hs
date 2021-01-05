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
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFWellFormedness
import SystemFLemmasWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasFTyping2

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
      -> t_x:FType -> ProofOf(HasFType g v_x t_x) 
      -> ProofOf(WFFE (concatF (FCons x t_x g) g')) -> e:Expr -> t:FType
      -> {p_e_t:HasFType | propOf p_e_t == HasFType (concatF (FCons x t_x g) g') e t && isFTVar p_e_t}
      -> ProofOf(HasFType (concatF g g') (subFV x v_x e) t) / [ftypSize p_e_t, 0] @-}
lem_subst_ftyp_ftvar :: FEnv -> FEnv -> Vname -> Expr -> FType -> HasFType -> WFFE
        -> Expr -> FType -> HasFType -> HasFType
lem_subst_ftyp_ftvar g g' x v_x t_x p_vx_tx p_env_wf e t (FTVar1 _env z _t)
  = case g' of
      (FEmpty)         -> p_vx_tx   
      (FCons _z _ g'') -> FTVar1 (concatF g g'') (z ? lem_in_env_concatF (FCons x t_x g) g'' z
                                                    ? lem_in_env_concatF g g'' z) t
lem_subst_ftyp_ftvar g g' x v_x t_x p_vx_tx p_env_wf e t (FTVar2 _env z _t p_z_t w t_w)
  = case g' of
      (FEmpty)           -> case ( x == z ) of
        (True)  -> impossible "it is"
        (False) -> p_z_t 
      (FCons _w _tw g'') -> case ( x == z ) of
        (True)  -> lem_weaken_ftyp (concatF g g'') FEmpty p_gg''_wf v_x t p_gg''_vx_tx w t_w 
          where
            (WFFBind _env' p_env'_wf _ _ _ _) = p_env_wf
            p_gg''_wf = lem_strengthen_wffe g x t_x g'' p_env'_wf
            p_gg''_vx_tx = lem_subst_ftyp g g'' x v_x t_x p_vx_tx p_env'_wf e t p_z_t
        (False) -> FTVar2 (concatF g g'') (z ? lem_in_env_concatF (FCons x t_x g) g'' z
                                             ? lem_in_env_concatF g g'' z)
                          t p_z_tvx (w ? lem_fv_bound_in_fenv g v_x t_x p_vx_tx w
                                       ? lem_in_env_concatF (FCons x t_x g) g'' w   
                                       ? lem_in_env_concatF g g'' w) t_w
          where
            (WFFBind _gg'' p_gg''_wf _ _ _ _) = p_env_wf
            p_z_tvx = lem_subst_ftyp g g'' x v_x t_x p_vx_tx p_gg''_wf e t p_z_t
lem_subst_ftyp_ftvar g g' x v_x t_x p_vx_tx p_env_wf e t (FTVar3 _env z _t p_z_t a_ k_a)
  = case g' of             -- g'' = Empty so x = w and p_z_t :: HasFType(g (FV z) t)
      (FEmpty)            -> impossible "a != x" 
      (FConsT _ _ka g'')  -> case (x == z) of
        (True)  -> lem_weaken_tv_ftyp (concatF g g'') FEmpty p_gg''_wf v_x t p_gg''_vx_tx a k_a
          where
            (WFFBindT _env' p_env'_wf _ _) = p_env_wf
            p_gg''_wf = lem_strengthen_wffe g x t_x g'' p_env'_wf
            a = a_ ? lem_in_env_concatF g g'' a_
                   ? lem_in_env_concatF (FCons x t_x g) g'' a_
                   ? lem_fv_bound_in_fenv g v_x t_x p_vx_tx a_
            p_gg''_vx_tx = lem_subst_ftyp g g'' x v_x t_x p_vx_tx p_env'_wf e t p_z_t
        (False) -> FTVar3 (concatF g g'') (z ? lem_in_env_concatF g g'' z
                                             ? lem_in_env_concatF (FCons x t_x g) g'' z) 
                          t p_z_tvx a k_a
          where
            (WFFBindT _gg'' p_gg''_wf _ _) = p_env_wf
            a = a_ ? lem_in_env_concatF g g'' a_
                   ? lem_in_env_concatF (FCons x t_x g) g'' a_
                   ? lem_fv_bound_in_fenv g v_x t_x p_vx_tx a_
            p_z_tvx = lem_subst_ftyp g g'' x v_x t_x p_vx_tx p_gg''_wf e t p_z_t

{-@ lem_subst_ftyp :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> { x:Vname | (not (in_envF x g)) && not (in_envF x g') } -> v_x:Value
        -> t_x:FType -> ProofOf(HasFType g v_x t_x) 
        -> ProofOf(WFFE (concatF (FCons x t_x g) g')) -> e:Expr -> t:FType
        -> { p_e_t:HasFType | propOf p_e_t == HasFType (concatF (FCons x t_x g) g') e t }
        -> ProofOf(HasFType (concatF g g') (subFV x v_x e) t) / [ftypSize p_e_t, 1] @-}
lem_subst_ftyp :: FEnv -> FEnv -> Vname -> Expr -> FType -> HasFType -> WFFE
        -> Expr -> FType -> HasFType -> HasFType
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t (FTBC _env b) = FTBC (concatF g g') b
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t (FTIC _env n) = FTIC (concatF g g') n
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t p_e_t@(FTVar1 _env z _t)
  = lem_subst_ftyp_ftvar g g' x v_x t_x p_vx_tx p_env_wf e t p_e_t
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t p_e_t@(FTVar2 _env z _t p_z_t w t_w)
  = lem_subst_ftyp_ftvar g g' x v_x t_x p_vx_tx p_env_wf e t p_e_t
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t p_e_t@(FTVar3 _env z _t p_z_t a k)
  = lem_subst_ftyp_ftvar g g' x v_x t_x p_vx_tx p_env_wf e t p_e_t
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t (FTPrm _env c) = FTPrm (concatF g g') c
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t (FTAbs env_ z t_z k_z p_env_tz e' t' y_ p_yenv_e'_t')
  = FTAbs (concatF g g') z t_z k_z p_g'g_tz (subFV x v_x e') t' y p_yg'g_e'vx_t'
      where
        p_g'g_tz       = lem_strengthen_wfft g x t_x g' t_z k_z p_env_tz 
        y              = y_ ? lem_in_env_concatF g g' y_
                            ? lem_in_env_concatF (FCons x t_x g) g' y_
                            ? lem_fv_bound_in_fenv g v_x t_x p_vx_tx y_
        p_yenv_wf      = WFFBind (concatF (FCons x t_x g) g') p_env_wf y t_z k_z p_env_tz
        p_yg'g_e'vx_t' = lem_subst_ftyp g (FCons y t_z g') x v_x t_x p_vx_tx p_yenv_wf
                                        (unbind z y e') t' p_yenv_e'_t' 
                                        ? lem_commute_subFV_subBV1 z (FV y) x 
                                            (v_x ? lem_freeBV_emptyB g v_x t_x p_vx_tx) e'
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t (FTApp env_ e' t_z t' p_env_e'_tzt' e_z p_env_ez_tz)
  = FTApp (concatF g g') (subFV x v_x e') t_z t' p_g'g_e'vx_tzt' (subFV x v_x e_z) p_g'g_ezvx_tz
      where
        p_g'g_e'vx_tzt' = lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e' (FTFunc t_z t') p_env_e'_tzt'
        p_g'g_ezvx_tz   = lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e_z t_z p_env_ez_tz
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t (FTAbsT env_ a k e' t' a'_ p_a'env_e'_t')
  = FTAbsT (concatF g g') a k (subFV x v_x e') t' a' p_a'g'g_e'_t'
      where
        a'            = a'_ ? lem_in_env_concatF g g' a'_
                            ? lem_in_env_concatF (FCons x t_x g) g' a'_
                            ? lem_fv_bound_in_fenv g v_x t_x p_vx_tx a'_
        p_a'env_wf    = WFFBindT (concatF (FCons x t_x g) g') p_env_wf a' k
        p_a'g'g_e'_t' = lem_subst_ftyp g (FConsT a' k g') x v_x t_x p_vx_tx p_a'env_wf
                            (unbind_tv a a' e') (unbindFT a a' t') p_a'env_e'_t'
                            ? lem_commute_subFV_unbind_tv x (v_x ? lem_freeBV_emptyB g v_x t_x p_vx_tx) 
                                                         a a' e'
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t (FTAppT env_ e' a k t' p_env_e'_at' liqt p_env_er_liqt)
  = FTAppT (concatF g g') (subFV x v_x e') a k t' p_g'g_e'_at' 
           (tsubFV x (v_x ? lem_fv_subset_bindsF g v_x t_x p_vx_tx
                          ? lem_freeBV_emptyB g v_x t_x p_vx_tx)
                     liqt ? lem_erase_tsubFV x v_x liqt
                          ? lem_binds_cons_concatF g g' x t_x) p_g'g_er_liqt
      where
        p_g'g_e'_at'  = lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e' (FTPoly a k t') p_env_e'_at'
        p_g'g_er_liqt = lem_strengthen_wfft g x t_x g' (erase liqt) k p_env_er_liqt
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t (FTLet env_ e_z t_z p_env_ez_tz z e' t_ y_ p_yenv_e'_t)
  = FTLet (concatF g g') (subFV x v_x e_z) t_z p_g'g_ezvx_tz z (subFV x v_x e') t y p_yg'g_e'vx_t
      where
        y              = y_ ? lem_in_env_concatF g g' y_
                            ? lem_in_env_concatF (FCons x t_x g) g' y_
                            ? lem_fv_bound_in_fenv g v_x t_x p_vx_tx y_
        p_env_tz       = lem_ftyping_wfft env_ e_z t_z p_env_ez_tz p_env_wf
        p_yenv_wf      = WFFBind (concatF (FCons x t_x g) g') p_env_wf y t_z Star p_env_tz
        p_g'g_ezvx_tz  = lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e_z t_z p_env_ez_tz
        p_yg'g_e'vx_t  = lem_subst_ftyp g (FCons y t_z g') x v_x t_x p_vx_tx p_yenv_wf
                                        (unbind z y e') t p_yenv_e'_t 
                                        ? lem_commute_subFV_subBV1 z (FV y) x 
                                            (v_x ? lem_freeBV_emptyB g v_x t_x p_vx_tx) e'
lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e t (FTAnn env_ e' t_ liqt p_env_e'_t)
  = FTAnn (concatF g g') (subFV x v_x e') t liqt' p_g'g_e'_t
                         ? lem_binds_cons_concatF g g' x t_x 
      where
        liqt'      = tsubFV x (v_x ? lem_fv_subset_bindsF g v_x t_x p_vx_tx
                                   ? lem_freeBV_emptyB g v_x t_x p_vx_tx) (liqt
                         ? lem_erase_tsubFV x v_x liqt
                         ? lem_binds_cons_concatF g g' x t_x )
        p_g'g_e'_t = lem_subst_ftyp g g' x v_x t_x p_vx_tx p_env_wf e' t p_env_e'_t


{-@ lem_subst_tv_ftyp :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> { a:Vname | (not (in_envF a g)) && not (in_envF a g') } 
        -> { t_a:UserType | Set_sub (free t_a) (vbindsF  g) && Set_sub (freeTV t_a) (tvbindsF g) &&
                            Set_emp (tfreeBV t_a) && Set_emp (tfreeBTV t_a) }   -> k_a:Kind
        -> ProofOf(WFFT g (erase t_a) k_a) -> ProofOf(WFFE (concatF (FConsT a k_a g) g')) 
        -> e:Expr -> t:FType -> {p_e_t:HasFType | propOf p_e_t == HasFType (concatF (FConsT a k_a g) g') e t}
        -> ProofOf(HasFType (concatF g (fesubFV a (erase t_a) g')) 
                            (subFTV a t_a e) (ftsubFV a (erase t_a) t)) / [ftypSize p_e_t, 1] @-}
lem_subst_tv_ftyp :: FEnv -> FEnv -> Vname -> Type -> Kind -> WFFT -> WFFE
        -> Expr -> FType -> HasFType -> HasFType
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta pf_wf_env e t (FTBC _env b) 
  = FTBC (concatF g (fesubFV a (erase t_a) g')) b ? lem_in_fenv_fesub g' a (erase t_a) a
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta pf_wf_env e t (FTIC _env n)
  = FTIC (concatF g (fesubFV a (erase t_a) g')) n ? lem_in_fenv_fesub g' a (erase t_a) a
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta pf_wf_env e t (FTVar1 _env z _t)
  = case g' of
      (FEmpty)         -> impossible "a <> z"
      (FCons _z _ g'') -> FTVar1 (concatF g (fesubFV a (erase t_a) g'')) 
                                 (z ? lem_in_env_concatF (FConsT a k_a g) g'' z
                                    ? lem_in_env_concatF g g'' z) (ftsubFV a (erase t_a) t)
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta pf_wf_env e t (FTVar2 _env z _t p_z_t w t_w)
  = case g' of
      (FEmpty)           -> impossible "a <> w"
      (FCons _w _tw g'') -> case ( a == z ) of
        (True)  -> impossible ("by lemma" ? lem_ftvar_v_in_env (concatF (FConsT a k_a g) g'')
                                                                 z t p_z_t)
        (False) -> FTVar2 (concatF g (fesubFV a (erase t_a) g''))
                          (z ? lem_in_env_concatF (FConsT a k_a g) g'' z
                             ? lem_in_env_concatF g g'' z)
                          (ftsubFV a (erase t_a) t) p_z_tta 
                          (w ? lem_in_env_concatF (FConsT a k_a g) g'' w   
                             ? lem_in_env_concatF g g'' w) (ftsubFV a (erase t_a) t_w)
          where
            (WFFBind _gg'' p_gg''_wf _ _ _ _) = pf_wf_env
            p_z_tta = lem_subst_tv_ftyp g g'' a t_a k_a p_g_ta p_gg''_wf e t p_z_t
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta pf_wf_env e t p_env_z_t@(FTVar3 _env z _t p_z_t a1_ k1)
  = case g' of             -- g'' = Empty so x = w and p_z_t :: HasFType(g (FV z) t)
      (FEmpty)              -> case ( a == z ) of
            (True)  -> impossible ("by lemma" ? lem_ftvar_v_in_env (FConsT a k_a g) z t p_env_z_t)
            (False) -> p_z_t ? lem_ftsubFV_notin a (erase t_a) 
                                                 (t ? lem_ffreeTV_bound_in_fenv g t Star p_g_t a)
          where
            (WFFBindT _ pf_wf_g _ _) = pf_wf_env
            p_g_t = lem_ftyping_wfft g e t p_z_t pf_wf_g
      (FConsT _a1 _k1 g'')  -> case ( a == z ) of
        (True)  -> impossible ("by lemma" ? lem_ftvar_v_in_env (concatF (FConsT a k_a g) g'')                                                                                     z t p_z_t)
        (False) -> FTVar3 (concatF g (fesubFV a (erase t_a) g'')) 
                          (z ? lem_in_env_concatF g g'' z
                             ? lem_in_env_concatF (FConsT a k_a g) g'' z) 
                          (ftsubFV a (erase t_a) t) p_z_tta a1 k1
          where
            (WFFBindT _gg'' p_gg''_wf _ _) = pf_wf_env
            a1 = a1_ ? lem_in_env_concatF g g'' a1_
                     ? lem_in_env_concatF (FConsT a k_a g) g'' a1_
            p_z_tta = lem_subst_tv_ftyp g g'' a t_a k_a p_g_ta p_gg''_wf e t p_z_t
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta pf_wf_env e t (FTPrm _env c) 
  = FTPrm (concatF g (fesubFV a (erase t_a) g')) c 
          ? lem_in_fenv_fesub g' a (erase t_a) a
          ? lem_ftsubFV_notin a  (erase t_a) (erase_ty c)
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta pf_wf_env e t (FTAbs env_ z t_z k_z p_env_tz e' t' y_ p_yenv_e'_t')
  = FTAbs (concatF g (fesubFV a (erase t_a) g')) z (ftsubFV a (erase t_a) t_z) k_z p_g'g_tz 
          (subFTV a t_a e') (ftsubFV a (erase t_a) t') y p_yg'g_e'ta_t'
      where
        p_g'g_tz       = lem_subst_tv_wfft g g' a (erase t_a) k_a p_g_ta t_z k_z p_env_tz 
        y              = y_ ? lem_in_env_concatF g g' y_
                            ? lem_in_env_concatF (FConsT a k_a g) g' y_
        p_yenv_wf      = WFFBind (concatF (FConsT a k_a g) g') pf_wf_env y t_z k_z p_env_tz
        p_yg'g_e'ta_t' = lem_subst_tv_ftyp g (FCons y t_z g') a t_a k_a p_g_ta p_yenv_wf
                                        (unbind z y e') t' p_yenv_e'_t' 
                                        ? lem_commute_subFTV_unbind a t_a z y e'
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e t (FTApp env_ e' t_z t' p_env_e'_tzt' e_z p_env_ez_tz)
  = FTApp (concatF g (fesubFV a (erase t_a) g')) (subFTV a t_a e') (ftsubFV a (erase t_a) t_z) 
          (ftsubFV a (erase t_a) t') p_g'g_e'ta_tzt' (subFTV a t_a e_z) p_g'g_ezta_tz
      where
        p_g'g_e'ta_tzt' = lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e' (FTFunc t_z t') p_env_e'_tzt'
        p_g'g_ezta_tz   = lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e_z t_z p_env_ez_tz
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta pf_wf_env e t p_e_t@(FTAbsT env a' k' e' t' a''_ p_a''env_e'_t')
  = FTAbsT (concatF g (fesubFV a (erase t_a) g')) a' k' (subFTV a t_a e') 
           (ftsubFV a (erase t_a) t') a'' p_a''g'g_e'_t'
      where
        p_env_t        = lem_ftyping_wfft env e t p_e_t pf_wf_env
        a''            = a''_ ? lem_in_env_concatF g g' a''_
                              ? lem_in_env_concatF (FConsT a k_a g) g' a''_
                              ? lem_erase_freeTV t_a
        p_a''env_wf    = WFFBindT (concatF (FConsT a k_a g) g') pf_wf_env a'' k'
        p_a''g'g_e'_t' = lem_subst_tv_ftyp g (FConsT a'' k' g') a t_a k_a p_g_ta p_a''env_wf
                            (unbind_tv a' a'' e') (unbindFT a' a'' t') p_a''env_e'_t'
                            ? lem_commute_subFTV_unbind_tv a t_a a' a'' e'
                            ? lem_commute_ftsubFV_unbindFT a (erase t_a
                                  ? lem_ffreeBV_empty g (erase t_a) k_a p_g_ta) a' a'' t'
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e t (FTAppT env_ e' a' k' t' p_env_e'_a't' liqt p_env_er_liqt)
  = FTAppT (concatF g (fesubFV a (erase t_a) g')) (subFTV a t_a e') a' k' 
           (ftsubFV a (erase t_a) t') p_g'g_e'_a't' 
           (tsubFTV a t_a liqt ? lem_erase_tsubFTV a t_a liqt
                               ? lem_binds_consT_concatF g g' a k_a) p_g'g_er_liqt
      where
        p_g'g_e'_a't' = lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e' (FTPoly a' k' t') p_env_e'_a't'
        p_g'g_er_liqt = lem_subst_tv_wfft g g' a (erase t_a) k_a p_g_ta (erase liqt) k' p_env_er_liqt
                            ? lem_commute_ftsubFV_ftsubBV a (erase t_a 
                                  ? lem_ffreeBV_empty g (erase t_a) k_a p_g_ta) 
                                  a' (erase liqt) t'
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e t (FTLet env_ e_z t_z p_env_ez_tz z e' t_ y_ p_yenv_e'_t)
  = FTLet (concatF g (fesubFV a (erase t_a) g')) (subFTV a t_a e_z) (ftsubFV a (erase t_a) t_z) 
          p_g'g_ezta_tz z (subFTV a t_a e') (ftsubFV a (erase t_a) t) y p_yg'g_e'ta_t
      where
        y              = y_ ? lem_in_env_concatF g g' y_
                            ? lem_in_env_concatF (FConsT a k_a g) g' y_
        p_env_tz       = lem_ftyping_wfft env_ e_z t_z p_env_ez_tz p_env_wf
        p_yenv_wf      = WFFBind (concatF (FConsT a k_a g) g') p_env_wf y t_z Star p_env_tz
        p_g'g_ezta_tz  = lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e_z t_z p_env_ez_tz
        p_yg'g_e'ta_t  = lem_subst_tv_ftyp g (FCons y t_z g') a t_a k_a p_g_ta p_yenv_wf
                                           (unbind z y e') t p_yenv_e'_t 
                                           ? lem_commute_subFTV_unbind a t_a z y e' 
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta pf_wf_env e t (FTAnn env_ e' t_ liqt p_env_e'_t)
  = FTAnn (concatF g (fesubFV a (erase t_a) g')) (subFTV a t_a e') (ftsubFV a (erase t_a) t) 
          liqt' p_g'g_e'_t
      where
        liqt'      = tsubFTV a t_a (liqt ? lem_erase_tsubFTV a t_a liqt
                                         ? lem_binds_consT_concatF g g' a k_a)
        p_g'g_e'_t = lem_subst_tv_ftyp g g' a t_a k_a p_g_ta pf_wf_env e' t p_env_e'_t
