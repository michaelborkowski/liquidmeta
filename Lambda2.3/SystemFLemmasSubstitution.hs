{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SystemFLemmasSubstitution where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import LocalClosure
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasWellFormedness
import SystemFLemmasWeaken

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
      -> ProofOf(HasFType (concatF g g') (subFV x v_x e) t) 
       / [esize e, fenvsize g', 0] @-}
lem_subst_ftyp_ftvar :: FEnv -> FEnv -> Vname -> Expr -> FType -> HasFType 
        -> Expr -> FType -> HasFType -> HasFType
lem_subst_ftyp_ftvar g g' x v_x t_x p_vx_tx e t (FTVar1 _env z _t)
  = case g' of
      (FEmpty)         -> p_vx_tx   
      (FCons _z _ g'') -> FTVar1 (concatF g g'') (z ? lem_in_env_concatF (FCons x t_x g) g'' z) t
lem_subst_ftyp_ftvar g g' x v_x t_x p_vx_tx e t (FTVar2 _env z _t p_z_t w t_w)
  = case g' of
      (FEmpty)           -> case ( x == z ) of
        (True)  -> impossible "it is"
        (False) -> p_z_t 
      (FCons _w _tw g'') -> case ( x == z ) of
        (True)  -> lem_weaken_ftyp (concatF g g'') FEmpty v_x t p_gg''_vx_tx w t_w 
          where
            p_gg''_vx_tx = lem_subst_ftyp g g'' x v_x t_x p_vx_tx e t p_z_t
        (False) -> FTVar2 (concatF g g'') (z ? lem_in_env_concatF (FCons x t_x g) g'' z)
                          t p_z_tvx (w ? lem_in_env_concatF g g'' w) t_w
          where
            p_z_tvx = lem_subst_ftyp g g'' x v_x t_x p_vx_tx e t p_z_t
lem_subst_ftyp_ftvar g g' x v_x t_x p_vx_tx e t (FTVar3 _env z _t p_z_t a_ k_a)
  = case g' of             -- g'' = Empty so x = w and p_z_t :: HasFType(g (FV z) t)
      (FEmpty)            -> impossible "a != x" 
      (FConsT _ _ka g'')  -> case (x == z) of
        (True)  -> lem_weaken_tv_ftyp (concatF g g'') FEmpty v_x t p_gg''_vx_tx a k_a
          where
            a = a_ ? lem_in_env_concatF g g'' a_
            p_gg''_vx_tx = lem_subst_ftyp g g'' x v_x t_x p_vx_tx e t p_z_t
        (False) -> FTVar3 (concatF g g'') (z ? lem_in_env_concatF (FCons x t_x g) g'' z) 
                          t p_z_tvx a k_a
          where
            a = a_ ? lem_in_env_concatF g g'' a_
            p_z_tvx = lem_subst_ftyp g g'' x v_x t_x p_vx_tx e t p_z_t

{-@ lem_subst_ftyp :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> { x:Vname | (not (in_envF x g)) && not (in_envF x g') } -> v_x:Value
        -> t_x:FType -> ProofOf(HasFType g v_x t_x) -> e:Expr -> t:FType
        -> { p_e_t:HasFType | propOf p_e_t == HasFType (concatF (FCons x t_x g) g') e t }
        -> ProofOf(HasFType (concatF g g') (subFV x v_x e) t) 
         / [esize e, fenvsize g', 1] @-}
lem_subst_ftyp :: FEnv -> FEnv -> Vname -> Expr -> FType -> HasFType 
        -> Expr -> FType -> HasFType -> HasFType
lem_subst_ftyp g g' x v_x t_x p_vx_tx e t (FTBC _env b) = FTBC (concatF g g') b
lem_subst_ftyp g g' x v_x t_x p_vx_tx e t (FTIC _env n) = FTIC (concatF g g') n
lem_subst_ftyp g g' x v_x t_x p_vx_tx e t p_e_t@(FTVar1 _env z _t)
  = lem_subst_ftyp_ftvar g g' x v_x t_x p_vx_tx e t p_e_t
lem_subst_ftyp g g' x v_x t_x p_vx_tx e t p_e_t@(FTVar2 _env z _t p_z_t w t_w)
  = lem_subst_ftyp_ftvar g g' x v_x t_x p_vx_tx e t p_e_t
lem_subst_ftyp g g' x v_x t_x p_vx_tx e t p_e_t@(FTVar3 _env z _t p_z_t a k)
  = lem_subst_ftyp_ftvar g g' x v_x t_x p_vx_tx e t p_e_t
lem_subst_ftyp g g' x v_x t_x p_vx_tx e t (FTPrm _env c) = FTPrm (concatF g g') c
lem_subst_ftyp g g' x v_x t_x p_vx_tx e t (FTAbs env_ t_z k_z p_env_tz e' t' nms mk_p_yenv_e'_t')
  = FTAbs (concatF g g') t_z k_z p_g'g_tz (subFV x v_x e') t' nms' mk_p_yg'g_e'vx_t'
      where
        p_g'g_tz       = lem_strengthen_wfft g x t_x g' t_z k_z p_env_tz 
        {-@ mk_p_yg'g_e'vx_t' :: { y:Vname | NotElem y nms' }
              -> ProofOf(HasFType (FCons y t_z (concatF g g')) (unbind y (subFV x v_x e')) t') @-}
        mk_p_yg'g_e'vx_t' y = lem_subst_ftyp g (FCons y t_z g') x v_x t_x p_vx_tx 
                                             (unbind y e') t' (mk_p_yenv_e'_t' y)
                                             ? lem_commute_subFV_unbind x 
                                                 (v_x ? lem_ftyp_islc g v_x t_x p_vx_tx) y e'
        nms'                = x:(unionFEnv nms (concatF g g'))
lem_subst_ftyp g g' x v_x t_x p_vx_tx e t (FTApp env_ e' t_z t' p_env_e'_tzt' e_z p_env_ez_tz)
  = FTApp (concatF g g') (subFV x v_x e') t_z t' p_g'g_e'vx_tzt' (subFV x v_x e_z) p_g'g_ezvx_tz
      where
        p_g'g_e'vx_tzt' = lem_subst_ftyp g g' x v_x t_x p_vx_tx e' (FTFunc t_z t') p_env_e'_tzt'
        p_g'g_ezvx_tz   = lem_subst_ftyp g g' x v_x t_x p_vx_tx e_z t_z p_env_ez_tz
lem_subst_ftyp g g' x v_x t_x p_vx_tx e t (FTAbsT env_ k e' t' nms mk_p_a'env_e'_t')
  = FTAbsT (concatF g g') k (subFV x v_x e') t' nms' mk_p_a'g'g_e'_t'
      where
        {-@ mk_p_a'g'g_e'_t' :: { a':Vname | NotElem a' nms' }
              -> ProofOf(HasFType (FConsT a' k (concatF g g')) (unbind_tv a' (subFV x v_x e')) 
                                                               (unbindFT a' t') )@-}
        mk_p_a'g'g_e'_t' a' = lem_subst_ftyp g (FConsT a' k g') x v_x t_x p_vx_tx 
                                             (unbind_tv a' e') (unbindFT a' t') (mk_p_a'env_e'_t' a')
                                             ? lem_commute_subFV_unbind_tv x 
                                                 (v_x ? lem_ftyp_islc g v_x t_x p_vx_tx) a' e'
        nms'                = x:(unionFEnv nms (concatF g g'))
lem_subst_ftyp g g' x v_x t_x p_vx_tx e t (FTAppT env_ e' k t' p_env_e'_at' liqt p_env_er_liqt)
  = FTAppT (concatF g g') (subFV x v_x e') k t' p_g'g_e'_at' 
           (tsubFV x (v_x ? lem_fv_subset_bindsF g v_x t_x p_vx_tx)
                     (liqt ? lem_erase_tsubFV x v_x liqt
                           ? lem_binds_cons_concatF g g' x t_x
                           ? lem_islct_at_tsubFV 0 0 x (v_x ? lem_ftyp_islc g v_x t_x p_vx_tx) liqt))
           p_g'g_er_liqt 
      where
        p_g'g_e'_at'  = lem_subst_ftyp g g' x v_x t_x p_vx_tx e' (FTPoly k t') p_env_e'_at'
        p_g'g_er_liqt = lem_strengthen_wfft g x t_x g' (erase liqt) k p_env_er_liqt
lem_subst_ftyp g g' x v_x t_x p_vx_tx e t (FTLet env_ e_z t_z p_env_ez_tz e' t_ nms mk_p_yenv_e'_t)
  = FTLet (concatF g g') (subFV x v_x e_z) t_z p_g'g_ezvx_tz (subFV x v_x e') t nms' mk_p_yg'g_e'vx_t
      where
        p_g'g_ezvx_tz   = lem_subst_ftyp g g' x v_x t_x p_vx_tx e_z t_z p_env_ez_tz
        {-@ mk_p_yg'g_e'vx_t :: { y:Vname | NotElem y nms' }
                -> ProofOf(HasFType (FCons y t_z (concatF g g')) (unbind y (subFV x v_x e')) t) @-}
        mk_p_yg'g_e'vx_t y = lem_subst_ftyp g (FCons y t_z g') x v_x t_x p_vx_tx
                                            (unbind y e') t (mk_p_yenv_e'_t y)
                                            ? lem_commute_subFV_unbind x 
                                                (v_x ? lem_ftyp_islc g v_x t_x p_vx_tx) y e'
        nms'            = x:(unionFEnv nms (concatF g g'))
lem_subst_ftyp g g' x v_x t_x p_vx_tx e t (FTAnn env_ e' t_ liqt p_env_e'_t)
  = FTAnn (concatF g g') (subFV x v_x e') t liqt' p_g'g_e'_t
      where
        liqt'      = tsubFV x (v_x ? lem_fv_subset_bindsF g v_x t_x p_vx_tx) 
                            (liqt ? lem_erase_tsubFV x v_x liqt
                                  ? lem_binds_cons_concatF g g' x t_x 
                                  ? lem_islct_at_tsubFV 0 0 x 
                                        (v_x ? lem_ftyp_islc g v_x t_x p_vx_tx) liqt)
        p_g'g_e'_t = lem_subst_ftyp g g' x v_x t_x p_vx_tx e' t p_env_e'_t
 
{-@ lem_subst_tv_ftyp :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> { a:Vname | (not (in_envF a g)) && not (in_envF a g') } 
        -> { t_a:UserType | Set_sub (free t_a) (vbindsF  g) && Set_sub (freeTV t_a) (tvbindsF g) &&
                            isLCT t_a }   -> k_a:Kind
        -> ProofOf(WFFT g (erase t_a) k_a) -> ProofOf(WFFE (concatF (FConsT a k_a g) g')) 
        -> e:Expr -> t:FType 
        -> {p_e_t:HasFType | propOf p_e_t == HasFType (concatF (FConsT a k_a g) g') e t}
        -> ProofOf(HasFType (concatF g (fesubFV a (erase t_a) g')) 
                            (subFTV a t_a e) (ftsubFV a (erase t_a) t)) / [esize e, fenvsize g'] @-}
lem_subst_tv_ftyp :: FEnv -> FEnv -> Vname -> Type -> Kind -> WFFT -> WFFE
        -> Expr -> FType -> HasFType -> HasFType
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e t (FTBC _env b) 
  = FTBC (concatF g (fesubFV a (erase t_a) g')) b ? lem_in_fenv_fesub g' a (erase t_a) a
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e t (FTIC _env n)
  = FTIC (concatF g (fesubFV a (erase t_a) g')) n ? lem_in_fenv_fesub g' a (erase t_a) a
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e t (FTVar1 _env z _t)
  = case g' of
      (FEmpty)         -> impossible "a <> z"
      (FCons _z _ g'') -> FTVar1 (concatF g (fesubFV a (erase t_a) g'')) 
                                 (z ? lem_in_env_concatF g g'' z) (ftsubFV a (erase t_a) t)
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e t (FTVar2 _env z _t p_z_t w t_w)
  = case g' of
      (FEmpty)           -> impossible "a <> w"
      (FCons _w _tw g'') -> case ( a == z ) of
        (True)  -> impossible ("by lemma" ? lem_fv_subset_bindsF (concatF (FConsT a k_a g) g'')
                                                                 (FV z) t p_z_t)
        (False) -> FTVar2 (concatF g (fesubFV a (erase t_a) g''))
                          (z ? lem_in_env_concatF (FConsT a k_a g) g'' z)
                          (ftsubFV a (erase t_a) t) p_z_tta 
                          (w ? lem_in_env_concatF g g'' w) (ftsubFV a (erase t_a) t_w)
          where
            (WFFBind _g'g p_g'g_wf _ _ _ _) = p_env_wf
            p_z_tta = lem_subst_tv_ftyp g g'' a t_a k_a p_g_ta p_g'g_wf e t p_z_t
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e t p_env_z_t@(FTVar3 _env z _t p_z_t a1_ k1)
  = case g' of             -- g'' = Empty so x = w and p_z_t :: HasFType(g (FV z) t)
      (FEmpty)              -> case ( a == a1_ ) of 
            (True)  -> p_z_t ? lem_ftsubFV_notin a (erase t_a) 
                                                 (t ? lem_ffreeTV_bound_in_fenv g t Star p_g_t a) 
          where
            (WFFBindT _ pf_wf_g _ _) = p_env_wf
            p_g_t = lem_ftyping_wfft g e t p_z_t pf_wf_g
      (FConsT _a1 _k1 g'')  -> case ( a == z ) of
        (True)  -> impossible ("by lemma" ? lem_fv_subset_bindsF (concatF (FConsT a k_a g) g'') (FV z) t p_z_t)
        (False) -> FTVar3 (concatF g (fesubFV a (erase t_a) g'')) 
                          (z ? lem_in_env_concatF (FConsT a k_a g) g'' z) 
                          (ftsubFV a (erase t_a) t) p_z_tta a1 k1
          where
            (WFFBindT _g'g p_g'g_wf _ _) = p_env_wf
            a1 = a1_ ? lem_in_env_concatF g g'' a1_
            p_z_tta = lem_subst_tv_ftyp g g'' a t_a k_a p_g_ta p_g'g_wf e t p_z_t
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e t (FTPrm _env c) 
  = FTPrm (concatF g (fesubFV a (erase t_a) g')) c 
          ? lem_ftsubFV_notin a  (erase t_a) (erase_ty c)
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e t (FTAbs env_ t_z k_z p_env_tz e' t' nms mk_p_yenv_e'_t')
  = FTAbs (concatF g (fesubFV a (erase t_a) g')) (ftsubFV a (erase t_a) t_z) k_z p_g'g_tz 
          (subFTV a t_a e') (ftsubFV a (erase t_a) t') nms' mk_p_yg'g_e'ta_t'
      where
        p_g'g_tz            = lem_subst_tv_wfft g g' a (erase t_a) k_a p_g_ta t_z k_z p_env_tz 
        {-@ mk_p_yg'g_e'ta_t' :: { y:Vname | NotElem y nms' }
              -> ProofOf(HasFType (FCons y (ftsubFV a (erase t_a) t_z) (concatF g (fesubFV a (erase t_a) g'))) 
                                  (unbind y (subFTV a t_a e')) (ftsubFV a (erase t_a) t')) @-}
        mk_p_yg'g_e'ta_t' y = lem_subst_tv_ftyp g (FCons y t_z g') a t_a k_a p_g_ta p_yenv_wf
                                        (unbind y e') t' (mk_p_yenv_e'_t' y)
                                        ? lem_commute_subFTV_unbind a t_a y e'
          where
            p_yenv_wf       = WFFBind (concatF (FConsT a k_a g) g') p_env_wf y t_z k_z p_env_tz
        nms'                = a:(unionFEnv nms (concatF g g'))
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e t (FTApp env_ e' t_z t' p_env_e'_tzt' e_z p_env_ez_tz)
  = FTApp (concatF g (fesubFV a (erase t_a) g')) (subFTV a t_a e') (ftsubFV a (erase t_a) t_z) 
          (ftsubFV a (erase t_a) t') p_g'g_e'ta_tzt' (subFTV a t_a e_z) p_g'g_ezta_tz
      where
        p_g'g_e'ta_tzt' = lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e' (FTFunc t_z t') p_env_e'_tzt'
        p_g'g_ezta_tz   = lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e_z t_z p_env_ez_tz
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e t p_e_t@(FTAbsT env k' e' t' nms mk_p_a'env_e'_t')
  = FTAbsT (concatF g (fesubFV a (erase t_a) g')) k' (subFTV a t_a e') 
           (ftsubFV a (erase t_a) t') nms' mk_p_a'g'g_e'_t'
      where
        p_env_t        = lem_ftyping_wfft env e t p_e_t p_env_wf
        {-@ mk_p_a'g'g_e'_t' :: { a':Vname | NotElem a' nms' }
              -> ProofOf(HasFType (FConsT a' k' (concatF g (fesubFV a (erase t_a) g')))
                             (unbind_tv a' (subFTV a t_a e')) (unbindFT a' (ftsubFV a (erase t_a) t'))) @-}
        mk_p_a'g'g_e'_t' a' = lem_subst_tv_ftyp g (FConsT a' k' g') a t_a k_a p_g_ta p_a'env_wf
                                  (unbind_tv a' e') (unbindFT a' t') (mk_p_a'env_e'_t' a')
                                  ? lem_commute_subFTV_unbind_tv a t_a a' e'
                                  ? lem_commute_ftsubFV_unbindFT a (erase t_a 
                                        ? lem_wfft_islcft g (erase t_a) k_a p_g_ta) a' t'
          where
            p_a'env_wf     = WFFBindT (concatF (FConsT a k_a g) g') p_env_wf a' k'
        nms'                = a:(unionFEnv nms (concatF g g'))
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e t (FTAppT env_ e' k' t' p_env_e'_a't' liqt p_env_er_liqt)
  = FTAppT (concatF g (fesubFV a (erase t_a) g')) (subFTV a t_a e') k' 
           (ftsubFV a (erase t_a) t') p_g'g_e'_a't' 
           (tsubFTV a t_a liqt ? lem_erase_tsubFTV a t_a liqt
                               ? lem_binds_consT_concatF g g' a k_a
                               ? lem_islct_at_tsubFTV 0 0 a t_a liqt) p_g'g_er_liqt
      where
        p_g'g_e'_a't' = lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e' (FTPoly k' t') p_env_e'_a't'
        p_g'g_er_liqt = lem_subst_tv_wfft g g' a (erase t_a) k_a p_g_ta (erase liqt) k' p_env_er_liqt
                            ? lem_commute_ftsubFV_ftsubBV a (erase t_a
                                  ? lem_wfft_islcft g (erase t_a) k_a p_g_ta) (erase liqt) t'
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e t (FTLet env_ e_z t_z p_env_ez_tz e' t_ nms mk_p_yenv_e'_t)
  = FTLet (concatF g (fesubFV a (erase t_a) g')) (subFTV a t_a e_z) (ftsubFV a (erase t_a) t_z) 
          p_g'g_ezta_tz (subFTV a t_a e') (ftsubFV a (erase t_a) t) nms' mk_p_yg'g_e'ta_t
      where
        p_env_tz       = lem_ftyping_wfft env_ e_z t_z p_env_ez_tz p_env_wf
        p_g'g_ezta_tz  = lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e_z t_z p_env_ez_tz
        {-@ mk_p_yg'g_e'ta_t :: { y:Vname | NotElem y nms' }
              -> ProofOf(HasFType (FCons y (ftsubFV a (erase t_a) t_z) (concatF g (fesubFV a (erase t_a) g')))
                                  (unbind y (subFTV a t_a e')) (ftsubFV a (erase t_a) t)) @-}
        mk_p_yg'g_e'ta_t y = lem_subst_tv_ftyp g (FCons y t_z g') a t_a k_a p_g_ta p_yenv_wf
                                               (unbind y e') t (mk_p_yenv_e'_t y)
                                               ? lem_commute_subFTV_unbind a t_a y e' 
          where
            p_yenv_wf      = WFFBind (concatF (FConsT a k_a g) g') p_env_wf y t_z Star p_env_tz
        nms'               = a:(unionFEnv nms (concatF g g'))
lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e t (FTAnn env_ e' t_ liqt p_env_e'_t)
  = FTAnn (concatF g (fesubFV a (erase t_a) g')) (subFTV a t_a e') (ftsubFV a (erase t_a) t) 
          liqt' p_g'g_e'_t
      where
        liqt'      = tsubFTV a t_a (liqt ? lem_erase_tsubFTV a t_a liqt
                                         ? lem_binds_consT_concatF g g' a k_a
                                         ? lem_islct_at_tsubFTV 0 0 a t_a liqt)
        p_g'g_e'_t = lem_subst_tv_ftyp g g' a t_a k_a p_g_ta p_env_wf e' t p_env_e'_t
