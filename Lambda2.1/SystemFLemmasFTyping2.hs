{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SystemFLemmasFTyping2 where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import PrimitivesWFType
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasWellFormedness
import SystemFLemmasFTyping

{-@ reflect foo23 @-}
foo23 x = Just x
foo23 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development for the Underlying STLC :: Technical LEMMAS
------------------------------------------------------------------------------

{-@ lem_weaken_ftyp :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> ProofOf(WFFE (concatF g g')) -> e:Expr -> t:FType 
        -> { p_e_t:HasFType | propOf p_e_t == HasFType (concatF g g') e t }
        -> { x:Vname | not (in_envF x g) && not (in_envF x g') } -> t_x:FType
        -> { pf:HasFType | propOf pf == (HasFType (concatF (FCons x t_x g) g') e t) }
           / [ftypSize p_e_t] @-}
lem_weaken_ftyp :: FEnv -> FEnv -> WFFE -> Expr -> FType 
                -> HasFType ->  Vname -> FType -> HasFType
lem_weaken_ftyp g g' pf_wf_env e t (FTBC _env b) x t_x  
    = FTBC  (concatF (FCons x t_x g) g') b
lem_weaken_ftyp g g' pf_wf_env e t (FTIC _env n) x t_x  
    = FTIC  (concatF (FCons x t_x g) g') n
lem_weaken_ftyp g g' pf_wf_env e t p_y_ty@(FTVar1 env y t_y) x t_x 
    = case g' of 
        (FEmpty)           -> FTVar2 (FCons y t_y env) y t_y p_y_ty x t_x
        (FCons _y _ty g'') -> FTVar1 (concatF (FCons x t_x g) g'') y t_y 
                                    -- (g; g' == _g, z:t_z) |- y : t_y
lem_weaken_ftyp g g' pf_wf_env e t p_y_ty@(FTVar2 gg y t_y p_gg'_y_ty z t_z) x t_x
    = case g' of
        (FEmpty)           -> FTVar2 (FCons z t_z gg) y t_y p_y_ty x t_x
        (FCons _z _tz g'') -> FTVar2 (concatF (FCons x t_x g) g'') 
                                  (y `withProof` lem_in_env_concatF g g'' y
                                     `withProof` lem_in_env_concatF (FCons x t_x g) g'' y) t_y
                                     (lem_weaken_ftyp g g'' pf_wf_env' e t p_gg'_y_ty x t_x)
                                     z t_z
          where
            (WFFBind _ pf_wf_env' _ _ _ _) = pf_wf_env
lem_weaken_ftyp g g' pf_wf_env e t p_y_ty@(FTVar3 env y t_y p_gg'_y_ty a k) x t_x  
    = case g' of
        (FEmpty)           -> FTVar2 (FConsT a k env) y t_y p_y_ty x t_x
        (FConsT _a _k g'') -> FTVar3 (concatF (FCons x t_x g) g'') 
                                  (y `withProof` lem_in_env_concatF g g'' y
                                     `withProof` lem_in_env_concatF (FCons x t_x g) g'' y) t_y
                                     (lem_weaken_ftyp g g'' pf_wf_env' e t p_gg'_y_ty x t_x)
                                     a k
          where
            (WFFBindT _ pf_wf_env' _ _) = pf_wf_env
lem_weaken_ftyp g g' pf_wf_env e t (FTPrm _env c)  x t_x 
    = FTPrm (concatF (FCons x t_x g) g') c
lem_weaken_ftyp g g' pf_wf_env e t p_e_t@(FTAbs env y t_y k_y p_env_ty e' t' y' p_y'_e'_t') x t_x 
    = FTAbs (concatF (FCons x t_x g) g') y t_y k_y p_env'_ty e' t' y'' p_y''x_e'_t'
        where
            p_env'_ty    = lem_weaken_wfft g g' t_y k_y p_env_ty x t_x
            y''_         = fresh_varF (concatF (FCons x t_x g) g')
            y''          = y''_ ? lem_in_env_concatF g g' y''_
                                ? lem_in_env_concatF (FCons x t_x g) g' y''_
                                ? lem_fv_bound_in_fenv (concatF g g') e t p_e_t y''_
            pf_y'env_wf  = WFFBind (concatF g g') pf_wf_env y'  t_y k_y p_env_ty
            pf_y''env_wf = WFFBind (concatF g g') pf_wf_env y'' t_y k_y p_env_ty
            p_y''_e'_t'  = lem_change_var_ftyp (concatF g g') y' t_y FEmpty pf_y'env_wf
                                (unbind y y' e') t' p_y'_e'_t' y''
                                ? lem_subFV_unbind y y' (FV y'') e'
            p_y''x_e'_t' = lem_weaken_ftyp g (FCons y'' t_y g') pf_y''env_wf 
                                (unbind y y'' e') t' p_y''_e'_t' x t_x
lem_weaken_ftyp g g' pf_wf_env e t (FTApp env e1 s s' p_e1_ss' e2 p_e2_s)  x t_x  
    = FTApp (concatF (FCons x t_x g) g') e1 s s' p_env'_e1_ss' e2 p_env'_e2_s
        where
          p_env'_e1_ss' = lem_weaken_ftyp g g' pf_wf_env e1 (FTFunc s s') p_e1_ss' x t_x
          p_env'_e2_s   = lem_weaken_ftyp g g' pf_wf_env e2 s             p_e2_s   x t_x
lem_weaken_ftyp g g' pf_wf_env e t p_e_t@(FTAbsT env a k e' t' a' p_a'_e'_t') x t_x  
    = FTAbsT (concatF (FCons x t_x g) g') a k e' t' a'' p_a''x_e'_t'
        where
          p_env_t      = lem_ftyping_wfft env e t p_e_t pf_wf_env
          a''_         = fresh_varF (concatF (FCons x t_x g) g')
          a''          = a''_ ? lem_in_env_concatF g g' a''_
                              ? lem_in_env_concatF (FCons x t_x g) g' a''_
                              ? lem_fv_bound_in_fenv env e t p_e_t a''_
                              ? lem_ffreeTV_bound_in_fenv env t Star p_env_t a''_
          p_a'env_wf   = WFFBindT env pf_wf_env a'  k 
          p_a''env_wf  = WFFBindT env pf_wf_env a'' k 
          p_a''_e'_t'  = lem_change_tvar_ftyp (concatF g g') a' k FEmpty p_a'env_wf
                                    (unbind_tv a a' e') (unbindFT a a' t') p_a'_e'_t' a''
                           ? lem_chgFTV_unbind_tv a a' a''
                                (e' ? lem_fv_bound_in_fenv (concatF g g') e t p_e_t a')
                           ? lem_ftsubFV_unbindFT a a' (FTBasic (FTV a''))  t' 
          p_a''x_e'_t' = lem_weaken_ftyp g (FConsT a'' k g') p_a''env_wf 
                                    (unbind_tv a a'' e') (unbindFT a a'' t') p_a''_e'_t' x t_x
lem_weaken_ftyp g g' pf_wf_env e t (FTAppT env e' a k t' p_e'_at' rt pf_env_rt) x t_x  
    = FTAppT (concatF (FCons x t_x g) g') e' a k t' p_y_e'_at'
             (rt ? lem_binds_cons_concatF g g' x t_x) pf_env'_rt
        where      
          p_y_e'_at' = lem_weaken_ftyp g g' pf_wf_env e' (FTPoly a k t') p_e'_at' x t_x
          pf_env'_rt = lem_weaken_wfft g g' (erase rt) k pf_env_rt x t_x
lem_weaken_ftyp g g' pf_wf_env e t p_e_t@(FTLet env e_y t_y p_ey_ty y e' t' y' p_y'_e'_t') x t_x
    = FTLet (concatF (FCons x t_x g) g') e_y t_y p_env'_ey_ty y e' t' y'' p_y''x_e'_t'
        where
            p_env_ty     = lem_ftyping_wfft env e_y t_y p_ey_ty pf_wf_env
            y''_         = fresh_varF (concatF (FCons x t_x g) g')
            y''          = y''_ ? lem_in_env_concatF g g' y''_
                                ? lem_in_env_concatF (FCons x t_x g) g' y''_
                                ? lem_fv_bound_in_fenv (concatF g g') e t p_e_t y''_
            p_y'env_wf   = WFFBind env pf_wf_env y'  t_y Star p_env_ty
            p_y''env_wf  = WFFBind env pf_wf_env y'' t_y Star p_env_ty
            p_env'_ey_ty = lem_weaken_ftyp g g' pf_wf_env e_y t_y p_ey_ty x t_x
            p_y''_e'_t'  = lem_change_var_ftyp (concatF g g') y' t_y FEmpty p_y'env_wf 
                                               (unbind y y' e') t' p_y'_e'_t' y'' 
                                               ? lem_subFV_unbind y y' (FV y'') e'
            p_y''x_e'_t' = lem_weaken_ftyp g (FCons y'' t_y g') p_y''env_wf
                                           (unbind y y'' e') t' p_y''_e'_t' x t_x
lem_weaken_ftyp g g' pf_wf_env e t (FTAnn _ e' _t liqt p_e'_t)  x t_x  
    = FTAnn (concatF (FCons x t_x g) g') e' t (liqt ? lem_binds_cons_concatF g g' x t_x)
            (lem_weaken_ftyp g g' pf_wf_env e' t p_e'_t x t_x)

{-@ lem_weaken_tv_ftyp :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> ProofOf(WFFE (concatF g g')) -> e:Expr -> t:FType 
        -> { p_e_t:HasFType | propOf p_e_t == HasFType (concatF g g') e t }
        -> { a:Vname | not (in_envF a g) && not (in_envF a g') } -> k:Kind
        -> { pf:HasFType | propOf pf == (HasFType (concatF (FConsT a k g) g') e t) }
           / [ftypSize p_e_t] @-}
lem_weaken_tv_ftyp :: FEnv -> FEnv -> WFFE -> Expr -> FType 
                -> HasFType -> Vname -> Kind -> HasFType
lem_weaken_tv_ftyp g g' pf_wf_env e t (FTBC _env b) a k 
    = FTBC  (concatF (FConsT a k g) g') b
lem_weaken_tv_ftyp g g' pf_wf_env e t (FTIC _env n) a k 
    = FTIC  (concatF (FConsT a k g) g') n
lem_weaken_tv_ftyp g g' pf_wf_env e t p_x_tx@(FTVar1 env x t_x) a k 
    = case g' of 
        (FEmpty)           -> FTVar3 (FCons x t_x env) x t_x p_x_tx a k
        (FCons  _z _ g'')  -> FTVar1 (concatF (FConsT a k g) g'') x t_x 
lem_weaken_tv_ftyp g g' pf_wf_env e t p_y_ty@(FTVar2 gg y t_y p_gg'_y_ty z t_z) a k 
    = case g' of
        (FEmpty)           -> FTVar3 (FCons z t_z gg) y t_y p_y_ty a k
        (FCons _z _tz g'') -> FTVar2 (concatF (FConsT a k g) g'') 
                                  (y `withProof` lem_in_env_concatF g g'' y
                                     `withProof` lem_in_env_concatF (FConsT a k g) g'' y) t_y
                                     (lem_weaken_tv_ftyp g g'' pf_wf_env' e t p_gg'_y_ty a k)
                                     z t_z
          where
            (WFFBind _ pf_wf_env' _ _ _ _) = pf_wf_env
lem_weaken_tv_ftyp g g' pf_wf_env e t p_y_ty@(FTVar3 env y t_y p_gg'_y_ty a1 k1) a k 
    = case g' of
        (FEmpty)           -> FTVar3 (FConsT a1 k1 env) y t_y p_y_ty a k
        (FConsT _a _k g'') -> FTVar3 (concatF (FConsT a k g) g'') 
                                  (y `withProof` lem_in_env_concatF g g'' y
                                     `withProof` lem_in_env_concatF (FConsT a k g) g'' y) t_y
                                     (lem_weaken_tv_ftyp g g'' pf_wf_env' e t p_gg'_y_ty a k)
                                     a1 k1
          where
            (WFFBindT _ pf_wf_env' _ _) = pf_wf_env
lem_weaken_tv_ftyp g g' pf_wf_env e t (FTPrm _env c) a k 
    = FTPrm (concatF (FConsT a k g) g') c
lem_weaken_tv_ftyp g g' pf_wf_env e t p_e_t@(FTAbs env y t_y k_y p_env_ty e' t' y' p_y'_e'_t') a k  
    = FTAbs (concatF (FConsT a k g) g') y t_y k_y p_env'_ty e' t' y'' p_y''a_e'_t'
        where
            p_env'_ty    = lem_weaken_tv_wfft g g' t_y k_y p_env_ty a k
            y''_         = fresh_varF (concatF (FConsT a k g) g')
            y''          = y''_ ? lem_in_env_concatF g g' y''_
                                ? lem_in_env_concatF (FConsT a k g) g' y''_
                                ? lem_fv_bound_in_fenv (concatF g g') e t p_e_t y''_
            pf_y'env_wf  = WFFBind (concatF g g') pf_wf_env y'  t_y k_y p_env_ty
            pf_y''env_wf = WFFBind (concatF g g') pf_wf_env y'' t_y k_y p_env_ty
            p_y''_e'_t'  = lem_change_var_ftyp (concatF g g') y' t_y FEmpty pf_y'env_wf
                                (unbind y y' e') t' p_y'_e'_t' y''
                                ? lem_subFV_unbind y y' (FV y'') e'
            p_y''a_e'_t' = lem_weaken_tv_ftyp g (FCons y'' t_y g') pf_y''env_wf 
                                (unbind y y'' e') t' p_y''_e'_t' a k
lem_weaken_tv_ftyp g g' pf_wf_env e t (FTApp env e1 s s' p_e1_ss' e2 p_e2_s) a k  
    = FTApp (concatF (FConsT a k g) g') e1 s s' p_env'_e1_ss' e2 p_env'_e2_s
        where
          p_env'_e1_ss' = lem_weaken_tv_ftyp g g' pf_wf_env e1 (FTFunc s s') p_e1_ss' a k
          p_env'_e2_s   = lem_weaken_tv_ftyp g g' pf_wf_env e2 s             p_e2_s   a k
lem_weaken_tv_ftyp g g' pf_wf_env e t p_e_t@(FTAbsT env a1 k1 e' t' a1' p_a1'_e'_t') a k  
    = FTAbsT (concatF (FConsT a k g) g') a1 k1 e' t' a1'' p_a1''a_e'_t'
        where
          p_env_t       = lem_ftyping_wfft env e t p_e_t pf_wf_env
          a1''_         = fresh_varF (concatF (FConsT a k g) g')
          a1''          = a1''_ ? lem_in_env_concatF g g' a1''_
                                ? lem_in_env_concatF (FConsT a k g) g' a1''_
                                ? lem_fv_bound_in_fenv env e t p_e_t a1''_
                                ? lem_ffreeTV_bound_in_fenv env t Star p_env_t a1''_
          p_a1'env_wf   = WFFBindT env pf_wf_env a1'  k1 
          p_a1''env_wf  = WFFBindT env pf_wf_env a1'' k1 
          p_a1''_e'_t'  = lem_change_tvar_ftyp (concatF g g') a1' k1 FEmpty p_a1'env_wf
                                     (unbind_tv a1 a1' e') (unbindFT a1 a1' t') p_a1'_e'_t' a1''
                            ? lem_chgFTV_unbind_tv a1 a1' a1''
                                 (e' ? lem_fv_bound_in_fenv (concatF g g') e t p_e_t a1')
                            ? lem_ftsubFV_unbindFT a1 a1' (FTBasic (FTV a1''))  t' 
          p_a1''a_e'_t' = lem_weaken_tv_ftyp g (FConsT a1'' k1 g') p_a1''env_wf 
                                    (unbind_tv a1 a1'' e') (unbindFT a1 a1'' t') p_a1''_e'_t' a k
lem_weaken_tv_ftyp g g' pf_wf_env e t (FTAppT env e' a1 k1 t' p_e'_a1t' rt pf_env_rt) a k 
    = FTAppT (concatF (FConsT a k g) g') e' a1 k1 t' p_a_e'_a1t'
             (rt ? lem_binds_consT_concatF g g' a k) pf_env'_rt
        where      
          p_a_e'_a1t' = lem_weaken_tv_ftyp g g' pf_wf_env e' (FTPoly a1 k1 t') p_e'_a1t' a k
          pf_env'_rt  = lem_weaken_tv_wfft g g' (erase rt) k1 pf_env_rt a k
lem_weaken_tv_ftyp g g' pf_wf_env e t p_e_t@(FTLet env e_y t_y p_ey_ty y e' t' y' p_y'_e'_t') a k 
    = FTLet (concatF (FConsT a k g) g') e_y t_y p_env'_ey_ty y e' t' y'' p_y''a_e'_t'
        where
            p_env_ty     = lem_ftyping_wfft env e_y t_y p_ey_ty pf_wf_env
            y''_         = fresh_varF (concatF (FConsT a k g) g')
            y''          = y''_ ? lem_in_env_concatF g g' y''_
                                ? lem_in_env_concatF (FConsT a k g) g' y''_
                                ? lem_fv_bound_in_fenv (concatF g g') e t p_e_t y''_
            p_y'env_wf   = WFFBind env pf_wf_env y'  t_y Star p_env_ty
            p_y''env_wf  = WFFBind env pf_wf_env y'' t_y Star p_env_ty
            p_env'_ey_ty = lem_weaken_tv_ftyp g g' pf_wf_env e_y t_y p_ey_ty a k
            p_y''_e'_t'  = lem_change_var_ftyp (concatF g g') y' t_y FEmpty p_y'env_wf 
                                               (unbind y y' e') t' p_y'_e'_t' y'' 
                                               ? lem_subFV_unbind y y' (FV y'') e'
            p_y''a_e'_t' = lem_weaken_tv_ftyp g (FCons y'' t_y g') p_y''env_wf
                                           (unbind y y'' e') t' p_y''_e'_t' a k
lem_weaken_tv_ftyp g g' pf_wf_env e t (FTAnn _ e' _t liqt p_e'_t) a k 
    = FTAnn (concatF (FConsT a k g) g') e' t (liqt ? lem_binds_consT_concatF g g' a k)
            (lem_weaken_tv_ftyp g g' pf_wf_env e' t p_e'_t a k)

{-@ lem_weaken_many_ftyp :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> ProofOf(WFFE (concatF g g')) -> e:Expr -> t:FType -> ProofOf(HasFType g e t)
        -> ProofOf(HasFType (concatF g g') e t) @-}
lem_weaken_many_ftyp :: FEnv -> FEnv -> WFFE -> Expr -> FType -> HasFType -> HasFType
lem_weaken_many_ftyp g FEmpty           p_g_wf    e t p_g_e_t = p_g_e_t
lem_weaken_many_ftyp g (FCons x t_x g') p_xenv_wf e t p_g_e_t
  = lem_weaken_ftyp (concatF g g') FEmpty p_env_wf e t p_g'g_e_t x t_x
      where
        (WFFBind _ p_env_wf _ _ _ _) = p_xenv_wf
        p_g'g_e_t = lem_weaken_many_ftyp g g' p_env_wf e t p_g_e_t
lem_weaken_many_ftyp g (FConsT a k g') p_xenv_wf e t p_g_e_t
  = lem_weaken_tv_ftyp (concatF g g') FEmpty p_env_wf e t p_g'g_e_t a k
      where
        (WFFBindT _ p_env_wf _ _) = p_xenv_wf
        p_g'g_e_t = lem_weaken_many_ftyp g g' p_env_wf e t p_g_e_t
