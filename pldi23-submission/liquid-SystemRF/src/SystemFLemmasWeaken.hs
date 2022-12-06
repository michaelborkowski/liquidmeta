{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--interpreter" @-}
{-@ LIQUID "--short-names" @-}

module SystemFLemmasWeaken where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof,(?))
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasWellFormedness

------------------------------------------------------------------------------
----- | METATHEORY Development for the Underlying STLC :: Technical LEMMAS
------------------------------------------------------------------------------

{-@ lem_weaken_ftyp :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> e:Expr -> t:FType -> { p_e_t:HasFType | propOf p_e_t == HasFType (concatF g g') e t }
        -> { x:Vname | not (in_envF x g) && not (in_envF x g') } -> t_x:FType
        -> { pf:HasFType | propOf pf == (HasFType (concatF (FCons x t_x g) g') e t) }
           / [esize e, fenvsize g'] @-}
lem_weaken_ftyp :: FEnv -> FEnv -> Expr -> FType -> HasFType ->  Vname -> FType -> HasFType
lem_weaken_ftyp g g' e t (FTBC _env b) x t_x  
    = FTBC  (concatF (FCons x t_x g) g') b
lem_weaken_ftyp g g' e t (FTIC _env n) x t_x  
    = FTIC  (concatF (FCons x t_x g) g') n
lem_weaken_ftyp g g' e t p_y_ty@(FTVar1 env y t_y) x t_x 
    = case g' of 
        (FEmpty)           -> FTVar2 (FCons y t_y env) y t_y p_y_ty x t_x
        (FCons _y _ty g'') -> FTVar1 (concatF (FCons x t_x g) g'') y t_y 
                                    -- (g; g' == _g, z:t_z) |- y : t_y
lem_weaken_ftyp g g' e t p_y_ty@(FTVar2 gg y t_y p_gg'_y_ty z t_z) x t_x
    = case g' of
        (FEmpty)           -> FTVar2 (FCons z t_z gg) y t_y p_y_ty x t_x
        (FCons _z _tz g'') -> FTVar2 (concatF (FCons x t_x g) g'') 
                                     (y `withProof` lem_in_env_concatF g g'' y) t_y
                                     (lem_weaken_ftyp g g'' e t p_gg'_y_ty x t_x) z t_z
lem_weaken_ftyp g g' e t p_y_ty@(FTVar3 env y t_y p_gg'_y_ty a k) x t_x  
    = case g' of
        (FEmpty)           -> FTVar2 (FConsT a k env) y t_y p_y_ty x t_x
        (FConsT _a _k g'') -> FTVar3 (concatF (FCons x t_x g) g'') 
                                     (y `withProof` lem_in_env_concatF g g'' y) t_y
                                     (lem_weaken_ftyp g g'' e t p_gg'_y_ty x t_x) a k
lem_weaken_ftyp g g' e t (FTPrm _env c)  x t_x 
    = FTPrm (concatF (FCons x t_x g) g') c
lem_weaken_ftyp g g' e t p_e_t@(FTAbs env t_y k_y p_env_ty e' t' nms mk_p_y'_e'_t') x t_x 
    = FTAbs (concatF (FCons x t_x g) g') t_y k_y p_env'_ty e' t' nms' mk_p_y'x_e'_t'
        where
            p_env'_ty    = lem_weaken_wfft g g' t_y k_y p_env_ty x t_x
            {-@ mk_p_y'x_e'_t' :: { y:Vname | NotElem y nms' } 
                    -> ProofOf(HasFType (FCons y t_y (concatF (FCons x t_x g) g')) (unbind y e') t') @-}
            mk_p_y'x_e'_t' y' = lem_weaken_ftyp g (FCons (y' ? lem_in_env_concatF g g' y') t_y g') 
                                                (unbind y' e') t' (mk_p_y'_e'_t' y') x t_x
            nms'         = x:(unionFEnv nms (concatF g g'))
lem_weaken_ftyp g g' e t (FTApp env e1 s s' p_e1_ss' e2 p_e2_s)  x t_x  
    = FTApp (concatF (FCons x t_x g) g') e1 s s' p_env'_e1_ss' e2 p_env'_e2_s
        where
          p_env'_e1_ss' = lem_weaken_ftyp g g' e1 (FTFunc s s') p_e1_ss' x t_x
          p_env'_e2_s   = lem_weaken_ftyp g g' e2 s             p_e2_s   x t_x
lem_weaken_ftyp g g' e t p_e_t@(FTAbsT env k e' t' nms mk_p_a'_e'_t') x t_x  
    = FTAbsT (concatF (FCons x t_x g) g') k e' t' nms' mk_p_a'x_e'_t'
        where
          {-@ mk_p_a'x_e'_t' :: { a:Vname | NotElem a nms' }
               -> ProofOf(HasFType (FConsT a k (concatF (FCons x t_x g) g')) (unbind_tv a e') (unbindFT a t')) @-}
          mk_p_a'x_e'_t' a' = lem_weaken_ftyp g (FConsT (a' ? lem_in_env_concatF g g' a') k g') 
                                              (unbind_tv a' e') (unbindFT a' t') (mk_p_a'_e'_t' a') x t_x
          nms'         = x:(unionFEnv nms (concatF g g'))
lem_weaken_ftyp g g' e t (FTAppT env e' k t' p_e'_at' rt pf_env_rt) x t_x  
    = FTAppT (concatF (FCons x t_x g) g') e' k t' p_y_e'_at'
             (rt ? lem_binds_cons_concatF g g' x t_x) pf_env'_rt
        where      
          p_y_e'_at' = lem_weaken_ftyp g g' e' (FTPoly k t') p_e'_at' x t_x
          pf_env'_rt = lem_weaken_wfft g g' (erase rt) k pf_env_rt x t_x
lem_weaken_ftyp g g'  e t p_e_t@(FTLet env e_y t_y p_ey_ty e' t' nms mk_p_y_e'_t') x t_x
    = FTLet (concatF (FCons x t_x g) g') e_y t_y p_env'_ey_ty e' t' nms' mk_p_yx_e'_t'
        where
            p_env'_ey_ty = lem_weaken_ftyp g g' e_y t_y p_ey_ty x t_x
            {-@ mk_p_yx_e'_t' :: { y:Vname | NotElem y nms' }
                    -> ProofOf(HasFType (FCons y t_y (concatF (FCons x t_x g) g')) (unbind y e') t') @-}
            mk_p_yx_e'_t' y = lem_weaken_ftyp g (FCons (y ? lem_in_env_concatF g g' y) t_y g') 
                                              (unbind y e') t' (mk_p_y_e'_t' y) x t_x
            nms'            = x:(unionFEnv nms (concatF g g'))
lem_weaken_ftyp g g' e t (FTAnn _ e' _t liqt p_e'_t)  x t_x 
    = FTAnn (concatF (FCons x t_x g) g') e' t (liqt ? lem_binds_cons_concatF g g' x t_x)
            (lem_weaken_ftyp g g' e' t p_e'_t x t_x)

 
{-@ lem_weaken_tv_ftyp :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> e:Expr -> t:FType -> { p_e_t:HasFType | propOf p_e_t == HasFType (concatF g g') e t }
        -> { a:Vname | not (in_envF a g) && not (in_envF a g') } -> k:Kind
        -> { pf:HasFType | propOf pf == (HasFType (concatF (FConsT a k g) g') e t) }
           / [esize e, fenvsize g'] @-}
lem_weaken_tv_ftyp :: FEnv -> FEnv -> Expr -> FType -> HasFType -> Vname -> Kind -> HasFType
lem_weaken_tv_ftyp g g' e t (FTBC _env b) a k 
    = FTBC  (concatF (FConsT a k g) g') b
lem_weaken_tv_ftyp g g' e t (FTIC _env n) a k 
    = FTIC  (concatF (FConsT a k g) g') n
lem_weaken_tv_ftyp g g' e t p_x_tx@(FTVar1 env x t_x) a k 
    = case g' of 
        (FEmpty)           -> FTVar3 (FCons x t_x env) x t_x p_x_tx a k
        (FCons  _z _ g'')  -> FTVar1 (concatF (FConsT a k g) g'') x t_x 
lem_weaken_tv_ftyp g g' e t p_y_ty@(FTVar2 gg y t_y p_gg'_y_ty z t_z) a k 
    = case g' of
        (FEmpty)           -> FTVar3 (FCons z t_z gg) y t_y p_y_ty a k
        (FCons _z _tz g'') -> FTVar2 (concatF (FConsT a k g) g'') 
                                     (y `withProof` lem_in_env_concatF g g'' y) t_y
                                     (lem_weaken_tv_ftyp g g'' e t p_gg'_y_ty a k) z t_z
lem_weaken_tv_ftyp g g' e t p_y_ty@(FTVar3 env y t_y p_gg'_y_ty a1 k1) a k 
    = case g' of
        (FEmpty)           -> FTVar3 (FConsT a1 k1 env) y t_y p_y_ty a k
        (FConsT _a _k g'') -> FTVar3 (concatF (FConsT a k g) g'') 
                                     (y `withProof` lem_in_env_concatF g g'' y) t_y
                                     (lem_weaken_tv_ftyp g g'' e t p_gg'_y_ty a k) a1 k1
lem_weaken_tv_ftyp g g' e t (FTPrm _env c) a k 
    = FTPrm (concatF (FConsT a k g) g') c
lem_weaken_tv_ftyp g g' e t p_e_t@(FTAbs env t_y k_y p_env_ty e' t' nms mk_p_y'_e'_t') a k  
    = FTAbs (concatF (FConsT a k g) g') t_y k_y p_env'_ty e' t' nms' mk_p_y'a_e'_t'
        where
            p_env'_ty    = lem_weaken_tv_wfft g g' t_y k_y p_env_ty a k
            {-@ mk_p_y'a_e'_t' :: { y:Vname | NotElem y nms' }
                    -> ProofOf(HasFType (FCons y t_y (concatF (FConsT a k g) g')) (unbind y e') t') @-}
            mk_p_y'a_e'_t' y' = lem_weaken_tv_ftyp g (FCons (y' ? lem_in_env_concatF g g' y') t_y g') 
                                                   (unbind y' e') t' (mk_p_y'_e'_t' y') a k
            nms'         = a:(unionFEnv nms (concatF g g'))
lem_weaken_tv_ftyp g g' e t (FTApp env e1 s s' p_e1_ss' e2 p_e2_s) a k  
    = FTApp (concatF (FConsT a k g) g') e1 s s' p_env'_e1_ss' e2 p_env'_e2_s
        where
          p_env'_e1_ss' = lem_weaken_tv_ftyp g g' e1 (FTFunc s s') p_e1_ss' a k
          p_env'_e2_s   = lem_weaken_tv_ftyp g g' e2 s             p_e2_s   a k
lem_weaken_tv_ftyp g g' e t p_e_t@(FTAbsT env k' e' t' nms mk_p_a'_e'_t') a k  
    = FTAbsT (concatF (FConsT a k g) g') k' e' t' nms' mk_p_a'a_e'_t'
        where
          {-@ mk_p_a'a_e'_t' :: { a':Vname | NotElem a' nms' }
                  -> ProofOf(HasFType (FConsT a' k' (concatF (FConsT a k g) g')) (unbind_tv a' e') 
                                      (unbindFT a' t')) @-}
          mk_p_a'a_e'_t' a' = lem_weaken_tv_ftyp g (FConsT (a' ? lem_in_env_concatF g g' a') k' g') 
                                                 (unbind_tv a' e') (unbindFT a' t') (mk_p_a'_e'_t' a') a k
          nms'         = a:(unionFEnv nms (concatF g g'))
lem_weaken_tv_ftyp g g' e t (FTAppT env e' k1 t' p_e'_a1t' rt pf_env_rt) a k 
    = FTAppT (concatF (FConsT a k g) g') e' k1 t' p_a_e'_a1t'
             (rt ? lem_binds_consT_concatF g g' a k) pf_env'_rt
        where      
          p_a_e'_a1t' = lem_weaken_tv_ftyp g g' e' (FTPoly k1 t') p_e'_a1t' a k
          pf_env'_rt  = lem_weaken_tv_wfft g g' (erase rt) k1 pf_env_rt a k
lem_weaken_tv_ftyp g g' e t p_e_t@(FTLet env e_y t_y p_ey_ty e' t' nms mk_p_y_e'_t') a k 
    = FTLet (concatF (FConsT a k g) g') e_y t_y p_env'_ey_ty e' t' nms' mk_p_ya_e'_t'
        where
            p_env'_ey_ty    = lem_weaken_tv_ftyp g g' e_y t_y p_ey_ty a k
            {-@ mk_p_ya_e'_t' :: { y:Vname | NotElem y nms' }
                    -> ProofOf(HasFType (FCons y t_y (concatF (FConsT a k g) g')) (unbind y e') t') @-}
            mk_p_ya_e'_t' y = lem_weaken_tv_ftyp g (FCons (y ? lem_in_env_concatF g g' y) t_y g') 
                                                 (unbind y e') t' (mk_p_y_e'_t' y) a k
            nms'            = a:(unionFEnv nms (concatF g g'))
lem_weaken_tv_ftyp g g' e t (FTAnn _ e' _t liqt p_e'_t) a k 
    = FTAnn (concatF (FConsT a k g) g') e' t (liqt ? lem_binds_consT_concatF g g' a k)
            (lem_weaken_tv_ftyp g g' e' t p_e'_t a k)

{-@ lem_weaken_pftyp :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> ps:Preds -> ProofOf(PHasFType (concatF g g') ps)
        -> { x:Vname | not (in_envF x g) && not (in_envF x g') } -> t_x:FType
        -> ProofOf(PHasFType (concatF (FCons x t_x g) g') ps) / [predsize ps] @-}
lem_weaken_pftyp :: FEnv -> FEnv -> Preds -> PHasFType ->  Vname -> FType -> PHasFType
lem_weaken_pftyp g g' ps (PFTEmp _) x t_x = PFTEmp (concatF (FCons x t_x g) g')
lem_weaken_pftyp g g' ps (PFTCons _ p pf_p_bl ps' pf_ps'_bl) x t_x 
  = PFTCons (concatF (FCons x t_x g) g') p pf'_p_bl ps' pf'_ps'_bl
      where
        pf'_p_bl   = lem_weaken_ftyp  g g' p (FTBasic TBool) pf_p_bl x t_x
        pf'_ps'_bl = lem_weaken_pftyp g g' ps'             pf_ps'_bl x t_x  

{-@ lem_weaken_tv_pftyp :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> ps:Preds -> ProofOf(PHasFType (concatF g g') ps)
        -> { a:Vname | not (in_envF a g) && not (in_envF a g') } -> k:Kind
        -> ProofOf(PHasFType (concatF (FConsT a k g) g') ps) / [predsize ps] @-}
lem_weaken_tv_pftyp :: FEnv -> FEnv -> Preds -> PHasFType -> Vname -> Kind -> PHasFType
lem_weaken_tv_pftyp g g' ps (PFTEmp _) a k = PFTEmp (concatF (FConsT a k g) g')
lem_weaken_tv_pftyp g g' ps (PFTCons _ p pf_p_bl ps' pf_ps'_bl) a k 
  = PFTCons (concatF (FConsT a k g) g') p pf'_p_bl ps' pf'_ps'_bl
      where
        pf'_p_bl   = lem_weaken_tv_ftyp  g g' p (FTBasic TBool) pf_p_bl a k
        pf'_ps'_bl = lem_weaken_tv_pftyp g g' ps'             pf_ps'_bl a k 
