{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SystemFLemmasFTyping where

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

{-@ reflect foo23 @-}
foo23 x = Just x
foo23 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development for the Underlying STLC :: Technical LEMMAS
------------------------------------------------------------------------------

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 
-- Consequences of the System F Typing Judgments -
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 

{-@ lem_ftyping_wfft :: g:FEnv -> e:Expr -> t:FType -> { p_e_t:HasFType | propOf p_e_t == HasFType g e t }
                      -> ProofOf(WFFE g) -> ProofOf(WFFT g t Star) / [ ftypSize p_e_t] @-} 
lem_ftyping_wfft :: FEnv -> Expr -> FType -> HasFType -> WFFE -> WFFT
lem_ftyping_wfft g e t (FTBC _g b) p_wf_g  = WFFTKind g (FTBasic TBool) (WFFTBasic g TBool)
lem_ftyping_wfft g e t (FTIC _g n) p_wf_g  = WFFTKind g (FTBasic TInt)  (WFFTBasic g TInt)
lem_ftyping_wfft g e t (FTVar1 _g' x t') p_wf_g 
    = case p_wf_g of
        (WFFEmpty)                          -> impossible "in_envF x g"
        (WFFBind g' p_g' _x _t' k' p_g'_t') -> case k' of 
          Base -> WFFTKind g t p_g_t'
            where
              p_g_t' = lem_weaken_wfft g' FEmpty t k' p_g'_t' x t
          Star -> lem_weaken_wfft g' FEmpty t k' p_g'_t' x t
lem_ftyping_wfft g e t (FTVar2 g' x _t p_g'_x_t y s) p_wf_g
    = case p_wf_g of
        (WFFEmpty)                         -> impossible "in_envF y g"
        (WFFBind g' p_g' _y _s k_s p_g'_s) -> p_g_t 
          where
            p_g'_t = lem_ftyping_wfft g' e t p_g'_x_t p_g'
            p_g_t  = lem_weaken_wfft g' FEmpty t Star p_g'_t y s
lem_ftyping_wfft g e t (FTVar3 g' x _t p_g'_x_t a k) p_wf_g
    = case p_wf_g of
        (WFFEmpty)                     -> impossible "in_envF a g"
        (WFFBindT g' p_g' _a _k)       -> p_g_t 
          where 
            p_g_t' = lem_ftyping_wfft g' e t p_g'_x_t p_g'
            p_g_t  = lem_weaken_tv_wfft g' FEmpty t Star p_g_t' a k
lem_ftyping_wfft g e t (FTPrm _g c) p_wf_g 
    = lem_weaken_many_wfft FEmpty g (erase_ty c) Star pf_emp_tyc ? lem_empty_concatF g
        where
          pf_emp_tyc = lem_erase_wftype Empty (ty c) Star (lem_wf_ty c)
lem_ftyping_wfft g e t (FTAbs _g x t_x k_x pf_g_tx e' t' y pf_e'_t') pf_wf_g
    = WFFTFunc g t_x k_x pf_g_tx t' Star pf_g_t'
        where
          pf_wf_yg = WFFBind g pf_wf_g y t_x k_x pf_g_tx  
          pf_yg_t' = lem_ftyping_wfft (FCons y t_x g) (unbind x y e') t' pf_e'_t' pf_wf_yg
          pf_g_t'  = lem_strengthen_wfft g y t_x FEmpty t' Star pf_yg_t'
lem_ftyping_wfft g e t (FTApp _g e1 t_x t' p_e1_txt' e2 p_e2_tx) p_wf_g
    = if ( k' == Star ) then p_g_t' else WFFTKind g t' p_g_t'
        where
          p_g_txt' = lem_ftyping_wfft g e1 (FTFunc t_x t') p_e1_txt' p_wf_g
          (WFFTFunc _ _ _ p_g_tx _ k' p_g_t') = lem_wfftfunc_for_wf_ftfunc g t_x t' Star p_g_txt'
lem_ftyping_wfft g e t (FTAbsT _g a k e' t' a' pf_a'g_e'_t') pf_wf_g
    = WFFTPoly g a k t' Star a' pf_a'g_t'
        where
          pf_wf_a'g = WFFBindT g pf_wf_g a' k
          pf_a'g_t' = lem_ftyping_wfft (FConsT a' k g) (unbind_tv a a' e') (unbindFT a a' t')
                                       pf_a'g_e'_t' pf_wf_a'g
lem_ftyping_wfft g e t (FTAppT _g e' a k t' pf_e'_at' liqt pf_g_erliqt) pf_wf_g
    = if (k_t' == Star) then pf_g_t'liqt else WFFTKind g t pf_g_t'liqt
       where
         pf_g_at'    = lem_ftyping_wfft g e' (FTPoly a k t') pf_e'_at' pf_wf_g
         (WFFTPoly _ _a _k _t' k_t' a' pf_a'g_t') = lem_wfftpoly_for_wf_ftpoly g a k t' pf_g_at'
         pf_g_t'liqt = lem_subst_tv_wfft g FEmpty a' (erase liqt) k 
                                      pf_g_erliqt (unbindFT a a' t') k_t' pf_a'g_t' 
                                      ? lem_ftsubFV_unbindFT a a' (erase liqt) t'
lem_ftyping_wfft g e t (FTLet _g e_x t_x p_ex_tx x e' _t {-p_g_t-} y p_e'_t) p_wf_g  
    = lem_strengthen_wfft g y t_x FEmpty t Star pf_yg_t
        where 
          pf_g_tx = lem_ftyping_wfft g e_x t_x p_ex_tx p_wf_g
          p_wf_yg = WFFBind g p_wf_g y t_x Star pf_g_tx
          pf_yg_t = lem_ftyping_wfft (FCons y t_x g) (unbind x y e') t p_e'_t p_wf_yg
lem_ftyping_wfft g e t (FTAnn _g e' _t liqt p_e'_t) p_wf_g
    = lem_ftyping_wfft g e' t p_e'_t p_wf_g

--        -> e:Expr -> { t:FType | Set_sub (ffreeTV t) (bindsF (concatF (FCons x t_x g) g')) }
-- We can alpha-rename a variable anywhere in the environment and recursively alter the type
--   derivation tree. NB this is the base type judgement so there are no variables in the 
--   types to worry about
{-@ lem_change_var_ftyp :: g:FEnv -> { x:Vname | not (in_envF x g) } -> t_x:FType
        -> { g':FEnv | not (in_envF x g') && Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> ProofOf(WFFE (concatF (FCons x t_x g) g')) -> e:Expr -> t:FType 
        -> { p_e_t:HasFType | propOf p_e_t == HasFType (concatF (FCons x t_x g) g') e t }
        -> { y:Vname | not (in_envF y g) && not (in_envF y g') }
        -> { pf:HasFType | propOf pf == (HasFType (concatF (FCons y t_x g) g') (subFV x (FV y) e) t) 
                           && ftypSize pf == ftypSize p_e_t } / [ftypSize p_e_t] @-}
lem_change_var_ftyp :: FEnv -> Vname -> FType -> FEnv -> WFFE -> Expr -> FType 
                -> HasFType ->  Vname -> HasFType
lem_change_var_ftyp g x t_x g' pf_wf_env e t (FTBC _ b) y
    = FTBC (concatF (FCons y t_x g) g') b
lem_change_var_ftyp g x t_x g' pf_wf_env e t (FTIC _ n) y
    = FTIC (concatF (FCons y t_x g) g') n 
lem_change_var_ftyp g x t_x g' pf_wf_env e t p_z_t@(FTVar1 _ z _t) y
    = case g' of 
        (FEmpty)           -> FTVar1 g y t_x 
        (FCons  _z _ g'')  -> FTVar1 (concatF (FCons y t_x g) g'') z t
        (FConsT a k g'')   -> impossible ""
lem_change_var_ftyp g x t_x g' pf_wf_env e t (FTVar2 _ z _t p_z_t w t_w) y
    = case g' of             -- g''=Emp so x=w and p_z_t :: HasFType(g (FV z) t)
        (FEmpty)           -> case (x == z) of
                                (True)  -> impossible "it is"
                                (False) -> FTVar2 g z t p_z_t y t_x 
        (FCons _w _tw g'') -> case (x == z) of
                    (True)  -> FTVar2 (concatF (FCons y t_x g) g'') 
                                 (y `withProof` lem_in_env_concatF (FCons y t_x g) g'' y)
                                 t (lem_change_var_ftyp g x t_x g'' pf_wf_env' (FV z) t p_z_t y) w t_w
                    (False) -> FTVar2 (concatF (FCons y t_x g) g'')
                                 (z `withProof` lem_in_env_concatF (FCons y t_x g) g'' z
                                    `withProof` lem_in_env_concatF (FCons x t_x g) g'' z)
                                 t (lem_change_var_ftyp g x t_x g'' pf_wf_env' (FV z) t p_z_t y) w t_w
          where
            (WFFBind _ pf_wf_env' _ _ _ _) = pf_wf_env
        (FConsT a k g'')   -> impossible ""
lem_change_var_ftyp g x t_x g' pf_wf_env e t (FTVar3 _ z _t p_z_t a k) y
    = case g' of
        (FEmpty)           -> impossible ""
        (FCons w t_w g'')  -> impossible ""
        (FConsT _a _k g'') -> case (x == z) of
                    (True)   -> FTVar3 (concatF (FCons y t_x g) g'') 
                                  (y `withProof` lem_in_env_concatF (FCons y t_x g) g'' y)
                                  t (lem_change_var_ftyp g x t_x g'' pf_wf_env' (FV z) t p_z_t y) a k
                    (False)  -> FTVar3 (concatF (FCons y t_x g) g'')
                                  (z `withProof` lem_in_env_concatF (FCons y t_x g) g'' z
                                     `withProof` lem_in_env_concatF (FCons x t_x g) g'' z)
                                  t (lem_change_var_ftyp g x t_x g'' pf_wf_env' (FV z) t p_z_t y) a k
          where
            (WFFBindT _ pf_wf_env' _ _) = pf_wf_env
lem_change_var_ftyp g x t_x g' pf_wf_env e t (FTPrm _ c) y
    = FTPrm (concatF (FCons y t_x g) g') c
lem_change_var_ftyp g x t_x g' pf_wf_env e t p_e_t@(FTAbs gg z b k p_gg_b e' b' z' p_z'_e'_b') y
    = FTAbs (concatF (FCons y t_x g) g') z b k p_env'_b (subFV x (FV y) e') b' z'' p_z''y_e'_b'
        where
            p_env'_b     = lem_change_var_wfft g x t_x g' b k p_gg_b y
            z''_         = fresh_var_excludingF (concatF (FCons x t_x g) g') y
            z''          = z''_ ? lem_in_env_concatF g g' z''_
                                ? lem_in_env_concatF (FCons x t_x g) g' z''_
                                ? lem_fv_bound_in_fenv (concatF (FCons x t_x g) g') e t p_e_t z''_
            pf_wf_z'env  = WFFBind (concatF (FCons x t_x g) g') pf_wf_env z'  b k p_gg_b
            pf_wf_z''env = WFFBind (concatF (FCons x t_x g) g') pf_wf_env z'' b k p_gg_b
            p_z''_e'_b'  = lem_change_var_ftyp  (concatF (FCons x t_x g) g') z' b FEmpty pf_wf_z'env
                                    (unbind z z' e') b' p_z'_e'_b' z'' 
                                    ? lem_subFV_unbind z z' (FV z'') e'
            p_z''y_e'_b' = lem_change_var_ftyp g x t_x (FCons z'' b g') pf_wf_z''env
                                    (unbind z z'' e') b' p_z''_e'_b' y
                                    ? lem_commute_subFV_unbind x y z z'' e'
lem_change_var_ftyp g x t_x g' pf_wf_env e t (FTApp _ e1 t1 t2 p_e1_t1t2 e2 p_e2_t1) y
    = FTApp (concatF (FCons y t_x g) g') (subFV x (FV y) e1) t1 t2 
            (lem_change_var_ftyp g x t_x g' pf_wf_env e1 (FTFunc t1 t2) p_e1_t1t2 y)
            (subFV x (FV y) e2) (lem_change_var_ftyp g x t_x g' pf_wf_env e2 t1 p_e2_t1 y)
lem_change_var_ftyp g x t_x g' pf_wf_env e t p_e_t@(FTAbsT env a k e' t' a' p_a'_e'_t') y
    = FTAbsT (concatF (FCons y t_x g) g') a k (subFV x (FV y) e') t' a'' p_a''y_e'_t'
        where
          p_env_t      = lem_ftyping_wfft env e t p_e_t pf_wf_env
          a''_         = fresh_var_excludingF (concatF (FCons x t_x g) g') y 
          a''          = a''_ ? lem_in_env_concatF g g' a''_
                              ? lem_in_env_concatF (FCons x t_x g) g' a''_
                              ? lem_in_env_concatF (FCons y t_x g) g' a''_
                              ? lem_fv_bound_in_fenv env e t p_e_t a''_
                              ? lem_ffreeTV_bound_in_fenv env t Star p_env_t a''_
          p_a'env_wf   = WFFBindT env pf_wf_env a'  k 
          p_a''env_wf  = WFFBindT env pf_wf_env a'' k 
          p_a''_e'_t'  = lem_change_tvar_ftyp (concatF (FCons x t_x g) g') a' k FEmpty p_a'env_wf
                                    (unbind_tv a a' e') (unbindFT a a' t') p_a'_e'_t' a''
                           ? lem_chgFTV_unbind_tv a a' a''
                                (e' ? lem_fv_bound_in_fenv (concatF (FCons x t_x g) g') e t p_e_t a')
                           ? lem_ftsubFV_unbindFT a a' (FTBasic (FTV a''))  t' 
          p_a''y_e'_t' = lem_change_var_ftyp g x t_x (FConsT a'' k g') p_a''env_wf 
                                    (unbind_tv a a'' e') (unbindFT a a'' t') p_a''_e'_t' y
                           ? lem_commute_subFV_unbind_tv x (FV y) a a'' e'
lem_change_var_ftyp g x t_x g' pf_wf_env e t (FTAppT _ e' a k t' p_e'_at' rt pf_env_rt) y
    = FTAppT (concatF (FCons y t_x g) g') (subFV x (FV y) e') a k t' p_y_e'_at'
             (tsubFV x (FV y) rt ? lem_erase_tsubFV x (FV y) rt 
                                 ? lem_binds_cons_concatF g g' x t_x
                                 ? lem_binds_cons_concatF g g' y t_x) 
             pf_env'_rt
        where      
          p_y_e'_at' = lem_change_var_ftyp g x t_x g' pf_wf_env e' (FTPoly a k t') p_e'_at' y
          pf_env'_rt = lem_change_var_wfft g x t_x g' (erase rt) k pf_env_rt y
                                 ? lem_erase_tsubFV x (FV y) rt
lem_change_var_ftyp g x t_x g' pf_wf_env e t p_e_t@(FTLet env e_z t_z p_ez_tz z e' t' z' p_z'_e'_t') y
    = FTLet (concatF (FCons y t_x g) g') (subFV x (FV y) e_z) t_z p_env'_ez_tz z
            (subFV x (FV y) e') t' z'' p_z''y_e'_t'
        where
          p_env_tz     = lem_ftyping_wfft env e_z t_z p_ez_tz pf_wf_env
          z''_         = fresh_var_excludingF (concatF (FCons x t_x g) g') y
          z''          = z''_ ? lem_in_env_concatF g g' z''_
                              ? lem_in_env_concatF (FCons x t_x g) g' z''_
                              ? lem_fv_bound_in_fenv (concatF (FCons x t_x g) g') e t p_e_t z''_
          p_z'env_wf   = WFFBind env pf_wf_env z'  t_z Star p_env_tz
          p_z''env_wf  = WFFBind env pf_wf_env z'' t_z Star p_env_tz
          p_env'_ez_tz = lem_change_var_ftyp g x t_x g' pf_wf_env e_z t_z p_ez_tz y
          p_z''_e'_t'  = lem_change_var_ftyp (concatF (FCons x t_x g) g') z' t_z FEmpty p_z'env_wf
                                             (unbind z z' e')  t' p_z'_e'_t'  z''
                                             ? lem_subFV_unbind z z' (FV z'') e'
          p_z''y_e'_t' = lem_change_var_ftyp g x t_x (FCons z'' t_z g') p_z''env_wf
                                             (unbind z z'' e') t' p_z''_e'_t' y
                                             ? lem_commute_subFV_unbind x y z z'' e'
lem_change_var_ftyp g x t_x g' pf_wf_env e t (FTAnn _ e' _t liqt p_e'_t) y
    = FTAnn (concatF (FCons y t_x g) g') (subFV x (FV y) e') t liqt' p_env'_e'_t
                                              ? lem_binds_cons_concatF g g' x t_x
                                              ? lem_binds_cons_concatF g g' y t_x
        where
          liqt'       = tsubFV x (FV y) (liqt ? lem_erase_tsubFV x (FV y) liqt)
                                              ? lem_binds_cons_concatF g g' x t_x
                                              ? lem_binds_cons_concatF g g' y t_x
          p_env'_e'_t = lem_change_var_ftyp g x t_x g' pf_wf_env e' t p_e'_t y


--        -> e:Expr -> { t:FType | Set_sub (ffreeTV t) (bindsF (concatF (FConsT a k g) g')) }
{-@ lem_change_tvar_ftyp :: g:FEnv -> { a:Vname | not (in_envF a g) } -> k:Kind 
        -> { g':FEnv | not (in_envF a g') && Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> ProofOf(WFFE (concatF (FConsT a k g) g')) -> e:Expr -> t:FType 
        -> { p_e_t:HasFType | propOf p_e_t == HasFType (concatF (FConsT a k g) g') e t }
        -> { a':Vname | not (in_envF a' g) && not (in_envF a' g') }
        -> { pf:HasFType | propOf pf == (HasFType (concatF (FConsT a' k g) 
                                                     (fesubFV a (FTBasic (FTV a')) g')) 
                                           (chgFTV a a' e) (ftsubFV a (FTBasic (FTV a')) t)) && 
                             ftypSize pf == ftypSize p_e_t } / [ftypSize p_e_t] @-}
lem_change_tvar_ftyp :: FEnv -> Vname -> Kind -> FEnv -> WFFE -> Expr -> FType 
                -> HasFType ->  Vname -> HasFType
lem_change_tvar_ftyp g a k g' pf_wf_env e t (FTBC _ b) a'
    = FTBC (concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g')) b
lem_change_tvar_ftyp g a k g' pf_wf_env e t (FTIC _ n) a'
    = FTIC (concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g')) n 
lem_change_tvar_ftyp g a k g' pf_wf_env e t p_z_t@(FTVar1 _ z _t) a'
    = case g' of 
        (FEmpty)           -> impossible ""
        (FCons  _z _ g'')  -> FTVar1 (concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g'')) z 
                                     (ftsubFV a (FTBasic (FTV a')) t)
        (FConsT a1 k1 g'') -> impossible ""
lem_change_tvar_ftyp g a k g' pf_wf_env e t p_z_t@(FTVar2 _ z _t p_env'_z_t w t_w) a'
    = case g' of             
        (FEmpty)           -> impossible "a <> w"
        (FCons _w _tw g'') -> case ( a == z ) of
            True  -> impossible ("by lemma" ? lem_ftvar_v_in_env (concatF (FConsT a k g) g') 
                                                                 z t p_z_t)
            False -> FTVar2 (concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g''))
                            (z ? lem_in_env_concatF (FConsT a' k g) g'' z
                               ? lem_in_env_concatF (FConsT a  k g) g'' z)
                            (ftsubFV a (FTBasic (FTV a')) t) p_env''_z_t w 
                            (ftsubFV a (FTBasic (FTV a')) t_w)
          where
            g'''        = fesubFV a (FTBasic (FTV a')) g''
            (WFFBind _ pf_wf_env' _ _ _ _) = pf_wf_env
            p_env''_z_t = lem_change_tvar_ftyp g a k g'' pf_wf_env' (FV z) t p_env'_z_t a'
        (FConsT a1 k1 g'')  -> impossible "a1 <> w"
lem_change_tvar_ftyp g a k g' pf_wf_env e t p_z_t@(FTVar3 _ z _t p_env'_z_t a1 k1) a'
    = case g' of
        (FEmpty)             -> case ( a == z ) of
            (True)  -> impossible ("by lemma" ? lem_ftvar_v_in_env (FConsT a k g) z t p_z_t)
            (False) -> FTVar3 g z t p_env'_z_t a' k 
                              ? lem_ftsubFV_notin a (FTBasic (FTV a')) 
                                    (t ? lem_ffreeTV_bound_in_fenv g t Star p_g_t a)
          where
            (WFFBindT _ pf_wf_g _ _) = pf_wf_env
            p_g_t = lem_ftyping_wfft g e t p_env'_z_t pf_wf_g
        (FCons w t_w g'')    -> impossible "a1 <> w"
        (FConsT _a1 _k1 g'') -> case ( a == z ) of
            (True)  -> impossible ("by lemma" ? lem_ftvar_v_in_env (concatF (FConsT a k g) g')
                                                                   z t p_z_t)
            (False) -> FTVar3 (concatF (FConsT a' k g) g''')
                              (z ? lem_in_env_concatF (FConsT a' k g) g'' z
                                 ? lem_in_env_concatF (FConsT a  k g) g'' z)
                              (ftsubFV a (FTBasic (FTV a')) t) p_env''_z_t a1 k1
          where
            g'''        = fesubFV a (FTBasic (FTV a')) g''
            (WFFBindT _ pf_wf_env' _ _) = pf_wf_env
            p_env''_z_t = lem_change_tvar_ftyp g a k g'' pf_wf_env' (FV z) t p_env'_z_t a'
lem_change_tvar_ftyp g a k g' pf_wf_env e t (FTPrm _ c) a'
    = FTPrm (concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g')) c
            ? lem_chgFTV_notin a a' (Prim c)
            ? lem_ftsubFV_notin  a (FTBasic (FTV a')) (erase_ty c)
lem_change_tvar_ftyp g a k g' pf_wf_env e t p_e_t@(FTAbs gg z b k_b p_gg_b e' b' z' p_z'_e'_b') a'
    = FTAbs (concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g')) 
            z (ftsubFV a (FTBasic (FTV a')) b) k_b p_env'_b 
            (chgFTV a a' e') (ftsubFV a (FTBasic (FTV a')) b') z'' p_z''a'_e'_b'
        where
            p_env'_b      = lem_change_tvar_wfft g a k g' b k_b p_gg_b a'
            z''_          = fresh_var_excludingF (concatF (FConsT a k g) g') a'
            z''           = z''_ ? lem_in_env_concatF g g' z''_
                                 ? lem_in_env_concatF (FConsT a k g) g' z''_
                                 ? lem_fv_bound_in_fenv (concatF (FConsT a k g) g') e t p_e_t z''_
            pf_wf_z'env   = WFFBind (concatF (FConsT a k g) g') pf_wf_env z'  b k_b p_gg_b
            pf_wf_z''env  = WFFBind (concatF (FConsT a k g) g') pf_wf_env z'' b k_b p_gg_b
            p_z''_e'_b'   = lem_change_var_ftyp  (concatF (FConsT a k g) g') z' b FEmpty pf_wf_z'env
                                    (unbind z z' e') b' p_z'_e'_b' z'' 
                                    ? lem_subFV_unbind z z' (FV z'') e'
            p_z''a'_e'_b' = lem_change_tvar_ftyp g a k (FCons z'' b g') pf_wf_z''env
                                    (unbind z z'' e') b' p_z''_e'_b' a'
                                    ? lem_commute_chgFTV_subBV z (FV z'') a a' e'
                                    ? lem_chgFTV_notin a a' (FV z'')   
lem_change_tvar_ftyp g a k g' pf_wf_env e t (FTApp _ e1 t1 t2 p_e1_t1t2 e2 p_e2_t1) a'
    = FTApp (concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g')) 
            (chgFTV a a' e1) (ftsubFV a (FTBasic (FTV a')) t1) 
            (ftsubFV a (FTBasic (FTV a')) t2) p_a'_e1_t1t2 (chgFTV a a' e2) p_a'_e2_t1
        where
          p_a'_e1_t1t2 = lem_change_tvar_ftyp g a k g' pf_wf_env e1 (FTFunc t1 t2) p_e1_t1t2 a'
          p_a'_e2_t1   = lem_change_tvar_ftyp g a k g' pf_wf_env e2 t1             p_e2_t1   a'
lem_change_tvar_ftyp g a k g' pf_wf_env e t p_e_t@(FTAbsT env a1 k1 e' t' a1' p_a1'_e'_t') a'
    = FTAbsT (concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g')) 
             a1 k1 (chgFTV a a' e') (ftsubFV a (FTBasic (FTV a')) t') a1'' p_a1''y_e'_t'
        where
          p_env_t       = lem_ftyping_wfft env e t p_e_t pf_wf_env
          a1''_         = fresh_var_excludingF (concatF (FConsT a k g) g') a'
          a1''          = a1''_ ? lem_in_env_concatF g g' a1''_
                                ? lem_in_env_concatF (FConsT a  k g) g' a1''_
                                ? lem_in_env_concatF (FConsT a' k g) g' a1''_
                                ? lem_fv_bound_in_fenv env e t p_e_t a1''_
                                ? lem_ffreeTV_bound_in_fenv env t Star p_env_t a1''_
          p_a1'env_wf   = WFFBindT env pf_wf_env a1'  k1 
          p_a1''env_wf  = WFFBindT env pf_wf_env a1'' k1 
          p_a1''_e'_t'  = lem_change_tvar_ftyp (concatF (FConsT a k g) g') a1' k1 FEmpty p_a1'env_wf
                                    (unbind_tv a1 a1' e') (unbindFT a1 a1' t') p_a1'_e'_t' a1''
                            ? lem_chgFTV_unbind_tv a1 a1' a1''
                                 (e' ? lem_fv_bound_in_fenv (concatF (FConsT a k g) g') e t p_e_t a1')
                            ? lem_ftsubFV_unbindFT a1 a1' (FTBasic (FTV a1''))  t' 
          p_a1''y_e'_t' = lem_change_tvar_ftyp g a k (FConsT a1'' k1 g') p_a1''env_wf 
                                    (unbind_tv a1 a1'' e') (unbindFT a1 a1'' t') p_a1''_e'_t' a'
                           ? lem_commute_chgFTV_unbind_tv a a' a1 a1'' e'
                           ? lem_commute_ftsubFV_unbindFT a (FTBasic (FTV a')) a1 a1'' t'
lem_change_tvar_ftyp g a k g' pf_wf_env e t (FTAppT env e' a1 k1 t' p_e'_a1t' rt pf_env_rt) a'
    = FTAppT (concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g')) 
             (chgFTV a a' e') a1 k1 (ftsubFV a (FTBasic (FTV a')) t') p_a'_e'_a1t'
             (tchgFTV a a' rt ? lem_erase_tchgFTV a a' rt  
                              ? lem_binds_consT_concatF g g' a  k
                              ? lem_binds_consT_concatF g g' a' k) 
             pf_env'_rt 
        where      
          p_a'_e'_a1t' = lem_change_tvar_ftyp g a k g' pf_wf_env e' (FTPoly a1 k1 t') p_e'_a1t' a'
          pf_env'_rt   = lem_change_tvar_wfft g a k g' (erase rt) k1 pf_env_rt a'
                              ? lem_commute_ftsubFV_ftsubBV a (FTBasic (FTV a')) a1 (erase rt) t'
lem_change_tvar_ftyp g a k g' pf_wf_env e t p_e_t@(FTLet env e_z t_z p_ez_tz z e' t' z' p_z'_e'_t') a'
    = FTLet (concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g'))
            (chgFTV a a' e_z) (ftsubFV a (FTBasic (FTV a')) t_z) p_env'_ez_tz z
            (chgFTV a a' e') (ftsubFV a (FTBasic (FTV a')) t') z'' p_z''y_e'_t'
        where
          p_env_tz     = lem_ftyping_wfft env e_z t_z p_ez_tz pf_wf_env
          z''_         = fresh_var_excludingF (concatF (FConsT a k g) g') a'
          z''          = z''_ ? lem_in_env_concatF g g' z''_
                              ? lem_in_env_concatF (FConsT a k g) g' z''_
                              ? lem_fv_bound_in_fenv (concatF (FConsT a k g) g') e t p_e_t z''_
          p_z'env_wf   = WFFBind env pf_wf_env z'  t_z Star p_env_tz
          p_z''env_wf  = WFFBind env pf_wf_env z'' t_z Star p_env_tz
          p_env'_ez_tz = lem_change_tvar_ftyp g a k g' pf_wf_env e_z t_z p_ez_tz a'
          p_z''_e'_t'  = lem_change_var_ftyp (concatF (FConsT a k g) g') z' t_z FEmpty p_z'env_wf
                                             (unbind z z' e')  t' p_z'_e'_t'  z''
                                             ? lem_subFV_unbind z z' (FV z'') e'
          p_z''y_e'_t' = lem_change_tvar_ftyp g a k (FCons z'' t_z g') p_z''env_wf
                                             (unbind z z'' e') t' p_z''_e'_t' a'
                                             ? lem_commute_chgFTV_subBV z (FV z'') a a' e'
lem_change_tvar_ftyp g a k g' pf_wf_env e t (FTAnn _ e' _t liqt p_e'_t) a'
    = FTAnn (concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g'))
            (chgFTV a a' e') (ftsubFV a (FTBasic (FTV a')) t) liqt'  p_env'_e'_t
            ? lem_binds_consT_concatF g g' a  k
            ? lem_binds_consT_concatF g g' a' k
        where
          liqt'       = tchgFTV a a' (liqt ? lem_erase_tchgFTV a a' liqt)
                                              ? lem_binds_consT_concatF g g' a  k
                                              ? lem_binds_consT_concatF g g' a' k 
          p_env'_e'_t = lem_change_tvar_ftyp g a k g' pf_wf_env e' t p_e'_t a'
