{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SystemFLemmasWellFormedness where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof,(?))
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import PrimitivesFTyping
import BasicPropsSubstitution
import BasicPropsEnvironments
import WellFormedness
import BasicPropsWellFormedness

------------------------------------------------------------------------------
----- | METATHEORY Development for the Underlying STLC :: Technical LEMMAS
------------------------------------------------------------------------------

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 
-- Consequences of the System F Well-Formedness Judgments -
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 

{-@ lem_weaken_wfft :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
      -> t:FType -> k:Kind -> { p_t_wf:WFFT | propOf p_t_wf == WFFT (concatF g g') t k }
      -> { x:Vname | not (in_envF x g) && not (in_envF x g') } -> t_x:FType
      -> { pf:WFFT | propOf pf == (WFFT (concatF (FCons x t_x g) g') t k) } 
       / [ftsize t, fenvsize g', ksize k] @-}
lem_weaken_wfft :: FEnv -> FEnv -> FType -> Kind -> WFFT -> Vname -> FType -> WFFT
lem_weaken_wfft g g' t k p_t_wf@(WFFTBasic gg b) x t_x
  = WFFTBasic (concatF (FCons x t_x g) g') b
lem_weaken_wfft g g' t k_t pf_t_wf@(WFFTFV1 gg a' k') x t_x = case g' of
  FEmpty               -> WFFTFV2 g a' k' pf_t_wf 
                            (x ? lem_ffreeTV_bound_in_fenv g t k_t pf_t_wf x) t_x
  (FConsT _a' _k' g'') -> WFFTFV1 (concatF (FCons x t_x g) g'')   a' k'
lem_weaken_wfft g g' t k_t pf_t_wf@(WFFTFV2 gg a' k' pf_gg_a' z t_z) x t_x = case g' of
  FEmpty             -> WFFTFV2 g a' k_t pf_t_wf 
                            (x ? lem_ffreeTV_bound_in_fenv g t k_t pf_t_wf x) t_x 
  (FCons _z _tz g'') -> WFFTFV2 (concatF (FCons x t_x g) g'') a' k' 
                            (lem_weaken_wfft g g'' (FTBasic (FTV a')) k' pf_gg_a' x t_x)  z t_z
lem_weaken_wfft g g' t k_t pf_t_wf@(WFFTFV3 gg a k pf_gg_a a' k') x t_x = case g' of
  FEmpty               -> WFFTFV2 g a k_t pf_t_wf 
                            (x ? lem_ffreeTV_bound_in_fenv g t k_t pf_t_wf x) t_x 
  (FConsT _a' _k' g'') -> WFFTFV3 (concatF (FCons x t_x g) g'') a k
                            (lem_weaken_wfft g g'' (FTBasic (FTV a)) k pf_gg_a x t_x)   a' k'
lem_weaken_wfft g g' _ _ (WFFTFunc _ t1 k1 p_gg_t1 t2 k2 p_gg_t2) x t_x
  = WFFTFunc (concatF (FCons x t_x g) g') t1 k1 (lem_weaken_wfft g g' t1 k1 p_gg_t1 x t_x)
                                          t2 k2 (lem_weaken_wfft g g' t2 k2 p_gg_t2 x t_x)
lem_weaken_wfft g g' tt kk pf_env_tt@(WFFTPoly env k t k_t nms mk_pf_aenv_t) x t_x
  = WFFTPoly (concatF (FCons x t_x g) g') k t k_t nms' mk_pf_aenv'_t
      where
        {-@ mk_pf_aenv'_t :: { a:Vname | NotElem a nms' }
                       -> ProofOf(WFFT (FConsT a k (concatF (FCons x t_x g) g')) (unbindFT a t) k_t) @-}
        mk_pf_aenv'_t a = lem_weaken_wfft g (FConsT (a ? lem_in_env_concatF g g' a) k g') 
                                          (unbindFT a t) k_t (mk_pf_aenv_t a) x t_x
        nms'         = x:(unionFEnv nms (concatF g g'))
lem_weaken_wfft g g' _ _ (WFFTKind env t pf_t_base) x t_x
  = WFFTKind (concatF (FCons x t_x g) g') t (lem_weaken_wfft g g' t Base pf_t_base x t_x)

{-@ lem_weaken_tv_wfft :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
      -> t:FType -> k_t:Kind -> { pf_t_wf:WFFT | propOf pf_t_wf == WFFT (concatF g g') t k_t }
      -> { a:Vname | not (in_envF a g) && not (in_envF a g') } -> k:Kind
      -> { pf:WFFT | propOf pf == (WFFT (concatF (FConsT a k g) g') t k_t) } 
       / [ftsize t, fenvsize g', ksize k_t] @-}
lem_weaken_tv_wfft :: FEnv -> FEnv -> FType -> Kind -> WFFT -> Vname -> Kind -> WFFT
lem_weaken_tv_wfft g g' t k_t p_t_wf@(WFFTBasic gg b) a k
  = WFFTBasic (concatF (FConsT a k g) g') b
lem_weaken_tv_wfft g g' t k_t pf_t_wf@(WFFTFV1 gg a' k') a k = case g' of
  FEmpty               -> WFFTFV3 g a' k_t pf_t_wf 
                            (a ? lem_ffreeTV_bound_in_fenv g t k_t pf_t_wf a) k
  (FConsT _a' _k' g'') -> WFFTFV1 (concatF (FConsT a k g) g'')  a' k'
lem_weaken_tv_wfft g g' t k_t pf_t_wf@(WFFTFV2 gg a' k' pf_gg_a' z t_z)   a k = case g' of
  FEmpty             -> WFFTFV3 g a' k_t pf_t_wf 
                            (a ? lem_ffreeTV_bound_in_fenv g t k_t pf_t_wf a) k
  (FCons _z _tz g'') -> WFFTFV2 (concatF (FConsT a k g) g'') a' k' 
                            (lem_weaken_tv_wfft g g'' (FTBasic (FTV a')) k' pf_gg_a' a k)  z t_z
lem_weaken_tv_wfft g g' t k_t pf_t_wf@(WFFTFV3 gg a' k' pf_gg_a' a'' k'') a k = case g' of
  FEmpty               -> WFFTFV3 g a' k_t pf_t_wf 
                            (a ? lem_ffreeTV_bound_in_fenv g t k_t pf_t_wf a) k
  (FConsT _a' _k' g'') -> WFFTFV3 (concatF (FConsT a k g) g'') a' k'
                            (lem_weaken_tv_wfft g g'' (FTBasic (FTV a')) k' pf_gg_a' a k)   a'' k''
lem_weaken_tv_wfft g g' _ _ (WFFTFunc _ t1 k1 p_gg_t1 t2 k2 p_gg_t2) a k
  = WFFTFunc (concatF (FConsT a k g) g') t1 k1 (lem_weaken_tv_wfft g g' t1 k1 p_gg_t1 a k)
                                         t2 k2 (lem_weaken_tv_wfft g g' t2 k2 p_gg_t2 a k)
lem_weaken_tv_wfft g g' tt kk pf_env_tt@(WFFTPoly env k' t' k_t' nms mk_pf_a'env_t') a k
  = WFFTPoly (concatF (FConsT a k g) g') k' t' k_t' nms' mk_pf_a'env'_t'
      where
        {-@ mk_pf_a'env'_t' :: { a':Vname | NotElem a' nms' }
                 -> ProofOf(WFFT (FConsT a' k' (concatF (FConsT a k g) g')) (unbindFT a' t') k_t') @-}
        mk_pf_a'env'_t' a' = lem_weaken_tv_wfft g (FConsT (a' ? lem_in_env_concatF g g' a') k' g') 
                                                (unbindFT a' t') k_t' (mk_pf_a'env_t' a') a k
        nms'               = a:(unionFEnv nms (concatF g g'))
lem_weaken_tv_wfft g g' _ _ (WFFTKind env t pf_t_base) a k
  = WFFTKind (concatF (FConsT a k g) g') t (lem_weaken_tv_wfft g g' t Base pf_t_base a k)

{-@ lem_weaken_many_wfft :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
      -> t:FType -> k:Kind -> ProofOf(WFFT g t k) -> ProofOf(WFFT (concatF g g') t k) @-}
lem_weaken_many_wfft :: FEnv -> FEnv -> FType -> Kind -> WFFT -> WFFT
lem_weaken_many_wfft g FEmpty            t k p_g_t = p_g_t 
lem_weaken_many_wfft g (FCons x t_x g')  t k p_g_t 
  = lem_weaken_wfft (concatF g g') FEmpty t k p_gg'_t x t_x 
     where
       p_gg'_t = lem_weaken_many_wfft g g' t k p_g_t 
lem_weaken_many_wfft g (FConsT a k_a g') t k p_g_t 
  = lem_weaken_tv_wfft (concatF g g') FEmpty t k p_gg'_t a k_a  
     where
       p_gg'_t = lem_weaken_many_wfft g g' t k p_g_t 

-- -- -- -- -- -- -- -- -- -- -- -- ---
-- -- Part of the Substitution Lemma --
-- -- -- -- -- -- -- -- -- -- -- -- ---

-- System F types have only type variables because there are no refineemnts, so there's only 
--     one version of the substitution lemmas:
{-@ lem_subst_tv_wfft :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> { a:Vname | not (in_envF a g) && not (in_envF a g') } -> t_a:FType -> k_a:Kind 
        -> ProofOf(WFFT g t_a k_a) -> t:FType -> k:Kind 
        -> { p_env_t:WFFT | propOf p_env_t == WFFT (concatF (FConsT a k_a g) g') t k }
        -> ProofOf(WFFT (concatF g (fesubFV a t_a g')) (ftsubFV a t_a t) k) 
         / [ftsize t, fenvsize g', ksize k] @-}
lem_subst_tv_wfft :: FEnv -> FEnv -> Vname -> FType -> Kind -> WFFT 
                          -> FType -> Kind -> WFFT -> WFFT
lem_subst_tv_wfft g g' a t_a k_a pf_g_ta t k (WFFTBasic _env b) -- _env = g'; a:k_a; g
  = WFFTBasic (concatF g (fesubFV a t_a g')) b
lem_subst_tv_wfft g g' a t_a k_a pf_g_ta t k (WFFTFV1 _env a' k')
  = case g' of
      FEmpty             -> pf_g_ta
      (FConsT _a _k g'') -> WFFTFV1 (concatF g (fesubFV a t_a g'')) 
                                    (a' ? lem_in_env_concatF g g'' a') k
lem_subst_tv_wfft g g' a t_a k_a pf_g_ta t k p_g_t@(WFFTFV2 _env a'_ k' pf_env_a' w_ t_w)
  = case g' of
      (FEmpty)           -> impossible "" 
      (FCons _w _tw g'') -> case ( a == a'_ ) of
        (True)  -> case ( k_a, k ) of
          (Base, Star) -> WFFTKind (concatF g (fesubFV a t_a g')) t_a p_env''_ta
            where
              p_env''_ta = lem_weaken_many_wfft g (fesubFV a t_a g') t_a k_a pf_g_ta 
          (Star, Base) -> impossible ("by lemma" ? lem_kind_for_tvF g g' a k_a
                                           ? lem_wf_ftv_kindF (concatF (FConsT a k_a g) g') a k p_g_t) 
          _            -> lem_weaken_many_wfft g (fesubFV a t_a g') t_a k_a pf_g_ta
        (False) -> WFFTFV2 (concatF g (fesubFV a t_a g'')) a' k' p_gg''_a' w (ftsubFV a t_a t_w)
          where
            a'          = a'_ -- ? lem_in_env_concatF g                g''  a'_  -- need ???
            w           = w_  ----- ? lem_in_env_concatF g g'' w_
            p_gg''_a'   = lem_subst_tv_wfft g g'' a t_a k_a pf_g_ta (FTBasic (FTV a')) k' pf_env_a'  
      (FConsT _ _ g'')   -> impossible "" 
lem_subst_tv_wfft g g' a t_a k_a pf_g_ta t k p_g_t@(WFFTFV3 _env a'_ k' pf_env_a' a1_ k1)
  = case g' of
      (FEmpty)           -> pf_env_a'
      (FConsT _a1 _k1 g'') -> case ( a == a'_ ) of
        (True)  -> case ( k_a, k ) of
          (Base, Star) -> WFFTKind (concatF g (fesubFV a t_a g')) t_a p_env''_ta
            where
              p_env''_ta = lem_weaken_many_wfft g (fesubFV a t_a g') t_a k_a pf_g_ta 
          (Star, Base) -> impossible ("by lemma" ? lem_kind_for_tvF g g' a k_a
                                           ? lem_wf_ftv_kindF (concatF (FConsT a k_a g) g') a k p_g_t)
          _            -> lem_weaken_many_wfft g (fesubFV a t_a g') t_a k_a pf_g_ta
        (False) -> WFFTFV3 (concatF g (fesubFV a t_a g'')) a' k' p_gg''_a' a1 k1 
          where
            a'          = a'_ ---- ? lem_in_env_concatF g                g''  a'_
            a1          = a1_ ---- ? lem_in_env_concatF g g'' a1_
            p_gg''_a'   = lem_subst_tv_wfft g g'' a t_a k_a pf_g_ta (FTBasic (FTV a')) k' pf_env_a'  
lem_subst_tv_wfft g g' a t_a k_a pf_g_ta  t k (WFFTFunc _env t1 k1 p_env_t1 t2 k2 p_env_t2)
  = WFFTFunc (concatF g (fesubFV a t_a g')) (ftsubFV a t_a t1) k1 p_g'g_t1ta 
                                            (ftsubFV a t_a t2) k2 p_g'g_t2ta
      where
        p_g'g_t1ta = lem_subst_tv_wfft g g' a t_a k_a pf_g_ta t1 k1 p_env_t1
        p_g'g_t2ta = lem_subst_tv_wfft g g' a t_a k_a pf_g_ta t2 k2 p_env_t2  
lem_subst_tv_wfft g g' a t_a k_a p_g_ta  t k (WFFTPoly _env k' t' k_t' nms  mk_p_a'env_t')
  = WFFTPoly (concatF g (fesubFV a t_a g')) k' (ftsubFV a t_a t') k_t' nms' mk_p_a'g'g_t'ta
      where
        {-@ mk_p_a'g'g_t'ta :: { a':Vname | NotElem a' nms' }
                -> ProofOf(WFFT (FConsT a' k' (concatF g (fesubFV a t_a g'))) 
                                (unbindFT a' (ftsubFV a t_a t')) k_t') @-}
        mk_p_a'g'g_t'ta a' = lem_subst_tv_wfft g (FConsT a' k' g') a t_a k_a p_g_ta 
                                               (unbindFT a' t') k_t' (mk_p_a'env_t' a')
                                               ? lem_commute_ftsubFV_unbindFT a 
                                                   (t_a ? lem_wfft_islcft g t_a k_a p_g_ta) a' t'
        nms'               = a:(unionFEnv nms (concatF g g'))
lem_subst_tv_wfft g g' a t_a k_a pf_g_ta t k (WFFTKind _env _t pf_env_t_base) 
  = WFFTKind (concatF g (fesubFV a t_a g')) (ftsubFV a t_a t) p_gg'_tta_base
      where
        p_gg'_tta_base = lem_subst_tv_wfft g g' a t_a k_a pf_g_ta t Base pf_env_t_base

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 
-- Consequences of the System F Typing Judgments -
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 

{-@ lem_ftyping_wfft :: g:FEnv -> e:Expr -> t:FType -> { p_e_t:HasFType | propOf p_e_t == HasFType g e t }
                               -> ProofOf(WFFE g) -> ProofOf(WFFT g t Star) 
                                / [esize e, fenvsize g] @-} 
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
lem_ftyping_wfft g e t (FTPrm _g c) p_wf_g  = lem_wfft_erase_ty g c
lem_ftyping_wfft g e t (FTAbs _g t_x k_x pf_g_tx e' t' nms mk_pf_e'_t') pf_wf_g
    = WFFTFunc g t_x k_x pf_g_tx t' Star pf_g_t'
        where
          y        = fresh_varF nms g
          pf_wf_yg = WFFBind g pf_wf_g y t_x k_x pf_g_tx  
          pf_yg_t' = lem_ftyping_wfft (FCons y t_x g) (unbind y e') t' (mk_pf_e'_t' y) pf_wf_yg
          pf_g_t'  = lem_strengthen_wfft g y t_x FEmpty t' Star pf_yg_t'
lem_ftyping_wfft g e t (FTApp _g e1 t_x t' p_e1_txt' e2 p_e2_tx) p_wf_g
    = if ( k' == Star ) then p_g_t' else WFFTKind g t' p_g_t'
        where
          p_g_txt' = lem_ftyping_wfft g e1 (FTFunc t_x t') p_e1_txt' p_wf_g
          (WFFTFunc _ _ _ p_g_tx _ k' p_g_t') = lem_wfftfunc_for_wf_ftfunc g t_x t' Star p_g_txt'
lem_ftyping_wfft g e t (FTAbsT _g k e' t' nms mk_pf_a'g_e'_t') pf_wf_g
    = WFFTPoly g k t' Star nms' mk_pf_a'g_t'
        where
          {-@ mk_pf_a'g_t' :: { a':Vname | NotElem a' nms' }
                -> ProofOf(WFFT (FConsT a' k g) (unbindFT a' t') Star) @-}
          mk_pf_a'g_t' a' = lem_ftyping_wfft (FConsT a' k g) (unbind_tv a' e') (unbindFT a' t')
                                             (mk_pf_a'g_e'_t' a') pf_wf_a'g
            where
              pf_wf_a'g   = WFFBindT g pf_wf_g a' k
          nms'            = unionFEnv nms g
lem_ftyping_wfft g e t p_e_t@(FTAppT _g e' k t' pf_e'_at' liqt pf_g_erliqt) pf_wf_g
   = if (k_t' == Star) then pf_g_t'liqt else WFFTKind g t pf_g_t'liqt
       where
         pf_g_at'    = lem_ftyping_wfft g e' (FTPoly k t') pf_e'_at' pf_wf_g
         (WFFTPoly _ _k _t' k_t' nms mk_pf_a'g_t') = lem_wfftpoly_for_wf_ftpoly g k t' pf_g_at'
         a'          = fresh_varF nms g
         pf_g_t'liqt = lem_subst_tv_wfft g FEmpty a' (erase liqt) k 
                                      pf_g_erliqt (unbindFT a' t') k_t' (mk_pf_a'g_t' a')
                                      ? lem_ftsubFV_unbindFT a' (erase liqt) (t'
                                      ? lem_ffreeTV_bound_in_fenv g (FTPoly k t') Star pf_g_at' a')
lem_ftyping_wfft g e t (FTLet _g e_x t_x p_ex_tx e' _t nms mk_p_e'_t) p_wf_g  
    = lem_strengthen_wfft g y t_x FEmpty t Star pf_yg_t
        where 
          y        = fresh_varF nms g
          pf_g_tx = lem_ftyping_wfft g e_x t_x p_ex_tx p_wf_g
          p_wf_yg = WFFBind g p_wf_g y t_x Star pf_g_tx
          pf_yg_t = lem_ftyping_wfft (FCons y t_x g) (unbind y e') t (mk_p_e'_t y) p_wf_yg
lem_ftyping_wfft g e t (FTAnn _g e' _t liqt p_e'_t) p_wf_g
    = lem_ftyping_wfft g e' t p_e'_t p_wf_g
