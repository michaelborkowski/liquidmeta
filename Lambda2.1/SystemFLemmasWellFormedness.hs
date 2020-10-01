{-# LANGUAGE GADTs #-}

{-@ LIQUID "--no-termination" @-}  -- TODO: assume
{-@ LIQUID "--no-totality" @-}     -- TODO: assume
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SystemFLemmasWellFormedness where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import PrimitivesFTyping
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness

{-@ reflect foo20 @-}
foo20 x = Just x
foo20 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development for the Underlying STLC :: Technical LEMMAS
------------------------------------------------------------------------------

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 
-- Consequences of the System F Well-Formedness Judgments -
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 

{-@ lem_change_var_wffe :: g:FEnv -> { x:Vname | not (in_envF x g) } -> t_x:FType
      -> { g':FEnv | not (in_envF x g') && Set_emp (Set_cap (bindsF g) (bindsF g')) }
      -> ProofOf(WFFE (concatF (FCons x t_x g) g'))
      -> { y:Vname | not (in_envF y g) && not (in_envF y g') }
      -> ProofOf(WFFE (concatF (FCons y t_x g)  g')) @-}
lem_change_var_wffe :: FEnv -> Vname -> FType -> FEnv -> WFFE -> Vname -> WFFE
{- -}
lem_change_var_wffe g x t_x FEmpty           p_env_wf y = case p_env_wf of
  (WFFBind  _g p_g_wf _x _tx k_x p_g_tx)         -> WFFBind g p_g_wf y t_x k_x p_g_tx
lem_change_var_wffe g x t_x (FCons z t_z g') p_env_wf y = case p_env_wf of
  (WFFBind env' p_env'_wf _z _tz k_z p_env'_tz)  -> WFFBind env'' p_env''_wf z t_z k_z p_env''_tz
    where
      env''      = concatF (FCons y t_x g) g'
      p_env''_wf = lem_change_var_wffe g x t_x g' p_env'_wf y
      p_env''_tz = lem_change_var_wfft g x t_x g' t_z k_z p_env'_tz y
lem_change_var_wffe g x t_x (FConsT a k g') p_env_wf y  = case p_env_wf of
  (WFFBindT env' p_env'_wf _a _k)                -> WFFBindT env'' p_env''_wf a k
    where
      env''      = concatF (FCons y t_x g) g'
      p_env''_wf = lem_change_var_wffe g x t_x g' p_env'_wf y
{- -}

{-@ lem_change_tvar_wffe :: g:FEnv -> { a:Vname | not (in_envF a g) } -> k:Kind
      -> { g':FEnv | not (in_envF a g') && Set_emp (Set_cap (bindsF g) (bindsF g')) }
      -> ProofOf(WFFE (concatF (FConsT a k g) g'))
      -> { a':Vname | not (in_envF a' g) && not (in_envF a' g') }
      -> ProofOf(WFFE (concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g'))) @-}
lem_change_tvar_wffe :: FEnv -> Vname -> Kind -> FEnv -> WFFE -> Vname -> WFFE
{- -}
lem_change_tvar_wffe g a k FEmpty           p_env_wf a'  = case p_env_wf of
  (WFFBindT _g p_g_wf _a _k)                    -> WFFBindT g p_g_wf a' k
lem_change_tvar_wffe g a k (FCons z t_z g') p_env_wf a'  = case p_env_wf of
  (WFFBind env' p_env'_wf _z _tz k_z p_env'_tz) -> WFFBind env'' p_env''_wf z 
                                                     (ftsubFV a (FTBasic (FTV a')) t_z) k_z p_env''_tz
    where
      env''      = concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g')
      p_env''_wf = lem_change_tvar_wffe g a k g' p_env'_wf a'
      p_env''_tz = lem_change_tvar_wfft g a k g' t_z k_z p_env'_tz a'
lem_change_tvar_wffe g a k (FConsT a1 k1 g') p_env_wf a' = case p_env_wf of
  (WFFBindT env' p_env'_wf _a1 _k1)             -> WFFBindT env'' p_env''_wf a1 k1
    where
      env''      = concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g')
      p_env''_wf = lem_change_tvar_wffe g a k g' p_env'_wf a'
{- -}

{-@ lem_change_var_wfft :: g:FEnv -> { x:Vname | not (in_envF x g) } -> t_x:FType
      -> { g':FEnv | not (in_envF x g') && Set_emp (Set_cap (bindsF g) (bindsF g')) }
      -> t:FType -> k:Kind -> { p_t_wf:WFFT | propOf p_t_wf == WFFT (concatF (FCons x t_x g) g') t k }
      -> { y:Vname | not (in_envF y g) && not (in_envF y g')  }
      -> { pf:WFFT | propOf pf == (WFFT (concatF (FCons y t_x g) g') t k)
                     && (wfftypSize pf == wfftypSize p_t_wf) } @-} -- / [wfftypSize p_t_wf ] @-}
lem_change_var_wfft :: FEnv -> Vname -> FType -> FEnv -> FType -> Kind -> WFFT -> Vname -> WFFT
--lem_change_var_wfft = undefined
{- -}
lem_change_var_wfft g x t_x g' t k p_t_wf@(WFFTBasic gg b) y
  = WFFTBasic (concatF (FCons y t_x g) g') b
lem_change_var_wfft g x t_x g' t k (WFFTFV1 gg a' k') y = case g' of
  (FConsT _a' _k' g'') -> WFFTFV1 (concatF (FCons y t_x g) g'') a' k'
lem_change_var_wfft g x t_x g' t k (WFFTFV2 gg a' k' pf_gg_a' z t_z) y = case g' of
  FEmpty {- x == z  -} -> case ( x == a' ) of
      True               -> impossible "it is"
      False              -> WFFTFV2 gg a' k' pf_gg_a' --a' k1
                               (y ? lem_ffreeTV_bound_in_fenv gg (FTBasic (FTV a')) k' pf_gg_a' y) t_z
--  FEmpty             -> WFFTFV2 g a' k' pf_gg_a' y t_z
  (FCons _z _tz g'') -> WFFTFV2 (concatF (FCons y t_x g) g'') a' k' 
                          (lem_change_var_wfft g x t_x g'' (FTBasic (FTV a')) k' pf_gg_a' y) z t_z 
lem_change_var_wfft g x t_x g' _ _ (WFFTFV3 gg a k pf_gg_a a' k') y = case g' of
  FEmpty               -> impossible ""
  (FConsT _a' _k' g'') -> WFFTFV3 (concatF (FCons y t_x g) g'') a k
                            (lem_change_var_wfft g x t_x g'' (FTBasic (FTV a)) k pf_gg_a y) a' k'
lem_change_var_wfft g x t_x g' _ _ (WFFTFunc _ t1 k1 p_gg_t1 t2 k2 p_gg_t2) y
  = WFFTFunc (concatF (FCons y t_x g) g') t1 k1 (lem_change_var_wfft g x t_x g' t1 k1 p_gg_t1 y)
                                          t2 k2 (lem_change_var_wfft g x t_x g' t2 k2 p_gg_t2 y)
lem_change_var_wfft g x t_x g' tt kk pf_env_tt@(WFFTPoly env a k t k_t a' pf_a'env_t) y 
  = WFFTPoly (concatF (FCons y t_x g) g') a k t k_t a'' pf_a''env'_t
      where
        a''_         = fresh_var_excludingF (concatF (FCons x t_x g) g') y
        a''          = a''_ ? lem_in_env_concatF (FCons x t_x g) g' a''_
                            ? lem_in_env_concatF (FCons y t_x g) g' a''_
                            ? lem_ffreeTV_bound_in_fenv env tt kk pf_env_tt a''_
        pf_a''env_t  = lem_change_tvar_wfft (concatF (FCons x t_x g) g') a' k FEmpty
                                            (unbindFT a a' t) k_t pf_a'env_t a''  
        pf_a''env'_t = lem_change_var_wfft g x t_x (FConsT a'' k g') (unbindFT a a'' t) k_t 
                                  (pf_a''env_t ? lem_ftsubFV_unbindFT a a' (FTBasic (FTV a'')) t) y
lem_change_var_wfft g x t_x g' _ _ (WFFTKind env t pf_t_base) y
  = WFFTKind (concatF (FCons y t_x g) g') t (lem_change_var_wfft g x t_x g' t Base pf_t_base y)
{- -}

{-@ lem_change_tvar_wfft :: g:FEnv -> { a:Vname | not (in_envF a g) } -> k:Kind
      -> { g':FEnv | not (in_envF a g') && Set_emp (Set_cap (bindsF g) (bindsF g')) }
      -> t:FType -> k_t:Kind 
      -> { p_t_wf:WFFT | propOf p_t_wf == WFFT (concatF (FConsT a k g) g') t k_t }
      -> { a':Vname | not (in_envF a' g) && not (in_envF a' g') }
      -> { pf:WFFT | propOf pf == (WFFT (concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g')) 
                                        (ftsubFV a (FTBasic (FTV a')) t) k_t)
                     && (wfftypSize pf == wfftypSize p_t_wf) } @-} -- / [wfftypSize p_t_wf ] @-}
lem_change_tvar_wfft :: FEnv -> Vname -> Kind -> FEnv -> FType -> Kind -> WFFT -> Vname -> WFFT
--lem_change_tvar_wfft = undefined
{- -}
lem_change_tvar_wfft g a k g' _ _ p_t_wf@(WFFTBasic gg b) a'
  = WFFTBasic (concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g')) b
lem_change_tvar_wfft g a k g' _ _ (WFFTFV1 gg a0 k0) a' = case g' of
  FEmpty               -> WFFTFV1 g a' k
  (FConsT _a' _k' g'') -> WFFTFV1 (concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g'')) a0 k0
lem_change_tvar_wfft g a k g' _ _ (WFFTFV2 gg a0 k0 pf_gg_a0 z t_z) a' = case g' of
  FEmpty               -> impossible ""
  (FCons _z _tz g'')   -> case ( a == a0 ) of 
      True               -> WFFTFV2 (concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g'')) a' k0
                              (lem_change_tvar_wfft g a k g'' (FTBasic (FTV a0)) k0 pf_gg_a0 a')
                              z (ftsubFV a (FTBasic (FTV a')) t_z) 
                              ? toProof (     ftsubFV a (FTBasic (FTV a')) (FTBasic (FTV a0)) 
                                          === FTBasic (FTV a') )
      False              -> WFFTFV2 (concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g'')) a0 k0 
                              (lem_change_tvar_wfft g a k g'' (FTBasic (FTV a0)) k0 pf_gg_a0 a') 
                              z (ftsubFV a (FTBasic (FTV a')) t_z)
lem_change_tvar_wfft g a k g' _ _ (WFFTFV3 gg a0 k0 pf_gg_a0 a1 k1) a' = case g' of
  FEmpty {- a == a1 -} -> case ( a == a0 ) of
      True               -> impossible "it is"
      False              -> WFFTFV3 gg a0 k0 pf_gg_a0 --a' k1
                               (a' ? lem_ffreeTV_bound_in_fenv gg (FTBasic (FTV a0)) k0 pf_gg_a0 a') k1
  (FConsT _a1 _k1 g'') -> case ( a == a0 ) of
      True               -> WFFTFV3 (concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g'')) a' k0
                              (lem_change_tvar_wfft g a k g'' 
                                                  {-(ftsubFV a-} (FTBasic (FTV a0)) {-(FTBasic (FTV a')'))-}
                                                    k0 pf_gg_a0 a') a1 k1
      False              -> WFFTFV3 (concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g'')) a0 k0
                              (lem_change_tvar_wfft g a k g'' 
                                                    (ftsubFV a (FTBasic (FTV a1)) (FTBasic (FTV a0)) )
                                                    k0 pf_gg_a0 a') a1 k1
lem_change_tvar_wfft g a k g' _ _ (WFFTFunc _ t1 k1 p_gg_t1 t2 k2 p_gg_t2) a1
  = WFFTFunc (concatF (FConsT a1 k g) (fesubFV a (FTBasic (FTV a1)) g')) 
             (ftsubFV a (FTBasic (FTV a1)) t1) k1 (lem_change_tvar_wfft g a k g' t1 k1 p_gg_t1 a1)
             (ftsubFV a (FTBasic (FTV a1)) t2) k2 (lem_change_tvar_wfft g a k g' t2 k2 p_gg_t2 a1)
lem_change_tvar_wfft g a k g' tt kk pf_env_tt@(WFFTPoly env a' k' t k_t a'' pf_a''env_t) a1 
  = WFFTPoly (concatF (FConsT a1 k g) (fesubFV a (FTBasic (FTV a1)) g')) 
             a' k' (ftsubFV a (FTBasic (FTV a1)) t) k_t a''' pf_a'''env'_t
      where
        a'''_         = fresh_var_excludingF (concatF (FConsT a k g) g') a1
        a'''          = a'''_ ? lem_in_env_concatF (FConsT a  k g) g' a'''_
                              ? lem_in_env_concatF (FConsT a1 k g) g' a'''_
                              ? lem_ffreeTV_bound_in_fenv env tt kk pf_env_tt a'''_
        pf_a'''env_t  = lem_change_tvar_wfft (concatF (FConsT a k g) g') a'' k' FEmpty
                                             (unbindFT a' a'' t) k_t pf_a''env_t a'''  
        pf_a'''env'_t = lem_change_tvar_wfft g a k (FConsT a''' k' g') 
                                  {-(ftsubFV a (FTBasic (FTV a1))-} (unbindFT a' a''' t){-)-} k_t 
                                  (pf_a'''env_t ? lem_ftsubFV_unbindFT a' a'' (FTBasic (FTV a''')) t) a1
                                  ? lem_commute_ftsubFV_unbindFT a a1 a' a''' t
lem_change_tvar_wfft g a k g' _ _ (WFFTKind env t pf_t_base) a1
  = WFFTKind (concatF (FConsT a1 k g) (fesubFV a (FTBasic (FTV a1)) g')) 
             (ftsubFV a (FTBasic (FTV a1)) t)
             (lem_change_tvar_wfft g a k g' t Base pf_t_base a1)
{- -}

{-@ lem_weaken_wfft :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
      -> t:FType -> k:Kind -> { p_t_wf:WFFT | propOf p_t_wf == WFFT (concatF g g') t k }
      -> { x:Vname | not (in_envF x g) && not (in_envF x g') } -> t_x:FType
      -> { pf:WFFT | propOf pf == (WFFT (concatF (FCons x t_x g) g') t k) } @-}
-- not true with WFFTFV rules:    && (wfftypSize pf == wfftypSize p_t_wf) } @-} -- / [wfftypSize p_t_wf ] @-}
lem_weaken_wfft :: FEnv -> FEnv -> FType -> Kind -> WFFT -> Vname -> FType -> WFFT
--lem_weaken_wfft = undefined
{- -}
lem_weaken_wfft g g' t k p_t_wf@(WFFTBasic gg b) x t_x
  = WFFTBasic (concatF (FCons x t_x g) g') b
lem_weaken_wfft g g' t k_t pf_t_wf@(WFFTFV1 gg a' k') x t_x = case g' of
  FEmpty               -> WFFTFV2 g a' k' pf_t_wf 
                            (x ? lem_ffreeTV_subset_bindsF g t k_t pf_t_wf) t_x
  (FConsT _a' _k' g'') -> WFFTFV1 (concatF (FCons x t_x g) g'') a' k'
lem_weaken_wfft g g' t k_t pf_t_wf@(WFFTFV2 gg a' k' pf_gg_a' z t_z) x t_x = case g' of
  FEmpty             -> WFFTFV2 g {-(FCons z t_z gg)-} a' k_t pf_t_wf 
                            (x ? lem_ffreeTV_subset_bindsF g t k_t pf_t_wf) t_x 
  (FCons _z _tz g'') -> WFFTFV2 (concatF (FCons x t_x g) g'') a' k' 
                          (lem_weaken_wfft g g'' (FTBasic (FTV a')) k' pf_gg_a' x t_x) z t_z 
lem_weaken_wfft g g' t k_t pf_t_wf@(WFFTFV3 gg a k pf_gg_a a' k') x t_x = case g' of
  FEmpty               -> WFFTFV2 g {-(FConsT a' k' gg)-} a k_t pf_t_wf 
                            (x ? lem_ffreeTV_subset_bindsF g t k_t pf_t_wf) t_x 
  (FConsT _a' _k' g'') -> WFFTFV3 (concatF (FCons x t_x g) g'') a k
                            (lem_weaken_wfft g g'' (FTBasic (FTV a)) k pf_gg_a x t_x) a' k'
lem_weaken_wfft g g' _ _ (WFFTFunc _ t1 k1 p_gg_t1 t2 k2 p_gg_t2) x t_x
  = WFFTFunc (concatF (FCons x t_x g) g') t1 k1 (lem_weaken_wfft g g' t1 k1 p_gg_t1 x t_x)
                                          t2 k2 (lem_weaken_wfft g g' t2 k2 p_gg_t2 x t_x)
lem_weaken_wfft g g' tt kk pf_env_tt@(WFFTPoly env a k t k_t a' pf_a'env_t) x t_x
  = WFFTPoly (concatF (FCons x t_x g) g') a k t k_t a'' pf_a''env'_t
      where
        a''_         = fresh_varF (concatF (FCons x t_x g) g') 
        a''          = a''_ ? lem_in_env_concatF              g  g' a''_
                            ? lem_in_env_concatF (FCons x t_x g) g' a''_
                            ? lem_ffreeTV_bound_in_fenv env tt kk pf_env_tt a''_
        pf_a''env_t  = lem_change_tvar_wfft (concatF g g') a' k FEmpty
                                            (unbindFT a a' t) k_t pf_a'env_t a''  
        pf_a''env'_t = lem_weaken_wfft g (FConsT a'' k g') (unbindFT a a'' t) k_t 
                              (pf_a''env_t ? lem_ftsubFV_unbindFT a a' (FTBasic (FTV a'')) t) x t_x
lem_weaken_wfft g g' _ _ (WFFTKind env t pf_t_base) x t_x
  = WFFTKind (concatF (FCons x t_x g) g') t (lem_weaken_wfft g g' t Base pf_t_base x t_x)
{- -}

{-@ lem_weaken_tv_wfft :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
      -> t:FType -> k_t:Kind -> { pf_t_wf:WFFT | propOf pf_t_wf == WFFT (concatF g g') t k_t }
      -> { a:Vname | not (in_envF a g) && not (in_envF a g') } -> k:Kind
      -> { pf:WFFT | propOf pf == (WFFT (concatF (FConsT a k g) g') t k_t) } @-}
--                     && (wfftypSize pf == wfftypSize pf_t_wf) } @-} -- / [wfftypSize p_t_wf ] @-}
lem_weaken_tv_wfft :: FEnv -> FEnv -> FType -> Kind -> WFFT -> Vname -> Kind -> WFFT
--lem_weaken_tv_wfft = undefined
{- -}
lem_weaken_tv_wfft g g' t k_t p_t_wf@(WFFTBasic gg b) a k
  = WFFTBasic (concatF (FConsT a k g) g') b
lem_weaken_tv_wfft g g' t k_t pf_t_wf@(WFFTFV1 gg a' k') a k = case g' of
  FEmpty               -> WFFTFV3 g a' k_t pf_t_wf 
                            (a ? lem_ffreeTV_subset_bindsF g t k_t pf_t_wf) k
  (FConsT _a' _k' g'') -> WFFTFV1 (concatF (FConsT a k g) g'') a' k'
lem_weaken_tv_wfft g g' t k_t pf_t_wf@(WFFTFV2 gg a' k' pf_gg_a' z t_z)   a k = case g' of
  FEmpty             -> WFFTFV3 g a' k_t pf_t_wf 
                            (a ? lem_ffreeTV_subset_bindsF g t k_t pf_t_wf) k
  (FCons _z _tz g'') -> WFFTFV2 (concatF (FConsT a k g) g'') a' k' 
                            (lem_weaken_tv_wfft g g'' (FTBasic (FTV a')) k' pf_gg_a' a k) z t_z 
lem_weaken_tv_wfft g g' t k_t pf_t_wf@(WFFTFV3 gg a' k' pf_gg_a' a'' k'') a k = case g' of
  FEmpty               -> WFFTFV3 g a' k_t pf_t_wf 
                            (a ? lem_ffreeTV_subset_bindsF g t k_t pf_t_wf) k
  (FConsT _a' _k' g'') -> WFFTFV3 (concatF (FConsT a k g) g'') a' k'
                            (lem_weaken_tv_wfft g g'' (FTBasic (FTV a')) k' pf_gg_a' a k) a'' k''
lem_weaken_tv_wfft g g' _ _ (WFFTFunc _ t1 k1 p_gg_t1 t2 k2 p_gg_t2) a k
  = WFFTFunc (concatF (FConsT a k g) g') t1 k1 (lem_weaken_tv_wfft g g' t1 k1 p_gg_t1 a k)
                                         t2 k2 (lem_weaken_tv_wfft g g' t2 k2 p_gg_t2 a k)
lem_weaken_tv_wfft g g' tt kk pf_env_tt@(WFFTPoly env a' k' t' k_t' a'' pf_a''env_t') a k
  = WFFTPoly (concatF (FConsT a k g) g') a' k' t' k_t' a''' pf_a'''env'_t'
      where
        a'''_          = fresh_varF (concatF (FConsT a k g) g') 
        a'''           = a'''_ ? lem_in_env_concatF             g  g' a'''_
                               ? lem_in_env_concatF (FConsT a k g) g' a'''_
                               ? lem_ffreeTV_bound_in_fenv env tt kk pf_env_tt a'''_
        pf_a'''env_t'  = lem_change_tvar_wfft (concatF g g') a'' k' FEmpty
                                              (unbindFT a' a'' t') k_t' pf_a''env_t' a'''  
        pf_a'''env'_t' = lem_weaken_tv_wfft g (FConsT a''' k' g') (unbindFT a' a''' t') k_t' 
                           (pf_a'''env_t' ? lem_ftsubFV_unbindFT a' a'' (FTBasic (FTV a''')) t') a k
lem_weaken_tv_wfft g g' _ _ (WFFTKind env t pf_t_base) a k
  = WFFTKind (concatF (FConsT a k g) g') t (lem_weaken_tv_wfft g g' t Base pf_t_base a k)
{- -}

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
{-
{-@ lem_subst_tv_wffe :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> { a:Vname | not (in_envF a g) && not (in_envF a g') } -> t_a:FType -> k_a:Kind  
        -> ProofOf(WFFT g t_a k_a) -> ProofOf(WFFE (concatF (FConsT a k_a g) g'))
        -> ProofOf(WFFE (concatF g (fesubFV a t_a g'))) / [fenvSize g'] @-}
lem_subst_tv_wffe :: FEnv -> FEnv -> Vname -> FType -> Kind -> WFFT -> WFFE -> WFFE
lem_subst_tv_wffe g FEmpty  a t_a k_a pf_g_ta p_env_wf
  = case p_env_wf of
      (WFFBind _g p_g_wf _ _ _ _) -> p_g_wf
      (WFFBindT _g p_g_wf _ _)    -> p_g_wf
lem_subst_tv_wffe g (FCons x t_x g') a t_a k_a pf_g_ta p_env_wf
  = case p_env_wf of
      (WFFBind env' p_env'_wf _x _tx _kx p_env'_tx) 
         -> WFFBind env'' p_env''_wf x (tsubFTV a t_a t_x) k_x p_env''_txta
        where
          env''        = concatF g (fesubFV a t_a g')
          p_env''_wf   = lem_subst_tv_wffnv g g' a t_a k_a pf_g_ta p_env'_wf
          p_env''_txta = lem_subst_tv_wfft ...
-}

{-@ lem_subst_tv_wfft :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> { a:Vname | not (in_envF a g) && not (in_envF a g') } -> t_a:FType -> k_a:Kind 
        -> ProofOf(WFFT g t_a k_a) -> ProofOf(WFFE (concatF (FConsT a k_a g) g')) -> t:FType 
        -> k:Kind -> { p_env_t:WFFT | propOf p_env_t == WFFT (concatF (FConsT a k_a g) g') t k }
        -> ProofOf(WFFT (concatF g (fesubFV a t_a g')) (ftsubFV a t_a t) k) / [wfftypSize p_env_t] @-}
lem_subst_tv_wfft :: FEnv -> FEnv -> Vname -> FType -> Kind -> WFFT -> WFFE 
                          -> FType -> Kind -> WFFT -> WFFT
lem_subst_tv_wfft g g' a t_a k_a pf_g_ta p_env_wf t k (WFFTBasic _env b) -- _env = g'; a:k_a; g
  = WFFTBasic (concatF g (fesubFV a t_a g')) b
lem_subst_tv_wfft g g' a t_a k_a pf_g_ta p_env_wf t k (WFFTFV1 _env a' k')
  = case g' of
      FEmpty             -> pf_g_ta
      (FCons  _  _  g'') -> impossible ""
      (FConsT _a _k g'') -> WFFTFV1 (concatF g (fesubFV a t_a g'')) 
                                    (a' ? lem_in_env_concatF (FConsT a k_a g) g'' a'
                                        ? lem_in_env_concatF g g'' a') k
lem_subst_tv_wfft g g' a t_a k_a pf_g_ta p_env_wf t k (WFFTFV2 _env a' k' pf_env_a' w t_w)
  = undefined {-  = case g' of
      (FEmpty)           -> impossible "" {- case ( x == z ) of
                    (True)  -> impossible "it is"
                    (False) -> p_z_t -- ? toProof ( e === (FV z) ) -}
      (FCons _w _tw g'') -> case ( a == a' ) of
                    (True)  -> lem_weaken_ftyp (concatF g g'') FEmpty v_x t p_gg''_vx_tx w t_w 
                                               ? toProof ( e === FV x )
                                 where
                                   p_gg''_wf = lem_subst_tv_wffe ....
                                   p_gg''_ta = lem_subst_tv_wfft g g'' a t_a k_a p_g_ta 

                                                   e t p_z_t
                    (False) -> simpleWFFTV (concatF g (fesubFV a t_a g')) (FTBasic (FTV a')) k' {-
BTVar2 (concatB g g'') (z ? lem_in_env_concatB (BCons x t_x g) g'' z
                                                        ? lem_in_env_concatB g g'' z)
                                      t p_z_tvx (w ? lem_fv_bound_in_benv g v_x t_x p_vx_tx w
                                                   ? lem_in_env_concatB (BCons x t_x g) g'' w   
                                                   ? lem_in_env_concatB g g'' w) t_w
                                 where
                                   p_z_tvx = lem_subst_btyp g g'' x v_x t_x p_vx_tx e t p_z_t -}
      (FConsT _ _ g'')   -> impossible "" -}
lem_subst_tv_wfft g g' a t_a k_a pf_g_ta p_env_wf t k (WFFTFV3 _env a' k' pf_env_a' a1 k1)
  = undefined -- assume


lem_subst_tv_wfft g g' a t_a k_a pf_g_ta p_env_wf t k (WFFTFunc _env t1 k1 p_env_t1 t2 k2 p_env_t2)
  = undefined -- assume
{-  = WFFunc (concatE g (esubFV x v_x g')) z (tsubFV x v_x t_z) p_g'g_tzvx (tsubFV x v_x t') y p_yg'g_t'vx
      where
        {- @ y :: { yy:Vname | t == TFunc z t_z t' } @-}
        y           = y_ ? lem_in_env_esub g' x v_x y_ 
                         ? lem_in_env_concat g  g' y_ 
                         ? lem_in_env_concat (Cons x t_x g) g' y_
                         ? lem_in_env_concat (Cons x t_x g) g' y_
                         ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx y_
                         ---- ? lem_binds_esubFV g' x v_x  ---- if I can erase this, then delete??
        p_xg_wf     = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _) = p_xg_wf
        p_yenv_wf   = WFEBind (concatE (Cons x t_x g) g') p_env_wf y t_z p_env_tz
        p_vx_er_tx  = lem_typing_hasbtype g v_x t_x p_vx_tx p_g_wf
        p_g'g_tzvx  = lem_subst_wf g g'              x v_x t_x p_vx_tx p_env_wf  t_z p_env_tz
        p_yg'g_t'vx = lem_subst_wf g (Cons y t_z g') x v_x t_x p_vx_tx p_yenv_wf (unbindT z y t')  
                         (p_yenv_t' ? lem_erase_concat (Cons x t_x g) g')
                         ? lem_commute_tsubFV_tsubBV1 z (FV y) x v_x t'
                         -- ? toProof ( t === TFunc z t_z t' ) --
                         -- ? lem_erase_concat g (esubFV x v_x g') --
                         -- ? lem_erase_esubFV x v_x g' --}
lem_subst_tv_wfft g g' a t_a k_a p_g_ta p_env_wf t k (WFFTPoly _env a' k' t' k_t' a'' p_a''env_t')
  = undefined -- assume
{-  = WFExis (concatE g (esubFV x v_x g')) z (tsubFV x v_x t_z) p_g'g_tzvx (tsubFV x v_x t') y p_yg'g_t'vx
      where
        y           = y_ ? lem_in_env_esub g' x v_x y_ 
                         ? lem_in_env_concat g  g' y_ 
                         ? lem_in_env_concat (Cons x t_x g) g' y_
                         ? lem_in_env_concat (Cons x t_x g) g' y_
                         ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx y_
        p_xg_wf     = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _) = p_xg_wf
        p_yenv_wf   = WFEBind (concatE (Cons x t_x g) g') p_env_wf y t_z p_env_tz
        p_vx_er_tx  = lem_typing_hasbtype g v_x t_x p_vx_tx p_g_wf
        p_g'g_tzvx  = lem_subst_wf g g'              x v_x t_x p_vx_tx p_env_wf t_z p_env_tz
        p_yg'g_t'vx = lem_subst_wf g (Cons y t_z g') x v_x t_x p_vx_tx p_yenv_wf (unbindT z y t')  
                         (p_yenv_t' ? lem_erase_concat (Cons x t_x g) g')
                         ? lem_commute_tsubFV_tsubBV1 z (FV y) x v_x t'-}
lem_subst_tv_wfft g g' a t_a k_a pf_g_ta p_env_wf t k (WFFTKind _env _t pf_env_t_base) = undefined --assume
