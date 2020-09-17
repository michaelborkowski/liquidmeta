{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module BasicPropsWellFormedness where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import BasicPropsSubstitution
import BasicPropsEnvironments

{-@ reflect foo18 @-}
foo18 :: a -> Maybe a
foo18 x = Just x


------------------------------------------------------------------------------------------
-- | LEMMAS relating REFINEMENT ERASURE and WELL FORMEDNESS notions
------------------------------------------------------------------------------------------

{-@ lem_strengthen_wfft :: g:FEnv -> { x:Vname | not (in_envF x g) } -> t_x:FType 
        -> { g':FEnv | not (in_envF x g') && Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> t:FType -> k:Kind -> ProofOf(WFFT (concatF (FCons x t_x g) g') t k) 
        -> ProofOf(WFFT (concatF g g') t k) @-}
lem_strengthen_wfft :: FEnv -> Vname -> FType -> FEnv -> FType -> Kind -> WFFT -> WFFT
lem_strengthen_wfft g x t_x g' _ _ (WFFTBasic _ b) = WFFTBasic (concatF g g') b
lem_strengthen_wfft g x t_x g' _ _ (WFFTFV1 _ a k) 
  = case g' of 
      (FEmpty)            -> impossible ""
      (FCons z t_z g'')   -> impossible ""
      (FConsT _ _ g'')    -> WFFTFV1 (concatF g g'')
                                     (a ? lem_binds_cons_concatF g g'' x t_x) k 
lem_strengthen_wfft g x t_x g' _ _ (WFFTFV2 _ a k p_g_a y t) 
  = case g' of
      (FEmpty)            -> p_g_a
      (FCons z t_z g'')   -> WFFTFV2 (concatF g g'') a k 
                               (lem_strengthen_wfft g x t_x g'' (FTFV a) k p_g_a) y t
      (FConsT a' k' g'')  -> impossible ""
lem_strengthen_wfft g x t_x g' _ _ (WFFTFV3 _ a k p_g_a a' k') 
  = case g' of
      (FEmpty)            -> impossible ""
      (FCons z t_z g'')   -> impossible ""
      (FConsT a' k' g'')  -> WFFTFV3 (concatF g g'') a k
                               (lem_strengthen_wfft g x t_x g'' (FTFV a) k p_g_a) 
                               (a' ? lem_binds_cons_concatF g g'' x t_x) k'
lem_strengthen_wfft g x t_x g' _ _ (WFFTFunc _ t1 k1 p_xg_t1 t2 k2 p_xg_t2)
  = WFFTFunc (concatF g g') t1 k1 (lem_strengthen_wfft g x t_x g' t1 k1 p_xg_t1)
                            t2 k2 (lem_strengthen_wfft g x t_x g' t2 k2 p_xg_t2)
lem_strengthen_wfft g x t_x g' _ _ (WFFTPoly _ a k t k_t a' pf_a'g'xg_t)
  = WFFTPoly (concatF g g') a k t k_t 
             (a' ? lem_binds_cons_concatF g g' x t_x)
             (lem_strengthen_wfft g x t_x (FConsT a' k g') (unbindFT a a' t) k_t pf_a'g'xg_t)
lem_strengthen_wfft g x t_x g' _ _ (WFFTKind _ t pf_t_base)
  = WFFTKind (concatF g g') t (lem_strengthen_wfft g x t_x g' t Base pf_t_base)

{-@ lem_erase_wftype :: g:Env -> t:Type -> k:Kind -> ProofOf(WFType g t k)
                              -> ProofOf(WFFT (erase_env g) (erase t) k) @-}
lem_erase_wftype :: Env -> Type -> Kind -> WFType -> WFFT
lem_erase_wftype _ t k (WFRefn g x b p y pf_yg_p_bl) = WFFTBasic (erase_env g) b
lem_erase_wftype _ t _ (WFVar1 g a k)                = WFFTFV1 (erase_env g) a k
lem_erase_wftype _ t _ (WFVar2 g a k pf_g_a y t_y)
  = WFFTFV2 (erase_env g) a k (lem_erase_wftype g (FTV a) k pf_g_a) y (erase t_y)
lem_erase_wftype _ t _ (WFVar3 g a k pf_g_a a' k')
  = WFFTFV3 (erase_env g) a k (lem_erase_wftype g (FTV a) k pf_g_a) a' k'
lem_erase_wftype _ _ _ (WFFunc g x t_x k_x pf_g_tx t k y pf_yg_t)
  = WFFTFunc (erase_env g) (erase t_x) k_x (lem_erase_wftype g t_x k_x pf_g_tx)
                           (erase t) k pf_erase_g_t
      where
        pf_erase_g_t  = lem_strengthen_wfft (erase_env g) y (erase t_x) FEmpty
                            (erase t) k (pf_erase_yg_t ? lem_erase_tsubBV x (FV y) t)
        pf_erase_yg_t = lem_erase_wftype (Cons y t_x g) (unbindT x y t) k 
                            pf_yg_t ? lem_erase_tsubBV x (FV y) t
lem_erase_wftype _ _ _ (WFExis g x t_x k_x p_g_tx t k y pf_yg_t)
  = lem_strengthen_wfft (erase_env g) y (erase t_x) FEmpty
                        (erase t ? lem_erase_tsubBV x (FV y) t) k pf_erase_yg_t
      where
        pf_erase_yg_t = lem_erase_wftype (Cons y t_x g) (unbindT x y t) k pf_yg_t
lem_erase_wftype _ _ _ (WFPoly g a k t k_t a' pf_a'g_t)
  = WFFTPoly (erase_env g) a k (erase t) k_t a' 
             (lem_erase_wftype (ConsT a' k g) 
                               (unbind_tvT a a' t ? lem_erase_tsubBTV a (FTV a') t
                                                  ? lem_erase_freeTV t) 
                               k_t pf_a'g_t)
lem_erase_wftype _ _ _ (WFKind g t pf_t_base) 
  = WFFTKind (erase_env g) (erase t) (lem_erase_wftype g t Base pf_t_base)

{-@ lem_erase_env_wfenv :: g:Env -> ProofOf(WFEnv g) -> ProofOf(WFFE (erase_env g)) @-}
lem_erase_env_wfenv :: Env -> WFEnv -> WFFE
lem_erase_env_wfenv _ WFEEmpty                         = WFFEmpty
lem_erase_env_wfenv _ (WFEBind g pf_g_wf x t k p_g_t) 
  = WFFBind (erase_env g) (lem_erase_env_wfenv g pf_g_wf) 
            x (erase t) k (lem_erase_wftype g t k p_g_t)
lem_erase_env_wfenv _ (WFEBindT g pf_g_wf a k)
  = WFFBindT (erase_env g) (lem_erase_env_wfenv g pf_g_wf) a k
           

