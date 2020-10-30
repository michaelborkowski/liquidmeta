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

{-@ reflect foo20 @-}
foo20 :: a -> Maybe a
foo20 x = Just x

{-@ lem_btv_not_wf :: g:Env -> a:Vname -> x:Vname -> p:Pred -> k:Kind
                        -> ProofOf(WFType g (TRefn (BTV a) x p) k) -> { pf:_ | false } @-}
lem_btv_not_wf :: Env -> Vname -> Vname -> Pred -> Kind -> WFType -> Proof
lem_btv_not_wf g a x p k (WFBase {}) = ()
lem_btv_not_wf g a x p k (WFRefn _ _ _ pf_g_b _ _ _) 
  = () ? lem_btv_not_wf g a 1 (Bc True) Base pf_g_b
lem_btv_not_wf g a x p k (WFVar1 {}) = ()
lem_btv_not_wf g a x p k (WFVar2 {}) = ()
lem_btv_not_wf g a x p k (WFVar3 {}) = ()
lem_btv_not_wf g a x p k (WFFunc {}) = ()
lem_btv_not_wf g a x p k (WFExis {}) = ()
lem_btv_not_wf g a x p k (WFPoly {}) = ()
lem_btv_not_wf g a x p k (WFKind _ _ pf_g_t_base) 
  = () ? lem_btv_not_wf g a x p Base pf_g_t_base


-- These lemmas allow us to directly invert the Well Formedness Judgments of certain types 
--     by allowing us to bypass the possibility of WFKind
{-@ lem_wffunc_for_wf_tfunc :: g:Env -> x:Vname -> t_x:Type -> t:Type 
        -> { p_g_txt : WFType | propOf p_g_txt  == WFType g (TFunc x t_x t) Star }
        -> { p_g_txt': WFType | propOf p_g_txt' == WFType g (TFunc x t_x t) Star && isWFFunc p_g_txt' } @-}
lem_wffunc_for_wf_tfunc :: Env -> Vname -> Type -> Type -> WFType -> WFType
lem_wffunc_for_wf_tfunc g x t_x t p_g_txt@(WFFunc {})           = p_g_txt
lem_wffunc_for_wf_tfunc g x t_x t (WFKind _g _ext p_g_txt_base) 
  = impossible ("by lemma" ? lem_wf_tfunc_star g x t_x t p_g_txt_base)

{-@ lem_wf_tfunc_star :: g:Env -> x:Vname -> t_x:Type -> t:Type
        -> ProofOf(WFType g (TFunc x t_x t) Base) -> { pf:_ | false } @-}
lem_wf_tfunc_star :: Env -> Vname -> Type -> Type -> WFType -> Proof
lem_wf_tfunc_star g x t_x t (WFBase {}) = ()
lem_wf_tfunc_star g x t_x t (WFRefn {}) = ()
lem_wf_tfunc_star g x t_x t (WFVar1 {}) = ()
lem_wf_tfunc_star g x t_x t (WFVar2 {}) = ()
lem_wf_tfunc_star g x t_x t (WFVar3 {}) = ()
lem_wf_tfunc_star g x t_x t (WFFunc {}) = ()
lem_wf_tfunc_star g x t_x t (WFExis {}) = ()
lem_wf_tfunc_star g x t_x t (WFPoly {}) = ()
lem_wf_tfunc_star g x t_x t (WFKind _g txt p_g_txt_base) = ()

-- Given G |-w \exists x:t_x. t : k, we can produce a proof tree ending in WFExis
{-@ lem_wfexis_for_wf_texists :: g:Env -> x:Vname -> t_x:Type -> t:Type -> k:Kind
        -> { p_g_ex_t : WFType | propOf p_g_ex_t  == WFType g (TExists x t_x t) k }
        -> { p_g_ex_t': WFType | propOf p_g_ex_t' == WFType g (TExists x t_x t) k && isWFExis p_g_ex_t' } @-}
lem_wfexis_for_wf_texists :: Env -> Vname -> Type -> Type -> Kind -> WFType -> WFType
lem_wfexis_for_wf_texists g x t_x t k p_g_ex_t@(WFExis {})           = p_g_ex_t
lem_wfexis_for_wf_texists g x t_x t k (WFKind _g _ext p_g_ex_t_base) = p_g_ex_t_star
  where
    (WFExis _ _ _ k_x p_g_tx _ k_t y p_yg_t_kt) = p_g_ex_t_base
    {-@ p_yg_t_star :: { pf:WFType | propOf pf == WFType (Cons y t_x g) (unbindT x y t) Star } @-}
    p_yg_t_star = case k_t of 
      Base -> WFKind (Cons y t_x g) (unbindT x y t) p_yg_t_kt
      Star -> p_yg_t_kt
    p_g_ex_t_star = WFExis g x t_x k_x p_g_tx t Star y p_yg_t_star

{-@ lem_wfpoly_for_wf_tpoly :: g:Env -> a:Vname -> k:Kind -> t:Type 
        -> { p_g_at : WFType | propOf p_g_at  == WFType g (TPoly a k t) Star }
        -> { p_g_at': WFType | propOf p_g_at' == WFType g (TPoly a k t) Star && isWFPoly p_g_at' } @-}
lem_wfpoly_for_wf_tpoly :: Env -> Vname -> Kind -> Type -> WFType -> WFType
lem_wfpoly_for_wf_tpoly g a k t p_g_at@(WFPoly {})           = p_g_at
lem_wfpoly_for_wf_tpoly g a k t (WFKind _g _at p_g_at_base) 
  = impossible ("by lemma" ? lem_wf_tpoly_star g a k t p_g_at_base)

{-@ lem_wf_tpoly_star :: g:Env -> a:Vname -> k:Kind -> t:Type
        -> ProofOf(WFType g (TPoly a k t) Base) -> { pf:_ | false } @-}
lem_wf_tpoly_star :: Env -> Vname -> Kind -> Type -> WFType -> Proof
lem_wf_tpoly_star g a k t (WFBase {}) = ()
lem_wf_tpoly_star g a k t (WFRefn {}) = ()
lem_wf_tpoly_star g a k t (WFVar1 {}) = ()
lem_wf_tpoly_star g a k t (WFVar2 {}) = ()
lem_wf_tpoly_star g a k t (WFVar3 {}) = ()
lem_wf_tpoly_star g a k t (WFFunc {}) = ()
lem_wf_tpoly_star g a k t (WFExis {}) = ()
lem_wf_tpoly_star g a k t (WFPoly {}) = ()
lem_wf_tpoly_star g a k t (WFKind {}) = ()


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
                               (lem_strengthen_wfft g x t_x g'' (FTBasic (FTV a)) k p_g_a) y t
      (FConsT a' k' g'')  -> impossible ""
lem_strengthen_wfft g x t_x g' _ _ (WFFTFV3 _ a k p_g_a a' k') 
  = case g' of
      (FEmpty)            -> impossible ""
      (FCons z t_z g'')   -> impossible ""
      (FConsT a' k' g'')  -> WFFTFV3 (concatF g g'') a k
                               (lem_strengthen_wfft g x t_x g'' (FTBasic (FTV a)) k p_g_a) 
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
lem_erase_wftype _ _ _ (WFBase g b)                  = WFFTBasic (erase_env g) b
lem_erase_wftype _ t k pf_g_t@(WFRefn g x b pf_g_b p y pf_yg_p)  
  = case b of
      (FTV a)  -> lem_erase_wftype g (TRefn (FTV a) 1 (Bc True)) Base pf_g_b
      (BTV a)  -> impossible ("by lemma" ? lem_btv_not_wf g a x p k pf_g_t)
      TBool    -> WFFTBasic (erase_env g) TBool
      TInt     -> WFFTBasic (erase_env g) TInt
lem_erase_wftype _ t _ (WFVar1 g a k)                = WFFTFV1 (erase_env g) a k
lem_erase_wftype _ t _ (WFVar2 g a k pf_g_a y t_y)
  = WFFTFV2 (erase_env g) a k (lem_erase_wftype g (TRefn (FTV a) 1 (Bc True)) k pf_g_a) 
            y (erase t_y)
lem_erase_wftype _ t _ (WFVar3 g a k pf_g_a a' k')
  = WFFTFV3 (erase_env g) a k (lem_erase_wftype g (TRefn (FTV a) 1 (Bc True)) k pf_g_a) a' k'
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
                       (unbind_tvT a a' t ? lem_erase_unbind_tvT a a' t
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
           

