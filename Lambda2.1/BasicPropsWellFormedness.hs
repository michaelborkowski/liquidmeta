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
{-@ lem_wffunc_for_wf_tfunc :: g:Env -> x:Vname -> t_x:Type -> t:Type -> k:Kind 
        -> { p_g_txt : WFType | propOf p_g_txt  == WFType g (TFunc x t_x t) k }
        -> { p_g_txt': WFType | propOf p_g_txt' == WFType g (TFunc x t_x t) Star && isWFFunc p_g_txt' } @-}
lem_wffunc_for_wf_tfunc :: Env -> Vname -> Type -> Type -> Kind -> WFType -> WFType
lem_wffunc_for_wf_tfunc g x t_x t k p_g_txt@(WFFunc {})           = case k of 
  Base -> impossible ("by lemma" ? lem_wf_tfunc_star g x t_x t p_g_txt)
  Star -> p_g_txt
lem_wffunc_for_wf_tfunc g x t_x t k (WFKind _g _ext p_g_txt_base) 
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

{-@ lem_strengthen_wffe :: g:FEnv -> { x:Vname | not (in_envF x g) } -> t_x:FType 
        -> { g':FEnv | not (in_envF x g') && Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> ProofOf(WFFE (concatF (FCons x t_x g) g')) -> ProofOf(WFFE (concatF g g')) @-}
lem_strengthen_wffe :: FEnv -> Vname -> FType -> FEnv -> WFFE -> WFFE
lem_strengthen_wffe g x t_x (FEmpty)          p_env_wf = p_g_wf
  where
    (WFFBind _g p_g_wf _ _ _ _) = p_env_wf
lem_strengthen_wffe g x t_x (FCons  z t_z g') p_env_wf = p_gg'z_wf
  where
    (WFFBind _env' p_env'_wf _ _ k_z p_env'_tz) = p_env_wf
    p_gg'_wf  = lem_strengthen_wffe g x t_x g' p_env'_wf
    p_gg'_tz  = lem_strengthen_wfft g x t_x g' t_z k_z p_env'_tz
    p_gg'z_wf = WFFBind (concatF g g') p_gg'_wf z t_z k_z p_gg'_tz
lem_strengthen_wffe g x t_x (FConsT a k_a g') p_env_wf = p_gg'a_wf
  where
    (WFFBindT _env' p_env'_wf  _ _) = p_env_wf
    p_gg'_wf  = lem_strengthen_wffe g x t_x g' p_env'_wf
    p_gg'a_wf = WFFBindT (concatF g g') p_gg'_wf a k_a

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
           
-------------------------------------------------------------------------------------------
-- | TECHNICAL LEMMAS relating to the abscence of dangling BOUND VARIABLES without a binder
-------------------------------------------------------------------------------------------

{-@ lem_freeBV_unbind_empty :: x:Vname -> y:Vname 
        -> { e:Expr | Set_emp (freeBV (unbind x y e)) && Set_emp (freeBTV (unbind x y e)) }
        -> { pf:_ | (Set_emp (freeBV e) || freeBV e == Set_sng x) && Set_emp (freeBTV e) } @-}
lem_freeBV_unbind_empty :: Vname -> Vname -> Expr -> Proof
lem_freeBV_unbind_empty x y e = toProof ( S.empty === freeBV (unbind x y e)
                                      === S.difference (freeBV e) (S.singleton x) )

{-@ lem_freeBTV_unbind_tv_empty :: a:Vname -> a':Vname 
        -> { e:Expr | Set_emp (freeBTV (unbind_tv a a' e)) && Set_emp (freeBV (unbind_tv a a' e)) }
        -> { pf:_ | (Set_emp (freeBTV e) || freeBTV e == Set_sng a) && Set_emp (freeBV e) } @-}
lem_freeBTV_unbind_tv_empty :: Vname -> Vname -> Expr -> Proof
lem_freeBTV_unbind_tv_empty a a' e = toProof ( S.empty === freeBTV (unbind_tv a a' e)
                                      === S.difference (freeBTV e) (S.singleton a) )

{-@ lem_tfreeBV_unbindT_empty :: x:Vname -> y:Vname 
         -> { t:Type | Set_emp (tfreeBV (unbindT x y t)) && Set_emp (tfreeBTV (unbindT x y t)) }
         -> { pf:_ | (Set_emp (tfreeBV t) || tfreeBV t == Set_sng x) && Set_emp (tfreeBTV t) } @-}
lem_tfreeBV_unbindT_empty :: Vname -> Vname -> Type -> Proof
lem_tfreeBV_unbindT_empty x y t = toProof ( S.empty === tfreeBV (unbindT x y t)
                                        === S.difference (tfreeBV t) (S.singleton x) )

{-@ lem_freeBV_emptyB :: g:FEnv -> e:Expr -> t:FType -> ProofOf(HasFType g e t)
                              -> { pf:_ | Set_emp (freeBV e) && Set_emp (freeBTV e) } @-}
lem_freeBV_emptyB :: FEnv -> Expr ->  FType -> HasFType -> Proof 
lem_freeBV_emptyB g e t (FTBC _g b)    = case e of
  (Bc _) -> ()
lem_freeBV_emptyB g e t (FTIC _g n)    = case e of
  (Ic _) -> ()
lem_freeBV_emptyB g e t (FTVar1 _ x _) = case e of 
  (FV _) -> ()
lem_freeBV_emptyB g e t (FTVar2 g' x _ p_x_t y s) = case e of
  (FV _) -> () ? lem_freeBV_emptyB g' e t p_x_t
lem_freeBV_emptyB g e t (FTVar3 g' x _ p_x_t a k) = case e of
  (FV _) -> () ? lem_freeBV_emptyB g' e t p_x_t
lem_freeBV_emptyB g e t (FTPrm _g c)   = case e of
  (Prim _) -> ()
lem_freeBV_emptyB g e t (FTAbs _g x t_x k_x p_g_tx e' t' y p_yg_e'_t') = case e of
  (Lambda _ _) -> () ? lem_freeBV_unbind_empty x y (e' ? lem_freeBV_emptyB (FCons y t_x g) (unbind x y e')
                                                               t' p_yg_e'_t')
lem_freeBV_emptyB g e t (FTApp _g e' t_x t' p_e'_txt' e_x p_ex_tx) = case e of
  (App _ _) -> () ? lem_freeBV_emptyB g e' (FTFunc t_x t') p_e'_txt'
                  ? lem_freeBV_emptyB g e_x t_x p_ex_tx
lem_freeBV_emptyB g e t (FTAbsT _g a k e' t' a' p_e'_t') = case e of 
  (LambdaT {}) -> () ? lem_freeBV_emptyB (FConsT a' k g) (unbind_tv a a' e') (unbindFT a a' t') p_e'_t'
lem_freeBV_emptyB g e t (FTAppT _g e' a k t' p_e_at' liqt p_g_ert)
    = {-() ? lem_freeBV_emptyB g e' (FTPoly a k t') p_e_at'
         ? -} undefined 
lem_freeBV_emptyB g e t (FTLet _g e_x t_x p_ex_tx x e' t' y p_yg_e'_t') = case e of
  (Let {}) -> () ? lem_freeBV_emptyB g e_x t_x p_ex_tx
                 ? lem_freeBV_unbind_empty x y (e' ? lem_freeBV_emptyB (FCons y t_x g) (unbind x y e')
                                                               t' p_yg_e'_t')
lem_freeBV_emptyB g e t (FTAnn _g e' _t t1 p_e'_t) 
    = {-() ? lem_freeBV_emptyB g e' t p_e'_t-}          undefined 
lem_freeBV_emptyB g e t (FTEqv _g _e a1 k t1 p_e_a1t1 a2 t2 a)
    = lem_freeBV_emptyB g e (FTPoly a1 k t1) p_e_a1t1 

{-@ lem_tfreeBV_empty :: g:Env -> t:Type -> k:Kind -> { p_g_t:WFType | propOf p_g_t == WFType g t k }
            -> ProofOf(WFEnv g) -> { pf:Proof | Set_emp (tfreeBV t) &&
                                                Set_emp (tfreeBTV t) } / [wftypSize p_g_t] @-}
lem_tfreeBV_empty :: Env -> Type -> Kind -> WFType -> WFEnv -> Proof
lem_tfreeBV_empty g t k (WFBase _g b) p_g_wf = case t of 
  (TRefn _ _ _) -> () ? lem_freeBV_emptyB FEmpty (Bc True) (FTBasic TBool) (FTBC FEmpty True)
lem_tfreeBV_empty g t k p_g_t@(WFRefn _g x b p_g_b p y p_yg_p_bl) p_g_wf = case t of
  (TRefn _ _ _) -> case b of 
    (BTV a) -> impossible ("by lemma" ? lem_btv_not_wf g a x p k p_g_t)
    _       -> () ? lem_freeBV_unbind_empty x y (p ? pf_unbinds_empty)
      where
        {-@ pf_unbinds_empty :: { pf:_ | Set_emp (freeBV (unbind x y p)) 
                                      && Set_emp (freeBTV (unbind x y p)) } @-}
        pf_unbinds_empty = lem_freeBV_emptyB (FCons y (FTBasic b) (erase_env g)) (unbind x y p) 
                                             (FTBasic TBool) p_yg_p_bl
lem_tfreeBV_empty g t k (WFVar1 {}) p_g_wf = undefined
lem_tfreeBV_empty g t k (WFVar2 {}) p_g_wf = undefined
lem_tfreeBV_empty g t k (WFVar3 {}) p_g_wf = undefined
lem_tfreeBV_empty g t k (WFFunc _g x t_x k_x p_g_tx t' k' y p_yg_t') p_g_wf = case t of
  (TFunc _ _ _) -> () 
        ? lem_tfreeBV_empty g t_x k_x p_g_tx p_g_wf
        ? lem_tfreeBV_unbindT_empty x y (t' ? lem_tfreeBV_empty (Cons y t_x g) (unbindT x y t') k'
                                                                p_yg_t' p_yg_wf)
      where
        p_yg_wf = WFEBind g p_g_wf y t_x k_x p_g_tx
lem_tfreeBV_empty g t k (WFExis _g x t_x k_x p_g_tx t' k' y p_yg_t') p_g_wf = case t of
  (TExists _ _ _) -> () 
        ? lem_tfreeBV_empty g t_x k_x p_g_tx p_g_wf
        ? lem_tfreeBV_unbindT_empty x y (t' ? lem_tfreeBV_empty (Cons y t_x g) (unbindT x y t') k'
                                                                p_yg_t' p_yg_wf)
      where
        p_yg_wf = WFEBind g p_g_wf y t_x k_x p_g_tx
lem_tfreeBV_empty g t k (WFPoly {}) p_g_wf = undefined
lem_tfreeBV_empty g t k (WFKind _g _t p_g_t_base) p_g_wf = () ? lem_tfreeBV_empty g t Base p_g_t_base p_g_wf 

