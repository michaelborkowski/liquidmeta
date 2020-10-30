{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasNarrowingTyp where

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
import SystemFLemmasFTyping
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import Entailments
import LemmasChangeVarWF
import LemmasWeakenWF
import LemmasWellFormedness
import LemmasTyping
import LemmasSubtyping
import LemmasChangeVarTyp
import LemmasWeakenTyp
import SubstitutionLemmaWF
import DenotationsSelfify
import DenotationsSoundnessSub
import PrimitivesSemantics
import PrimitivesDenotations
import DenotationsSoundnessTyp
import LemmasExactness
import SubstitutionLemmaEnt
import SubstitutionLemmaTyp
import LemmasNarrowingEnt

{-@ reflect foo56 @-}
foo56 x = Just x
foo56 :: a -> Maybe a

--        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> e:Expr -> t:Type 
{-@ lem_narrow_typ :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
        -> t_x:Type -> ProofOf(Subtype g s_x t_x)  -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t }
        -> ProofOf(HasType (concatE (Cons x s_x g) g') e t) / [typSize p_e_t] @-}
lem_narrow_typ :: Env -> Env -> Vname -> Type -> Type -> Subtype 
                    -> Expr -> Type -> HasType -> HasType
lem_narrow_typ g g' x s_x t_x p_sx_tx {-p_env_wf-} e t (TBC _env b) 
  = TBC (concatE (Cons x s_x g) g') b 
lem_narrow_typ g g' x s_x t_x p_sx_tx {-p_env_wf-} e t (TIC _env n) 
  = TIC (concatE (Cons x s_x g) g') n 
lem_narrow_typ g g' x s_x t_x p_sx_tx {-p_env_wf-} e t (TVar1 _env z _t) = undefined {-
  = case g' of 
      (Empty)           -> p_vx_tx ? lem_free_bound_in_env g t_x k_x p_g_tx x
                                   ? toProof ( tsubFV x v_x t === t_x )
        where
          (WFEBind _g p_g_wf _x _tx k_x p_g_tx) = p_env_wf
      (Cons _z _ g'')  -> TVar1 (concatE g (esubFV x v_x g'')) --z 
                                (z ? lem_in_env_esub g'' x v_x z
                                   ? lem_in_env_concat g g'' z
                                   ? lem_in_env_concat (Cons x t_x g) g'' z)          
                                (tsubFV x v_x t) -}
lem_narrow_typ g g' x s_x t_x p_sx_tx {-p_env_wf-} e t (TVar2 env_ z _t p_z_t w_ t_w) = undefined{-
    = case g' of             -- g''=Emp so x=w and p_z_t :: HasBType(g (FV z) t)
        (Empty)           -> case (x == z) of
                               (True)  -> impossible "it is"
                               (False) -> p_z_t
                                           ? lem_free_bound_in_env g t p_g_t x
                                           ? toProof ( e === (FV z) )
                                   where
                                     (WFEBind g_ p_g_wf _ _ _) = p_env_wf
                                     p_g_t = lem_typing_wf g (FV z) t p_z_t p_g_wf
        (Cons _w _tw g'') -> case (x == z) of
                    (True)  -> lem_weaken_typ (concatE g (esubFV x v_x g'')) Empty p_env'_wf
                                              v_x (tsubFV x v_x t) p_gg''_vx_tx w (tsubFV x v_x t_w)
                                              ? toProof ( e === (FV x) )
                                   where
                                     w = w_ ? lem_in_env_esub g'' x v_x w_
                                            ? lem_in_env_concat g g'' w_
                                            ? lem_in_env_concat (Cons x t_x g) g'' w_
                                            ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx w_
                                     p_env'_wf    = lem_subst_wfenv g g'' x v_x t_x p_vx_tx p_gg''_wf
                                     p_gg''_vx_tx = lem_subst_typ g g'' x v_x t_x p_vx_tx p_gg''_wf
                                                                  e t p_z_t
                                     (WFEBind _gg'' p_gg''_wf _ _ _) = p_env_wf
                                     p_xg_wf = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
                                     (WFEBind _ p_g_wf _ _ _) = p_xg_wf
                                     p_vx_er_tx    = lem_typing_hasbtype g v_x t_x p_vx_tx p_g_wf
                    (False) -> TVar2 (concatE g (esubFV x v_x g'')) --z
                                 (z ? lem_in_env_esub g'' x v_x z
                                    ? lem_in_env_concat g g'' z
                                    ? lem_in_env_concat (Cons x t_x g) g'' z) 
                                 (tsubFV x v_x t) p_z_tvx w 
                                 (tsubFV x v_x t_w)
                                   where
                                     w = w_ ? lem_in_env_esub g'' x v_x w_
                                            ? lem_in_env_concat g g'' w_
                                            ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx w_
                                            ? lem_in_env_concat (Cons x t_x g) g'' w_
                                     (WFEBind _gg'' p_gg''_wf _ _ _) = p_env_wf
                                     p_z_tvx = lem_subst_typ g g'' x v_x t_x p_vx_tx
                                                             p_gg''_wf e t p_z_t
                                     p_xg_wf = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
                                     (WFEBind _ p_g_wf _ _ _) = p_xg_wf
                                     p_vx_er_tx    = lem_typing_hasbtype g v_x t_x p_vx_tx p_g_wf-}
lem_narrow_typ g g' x s_x t_x p_sx_tx {-p_env_wf-} e t (TVar3 env_ z _t p_z_t a_ k_a) = undefined 
lem_narrow_typ g g' x s_x t_x p_sx_tx {-p_env_wf-} e t (TPrm _en c) 
  = TPrm (concatE (Cons x s_x g) g') c 
lem_narrow_typ g g' x s_x t_x p_sx_tx {-p_env_wf-} e t (TAbs env_ z t_z k_z p_env_tz e' t' y_ p_yenv_e'_t') 
  = undefined {- = TAbs (concatE g (esubFV x v_x g')) z (tsubFV x v_x t_z) p_g'g_tzvx
         (subFV x v_x e') (tsubFV x v_x t') y p_yg'g_e'vx_t'vx
      where
        y                = y_  ? lem_in_env_esub g' x v_x y_ 
                               ? lem_in_env_concat g  g' y_ 
                               ? lem_in_env_concat (Cons x t_x g) g' y_
                               ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx y_
        p_xg_wf     = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _) = p_xg_wf
        p_vx_er_tx       = lem_typing_hasbtype g v_x t_x p_vx_tx p_g_wf
        p_yenv_wf        = WFEBind (concatE (Cons x t_x g) g') p_env_wf y t_z p_env_tz
        p_g'g_tzvx       = lem_subst_wf g g' x v_x t_x p_vx_tx p_env_wf t_z p_env_tz
        p_yg'g_e'vx_t'vx = lem_subst_typ g (Cons y t_z g') x v_x t_x p_vx_tx p_yenv_wf
                                         (unbind z y e') (unbindT z y t') p_yenv_e'_t'
                                         ? lem_commute_subFV_subBV1 z (FV y) x v_x e'
                                         ? lem_commute_tsubFV_tsubBV1 z (FV y) x v_x t' -}
lem_narrow_typ g g' x s_x t_x p_sx_tx {-p_env_wf-} e t (TApp env_ e' z t_z t' p_env_e'_tzt' e_z p_env_ez_tz) 
  = undefined {- TApp (concatE g (esubFV x v_x g')) (subFV x v_x e') z (tsubFV x v_x t_z) (tsubFV x v_x t') 
         p_g'g_e'vx_tzt'vx (subFV x v_x e_z)  p_g'g_ezvx_tzvx         
      where
        p_g'g_e'vx_tzt'vx = lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e' 
                                          (TFunc z t_z t') p_env_e'_tzt'
        p_g'g_ezvx_tzvx   = lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e_z t_z p_env_ez_tz -}
lem_narrow_typ g g' x s_x t_x p_sx_tx {-p_env_wf-} e t (TAbsT {}) = undefined 
lem_narrow_typ g g' x s_x t_x p_sx_tx {-p_env_wf-} e t (TAppT {}) = undefined 
lem_narrow_typ g g' x s_x t_x p_sx_tx {-p_env_wf-} e t (TLet env_ e_z t_z p_env_ez_tz z e' t_ k
                                                        p_env_t y_ p_yenv_e'_t) = undefined {-
  = TLet (concatE g (esubFV x v_x g')) (subFV x v_x e_z) (tsubFV x v_x t_z) p_g'g_ezvx_tzvx z
         (subFV x v_x e') (tsubFV x v_x t) p_g'g_t'vx y p_yg'g_e'vx_tvx
      where
        y                = y_  ? lem_in_env_esub g' x v_x y_ 
                               ? lem_in_env_concat g  g' y_ 
                               ? lem_in_env_concat (Cons x t_x g) g' y_
                               ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx y_
        p_xg_wf     = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _) = p_xg_wf
        p_vx_er_tx       = lem_typing_hasbtype g v_x t_x p_vx_tx p_g_wf
        p_env_tz         = lem_typing_wf env_ e_z t_z p_env_ez_tz p_env_wf
        p_yenv_wf        = WFEBind (concatE (Cons x t_x g) g') p_env_wf y t_z p_env_tz
        p_g'g_ezvx_tzvx  = lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e_z t_z p_env_ez_tz
        p_g'g_t'vx       = lem_subst_wf  g g' x v_x t_x p_vx_tx p_env_wf t p_env_t
        p_yg'g_e'vx_tvx  = lem_subst_typ g (Cons y t_z g') x v_x t_x p_vx_tx p_yenv_wf 
                                         (unbind z y e') (unbindT z y t) p_yenv_e'_t
                                         ? lem_commute_subFV_subBV1 z (FV y) x v_x e'
                                         ? lem_commute_tsubFV_tsubBV1 z (FV y) x v_x t -}
lem_narrow_typ g g' x s_x t_x p_sx_tx {-p_env_wf-} e t (TAnn env_ e' t_ p_env_e'_t) 
  = TAnn (concatE (Cons x s_x g) g') e' t p_env'_e'_t
      where
        p_env'_e'_t = lem_narrow_typ g g' x s_x t_x p_sx_tx {-p_env_wf-} e' t p_env_e'_t
lem_narrow_typ g g' x s_x t_x p_sx_tx {-p_env_wf-} e t (TSub env_ e_ s p_env_e_s t_ k p_env_t p_env_s_t) 
  = TSub (concatE (Cons x s_x g) g') e s p_env'_e_s t k p_env'_t p_env'_s_t
      where
        p_env'_e_s = lem_narrow_typ g g' x s_x t_x p_sx_tx {-p_env_wf-} e s p_env_e_s
        p_env'_t   = lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx {-p_env_wf-} t k p_env_t
        {-p_env_s    = lem_typing_wf (concatE (Cons x t_x g) g') e s p_env_e_s p_env_wf-}
        p_env'_s_t = lem_narrow_sub g g' x s_x t_x p_sx_tx {-p_env_wf-} s {-p_env_s-} t {-p_env_t-} p_env_s_t 

--        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) 
--        -> s:Type -> k_s:Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') s k_s)
--        -> t:Type -> k_t:Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') t k_t)
{-@ lem_narrow_sub :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
        -> t_x:Type -> ProofOf(Subtype g s_x t_x) -> s:Type -> t:Type
        -> { p_s_t:Subtype  | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t }
        -> { p'_s_t:Subtype | propOf p'_s_t == (Subtype (concatE (Cons x s_x g) g') s t) 
                              && subtypSize p_s_t == subtypSize p'_s_t } / [subtypSize p_s_t] @-}
lem_narrow_sub :: Env -> Env -> Vname -> Type -> Type -> Subtype {--> WFEnv-}
                    -> Type {-> Kind -> WFType-} -> Type {-> Kind -> WFType-} -> Subtype -> Subtype
lem_narrow_sub g g' x s_x t_x p_sx_tx {-p_env_wf-} s {-k_s p_env_s-} t {-k_t p_env_t-}
              (SBase env z1 b p1 z2 p2 y_ ent_yenv_p2) -- p_env_s_t
  = undefined {- SBase (concatE g (esubFV x v_x g')) z1 b (subFV x v_x p1) z2 (subFV x v_x p2) y
          ent_yenv'_p2vx  -- Entails (Cons y (TRefn b z1 (subFV x v_x p1)) env') (unbind z2 y (subFV x v_x p2))
      where
        y                = y_  ? lem_in_env_esub g' x v_x y_ 
                               ? lem_in_env_concat g  g' y_ 
                               ? lem_in_env_concat (Cons x t_x g) g' y_
                               ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx y_
        p_xg_wf          = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _)       = p_xg_wf
        p_vx_er_tx       = lem_typing_hasbtype g v_x t_x p_vx_tx p_g_wf
        (WFRefn _ _ _ _p2 w_ p_wenv_p2_bl) = p_env_t
        w                = w_  ? lem_in_env_concat g  g' w_ 
                               ? lem_in_env_concat (Cons x t_x g) g' w_
        p_yenv_wf        = WFEBind env p_env_wf y (TRefn b z1 p1) p_env_s
        p_yenv_p2_bl     = lem_change_var_btyp (erase_env env) w (BTBase b) BEmpty (unbind z2 w p2)
                                               (BTBase TBool) p_wenv_p2_bl y
                                               ? lem_subFV_unbind z2 w (FV y) p2
        --EntPred _yenv _p2 func_th_thp_tt = ent_yenv_p2 -- Entails (Cons y (TRefn b z1 p1) env) (unbind z2 y p2)
        ent_yenv'_p2vx   = lem_subst_ent g (Cons y (TRefn b z1 p1) g') x v_x t_x p_vx_tx p_yenv_wf
                                   (unbind z2 y p2 ? lem_fv_subset_bindsB (BCons y (BTBase b) (erase_env env)) 
                                           (unbind z2 y p2) (BTBase TBool) p_yenv_p2_bl)
                                   ent_yenv_p2 
                                   ? lem_commute_subFV_subBV1 z2 (FV y) x v_x p2 -}
lem_narrow_sub g g' x s_x t_x p_sx_tx {-p_env_wf-} ty1 {-ky1 p_env_ty1-} ty2 {-ky2 p_env_ty2-}
              (SFunc env_ x1 s1 x2 s2 p_s2_s1 t1 t2 y_ p_yenv_t1_t2) = undefined {-
  = SFunc (concatE g (esubFV x v_x g')) x1 (tsubFV x v_x s1) x2 (tsubFV x v_x s2)
          p_s2vx_s1vx (tsubFV x v_x t1) (tsubFV x v_x t2) y p_yg'g_t1vx_t2vx
      where 
        y                = y_  ? lem_in_env_esub g' x v_x y_ 
                               ? lem_in_env_concat g  g' y_ 
                               ? lem_in_env_concat (Cons x t_x g) g' y_
                               ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx y_
        p_xg_wf          = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _)       = p_xg_wf
        p_vx_er_tx       = lem_typing_hasbtype g v_x t_x p_vx_tx p_g_wf
        (WFFunc _ _ _s1 p_env_s1 _ w1 p_w1env_t1) = p_env_ty1
        (WFFunc _ _ _s2 p_env_s2 _ w2 p_w2env_t2) = p_env_ty2
        _p_yenv_t1       = lem_change_var_wf (concatE (Cons x t_x g) g') w1 s1 Empty 
                                             (unbindT x1 w1 t1) p_w1env_t1 y
                                             `withProof` lem_tsubFV_unbindT x1 w1 (FV y) t1
        p_yenv_t1        = lem_subtype_in_env_wf (concatE (Cons x t_x g) g') Empty y s2 s1 
                                             p_s2_s1 (unbindT x1 y t1) _p_yenv_t1
        p_yenv_t2        = lem_change_var_wf (concatE (Cons x t_x g) g') w2 s2 Empty
                                             (unbindT x2 w2 t2) p_w2env_t2 y
                                             `withProof` lem_tsubFV_unbindT x2 w2 (FV y) t2
        p_s2vx_s1vx      = lem_subst_sub g g' x v_x t_x p_vx_tx p_env_wf 
                                         s2 p_env_s2 s1 p_env_s1 p_s2_s1 
        p_yenv_wf        = WFEBind (concatE (Cons x t_x g) g') p_env_wf y s2 p_env_s2
        p_yg'g_t1vx_t2vx = lem_subst_sub g (Cons y s2 g') x v_x t_x p_vx_tx p_yenv_wf
                                         (unbindT x1 y t1) p_yenv_t1 
                                         (unbindT x2 y t2) p_yenv_t2 p_yenv_t1_t2
                                         ? lem_commute_tsubFV_tsubBV1 x1 (FV y) x v_x t1
                                         ? lem_commute_tsubFV_tsubBV1 x2 (FV y) x v_x t2 -}
lem_narrow_sub g g' x s_x t_x p_sx_tx {-p_env_wf-} t {-k p_env_t-} t2 {-k2 p_env_t2-}
              (SWitn env v_z t_z p_env_vz_tz _t z t' p_env_t_t'vz) = undefined {-
  = SWitn (concatE g (esubFV x v_x g')) (subFV x v_x v_z) (tsubFV x v_x t_z) p_g'g_vzvx_tzvx
          (tsubFV x v_x t) z (tsubFV x v_x t') p_g'g_tvx_t'vzvx
      where
        p_g'g_vzvx_tzvx  = lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf v_z t_z p_env_vz_tz
        (WFExis _ _ _ p_env_tz _ y p_yenv_t') = p_env_t2
        p_yenv_wf        = WFEBind env p_env_wf y t_z p_env_tz
        p_env_t'vz       = lem_subst_wf (concatE (Cons x t_x g) g') Empty y v_z t_z p_env_vz_tz 
                              p_yenv_wf (unbindT z y t') p_yenv_t' ? lem_tsubFV_unbindT z y v_z t'
        p_g'g_tvx_t'vzvx = lem_subst_sub g g' x v_x t_x p_vx_tx p_env_wf t p_env_t 
                                         (tsubBV z v_z t') p_env_t'vz p_env_t_t'vz
                                         ? lem_commute_tsubFV_tsubBV z v_z x v_x t' -}
lem_narrow_sub g g' x s_x t_x p_sx_tx {-p_env_wf-} t1 {-k1 p_env_t1-} t' {-k' p_env_t'-}
              (SBind env z t_z t _t' w_ p_wenv_t_t') = undefined {-
  = SBind (concatE g (esubFV x v_x g')) z (tsubFV x v_x t_z) (tsubFV x v_x t) (tsubFV x v_x t')
          w p_wenv'_tvx_t'vx
      where 
        w                = w_ ? lem_in_env_esub g' x v_x w_
                              ? lem_in_env_concat g g' w_
                              ? lem_in_env_concat (Cons x t_x g) g' w_
                              ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx w_
        p_xg_wf          = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _)       = p_xg_wf
        p_vx_er_tx       = lem_typing_hasbtype g v_x t_x p_vx_tx p_g_wf
        (WFExis _ _ _ p_env_tz _ y p_yenv_t) = p_env_t1
        p_wenv_wf        = WFEBind (concatE (Cons x t_x g) g') p_env_wf w t_z p_env_tz
        p_wenv_t         = lem_change_var_wf env y t_z Empty (unbindT z y t) p_yenv_t w
                                         ? lem_tsubFV_unbindT z y (FV w) t
        p_wenv_t'        = lem_weaken_wf env Empty t' p_env_t' w t_z
        p_wenv'_tvx_t'vx = lem_subst_sub g (Cons w t_z g') x v_x t_x p_vx_tx p_wenv_wf
                                         (unbindT z w t) p_wenv_t t' p_wenv_t' p_wenv_t_t'
                                         ? lem_commute_tsubFV_tsubBV z (FV w) x v_x t-}
lem_narrow_sub g g' x s_x t_x p_sx_tx {-p_env_wf-} t1 {-k1 p_env_t1-} t2 {-k2 p_env_t2-} 
               (SPoly env a1 k1 t1' a2 t2' a_ p_env_t1'_t2') 
  = SPoly (concatE (Cons x s_x g) g') a1 k1 t1' a2 t2' a p_env'_t1'_t2'
      where
        a              = a_ ? lem_in_env_concat (Cons x t_x g) g' a_
        p_env'_t1'_t2' = lem_narrow_sub g (ConsT a k1 g') x s_x t_x p_sx_tx 
                             (unbind_tvT a1 a t1') (unbind_tvT a2 a t2') p_env_t1'_t2'
