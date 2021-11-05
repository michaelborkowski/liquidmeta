{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SubstitutionLemmaTyp where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
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
import DenotationsSoundness
import PrimitivesSemantics
import PrimitivesDenotations
import LemmasExactness
import SubstitutionLemmaEnt

{-@ reflect foo63 @-}
foo63 x = Just x
foo63 :: a -> Maybe a

{-@ lem_subst_typ_tvar1 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> ProofOf(HasType g v_x t_x) 
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t && isTVar1 p_e_t}
        -> ProofOf(HasType (concatE g (esubFV x v_x g')) (subFV x v_x e) (tsubFV x v_x t)) / [typSize p_e_t, 0] @-}
lem_subst_typ_tvar1 :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_typ_tvar1 g g' x v_x t_x p_vx_tx p_env_wf e t (TVar1 _env z t' p_env_t) 
  = case g' of          -- empty case: e = FV z = FV x and t = self t' x = self t_x x
      (Empty)           -> lem_exact_type g v_x t_x p_vx_tx p_g_wf
                                   ? lem_free_bound_in_env g t_x p_g_tx x
                                   ? lem_tsubFV_notin x v_x t_x 
                                   ? lem_tsubFV_self x v_x t_x z 
        where
          (WFEBind _g p_g_wf _x _tx p_g_tx) = p_env_wf
      (Cons _z _ g'')  -> TVar1 (concatE g (esubFV x v_x g''))  -- z <> x, t = self t' (FV z)
                                (z ? lem_in_env_esub g'' x v_x z
                                   ? lem_in_env_concat g g'' z
                                   ? lem_in_env_concat (Cons x t_x g) g'' z)          
                                (tsubFV x v_x t') p_env'_t'vx
                                   ? lem_tsubFV_self2 x v_x t' z 
        where
          (WFEBind _ p_g''g_wf _z _tz p_g_tz) = p_env_wf
          p_env'_t'vx = lem_subst_wf' g g'' x v_x t_x p_vx_tx p_g''g_wf t' p_env_t

{-@ lem_subst_typ_tvar2 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> ProofOf(HasType g v_x t_x) 
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t && isTVar2 p_e_t}
        -> ProofOf(HasType (concatE g (esubFV x v_x g')) (subFV x v_x e) (tsubFV x v_x t)) / [typSize p_e_t, 0] @-}
lem_subst_typ_tvar2 :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_typ_tvar2 g g' x v_x t_x p_vx_tx p_env_wf e t (TVar2 env_ z _t p_z_t w_ t_w) 
    = case g' of             -- g'' = Empty so x = w and p_z_t :: HasFType(g (FV z) t)
        (Empty)           -> case (x == z) of
            (True)  -> impossible "it is"
            (False) -> p_z_t ? toProof ( tsubFV x v_x t === t )
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
                           (WFEBind _gg'' p_gg''_wf _ _ _) = p_env_wf
                           p_xg_wf = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
                           (WFEBind _ p_g_wf _ _ _) = p_xg_wf
                           w = w_ ? lem_in_env_esub g'' x v_x w_
                                  ? lem_in_env_concat g g'' w_
                                  ? lem_in_env_concat (Cons x t_x g) g'' w_
                                  ? lem_fv_bound_in_env g v_x t_x p_vx_tx p_g_wf w_
                           p_env'_wf    = lem_subst_wfenv g g'' x v_x t_x p_vx_tx p_gg''_wf
                           p_gg''_vx_tx = lem_subst_typ g g'' x v_x t_x p_vx_tx p_gg''_wf
                                                        e t p_z_t
            (False) -> TVar2 (concatE g (esubFV x v_x g'')) --z
                             (z ? lem_in_env_esub g'' x v_x z
                                ? lem_in_env_concat g g'' z
                                ? lem_in_env_concat (Cons x t_x g) g'' z) 
                             (tsubFV x v_x t) p_z_tvx w (tsubFV x v_x t_w)
                         where
                           (WFEBind _gg'' p_gg''_wf _ _ _) = p_env_wf
                           p_xg_wf = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
                           (WFEBind _ p_g_wf _ _ _) = p_xg_wf
                           w = w_ ? lem_in_env_esub g'' x v_x w_
                                  ? lem_in_env_concat g g'' w_
                                  ? lem_in_env_concat (Cons x t_x g) g'' w_
                                  ? lem_fv_bound_in_env g v_x t_x p_vx_tx p_g_wf w_
                           p_z_tvx = lem_subst_typ g g'' x v_x t_x p_vx_tx
                                                   p_gg''_wf e t p_z_t

{-@ lem_subst_typ_tabs :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> ProofOf(HasType g v_x t_x) 
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t && isTAbs p_e_t}
        -> ProofOf(HasType (concatE g (esubFV x v_x g')) (subFV x v_x e) (tsubFV x v_x t)) / [typSize p_e_t, 0] @-}
lem_subst_typ_tabs :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_typ_tabs g g' x v_x t_x p_vx_tx p_env_wf e t (TAbs env_ z t_z p_env_tz e' t' y_ p_yenv_e'_t') 
  = TAbs (concatE g (esubFV x v_x g')) z (tsubFV x v_x t_z) p_g'g_tzvx
         (subFV x v_x e') (tsubFV x v_x t') y p_yg'g_e'vx_t'vx
      where
        p_xg_wf          = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _) = p_xg_wf
        y                = y_  ? lem_in_env_esub g' x v_x y_ 
                               ? lem_in_env_concat g  g' y_ 
                               ? lem_in_env_concat (Cons x t_x g) g' y_
                               ? lem_fv_bound_in_env g v_x t_x p_vx_tx p_g_wf y_
        p_yenv_wf        = WFEBind (concatE (Cons x t_x g) g') p_env_wf y t_z p_env_tz
        p_g'g_tzvx       = lem_subst_wf' g g' x v_x t_x p_vx_tx p_env_wf t_z p_env_tz
        p_yg'g_e'vx_t'vx = lem_subst_typ g (Cons y t_z g') x v_x t_x p_vx_tx p_yenv_wf
                                         (unbind z y e') (unbindT z y t') p_yenv_e'_t'
                                         ? lem_commute_subFV_subBV1 z (FV y) x 
                                               (v_x ? lem_freeBV_empty g v_x t_x p_vx_tx p_g_wf) e'
                                         ? lem_commute_tsubFV_tsubBV1 z (FV y) x 
                                               (v_x ? lem_freeBV_empty g v_x t_x p_vx_tx p_g_wf) t' 

{-@ lem_subst_typ_tapp :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> ProofOf(HasType g v_x t_x) 
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t && isTApp p_e_t}
        -> ProofOf(HasType (concatE g (esubFV x v_x g')) (subFV x v_x e) (tsubFV x v_x t)) / [typSize p_e_t, 0] @-}
lem_subst_typ_tapp :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_typ_tapp g g' x v_x t_x p_vx_tx p_env_wf e t (TApp env_ e' z t_z t' p_env_e'_tzt' e_z p_env_ez_tz) 
  = TApp (concatE g (esubFV x v_x g')) (subFV x v_x e') z (tsubFV x v_x t_z) (tsubFV x v_x t') 
         p_g'g_e'vx_tzt'vx (subFV x v_x e_z)  p_g'g_ezvx_tzvx         
      where
        p_g'g_e'vx_tzt'vx = lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e' 
                                          (TFunc z t_z t') p_env_e'_tzt'
        p_g'g_ezvx_tzvx   = lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e_z t_z p_env_ez_tz 

{-@ lem_subst_typ_tsub :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> ProofOf(HasType g v_x t_x) 
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t && isTSub p_e_t}
        -> ProofOf(HasType (concatE g (esubFV x v_x g')) (subFV x v_x e) (tsubFV x v_x t)) / [typSize p_e_t, 0] @-}
lem_subst_typ_tsub :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_typ_tsub g g' x v_x t_x p_vx_tx p_env_wf e t (TSub env_ e_ s p_env_e_s t_ p_env_t p_env_s_t) 
  = TSub (concatE g (esubFV x v_x g')) (subFV x v_x e) (tsubFV x v_x s) p_g'g_e_s
         (tsubFV x v_x t) p_g'g_t p_g'g_s_t
      where
        p_g'g_e_s  = lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e s p_env_e_s
        p_g'g_t    = lem_subst_wf' g g' x v_x t_x p_vx_tx p_env_wf t p_env_t
        p_env_s    = lem_typing_wf (concatE (Cons x t_x g) g') e s p_env_e_s p_env_wf
        p_g'g_s_t  = lem_subst_sub g g' x v_x t_x p_vx_tx p_env_wf s p_env_s t p_env_t p_env_s_t

{-@ lem_subst_typ :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> ProofOf(HasType g v_x t_x) 
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t }
        -> ProofOf(HasType (concatE g (esubFV x v_x g')) (subFV x v_x e) (tsubFV x v_x t)) / [typSize p_e_t,1] @-}
lem_subst_typ :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e t (TBC _env b) 
  = TBC (concatE g (esubFV x v_x g')) b ? lem_tsubFV_tybc x v_x b
lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e t (TIC _env n) 
  = TIC (concatE g (esubFV x v_x g')) n ? lem_tsubFV_tyic x v_x n 
lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e t p_e_t@(TVar1 {})  
  = lem_subst_typ_tvar1 g g' x v_x t_x p_vx_tx p_env_wf e t p_e_t
lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e t p_e_t@(TVar2 env_ z _t p_z_t w_ t_w)
  = lem_subst_typ_tvar2 g g' x v_x t_x p_vx_tx p_env_wf e t p_e_t
lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e t (TPrm _en c) 
  = TPrm (concatE g (esubFV x v_x g')) c ? lem_tsubFV_ty x v_x c 
lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e t p_e_t@(TAbs env_ z t_z p_env_tz e' t' y_ p_yenv_e'_t') 
  = lem_subst_typ_tabs g g' x v_x t_x p_vx_tx p_env_wf e t p_e_t  
lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e t p_e_t@(TApp env_ e' z t_z t' p_env_e'_tzt' e_z p_env_ez_tz) 
  = lem_subst_typ_tapp g g' x v_x t_x p_vx_tx p_env_wf e t p_e_t
lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e t p_e_t@(TSub env_ e_ s p_env_e_s t_ p_env_t p_env_s_t) 
  = lem_subst_typ_tsub g g' x v_x t_x p_vx_tx p_env_wf e t p_e_t

 
{-@ lem_subst_sub_sbase :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> ProofOf(HasType g v_x t_x) 
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) 
        -> s:Type -> ProofOf(WFType (concatE (Cons x t_x g) g') s)
        -> t:Type -> ProofOf(WFType (concatE (Cons x t_x g) g') t)
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t && isSBase p_s_t }
        -> { p'_s_t:Subtype | propOf p'_s_t == Subtype (concatE g (esubFV x v_x g')) (tsubFV x v_x s) (tsubFV x v_x t)
                           && subtypSize' p_s_t == subtypSize' p'_s_t }
           / [subtypSize p_s_t, 0] @-}
lem_subst_sub_sbase :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Type -> WFType -> Type ->  WFType -> Subtype -> Subtype
lem_subst_sub_sbase g g' x v_x t_x p_vx_tx p_env_wf s p_env_s t p_env_t 
              (SBase env z1 b p1 z2 p2 y_ ent_yenv_p2) -- p_env_s_t
  = SBase (concatE g (esubFV x v_x g')) z1 b (subFV x v_x p1) z2 (subFV x v_x p2) y
          ent_yenv'_p2vx  -- Entails (Cons y (TRefn b z1 (subFV x v_x p1)) env') (unbind z2 y (subFV x v_x p2))
      where
        p_xg_wf          = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _)       = p_xg_wf
        y                = y_  ? lem_in_env_esub g' x v_x y_ 
                               ? lem_in_env_concat g  g' y_ 
                               ? lem_in_env_concat (Cons x t_x g) g' y_
                               ? lem_fv_bound_in_env g v_x t_x p_vx_tx p_g_wf y_
        (WFRefn _ _ _ _p2 w_ p_wenv_p2_bl) = p_env_t
        w                = w_  ? lem_in_env_concat g  g' w_ 
                               ? lem_in_env_concat (Cons x t_x g) g' w_
        p_yenv_wf        = WFEBind env p_env_wf y (TRefn b z1 p1) p_env_s
        p_yenv_p2_bl     = lem_change_var_ftyp (erase_env env) w (FTBasic b) FEmpty 
                                               (unbind z2 w p2) (FTBasic TBool) p_wenv_p2_bl y
                                               ? lem_subFV_unbind z2 w (FV y) p2
        --EntPred _yenv _p2 func_th_thp_tt = ent_yenv_p2 -- Entails (Cons y (TRefn b z1 p1) env) (unbind z2 y p2)
        ent_yenv'_p2vx   = lem_subst_ent g (Cons y (TRefn b z1 p1) g') x v_x t_x p_vx_tx p_yenv_wf
                               (unbind z2 y p2 ? lem_fv_subset_bindsF (FCons y (FTBasic b) (erase_env env)) 
                                   (unbind z2 y p2) (FTBasic TBool) p_yenv_p2_bl)
                               ent_yenv_p2 
                               ? lem_commute_subFV_subBV1 z2 (FV y) x 
                                   (v_x ? lem_freeBV_empty g v_x t_x p_vx_tx p_g_wf) p2 

{-@ lem_subst_sub_sfunc :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> ProofOf(HasType g v_x t_x) 
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) 
        -> s:Type -> ProofOf(WFType (concatE (Cons x t_x g) g') s)
        -> t:Type -> ProofOf(WFType (concatE (Cons x t_x g) g') t)
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t && isSFunc p_s_t }
        -> { p'_s_t:Subtype | propOf p'_s_t == Subtype (concatE g (esubFV x v_x g')) (tsubFV x v_x s) (tsubFV x v_x t)
                           && subtypSize' p_s_t == subtypSize' p'_s_t }
           / [subtypSize p_s_t, 0] @-}
lem_subst_sub_sfunc :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Type -> WFType -> Type -> WFType -> Subtype -> Subtype
lem_subst_sub_sfunc g g' x v_x t_x p_vx_tx p_env_wf ty1 p_env_ty1 ty2 p_env_ty2
              (SFunc env x1 s1 x2 s2 p_s2_s1 t1 t2 y_ p_yenv_t1_t2) 
  = SFunc (concatE g (esubFV x v_x g')) x1 (tsubFV x v_x s1) x2 (tsubFV x v_x s2)
          p_s2vx_s1vx (tsubFV x v_x t1) (tsubFV x v_x t2) y p_yg'g_t1vx_t2vx
      where 
        y                = y_  ? lem_in_env_esub g' x v_x y_ 
                               ? lem_in_env_concat g  g' y_ 
                               ? lem_in_env_concat (Cons x t_x g) g' y_
                               ? lem_fv_bound_in_env g v_x t_x p_vx_tx p_g_wf y_
        p_xg_wf          = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _)      = p_xg_wf
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
                                         ? lem_commute_tsubFV_tsubBV1 x1 (FV y) x 
                                             (v_x ? lem_freeBV_empty g v_x t_x p_vx_tx p_g_wf) t1
                                         ? lem_commute_tsubFV_tsubBV1 x2 (FV y) x 
                                             (v_x ? lem_freeBV_empty g v_x t_x p_vx_tx p_g_wf) t2 

{-@ lem_subst_sub_switn :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> ProofOf(HasType g v_x t_x) 
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) 
        -> s:Type -> ProofOf(WFType (concatE (Cons x t_x g) g') s)
        -> t:Type -> ProofOf(WFType (concatE (Cons x t_x g) g') t)
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t && isSWitn p_s_t }
        -> { p'_s_t:Subtype | propOf p'_s_t == Subtype (concatE g (esubFV x v_x g')) (tsubFV x v_x s) (tsubFV x v_x t)
                           && subtypSize' p_s_t == subtypSize' p'_s_t }
           / [subtypSize p_s_t, 0] @-}
lem_subst_sub_switn :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Type -> WFType -> Type -> WFType -> Subtype -> Subtype
lem_subst_sub_switn g g' x v_x t_x p_vx_tx p_env_wf t p_env_t t2 p_env_t2
              (SWitn env v_z t_z p_env_vz_tz _t z t' p_env_t_t'vz)
  = SWitn (concatE g (esubFV x v_x g')) (subFV x v_x v_z) (tsubFV x v_x t_z) p_g'g_vzvx_tzvx
          (tsubFV x v_x t) z (tsubFV x v_x t') p_g'g_tvx_t'vzvx
      where
        p_xg_wf          = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _)      = p_xg_wf
        (WFExis _ _ _ p_env_tz _ y p_yenv_t') = p_env_t2
        p_g'g_vzvx_tzvx  = lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf v_z t_z p_env_vz_tz
        p_yenv_wf        = WFEBind env p_env_wf y t_z p_env_tz
        p_env_t'vz       = lem_subst_wf' (concatE (Cons x t_x g) g') Empty y v_z t_z p_env_vz_tz 
                              p_yenv_wf (unbindT z y t') p_yenv_t' 
                              ? lem_tsubFV_unbindT z y v_z t'
        p_g'g_tvx_t'vzvx = lem_subst_sub g g' x v_x t_x p_vx_tx p_env_wf t p_env_t 
                                         (tsubBV z v_z t') p_env_t'vz p_env_t_t'vz
                                         ? lem_commute_tsubFV_tsubBV z v_z x 
                                             (v_x ? lem_freeBV_empty g v_x t_x p_vx_tx p_g_wf) t'

{-@ lem_subst_sub_sbind :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> ProofOf(HasType g v_x t_x) 
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) 
        -> s:Type -> ProofOf(WFType (concatE (Cons x t_x g) g') s)
        -> t:Type -> ProofOf(WFType (concatE (Cons x t_x g) g') t)
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t && isSBind p_s_t }
        -> { p'_s_t:Subtype | propOf p'_s_t == Subtype (concatE g (esubFV x v_x g')) (tsubFV x v_x s) (tsubFV x v_x t)
                           && subtypSize' p_s_t == subtypSize' p'_s_t }
           / [subtypSize p_s_t, 0] @-}
lem_subst_sub_sbind :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Type -> WFType -> Type -> WFType -> Subtype -> Subtype
lem_subst_sub_sbind g g' x v_x t_x p_vx_tx p_env_wf t1 p_env_t1 t' p_env_t'
              (SBind env z t_z t _t' w_ p_wenv_t_t') 
  = SBind (concatE g (esubFV x v_x g')) z (tsubFV x v_x t_z) (tsubFV x v_x t) (tsubFV x v_x t')
          w p_wenv'_tvx_t'vx
      where 
        p_xg_wf          = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _)       = p_xg_wf
        w                = w_ ? lem_in_env_esub g' x v_x w_
                              ? lem_in_env_concat g g' w_
                              ? lem_in_env_concat (Cons x t_x g) g' w_
                              ? lem_fv_bound_in_env g v_x t_x p_vx_tx p_g_wf w_
        (WFExis _ _ _ p_env_tz _ y p_yenv_t) = p_env_t1
        p_wenv_wf        = WFEBind (concatE (Cons x t_x g) g') p_env_wf w t_z p_env_tz
        p_wenv_t         = lem_change_var_wf env y t_z Empty (unbindT z y t) p_yenv_t w
                                             ? lem_tsubFV_unbindT z y (FV w) t
        p_wenv_t'        = lem_weaken_wf    env Empty t' p_env_t' w t_z
        p_wenv'_tvx_t'vx = lem_subst_sub g (Cons w t_z g') x v_x t_x p_vx_tx p_wenv_wf
                                         (unbindT z w t) p_wenv_t t' p_wenv_t' p_wenv_t_t'
                                         ? lem_commute_tsubFV_tsubBV z (FV w) x 
                                             (v_x ? lem_freeBV_empty g v_x t_x p_vx_tx p_g_wf) t

{-@ lem_subst_sub :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> ProofOf(HasType g v_x t_x) 
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) 
        -> s:Type -> ProofOf(WFType (concatE (Cons x t_x g) g') s)
        -> t:Type -> ProofOf(WFType (concatE (Cons x t_x g) g') t)
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t }
        -> { p'_s_t:Subtype | propOf p'_s_t == Subtype (concatE g (esubFV x v_x g')) (tsubFV x v_x s) (tsubFV x v_x t)
                           && subtypSize' p_s_t == subtypSize' p'_s_t }
           / [subtypSize p_s_t, 1] @-}
lem_subst_sub :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Type -> WFType -> Type -> WFType -> Subtype -> Subtype
lem_subst_sub g g' x v_x t_x p_vx_tx p_env_wf s p_env_s t p_env_t 
              p_s_t@(SBase env z1 b p1 z2 p2 y_ ent_yenv_p2) -- p_env_s_t
    = lem_subst_sub_sbase g g' x v_x t_x p_vx_tx p_env_wf s p_env_s t p_env_t p_s_t
lem_subst_sub g g' x v_x t_x p_vx_tx p_env_wf ty1 p_env_ty1 ty2 p_env_ty2
              p_ty1_ty2@(SFunc env_ x1 s1 x2 s2 p_s2_s1 t1 t2 y_ p_yenv_t1_t2) 
    = lem_subst_sub_sfunc g g' x v_x t_x p_vx_tx p_env_wf ty1 p_env_ty1 ty2 p_env_ty2 p_ty1_ty2
lem_subst_sub g g' x v_x t_x p_vx_tx p_env_wf t p_env_t t2 p_env_t2
              p_t_t2@(SWitn env v_z t_z p_env_vz_tz _t z t' p_env_t_t'vz) 
    = lem_subst_sub_switn g g' x v_x t_x p_vx_tx p_env_wf t p_env_t t2 p_env_t2 p_t_t2
lem_subst_sub g g' x v_x t_x p_vx_tx p_env_wf t1 p_env_t1 t' p_env_t'
              p_t1_t'@(SBind env z t_z t _t' w_ p_wenv_t_t') 
    = lem_subst_sub_sbind g g' x v_x t_x p_vx_tx p_env_wf t1 p_env_t1 t' p_env_t' p_t1_t'
