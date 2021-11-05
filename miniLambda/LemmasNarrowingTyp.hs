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
import SubstitutionLemmaTyp
import LemmasNarrowingEnt

{-@ reflect foo56 @-}
foo56 x = Just x
foo56 :: a -> Maybe a

{-@ lem_narrow_typ_tvar :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
        -> ProofOf(WFType g s_x) -> t_x:Type -> ProofOf(Subtype g s_x t_x)   
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t && isTVar p_e_t }
        -> ProofOf(HasType (concatE (Cons x s_x g) g') e t) / [typSize p_e_t, 0] @-}
lem_narrow_typ_tvar :: Env -> Env -> Vname -> Type -> WFType -> Type -> Subtype -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_narrow_typ_tvar g g' x s_x p_g_sx t_x p_sx_tx p_env_wf e t p_e_t@(TVar1 _env z t' p_env_t')
  = case g' of 
      (Empty)           -> p_z_tx  
        where
          (WFEBind _g p_g_wf _x _tx p_g_tx) = p_env_wf
          p_xg_wf     = WFEBind g p_g_wf x s_x p_g_sx 
          p_xg_sx     = lem_weaken_wf g Empty s_x p_g_sx x s_x 
          p_z_er_sx   = FTVar1 (erase_env g) z (erase s_x) ? lem_erase_subtype g s_x t_x p_sx_tx
          p_z_sx      = TVar1 g z s_x p_g_sx
          p_xtxg_t    = lem_typing_wf (Cons x t_x g) e t p_e_t p_env_wf 
          p_xsxg_t    = lem_subtype_in_env_wf g Empty x s_x t_x p_sx_tx t p_xtxg_t
          p_xg_sx_tx  = lem_weaken_subtype g Empty p_g_wf s_x p_g_sx t_x p_g_tx p_sx_tx x s_x
          p_xg_sx_tx' = lem_exact_subtype (Cons z s_x g) p_xg_wf s_x p_xg_sx t_x p_xg_sx_tx 
                                          (FV z) p_z_er_sx
          p_z_tx      = TSub (Cons x s_x g) (FV z) (self s_x (FV z)) p_z_sx (self t_x (FV z)) 
                             p_xsxg_t p_xg_sx_tx'
      (Cons _z _ g'')  -> TVar1 (concatE (Cons x s_x g) g'')  
                                (z ? lem_in_env_concat (Cons x s_x g) g'' z
                                   ? lem_in_env_concat g g'' z
                                   ? lem_in_env_concat (Cons x t_x g) g'' z) t' p_env'_t'
        where
          p_env'_t' = lem_subtype_in_env_wf g g'' x s_x t_x p_sx_tx t' p_env_t'
lem_narrow_typ_tvar g g' x s_x p_g_sx t_x p_sx_tx p_env_wf e _t (TVar2 env' z_ t p_z_t w t_w) 
  = case g' of             -- g''=Emp so x=w and p_z_t :: HasType(g (FV z) t)
        (Empty)           -> TVar2 g z_ t p_z_t w s_x
        (Cons _w _tw g'') -> TVar2 (concatE (Cons x s_x g) g'') z t p'_z_t w t_w 
          where
            (WFEBind _env' p_env'_wf _ _ _) = p_env_wf
            z      = z_ ? lem_in_env_concat (Cons x s_x g) g'' z_
                        ? lem_in_env_concat g g'' z_
                        ? lem_in_env_concat (Cons x t_x g) g'' z_
            p'_z_t = lem_narrow_typ g g'' x s_x p_g_sx t_x p_sx_tx p_env'_wf (FV z) t p_z_t

{-@ lem_narrow_typ :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
        -> ProofOf(WFType g s_x) -> t_x:Type -> ProofOf(Subtype g s_x t_x)   
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t }
        -> ProofOf(HasType (concatE (Cons x s_x g) g') e t) / [typSize p_e_t, 1] @-}
lem_narrow_typ :: Env -> Env -> Vname -> Type -> WFType -> Type -> Subtype -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_narrow_typ g g' x s_x p_g_sx t_x p_sx_tx p_env_wf e t (TBC _env b) 
  = TBC (concatE (Cons x s_x g) g') b 
lem_narrow_typ g g' x s_x p_g_sx t_x p_sx_tx p_env_wf e t (TIC _env n) 
  = TIC (concatE (Cons x s_x g) g') n 
lem_narrow_typ g g' x s_x p_g_sx t_x p_sx_tx p_env_wf e t p_e_t@(TVar1 _env z _ _) 
  = lem_narrow_typ_tvar g g' x s_x p_g_sx t_x p_sx_tx p_env_wf e t p_e_t
lem_narrow_typ g g' x s_x p_g_sx t_x p_sx_tx p_env_wf e t p_e_t@(TVar2 env_ z _t p_z_t w_ t_w) 
  = lem_narrow_typ_tvar g g' x s_x p_g_sx t_x p_sx_tx p_env_wf e t p_e_t
lem_narrow_typ g g' x s_x p_g_sx t_x p_sx_tx p_env_wf e t (TPrm _en c) 
  = TPrm (concatE (Cons x s_x g) g') c 
lem_narrow_typ g g' x s_x p_g_sx t_x p_sx_tx p_env_wf e t (TAbs env_ z t_z p_env_tz e' t' y_ p_yenv_e'_t') 
  = TAbs (concatE (Cons x s_x g) g') z t_z p_env'_tz e' t' y p_yenv'_e'_t'
      where
        y               = y_  ? lem_in_env_concat g  g' y_ 
                              ? lem_in_env_concat (Cons x t_x g) g' y_
                              ? lem_in_env_concat (Cons x s_x g) g' y_
        p_yenv_wf       = WFEBind (concatE (Cons x t_x g) g') p_env_wf y t_z p_env_tz
        p_env'_tz       = lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t_z p_env_tz
        p_yenv'_e'_t'   = lem_narrow_typ g (Cons y t_z g') x s_x p_g_sx t_x p_sx_tx p_yenv_wf
                                         (unbind z y e') (unbindT z y t') p_yenv_e'_t'
lem_narrow_typ g g' x s_x p_g_sx t_x p_sx_tx p_env_wf e t 
               (TApp env_ e' z t_z t' p_env_e'_tzt' e_z p_env_ez_tz) 
  = TApp (concatE (Cons x s_x g) g') e' z t_z t' p_env'_e'_tzt' e_z p_env'_ez_tz
      where
        p_env'_e'_tzt' = lem_narrow_typ g g' x s_x p_g_sx t_x p_sx_tx p_env_wf 
                                        e' (TFunc z t_z t') p_env_e'_tzt'
        p_env'_ez_tz   = lem_narrow_typ g g' x s_x p_g_sx t_x p_sx_tx p_env_wf e_z t_z p_env_ez_tz
lem_narrow_typ g g' x s_x p_g_sx t_x p_sx_tx p_env_wf e t 
               (TSub env_ e_ s p_env_e_s t_ p_env_t p_env_s_t) 
  = TSub (concatE (Cons x s_x g) g') e s p_env'_e_s t p_env'_t p_env'_s_t
      where
        p_env'_e_s = lem_narrow_typ g g' x s_x p_g_sx t_x p_sx_tx p_env_wf e s p_env_e_s
        p_env'_t   = lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t p_env_t
        p_env_s    = lem_typing_wf (concatE (Cons x t_x g) g') e s p_env_e_s p_env_wf
        p_env'_s_t = lem_narrow_sub g g' x s_x p_g_sx t_x p_sx_tx p_env_wf s p_env_s t p_env_t p_env_s_t 


{-@ lem_narrow_sub :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type -> ProofOf(WFType g s_x)
        -> t_x:Type -> ProofOf(Subtype g s_x t_x) -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
        -> s:Type -> ProofOf(WFType (concatE (Cons x t_x g) g') s) 
        -> t:Type -> ProofOf(WFType (concatE (Cons x t_x g) g') t)
        -> { p_s_t:Subtype  | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t }
        -> { p'_s_t:Subtype | propOf p'_s_t == (Subtype (concatE (Cons x s_x g) g') s t) 
                              && subtypSize' p_s_t == subtypSize' p'_s_t } / [subtypSize p_s_t, 1] @-}
lem_narrow_sub :: Env -> Env -> Vname -> Type -> WFType -> Type -> Subtype -> WFEnv
                    -> Type -> WFType -> Type -> WFType -> Subtype -> Subtype
lem_narrow_sub g g' x s_x p_g_sx t_x p_sx_tx p_env_wf s  p_env_s t p_env_t
              (SBase env z1 b p1 z2 p2 y_ ent_yenv_p2) -- p_env_s_t
  = SBase (concatE (Cons x s_x g) g') z1 b p1 z2 p2 y ent_yenv'_p2
      where
        y             = y_
        p_yenv_wf     = WFEBind (concatE (Cons x t_x g) g') p_env_wf y (TRefn b z1 p1) p_env_s
        (WFRefn _ _ _ _p2 w_ p_wenv_p2_bl) = p_env_t
        w                = w_  ? lem_in_env_concat g  g' w_
                               ? lem_in_env_concat (Cons x t_x g) g' w_
        p_yenv_p2_bl  = lem_change_var_ftyp (erase_env env) w (FTBasic b) FEmpty
                                            (unbind z2 w p2) (FTBasic TBool) p_wenv_p2_bl y
                                            ? lem_subFV_unbind z2 w (FV y) p2
        ent_yenv'_p2  = lem_narrow_ent g (Cons y (TRefn b z1 p1) g') x s_x t_x p_sx_tx 
                            p_g_sx p_yenv_wf (unbind z2 y p2 
                                ? lem_fv_subset_bindsF (FCons y (FTBasic b) (erase_env env))
                                                       (unbind z2 y p2) (FTBasic TBool) p_yenv_p2_bl)
                            ent_yenv_p2
lem_narrow_sub g g' x s_x p_g_sx t_x p_sx_tx p_env_wf ty1 p_env_ty1 ty2 p_env_ty2
              (SFunc env_ x1 s1 x2 s2 p_s2_s1 t1 t2 y p_yenv_t1_t2) 
  = SFunc (concatE (Cons x s_x g) g') x1 s1 x2 s2 p_env'_s2_s1 t1 t2 y p_yenv'_t1_t2
      where
        (WFFunc _ _ _ p_env_s1 _ w1 p_w1env_t1) = p_env_ty1
        (WFFunc _ _ _ p_env_s2 _ w2 p_w2env_t2) = p_env_ty2
        p_env'_s2_s1  = lem_narrow_sub g g' x s_x p_g_sx t_x p_sx_tx p_env_wf s2 p_env_s2
                                       s1 p_env_s1 p_s2_s1
        p_yenv_wf     = WFEBind (concatE (Cons x t_x g) g') p_env_wf y s2 p_env_s2
        _p_yenv_t1    = lem_change_var_wf (concatE (Cons x t_x g) g') w1 s1 Empty 
                                          (unbindT x1 w1 t1) p_w1env_t1 y
                                          ? lem_tsubFV_unbindT x1 w1 (FV y) t1
        p_yenv_t1     = lem_subtype_in_env_wf (concatE (Cons x t_x g) g') Empty y s2 s1 
                                              p_s2_s1 (unbindT x1 y t1) _p_yenv_t1
        p_yenv_t2     = lem_change_var_wf (concatE (Cons x t_x g) g') w2 s2 Empty
                                          (unbindT x2 w2 t2) p_w2env_t2 y
                                          ? lem_tsubFV_unbindT x2 w2 (FV y) t2
        p_yenv'_t1_t2 = lem_narrow_sub g (Cons y s2 g') x s_x p_g_sx t_x p_sx_tx p_yenv_wf
                                       (unbindT x1 y t1) p_yenv_t1 
                                       (unbindT x2 y t2) p_yenv_t2 p_yenv_t1_t2
lem_narrow_sub g g' x s_x p_g_sx t_x p_sx_tx p_env_wf t  p_env_t t2  p_env_t2
              (SWitn env v_z t_z p_env_vz_tz _t z t' p_env_t_t'vz) 
  = SWitn (concatE (Cons x s_x g) g') v_z t_z p_env'_vz_tz t z t' p_env'_t_t'vz
      where
        p_env'_vz_tz  = lem_narrow_typ g g' x s_x p_g_sx t_x p_sx_tx p_env_wf v_z t_z p_env_vz_tz
        (WFExis _ _ _ p_env_tz _ y p_yenv_t') = p_env_t2
        p_yenv_wf     = WFEBind (concatE (Cons x t_x g) g') p_env_wf y t_z p_env_tz
        p_env_t'vz    = lem_subst_wf'  (concatE (Cons x t_x g) g') Empty y v_z t_z p_env_vz_tz 
                                       p_yenv_wf (unbindT z y t') p_yenv_t' 
                                       ? lem_tsubFV_unbindT z y v_z t'
        p_env'_t_t'vz = lem_narrow_sub g g' x s_x p_g_sx t_x p_sx_tx p_env_wf t p_env_t
                                       (tsubBV z v_z t') p_env_t'vz p_env_t_t'vz
lem_narrow_sub g g' x s_x p_g_sx t_x p_sx_tx p_env_wf t1  p_env_t1 t'  p_env_t'
              (SBind env z t_z t _t' w p_wenv_t_t') 
  = SBind (concatE (Cons x s_x g) g') z t_z t t' w p_wenv'_t_t'
      where
        (WFExis _ _ _ p_env_tz _ y p_yenv_t) = p_env_t1
        p_wenv_wf     = WFEBind (concatE (Cons x t_x g) g') p_env_wf w t_z p_env_tz
        p_wenv_t      = lem_change_var_wf (concatE (Cons x t_x g) g') y t_z Empty (unbindT z y t) 
                                          p_yenv_t w ? lem_tsubFV_unbindT z y (FV w) t
        p_wenv_t'     = lem_weaken_wf  env Empty t' p_env_t' w t_z
        p_wenv'_t_t'  = lem_narrow_sub g (Cons w t_z g') x s_x p_g_sx t_x p_sx_tx p_wenv_wf
                                       (unbindT z w t) p_wenv_t t' p_wenv_t' p_wenv_t_t'
