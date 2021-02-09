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
import BasicPropsEraseTyping
import Entailments
import LemmasChangeVarWF
import LemmasWeakenWF
import LemmasWellFormedness
import LemmasTyping
import LemmasSubtyping
import LemmasChangeVarTyp
import LemmasWeakenTyp
import SubstitutionWFAgain
import DenotationsSelfify
import PrimitivesSemantics
import PrimitivesDenotations
import DenotationsSoundness
import LemmasExactness
import SubstitutionLemmaEnt
import SubstitutionLemmaTyp
import LemmasNarrowingEnt

{-@ reflect foo70 @-}
foo70 x = Just x
foo70 :: a -> Maybe a

{-@ lem_narrow_typ_tvar :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
        -> k_sx:Kind -> ProofOf(WFType g s_x k_sx) -> t_x:Type -> ProofOf(Subtype g s_x t_x)   
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t && isTVar p_e_t }
        -> ProofOf(HasType (concatE (Cons x s_x g) g') e t) / [typSize p_e_t, 0] @-}
lem_narrow_typ_tvar :: Env -> Env -> Vname -> Type -> Kind -> WFType -> Type -> Subtype -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_narrow_typ_tvar g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf e t p_e_t@(TVar1 _env z t' k' p_env_t') 
   = case g' of                                                -- t == self t'  (FV z) k'
      (Empty)           -> p_z_tx                              -- t == self t_x (FV z) k'
        where
          (WFEBind _g p_g_wf _x _tx k_x p_g_tx) = p_env_wf
          p_er_g_wf   = lem_erase_env_wfenv g p_g_wf
          p_env'_wf   = WFEBind g p_g_wf x s_x k_sx p_g_sx
          p_g_sx_star = if k_sx == Star then p_g_sx else WFKind g s_x p_g_sx 
          p_z_sx      = TVar1 g z s_x Star p_g_sx_star ? (self s_x (FV z) Star === s_x)
          p_env'_sx   = lem_weaken_wf' g Empty p_g_wf s_x k_sx p_g_sx x s_x
          p_env'_t'   = lem_weaken_wf' g Empty p_g_wf t_x k' p_env_t' x s_x
          p_xg_sx_tx  = lem_weaken_subtype g Empty p_g_wf s_x k_sx p_g_sx t_x k_x p_g_tx p_sx_tx x s_x
          p_z_er_tx   = lem_typing_hasftype (Cons x t_x g) (FV z) t p_e_t p_env_wf
                            ? lem_erase_subtype g s_x t_x p_sx_tx
          p_env'_sxk' = lem_sub_pullback_wftype (concatE (Cons x s_x g) g') p_env'_wf s_x t' 
                                                p_xg_sx_tx k_sx p_env'_sx k' p_env'_t'
          p_xg_sx_tx' = lem_exact_subtype (Cons x s_x g) p_env'_wf s_x k_sx p_env'_sx t_x 
                                          p_xg_sx_tx k' p_env'_t' (FV z) 
                                          (FTVar1 (erase_env g) z (erase t_x)
                                            ? lem_erase_subtype g s_x t_x p_sx_tx)
          p_z_self_sx = lem_exact_type (Cons x s_x g) (FV z) s_x p_z_sx k' p_env'_sxk' p_env'_wf
          p_xtxg_t    = lem_typing_wf (Cons x t_x g) (FV z) (self t_x (FV z) k') p_e_t p_env_wf
          p_xsxg_t    = lem_subtype_in_env_wf g Empty x s_x t_x p_sx_tx t Star p_xtxg_t
          p_z_tx      = TSub (Cons x s_x g) (FV z) (self s_x (FV z) k') p_z_self_sx 
                             (self t_x (FV z) k') Star {-k'-} p_xsxg_t p_xg_sx_tx'
      (Cons _z _ g'')  -> TVar1 (concatE (Cons x s_x g) g'')  
                                (z ? lem_in_env_concat (Cons x s_x g) g'' z
                                   ? lem_in_env_concat g g'' z
                                   ? lem_in_env_concat (Cons x t_x g) g'' z) t' k' p_env'_t'
        where
          p_env'_t'   = lem_subtype_in_env_wf g g'' x s_x t_x p_sx_tx t' k' p_env_t' 
lem_narrow_typ_tvar g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf e _t (TVar2 env' z_ t p_z_t w_ t_w) 
  = case g' of             -- g''=Emp so x=w and p_z_t :: HasType(g (FV z) t)
        (Empty)           -> TVar2 g z_ t p_z_t w_ s_x
        (Cons _w _tw g'') -> TVar2 (concatE (Cons x s_x g) g'') z t p'_z_t w t_w 
          where
            (WFEBind _env' p_env'_wf _ _ _ _) = p_env_wf
            z      = z_ ? lem_in_env_concat (Cons x s_x g) g'' z_
                        ? lem_in_env_concat g g'' z_
                        ? lem_in_env_concat (Cons x t_x g) g'' z_
            w      = w_ ? lem_in_env_concat (Cons x s_x g) g'' w_
                        ? lem_in_env_concat (Cons x t_x g) g'' w_
            p'_z_t = lem_narrow_typ g g'' x s_x k_sx p_g_sx t_x p_sx_tx p_env'_wf (FV z) t p_z_t
lem_narrow_typ_tvar g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf e t (TVar3 env_ z_ _t p_z_t a_ k_a) 
  = case g' of 
        (Empty)            -> impossible "x <> a"
        (ConsT _a _ka g'') -> TVar3 (concatE (Cons x s_x g) g'') z t p'_z_t a k_a
          where
            (WFEBindT _env' p_env'_wf _ _) = p_env_wf
            z      = z_ ? lem_in_env_concat (Cons x s_x g) g'' z_
                        ? lem_in_env_concat g g'' z_
                        ? lem_in_env_concat (Cons x t_x g) g'' z_
            a      = a_ ? lem_in_env_concat (Cons x s_x g) g'' a_
                        ? lem_in_env_concat (Cons x t_x g) g'' a_
            p'_z_t = lem_narrow_typ g g'' x s_x k_sx p_g_sx t_x p_sx_tx p_env'_wf (FV z) t p_z_t

{-@ lem_narrow_typ :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
        -> k_sx:Kind -> ProofOf(WFType g s_x k_sx) -> t_x:Type -> ProofOf(Subtype g s_x t_x)   
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t }
        -> ProofOf(HasType (concatE (Cons x s_x g) g') e t) / [typSize p_e_t, 1] @-}
lem_narrow_typ :: Env -> Env -> Vname -> Type -> Kind -> WFType -> Type -> Subtype -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf e t (TBC _env b) 
  = TBC (concatE (Cons x s_x g) g') b 
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf e t (TIC _env n) 
  = TIC (concatE (Cons x s_x g) g') n 
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf e t p_e_t@(TVar1 _env z _t _ _) 
  = lem_narrow_typ_tvar g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf e t p_e_t
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf e t p_e_t@(TVar2 env_ z _t p_z_t w_ t_w) 
  = lem_narrow_typ_tvar g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf e t p_e_t
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf e t p_e_t@(TVar3 env_ z _t p_z_t a_ k_a) 
  = lem_narrow_typ_tvar g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf e t p_e_t
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf e t (TPrm _en c) 
  = TPrm (concatE (Cons x s_x g) g') c 
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf e t 
               (TAbs env_ z t_z k_z p_env_tz e' t' y_ p_yenv_e'_t') 
  = TAbs (concatE (Cons x s_x g) g') z t_z k_z p_env'_tz e' t' y p_yenv'_e'_t'
      where
        y               = y_  ? lem_in_env_concat g  g' y_
                              ? lem_in_env_concat (Cons x t_x g) g' y_
                              ? lem_in_env_concat (Cons x s_x g) g' y_
        p_yenv_wf       = WFEBind (concatE (Cons x t_x g) g') p_env_wf y t_z k_z p_env_tz
        p_env'_tz       = lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t_z k_z p_env_tz
        p_yenv'_e'_t'   = lem_narrow_typ g (Cons y t_z g') x s_x k_sx p_g_sx t_x p_sx_tx p_yenv_wf
                                         (unbind z y e') (unbindT z y t') p_yenv_e'_t'
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf e t 
               (TApp env_ e' z t_z t' p_env_e'_tzt' e_z p_env_ez_tz) 
  = TApp (concatE (Cons x s_x g) g') e' z t_z t' p_env'_e'_tzt' e_z p_env'_ez_tz
      where
        p_env'_e'_tzt' = lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf
                                        e' (TFunc z t_z t') p_env_e'_tzt'
        p_env'_ez_tz   = lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf 
                                        e_z t_z p_env_ez_tz
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf e t 
               (TAbsT env a k e' t' k_t' a'_ p_a'env_e'_t' p_a'env_t')
  = TAbsT (concatE (Cons x s_x g) g') a k e' t' k_t' a' p_a'env'_e'_t' p_a'env'_t'
      where
        a'             = a'_ ? lem_in_env_concat g  g' a'_
                             ? lem_in_env_concat (Cons x t_x g) g' a'_
                             ? lem_in_env_concat (Cons x s_x g) g' a'_
        p_a'env_wf     = WFEBindT (concatE (Cons x t_x g) g') p_env_wf a' k
        p_a'env'_e'_t' = lem_narrow_typ g (ConsT a' k g') x s_x k_sx p_g_sx t_x p_sx_tx p_a'env_wf
                                        (unbind_tv a a' e') (unbind_tvT a a' t') p_a'env_e'_t'
        p_a'env'_t'    = lem_subtype_in_env_wf g (ConsT a' k g') x s_x t_x p_sx_tx 
                                        (unbind_tvT a a' t') k_t' p_a'env_t'
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf e t 
               (TAppT env e' a k s p_e'_as t' p_env_t') 
  = TAppT (concatE (Cons x s_x g) g') e' a k s p_env'_e'_as t' p_env'_t'
      where
        p_env'_e'_as = lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf
                                      e' (TPoly a k s) p_e'_as
        p_env'_t'    = lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t' k p_env_t'
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf e t 
               (TLet env_ e_z t_z p_env_ez_tz z e' t_ k p_env_t y p_yenv_e'_t) 
  = TLet (concatE (Cons x s_x g) g') e_z t_z p_env'_ez_tz z e' t k p_env'_t y p_yenv'_e'_t
      where
        p_env'_ez_tz   = lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf 
                                        e_z t_z p_env_ez_tz
        p_env_tz       = lem_typing_wf env_ e_z t_z p_env_ez_tz p_env_wf
        p_yenv_wf      = WFEBind (concatE (Cons x t_x g) g') p_env_wf y t_z Star p_env_tz
        p_env'_t       = lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t k p_env_t
        p_yenv'_e'_t   = lem_narrow_typ g (Cons y t_z g') x s_x k_sx p_g_sx t_x p_sx_tx p_yenv_wf
                                        (unbind z y e') (unbindT z y t) p_yenv_e'_t
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf e t (TAnn env_ e' t_ p_env_e'_t) 
  = TAnn (concatE (Cons x s_x g) g') e' t p_env'_e'_t
      where
        p_env'_e'_t = lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf e' t p_env_e'_t
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf e t 
               (TSub env_ e_ s p_env_e_s t_ k p_env_t p_env_s_t) 
  = TSub (concatE (Cons x s_x g) g') e s p_env'_e_s t k p_env'_t p_env'_s_t
      where
        p_env'_e_s = lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf e s p_env_e_s
        p_env'_t   = lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t k p_env_t
        p_env_s    = lem_typing_wf (concatE (Cons x t_x g) g') e s p_env_e_s p_env_wf
        p_env'_s_t = lem_narrow_sub g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf 
                                    s Star p_env_s t k p_env_t p_env_s_t 


{-@ lem_narrow_sub_sbase :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
        -> k_sx:Kind -> ProofOf(WFType g s_x k_sx) -> t_x:Type -> ProofOf(Subtype g s_x t_x) 
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
        -> s:Type -> k_s:Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') s k_s)
        -> t:Type -> k_t:Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') t k_t)
        -> { p_s_t:Subtype  | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t && isSBase p_s_t }
        -> { p'_s_t:Subtype | propOf p'_s_t == (Subtype (concatE (Cons x s_x g) g') s t) 
                              && subtypSize' p_s_t == subtypSize' p'_s_t } / [subtypSize p_s_t, 0] @-}
lem_narrow_sub_sbase :: Env -> Env -> Vname -> Type -> Kind -> WFType -> Type -> Subtype -> WFEnv
                    -> Type -> Kind -> WFType -> Type -> Kind -> WFType -> Subtype -> Subtype
lem_narrow_sub_sbase g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf s k_s p_env_s t k_t p_env_t
                     (SBase env z1 b p1 z2 p2 y ent_yenv_p2) -- p_env_s_t
  = SBase (concatE (Cons x s_x g) g') z1 b p1 z2 p2 y ent_yenv'_p2
      where
        p_yenv_wf     = WFEBind (concatE (Cons x t_x g) g') p_env_wf y s k_s p_env_s
        (w_, p_wenv_p2_bl) = lem_ftyp_for_wf_trefn env b z2 p2 k_t p_env_t
        w                = w_  ? lem_in_env_concat g  g' w_
                               ? lem_in_env_concat (Cons x t_x g) g' w_
        p_wenv_wf     = WFFBind (erase_env env) (lem_erase_env_wfenv env p_env_wf)
                                w (erase s) k_s (lem_erase_wftype env s k_s p_env_s)
        p_yenv_p2_bl  = lem_change_var_ftyp (erase_env env) w (FTBasic b) FEmpty p_wenv_wf
                                            (unbind 0 w p2) (FTBasic TBool) p_wenv_p2_bl y
                                            ? lem_subFV_unbind 0 w (FV y) p2
        ent_yenv'_p2  = lem_narrow_ent g (Cons y (TRefn b z1 p1) g') x s_x t_x p_sx_tx
                            k_sx p_g_sx p_yenv_wf (unbind 0 y p2
                                ? lem_fv_subset_bindsF (FCons y (FTBasic b) (erase_env env))
                                                       (unbind 0 y p2) (FTBasic TBool) p_yenv_p2_bl)
                            ent_yenv_p2

{-@ lem_narrow_sub_sfunc :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
        -> k_sx:Kind -> ProofOf(WFType g s_x k_sx) -> t_x:Type -> ProofOf(Subtype g s_x t_x) 
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
        -> s:Type -> k_s:Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') s k_s)
        -> t:Type -> k_t:Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') t k_t)
        -> { p_s_t:Subtype  | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t && isSFunc p_s_t }
        -> { p'_s_t:Subtype | propOf p'_s_t == (Subtype (concatE (Cons x s_x g) g') s t) 
                              && subtypSize' p_s_t == subtypSize' p'_s_t } / [subtypSize p_s_t, 0] @-}
lem_narrow_sub_sfunc :: Env -> Env -> Vname -> Type -> Kind -> WFType -> Type -> Subtype -> WFEnv
                    -> Type -> Kind -> WFType -> Type -> Kind -> WFType -> Subtype -> Subtype
lem_narrow_sub_sfunc g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf ty1 ky1 p_env_ty1 ty2 ky2 p_env_ty2
               (SFunc env x1 s1 x2 s2 p_s2_s1 t1 t2 y p_yenv_t1_t2) 
  = SFunc (concatE (Cons x s_x g) g') x1 s1 x2 s2 p_env'_s2_s1 t1 t2 y p_yenv'_t1_t2 
      where                    
        (WFFunc _ _ _ k_s1 p_env_s1 _ k_t1 w1 p_w1env_t1) 
                      = lem_wffunc_for_wf_tfunc env x1 s1 t1 ky1 p_env_ty1
        (WFFunc _ _ _ k_s2 p_env_s2 _ k_t2 w2 p_w2env_t2) 
                      = lem_wffunc_for_wf_tfunc env x2 s2 t2 ky2 p_env_ty2 
        p_env'_s2_s1  = lem_narrow_sub g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf 
                                       s2 k_s2 p_env_s2 s1 k_s1 p_env_s1 p_s2_s1
        p_yenv_wf     = WFEBind (concatE (Cons x t_x g) g') p_env_wf y  s2 k_s2 p_env_s2
        p_w1env_wf    = WFEBind (concatE (Cons x t_x g) g') p_env_wf w1 s1 k_s1 p_env_s1
        p_w2env_wf    = WFEBind (concatE (Cons x t_x g) g') p_env_wf w2 s2 k_s2 p_env_s2
        _p_yenv_t1    = lem_change_var_wf' (concatE (Cons x t_x g) g') w1 s1 Empty p_w1env_wf
                                           (unbindT x1 w1 t1) k_t1 p_w1env_t1 y
                                           ? lem_tsubFV_unbindT x1 w1 (FV y) t1
        p_yenv_t1     = lem_subtype_in_env_wf (concatE (Cons x t_x g) g') Empty y s2 s1 
                                              p_s2_s1 (unbindT x1 y t1) k_t1 _p_yenv_t1
        p_yenv_t2     = lem_change_var_wf' (concatE (Cons x t_x g) g') w2 s2 Empty p_w2env_wf
                                           (unbindT x2 w2 t2) k_t2 p_w2env_t2 y
                                           ? lem_tsubFV_unbindT x2 w2 (FV y) t2
        p_yenv'_t1_t2 = lem_narrow_sub g (Cons y s2 g') x s_x k_sx p_g_sx t_x p_sx_tx p_yenv_wf
                                       (unbindT x1 y t1) k_t1 p_yenv_t1 
                                       (unbindT x2 y t2) k_t2 p_yenv_t2 p_yenv_t1_t2

{-@ lem_narrow_sub_switn :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
        -> k_sx:Kind -> ProofOf(WFType g s_x k_sx) -> t_x:Type -> ProofOf(Subtype g s_x t_x) 
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
        -> s:Type -> k_s:Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') s k_s)
        -> t:Type -> k_t:Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') t k_t)
        -> { p_s_t:Subtype  | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t && isSWitn p_s_t }
        -> { p'_s_t:Subtype | propOf p'_s_t == (Subtype (concatE (Cons x s_x g) g') s t) 
                              && subtypSize' p_s_t == subtypSize' p'_s_t } / [subtypSize p_s_t, 0] @-}
lem_narrow_sub_switn :: Env -> Env -> Vname -> Type -> Kind -> WFType -> Type -> Subtype -> WFEnv
                    -> Type -> Kind -> WFType -> Type -> Kind -> WFType -> Subtype -> Subtype
lem_narrow_sub_switn g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf t k p_env_t t2 k2 p_env_t2
               (SWitn env v_z t_z p_env_vz_tz _t z t' p_env_t_t'vz) 
  = SWitn (concatE (Cons x s_x g) g') v_z t_z p_env'_vz_tz t z t' p_env'_t_t'vz  
      where
        p_env'_vz_tz  = lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf 
                                       v_z t_z p_env_vz_tz
        (WFExis _ _ _ k_z p_env_tz _ k' y p_yenv_t') 
                      = lem_wfexis_for_wf_texists env z t_z t' k2 p_env_t2
        p_yenv_wf     = WFEBind (concatE (Cons x t_x g) g') p_env_wf y t_z k_z p_env_tz
        p_env_t'vz    = lem_subst_wf' (concatE (Cons x t_x g) g') Empty y v_z t_z p_env_vz_tz
                                      p_yenv_wf (unbindT z y t') k' p_yenv_t'
                                      ? lem_tsubFV_unbindT z y v_z t'
        p_env'_t_t'vz = lem_narrow_sub g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf t k p_env_t
                                       (tsubBV z v_z t') k' p_env_t'vz p_env_t_t'vz  

{-@ lem_narrow_sub_sbind :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
        -> k_sx:Kind -> ProofOf(WFType g s_x k_sx) -> t_x:Type -> ProofOf(Subtype g s_x t_x) 
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
        -> s:Type -> k_s:Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') s k_s)
        -> t:Type -> k_t:Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') t k_t)
        -> { p_s_t:Subtype  | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t && isSBind p_s_t }
        -> { p'_s_t:Subtype | propOf p'_s_t == (Subtype (concatE (Cons x s_x g) g') s t) 
                              && subtypSize' p_s_t == subtypSize' p'_s_t } / [subtypSize p_s_t, 0] @-}
lem_narrow_sub_sbind :: Env -> Env -> Vname -> Type -> Kind -> WFType -> Type -> Subtype -> WFEnv
                    -> Type -> Kind -> WFType -> Type -> Kind -> WFType -> Subtype -> Subtype
lem_narrow_sub_sbind g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf t1 k1 p_env_t1 t' k' p_env_t'
                     (SBind env z t_z t _t' w p_wenv_t_t') 
  = SBind (concatE (Cons x s_x g) g') z t_z t t' w p_wenv'_t_t'
      where
        (WFExis _ _ _ k_z p_env_tz _ k y p_yenv_t) 
                      = lem_wfexis_for_wf_texists (concatE (Cons x t_x g) g') z t_z t k1 p_env_t1
        p_wenv_wf     = WFEBind (concatE (Cons x t_x g) g') p_env_wf w t_z k_z p_env_tz
        p_yenv_wf     = WFEBind (concatE (Cons x t_x g) g') p_env_wf y t_z k_z p_env_tz
        p_wenv_t      = lem_change_var_wf' (concatE (Cons x t_x g) g') y t_z Empty p_yenv_wf 
                                           (unbindT z y t) k
                                           p_yenv_t w ? lem_tsubFV_unbindT z y (FV w) t
        p_wenv_t'     = lem_weaken_wf'  env Empty p_env_wf t' k' p_env_t' w t_z
        p_wenv'_t_t'  = lem_narrow_sub g (Cons w t_z g') x s_x k_sx p_g_sx t_x p_sx_tx p_wenv_wf
                                       (unbindT z w t) k p_wenv_t t' k' p_wenv_t' p_wenv_t_t'

{-@ lem_narrow_sub_spoly :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
        -> k_sx:Kind -> ProofOf(WFType g s_x k_sx) -> t_x:Type -> ProofOf(Subtype g s_x t_x) 
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
        -> s:Type -> k_s:Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') s k_s)
        -> t:Type -> k_t:Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') t k_t)
        -> { p_s_t:Subtype  | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t && isSPoly p_s_t }
        -> { p'_s_t:Subtype | propOf p'_s_t == (Subtype (concatE (Cons x s_x g) g') s t) 
                              && subtypSize' p_s_t == subtypSize' p'_s_t } / [subtypSize p_s_t, 0] @-}
lem_narrow_sub_spoly :: Env -> Env -> Vname -> Type -> Kind -> WFType -> Type -> Subtype -> WFEnv
                    -> Type -> Kind -> WFType -> Type -> Kind -> WFType -> Subtype -> Subtype
lem_narrow_sub_spoly g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf t1 Star p_env_t1 t2 Star p_env_t2
                     (SPoly env a1 k t1' a2 t2' a p_env_t1'_t2') 
  = SPoly (concatE (Cons x s_x g) g') a1 k t1' a2 t2' a p_env'_t1'_t2'
      where
        (WFPoly _ _ _ _ k_t1' a1' p_a1'env_t1')
                       = lem_wfpoly_for_wf_tpoly env a1 k t1' p_env_t1
        (WFPoly _ _ _ _ k_t2' a2' p_a2'env_t2')
                       = lem_wfpoly_for_wf_tpoly env a2 k t2' p_env_t2
        p_aenv_wf      = WFEBindT env p_env_wf a   k
        p_a1'env_wf    = WFEBindT env p_env_wf a1' k
        p_a2'env_wf    = WFEBindT env p_env_wf a2' k
        p_aenv_t1'     = lem_change_tvar_wf' (concatE (Cons x t_x g) g') a1' k Empty p_a1'env_wf
                                             (unbind_tvT a1 a1' t1') k_t1' p_a1'env_t1' a
                                             ? lem_tchgFTV_unbind_tvT a1 a1' a t1'
        p_aenv_t2'     = lem_change_tvar_wf' (concatE (Cons x t_x g) g') a2' k Empty p_a2'env_wf
                                             (unbind_tvT a2 a2' t2') k_t2' p_a2'env_t2' a
                                             ? lem_tchgFTV_unbind_tvT a2 a2' a t2'
        p_env'_t1'_t2' = lem_narrow_sub g (ConsT a k g') x s_x k_sx p_g_sx t_x p_sx_tx p_aenv_wf 
                             (unbind_tvT a1 a t1') k_t1' p_aenv_t1' 
                             (unbind_tvT a2 a t2') k_t2' p_aenv_t2' p_env_t1'_t2'
lem_narrow_sub_spoly g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf t1 Base p_env_t1 t2 k2   p_env_t2
                     (SPoly env a1 k t1' a2 t2' a p_env_t1'_t2') 
  = impossible ("by lemma" ? lem_wf_tpoly_star env a1 k t1' p_env_t1)
lem_narrow_sub_spoly g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf t1 k1   p_env_t1 t2 Base p_env_t2
                     (SPoly env a1 k t1' a2 t2' a p_env_t1'_t2') 
  = impossible ("by lemma" ? lem_wf_tpoly_star env a2 k t2' p_env_t2)


{-@ lem_narrow_sub :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
        -> k_sx:Kind -> ProofOf(WFType g s_x k_sx) -> t_x:Type -> ProofOf(Subtype g s_x t_x) 
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
        -> s:Type -> k_s:Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') s k_s)
        -> t:Type -> k_t:Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') t k_t)
        -> { p_s_t:Subtype  | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t }
        -> { p'_s_t:Subtype | propOf p'_s_t == (Subtype (concatE (Cons x s_x g) g') s t) 
                              && subtypSize' p_s_t == subtypSize' p'_s_t } / [subtypSize p_s_t, 1] @-}
lem_narrow_sub :: Env -> Env -> Vname -> Type -> Kind -> WFType -> Type -> Subtype -> WFEnv
                    -> Type -> Kind -> WFType -> Type -> Kind -> WFType -> Subtype -> Subtype
lem_narrow_sub g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf s k_s p_env_s t k_t p_env_t
              p_s_t@(SBase env z1 b p1 z2 p2 y ent_yenv_p2) -- p_env_s_t
  = lem_narrow_sub_sbase g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf 
                         s k_s p_env_s t k_t p_env_t p_s_t
lem_narrow_sub g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf ty1 ky1 p_env_ty1 ty2 ky2 p_env_ty2
               p_ty1_ty2@(SFunc env x1 s1 x2 s2 p_s2_s1 t1 t2 y p_yenv_t1_t2) 
  = lem_narrow_sub_sfunc g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf 
                         ty1 ky1 p_env_ty1 ty2 ky2 p_env_ty2 p_ty1_ty2
lem_narrow_sub g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf t k p_env_t t2 k2 p_env_t2
               p_t_t2@(SWitn env v_z t_z p_env_vz_tz _t z t' p_env_t_t'vz) 
  = lem_narrow_sub_switn g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf 
                         t k p_env_t t2 k2 p_env_t2 p_t_t2
lem_narrow_sub g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf t1 k1 p_env_t1 t' k' p_env_t'
               p_t1_t'@(SBind env z t_z t _t' w p_wenv_t_t') 
  = lem_narrow_sub_sbind g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf 
                         t1 k1 p_env_t1 t' k' p_env_t' p_t1_t'
lem_narrow_sub g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf t1 k1 p_env_t1 t2 k2 p_env_t2
               p_t1_t2@(SPoly env a1 k t1' a2 t2' a p_env_t1'_t2') 
  = lem_narrow_sub_spoly g g' x s_x k_sx p_g_sx t_x p_sx_tx p_env_wf 
                         t1 k1 p_env_t1 t2 k2 p_env_t2 p_t1_t2
