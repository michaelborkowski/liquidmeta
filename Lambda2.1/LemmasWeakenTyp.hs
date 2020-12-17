{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasWeakenTyp where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import SameBinders
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
import SystemFAlphaEquivalence
import BasicPropsCSubst
import BasicPropsDenotes
import Entailments
import LemmasChangeVarWF
import LemmasChangeVarEnt
import LemmasWeakenWF
import LemmasWeakenEnt
import LemmasWellFormedness
import LemmasTyping
import LemmasSubtyping
import SubstitutionLemmaWF
import LemmasChangeVarTyp

{-@ reflect foo46 @-}
foo46 x = Just x
foo46 :: a -> Maybe a

-----------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
-----------------------------------------------------------

{-@ lem_weaken_typ_tvar1 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTVar1 p_e_t }
        -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) } -> t_x:Type 
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (Cons x t_x g) g') e t) } 
           / [typSize p_e_t, 0] @-}
lem_weaken_typ_tvar1 :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> Vname -> Type -> HasType          
lem_weaken_typ_tvar1 g g' p_env_wf e t p_y_t@(TVar1 gg y t_y k_y p_gg_ty) x_ t_x
 = undefined {- CHECKED
    = case g' of     -- env == concatE g (Cons y t_y g'')
        (Empty)           -> TVar2 (Cons y t_y gg) (y ? lem_free_bound_in_env gg t_y k_y p_gg_ty y) 
                                   t p_y_t x t_x 
          where
            x = x_ ? lem_in_env_concat g g' x_
                   ? lem_free_bound_in_env g t Star p_g_t x_
            (WFEBind _gg p_gg_wf _y _ty k_y p_gg_ty) = p_env_wf
            p_g_t  = lem_typing_wf g (FV y) t p_y_t p_env_wf
        (Cons _y _ty g'') -> TVar1 (concatE (Cons x_ t_x g) g'') y t_y k_y p_gxg_ty
          where
            (WFEBind _gg p_gg_wf _y _ty _ky _) = p_env_wf
            p_gxg_ty = lem_weaken_wf' g g'' p_gg_wf t_y k_y p_gg_ty x_ t_x
-- (g; g' == _g, z:t_z) |- y : t_y
-}
{-@ lem_weaken_typ_tvar2 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTVar2 p_e_t }
        -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) } -> t_x:Type 
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (Cons x t_x g) g') e t) } 
           / [typSize p_e_t, 0] @-}
lem_weaken_typ_tvar2 :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> Vname -> Type -> HasType          
lem_weaken_typ_tvar2 g g' p_env_wf e t p_y_ty@(TVar2 gg y t_y p_gg_y_ty z t_z) x_ t_x
 = undefined {- CHECKED
    = case g' of
        (Empty)           -> TVar2 (concatE g g') y t_y p_y_ty x t_x 
          where
            x = x_ ? lem_in_env_concat g g' x_ 
                   ? lem_in_env_concat gg (Cons z t_z Empty) x_
                   ? lem_free_bound_in_env gg t_y Star p_gg_ty x_
            (WFEBind _gg p_gg_wf _ _ _ _) = p_env_wf
            p_gg_ty = lem_typing_wf gg (FV y) t_y p_gg_y_ty p_gg_wf
        (Cons _z _tz g'') -> TVar2 (concatE (Cons x t_x g) g'') 
                                   (y `withProof` lem_in_env_concat g g'' y
                                      `withProof` lem_in_env_concat (Cons x t_x g) g'' y) 
                                   t_y p_gxg_y_ty z t_z
          where
            x = x_ ? lem_in_env_concat gg (Cons z t_z Empty) x_
            (WFEBind _gg p_gg_wf _ _ _ _) = p_env_wf 
            p_gxg_y_ty = lem_weaken_typ g g'' p_gg_wf e t p_gg_y_ty x t_x
-}

{-@ lem_weaken_typ_tvar3 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTVar3 p_e_t }
        -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) } -> t_x:Type 
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (Cons x t_x g) g') e t) } 
           / [typSize p_e_t, 0] @-}
lem_weaken_typ_tvar3 :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> Vname -> Type -> HasType
lem_weaken_typ_tvar3 g g' p_env_wf e t p_y_ty@(TVar3 {}) x t_x 
    = undefined

{-@ lem_weaken_typ_tabs :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTAbs p_e_t }
        -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) } -> t_x:Type 
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (Cons x t_x g) g') e t) } 
           / [typSize p_e_t, 0] @-}
lem_weaken_typ_tabs :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> Vname -> Type -> HasType          
lem_weaken_typ_tabs g g' p_env_wf e t p_e_t@(TAbs env y t_y k_y p_gg'_ty e' t' y' p_y'_e'_t') x t_x
 = undefined {- CHECKED
    = TAbs (concatE (Cons x t_x g) g') y t_y k_y p_gxg'_ty e' t' y'' p_y''x_e'_t'
        where
            p_env_t      = lem_typing_wf env e t p_e_t p_env_wf
            p_gxg'_ty    = lem_weaken_wf' g g' p_env_wf t_y k_y p_gg'_ty x t_x -- p_g_tx
            y''_         = fresh_var (concatE (Cons x t_x g) g')
            y''          = y''_ ? lem_in_env_concat g g' y''_
                                ? lem_in_env_concat (Cons x t_x g) g' y''_
                                ? lem_fv_bound_in_env (concatE g g') e t p_e_t p_env_wf y''_
                                ? lem_free_bound_in_env env t Star p_env_t y''_
            p_y'env_wf   = WFEBind env p_env_wf y'  t_y k_y p_gg'_ty
            p_y''env_wf  = WFEBind env p_env_wf y'' t_y k_y p_gg'_ty
            p_y''_e'_t'  = lem_change_var_typ (concatE g g') y' t_y Empty p_y'env_wf 
                                     (unbind y y' e') (unbindT y y' t') p_y'_e'_t' y'' 
                                     ? lem_subFV_unbind   y y' (FV y'') e' 
                                     ? lem_tsubFV_unbindT y y' (FV y'') t'
            p_y''x_e'_t' = lem_weaken_typ g (Cons y'' t_y g') p_y''env_wf (unbind y y'' e') 
                                     (unbindT y y'' t') p_y''_e'_t' x t_x
-}

{-@ lem_weaken_typ_tapp :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTApp p_e_t }
        -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) } -> t_x:Type 
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (Cons x t_x g) g') e t) } 
           / [typSize p_e_t, 0] @-}
lem_weaken_typ_tapp :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> Vname -> Type -> HasType          
lem_weaken_typ_tapp g g' p_env_wf e t (TApp env e1 z s s' p_env_e1_ss' e2 p_env_e2_s) x t_x 
 = undefined {- CHECKED
    = TApp (concatE (Cons x t_x g) g') e1 z s s' p_env'_e1_ss' e2 p_env'_e2_s
        where
          p_env'_e1_ss' = lem_weaken_typ g g' p_env_wf e1 (TFunc z s s') p_env_e1_ss' x t_x
          p_env'_e2_s   = lem_weaken_typ g g' p_env_wf e2 s              p_env_e2_s   x t_x
-}

{-@ lem_weaken_typ_tabst :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTAbsT p_e_t }
        -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) } -> t_x:Type 
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (Cons x t_x g) g') e t) } 
           / [typSize p_e_t, 0] @-}
lem_weaken_typ_tabst :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> Vname -> Type -> HasType          
lem_weaken_typ_tabst g g' p_env_wf e t p_y_ty@(TAbsT {}) x t_x 
    = undefined

{-@ lem_weaken_typ_tappt :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTAppT p_e_t }
        -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) } -> t_x:Type 
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (Cons x t_x g) g') e t) } 
           / [typSize p_e_t, 0] @-}
lem_weaken_typ_tappt :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> Vname -> Type -> HasType          
lem_weaken_typ_tappt g g' p_env_wf e t p_y_ty@(TAppT {}) x t_x 
    = undefined

{-@ lem_weaken_typ_tlet :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTLet p_e_t }
        -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) } -> t_x:Type 
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (Cons x t_x g) g') e t) } 
           / [typSize p_e_t, 0] @-}
lem_weaken_typ_tlet :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> Vname -> Type -> HasType          
lem_weaken_typ_tlet g g' p_env_wf e t 
               p_e_t@(TLet env e_y t_y p_env_ey_ty y e' t' k' p_env_t' y' p_y'env_e'_t') x t_x
 = undefined {- CHECKED
    = TLet (concatE (Cons x t_x g) g') e_y t_y p_env'_ey_ty y e' t' k' p_env'_t' y'' p_y''env'_e'_t'
        where
          p_env_t         = lem_typing_wf env e t p_e_t p_env_wf
          p_env_ty        = lem_typing_wf env e_y t_y p_env_ey_ty p_env_wf
          p_env'_t'       = lem_weaken_wf' g g' p_env_wf t' k' p_env_t' x t_x
          y''_            = fresh_var (concatE (Cons x t_x g) g') 
          y''             = y''_ ? lem_in_env_concat g g' y''_
                                 ? lem_in_env_concat (Cons x t_x g) g' y''_
                                 ? lem_fv_bound_in_env (concatE g g') e t p_e_t p_env_wf y''_
                                 ? lem_free_bound_in_env env t Star p_env_t y''_
          p_y'env_wf      = WFEBind env p_env_wf y'  t_y Star p_env_ty
          p_y''env_wf     = WFEBind env p_env_wf y'' t_y Star p_env_ty
          p_env'_ey_ty    = lem_weaken_typ g g' p_env_wf e_y t_y p_env_ey_ty x t_x
          p_y''env_e'_t'  = lem_change_var_typ (concatE g g') y' t_y Empty p_y'env_wf (unbind y y' e') 
                                               (unbindT y y' t') p_y'env_e'_t' y''
                                               ? lem_subFV_unbind   y y' (FV y'') e' 
                                               ? lem_tsubFV_unbindT y y' (FV y'') t'
          p_y''env'_e'_t' = lem_weaken_typ g (Cons y'' t_y g') p_y''env_wf (unbind y y'' e') 
                                           (unbindT y y'' t') p_y''env_e'_t' x t_x 
-}

{-@ lem_weaken_typ_tann :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTAnn p_e_t }
        -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) } -> t_x:Type 
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (Cons x t_x g) g') e t) } 
           / [typSize p_e_t, 0] @-}
lem_weaken_typ_tann :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> Vname -> Type -> HasType          
lem_weaken_typ_tann g g' p_env_wf e t (TAnn env e' _t p_env_e'_t) x t_x
 = undefined {- CHECKED
    = TAnn (concatE (Cons x t_x g) g') e' t p_env'_e'_t
        where
          p_env'_e'_t = lem_weaken_typ g g' p_env_wf e' t p_env_e'_t x t_x
-}

{-@ lem_weaken_typ_tsub :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTSub p_e_t }
        -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) } -> t_x:Type 
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (Cons x t_x g) g') e t) } 
           / [typSize p_e_t, 0] @-}
lem_weaken_typ_tsub :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> Vname -> Type -> HasType          
lem_weaken_typ_tsub g g' p_env_wf e t (TSub env _e s p_env_e_s _t k p_env_t p_env_s_t) x t_x
 = undefined {- CHECKED
    = TSub (concatE (Cons x t_x g) g') e s p_env'_e_s t k p_env'_t p_env'_s_t 
        where
          p_env_s    = lem_typing_wf      env e s p_env_e_s p_env_wf
          p_env'_e_s = lem_weaken_typ     g g' p_env_wf e s p_env_e_s x t_x
          p_env'_t   = lem_weaken_wf'     g g' p_env_wf t k p_env_t x t_x 
          p_env'_s_t = lem_weaken_subtype g g' p_env_wf s Star p_env_s t k p_env_t 
                                          p_env_s_t x t_x
-}

{-@ lem_weaken_typ :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t }
        -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) } -> t_x:Type 
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (Cons x t_x g) g') e t) } 
           / [typSize p_e_t, 1] @-}
lem_weaken_typ :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> Vname -> Type -> HasType          
lem_weaken_typ g g' p_env_wf e t (TBC _g b)      x t_x = TBC  (concatE (Cons x t_x g) g') b
lem_weaken_typ g g' p_env_wf e t (TIC _g n)      x t_x = TIC  (concatE (Cons x t_x g) g') n
lem_weaken_typ g g' p_env_wf e t p_y_t@(TVar1 gg y t_y k_y p_gg_ty) x_ t_x -- env == concatE g (Cons y t_y g'') 
    = lem_weaken_typ_tvar1 g g' p_env_wf e t p_y_t x_ t_x
lem_weaken_typ g g' p_env_wf e t p_y_ty@(TVar2 gg y t_y p_gg_y_ty z t_z) x_ t_x
    = lem_weaken_typ_tvar2 g g' p_env_wf e t p_y_ty x_ t_x
lem_weaken_typ g g' p_env_wf e t p_y_ty@(TVar3 {}) x t_x 
    = lem_weaken_typ_tvar3 g g' p_env_wf e t p_y_ty x t_x
lem_weaken_typ g g' p_env_wf e t (TPrm _g c)     x t_x = TPrm (concatE (Cons x t_x g) g') c
lem_weaken_typ g g' p_env_wf e t p_e_t@(TAbs env y t_y k_y p_gg'_ty e' t' y' p_y'_e'_t') x t_x
    = lem_weaken_typ_tabs g g' p_env_wf e t p_e_t x t_x
lem_weaken_typ g g' p_env_wf e t p_e_t@(TApp env e1 z s s' p_env_e1_ss' e2 p_env_e2_s) x t_x 
    = lem_weaken_typ_tapp g g' p_env_wf e t p_e_t x t_x
lem_weaken_typ g g' p_env_wf e t p_e_t@(TAbsT {}) x t_x 
    = lem_weaken_typ_tabst g g' p_env_wf e t p_e_t x t_x
lem_weaken_typ g g' p_env_wf e t p_e_t@(TAppT {}) x t_x 
    = lem_weaken_typ_tappt g g' p_env_wf e t p_e_t x t_x
lem_weaken_typ g g' p_env_wf e t 
               p_e_t@(TLet env e_y t_y p_env_ey_ty y e' t' k' p_env_t' y' p_y'env_e'_t') x t_x
    = lem_weaken_typ_tlet g g' p_env_wf e t p_e_t x t_x
lem_weaken_typ g g' p_env_wf e t p_e_t@(TAnn env e' _t p_env_e'_t) x t_x
    = lem_weaken_typ_tann g g' p_env_wf e t p_e_t x t_x
lem_weaken_typ g g' p_env_wf e t p_e_t@(TSub env _e s p_env_e_s _t k p_env_t p_env_s_t) x t_x
    = lem_weaken_typ_tsub g g' p_env_wf e t p_e_t x t_x

{-@ lem_weaken_tv_typ :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t }
        -> { a:Vname | (not (in_env a g)) && (not (in_env a g')) } -> k_a:Kind
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (ConsT a k_a g) g') 
                                                        e t) } / [typSize p_e_t] @-}
lem_weaken_tv_typ :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> Vname -> Kind -> HasType 
lem_weaken_tv_typ g g' p_env_wf e t (TBC _g b)      a k_a = TBC  (concatE (ConsT a k_a g) g') b
lem_weaken_tv_typ g g' p_env_wf e t (TIC _g n)      a k_a = TIC  (concatE (ConsT a k_a g) g') n
lem_weaken_tv_typ g g' p_env_wf e t (TVar1 {}) a k_a
  = undefined
lem_weaken_tv_typ g g' p_env_wf e t (TVar2 {}) a k_a
  = undefined
lem_weaken_tv_typ g g' p_env_wf e t (TVar3 {}) a k_a
  = undefined
lem_weaken_tv_typ g g' p_env_wf e t (TPrm {}) a k_a
  = undefined
lem_weaken_tv_typ g g' p_env_wf e t (TAbs {}) a k_a
  = undefined
lem_weaken_tv_typ g g' p_env_wf e t (TApp {}) a k_a
  = undefined
lem_weaken_tv_typ g g' p_env_wf e t (TAbsT {}) a k_a
  = undefined
lem_weaken_tv_typ g g' p_env_wf e t (TAppT {}) a k_a
  = undefined
lem_weaken_tv_typ g g' p_env_wf e t (TLet {}) a k_a
  = undefined
lem_weaken_tv_typ g g' p_env_wf e t (TAnn {}) a k_a
  = undefined
lem_weaken_tv_typ g g' p_env_wf e t (TSub env _e s p_e_s _t k p_env_t p_s_t) a k_a
  = TSub (concatE (ConsT a k_a g) g') e s p_env'_e_s t k p_env'_t p_env'_s_t
      where
        p_env_s    = lem_typing_wf         env e s p_e_s p_env_wf
        p_env'_e_s = lem_weaken_tv_typ     g g' p_env_wf e s p_e_s a k_a
        p_env'_t   = lem_weaken_tv_wf'     g g' p_env_wf t k p_env_t a k_a
        p_env'_s_t = lem_weaken_tv_subtype g g' p_env_wf s Star p_env_s t k p_env_t p_s_t a k_a

{-@ lem_weaken_many_typ :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type -> ProofOf(HasType g e t) 
      -> ProofOf(HasType (concatE g g') e t) @-}
lem_weaken_many_typ :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> HasType
lem_weaken_many_typ g Empty           p_g_wf    e t p_g_e_t = p_g_e_t
lem_weaken_many_typ g (Cons x t_x g') p_xenv_wf e t p_g_e_t 
  = lem_weaken_typ (concatE g g') Empty p_env_wf e t p_gg'_e_t x t_x
      where
        (WFEBind _ p_env_wf _ _ _ _) = p_xenv_wf
        p_gg'_e_t = lem_weaken_many_typ g g' p_env_wf e t p_g_e_t 
lem_weaken_many_typ g (ConsT a k_a g') p_aenv_wf e t p_g_e_t 
  = lem_weaken_tv_typ (concatE g g') Empty p_env_wf e t p_gg'_e_t a k_a
      where
        (WFEBindT _ p_env_wf _ _)    = p_aenv_wf
        p_gg'_e_t = lem_weaken_many_typ g g' p_env_wf e t p_g_e_t


{-@ lem_weaken_subtype_sbase :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE g g'))
      -> t:Type  -> k:Kind  -> ProofOf(WFType (concatE g g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE g g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t'&& isSBase p_t_t' }
      -> { x:Vname | not (in_env x g) && not (in_env x g') } -> t_x:Type
      -> ProofOf(Subtype (concatE (Cons x t_x g) g') t t') / [subtypSize p_t_t', 0] @-}
lem_weaken_subtype_sbase :: Env -> Env -> WFEnv -> Type -> Kind -> WFType 
      -> Type -> Kind -> WFType -> Subtype -> Vname -> Type -> Subtype
lem_weaken_subtype_sbase g g' p_env_wf t k p_env_t t' k' p_env_t' 
                       (SBase env z1 b p1 z2 p2 w pf_wenv_ent_p2) x_ t_x
    = SBase env' z1 b p1 z2 p2 w' pf_w'env'_ent_p2 
        where
          x                = x_ ? lem_in_env_concat g g' x_
          env'             = concatE (Cons x t_x g) g'
          w'               = fresh_var (concatE (Cons x t_x g) g')
          p_wenv_wf        = WFEBind env p_env_wf w t k p_env_t
          p_w'env_wf       = WFEBind env p_env_wf 
                                 (w' ? lem_in_env_concat g g' w'
                                     ? lem_in_env_concat (Cons x t_x g) g' w')
                                 t k p_env_t
          pf_w'env_ent_p2  = lem_change_var_ent (concatE g g') w t Empty p_wenv_wf
                                 (unbind z2 w p2 ? lem_free_subset_binds env t' k' p_env_t') 
                                 pf_wenv_ent_p2 
                                 (w' ? lem_free_bound_in_env env t' k' p_env_t' w')
                                 ? lem_subFV_unbind z2 w (FV w') p2
          pf_w'env'_ent_p2 = lem_weaken_ent g (Cons w' t g') 
                                 p_w'env_wf (unbind z2 w' p2) pf_w'env_ent_p2 x t_x 

{-@ lem_weaken_subtype_sfunc :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE g g'))
      -> t:Type  -> k:Kind  -> ProofOf(WFType (concatE g g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE g g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' && isSFunc p_t_t' }
      -> { x:Vname | not (in_env x g) && not (in_env x g') } -> t_x:Type
      -> ProofOf(Subtype (concatE (Cons x t_x g) g') t t') / [subtypSize p_t_t', 0] @-}
lem_weaken_subtype_sfunc :: Env -> Env -> WFEnv -> Type -> Kind -> WFType 
      -> Type -> Kind -> WFType -> Subtype -> Vname -> Type -> Subtype
lem_weaken_subtype_sfunc g g' p_env_wf ft1 k1 p_env_ft1 ft2 k2 p_env_ft2 
                       (SFunc env z1 s1 z2 s2 p_env_s2_s1 t1 t2 w p_wenv_t1_t2) x_ t_x
    = SFunc env' z1 s1 z2 s2 p_env'_s2_s1 t1 t2 w' p_w'env'_t1_t2
        where
          (WFFunc _ _ _ k_s1 p_env_s1 _ k_t1 w1 p_w1'env_t1)
                           = lem_wffunc_for_wf_tfunc (concatE g g') z1 s1 t1 k1 p_env_ft1
          (WFFunc _ _ _ k_s2 p_env_s2 _ k_t2 w2 p_w2env_t2)
                           = lem_wffunc_for_wf_tfunc (concatE g g') z2 s2 t2 k2 p_env_ft2
          x              = x_ ? lem_in_env_concat g g' x_
          env'           = concatE (Cons x t_x g) g'
          w'_            = fresh_var (concatE (Cons x t_x g) g') 
          w'             = w'_ ? lem_in_env_concat g g' w'_
                               ? lem_in_env_concat (Cons x t_x g) g' w'_
          p_wenv_wf      = WFEBind env p_env_wf w  s2 k_s2 p_env_s2
          p_w1env_wf     = WFEBind env p_env_wf w1 s2 k_s2 p_env_s2
          p_w2env_wf     = WFEBind env p_env_wf w2 s2 k_s2 p_env_s2
          p_w'env_wf     = WFEBind env p_env_wf w' s2 k_s2 p_env_s2
          p_w1env_t1     = lem_subtype_in_env_wf env Empty w1 s2 s1 p_env_s2_s1 
                                                 (unbindT z1 w1 t1) k_t1 p_w1'env_t1
          p_wenv_t1      = lem_change_var_wf' env w1 s2 Empty p_w1env_wf
                                              (unbindT z1 w1 t1) k_t1 p_w1env_t1 w
                                              ? lem_tsubFV_unbindT z1 w1 (FV w) t1
          p_wenv_t2      = lem_change_var_wf' env w2 s2 Empty p_w2env_wf
                                              (unbindT z2 w2 t2) k_t2 p_w2env_t2 w
                                              ? lem_tsubFV_unbindT z2 w2 (FV w) t2
          p_w'env_t1     = lem_change_var_wf' env w1 s2 Empty p_w1env_wf
                                              (unbindT z1 w1 t1) k_t1 p_w1env_t1 w'
                                              ? lem_tsubFV_unbindT z1 w1 (FV w') t1
          p_w'env_t2     = lem_change_var_wf' env w2 s2 Empty p_w2env_wf
                                              (unbindT z2 w2 t2) k_t2 p_w2env_t2 w'
                                              ? lem_tsubFV_unbindT z2 w2 (FV w') t2
          p_env'_s2_s1   = lem_weaken_subtype g g' p_env_wf s2 k_s2 p_env_s2 s1 k_s1
                                              p_env_s1 p_env_s2_s1 x t_x
          p_w'env_t1_t2  = lem_change_var_subtype env w s2 Empty p_wenv_wf
                                   (unbindT z1 w t1) k_t1 p_wenv_t1 (unbindT z2 w t2) k_t2 p_wenv_t2
                                   p_wenv_t1_t2 
                                   ( w' ? lem_free_bound_in_env env ft1 k1 p_env_ft1 w'
                                        ? lem_free_bound_in_env env ft2 k2 p_env_ft2 w' )
                                   ? lem_tsubFV_unbindT z1 w (FV w') t1
                                   ? lem_tsubFV_unbindT z2 w (FV w') t2
          p_w'env'_t1_t2 = lem_weaken_subtype g (Cons w' s2 g') p_w'env_wf
                                   (unbindT z1 w' t1) k_t1 p_w'env_t1 (unbindT z2 w' t2) k_t2
                                   p_w'env_t2 p_w'env_t1_t2 x t_x


{-@ lem_weaken_subtype_switn :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE g g'))
      -> t:Type  -> k:Kind  -> ProofOf(WFType (concatE g g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE g g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' && isSWitn p_t_t' }
      -> { x:Vname | not (in_env x g) && not (in_env x g') } -> t_x:Type
      -> ProofOf(Subtype (concatE (Cons x t_x g) g') t t') / [subtypSize p_t_t', 0] @-}
lem_weaken_subtype_switn :: Env -> Env -> WFEnv -> Type -> Kind -> WFType 
      -> Type -> Kind -> WFType -> Subtype -> Vname -> Type -> Subtype
lem_weaken_subtype_switn g g' p_env_wf t k p_env_t t2 k2 p_env_t2
                   (SWitn env v_z t_z p_env_vz_tz _t z t' p_env_t_t'vz) x_ t_x 
    = SWitn env' v_z t_z p_env'_vz_tz t z t' p_env'_t_t'vz
        where
          (WFExis _ _ _ k_z p_env_tz _ k' z' p_z'env_t')
                        = lem_wfexis_for_wf_texists (concatE g g') z t_z t' k2 p_env_t2
          x             = x_ ? lem_in_env_concat g g' x_
          env'          = concatE (Cons x t_x g) g'
          p_z'env_wf    = WFEBind env p_env_wf z' t_z k_z p_env_tz
          p_env_t'vz    = lem_subst_wf' (concatE g g') Empty z' v_z t_z p_env_vz_tz p_z'env_wf 
                                        (unbindT z z' t') k' p_z'env_t'
          p_env'_vz_tz  = lem_weaken_typ g g' p_env_wf v_z t_z p_env_vz_tz x t_x
                                         ? lem_tsubFV_unbindT z z' v_z t'
          p_env'_t_t'vz = lem_weaken_subtype g g' p_env_wf t k p_env_t
                                             (tsubBV z v_z t') k' p_env_t'vz p_env_t_t'vz x t_x


{-@ lem_weaken_subtype_sbind :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE g g'))
      -> t:Type  -> k:Kind  -> ProofOf(WFType (concatE g g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE g g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' && isSBind p_t_t' }
      -> { x:Vname | not (in_env x g) && not (in_env x g') } -> t_x:Type
      -> ProofOf(Subtype (concatE (Cons x t_x g) g') t t') / [subtypSize p_t_t', 0] @-}
lem_weaken_subtype_sbind :: Env -> Env -> WFEnv -> Type -> Kind -> WFType 
      -> Type -> Kind -> WFType -> Subtype -> Vname -> Type -> Subtype
lem_weaken_subtype_sbind g g' p_env_wf t1 k1 p_env_t1 t' k' p_env_t'
                   (SBind env z t_z t _t' z' p_z'env_t_t') x_ t_x
    = SBind env' z t_z t t' z'' p_z''env'_t_t'
        where
          (WFExis _ _ _ k_z p_env_tz _ k w p_wenv_t)
                         = lem_wfexis_for_wf_texists (concatE g g') z t_z t k1 p_env_t1
          x              = x_ ? lem_in_env_concat g g' x_
          z''_           = fresh_var (concatE (Cons x t_x g) g') 
          z''            = z''_ ? lem_in_env_concat g g' z''_
                                ? lem_in_env_concat (Cons x t_x g) g' z''_
                                ? lem_free_bound_in_env env t1 k1 p_env_t1 z''_
                                ? lem_free_bound_in_env env t' k' p_env_t' z''_
          env'           = concatE (Cons x t_x g) g'
          p_wenv_wf      = WFEBind env p_env_wf w   t_z k_z p_env_tz 
          p_z'env_wf     = WFEBind env p_env_wf z'  t_z k_z p_env_tz
          p_z''env_wf    = WFEBind env p_env_wf z'' t_z k_z p_env_tz
          p_z'env_t      = lem_change_var_wf' env w t_z Empty p_wenv_wf (unbindT z w t) k p_wenv_t z'
                                              ? lem_tsubFV_unbindT z w (FV z') t
          p_z''env_t     = lem_change_var_wf' env w t_z Empty p_wenv_wf (unbindT z w t) k p_wenv_t z''
                                              ? lem_tsubFV_unbindT z w (FV z'') t
          p_z'env_t'     = lem_weaken_wf' env Empty p_env_wf t' k' p_env_t' z'  t_z
          p_z''env_t'    = lem_weaken_wf' env Empty p_env_wf t' k' p_env_t' z'' t_z
          p_z''env_t_t'  = lem_change_var_subtype (concatE g g') z' t_z Empty
                                   p_z'env_wf (unbindT z z' t) k p_z'env_t t' k' p_z'env_t' 
                                   p_z'env_t_t' z'' 
                                   ? lem_tsubFV_unbindT z z' (FV z'') t
                                   ? lem_free_bound_in_env env t' k' p_env_t' z'
                                   ? lem_tsubFV_notin z' (FV z'') t'
          p_z''env'_t_t' = lem_weaken_subtype g (Cons z'' t_z g') p_z''env_wf
                                   (unbindT z z'' t) k p_z''env_t t' k' p_z''env_t' 
                                   p_z''env_t_t' x t_x


{-@ lem_weaken_subtype_spoly :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE g g'))
      -> t:Type  -> k:Kind  -> ProofOf(WFType (concatE g g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE g g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' && isSPoly p_t_t' }
      -> { x:Vname | not (in_env x g) && not (in_env x g') } -> t_x:Type
      -> ProofOf(Subtype (concatE (Cons x t_x g) g') t t') / [subtypSize p_t_t', 0] @-}
lem_weaken_subtype_spoly :: Env -> Env -> WFEnv -> Type -> Kind -> WFType 
      -> Type -> Kind -> WFType -> Subtype -> Vname -> Type -> Subtype
lem_weaken_subtype_spoly g g' p_env_wf t1 k1 p_env_t1 t2 k2 p_env_tw (SPoly {}) x_ t_x
    = undefined


{-@ lem_weaken_subtype :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE g g'))
      -> t:Type  -> k:Kind  -> ProofOf(WFType (concatE g g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE g g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' }
      -> { x:Vname | not (in_env x g) && not (in_env x g') } -> t_x:Type
      -> ProofOf(Subtype (concatE (Cons x t_x g) g') t t') / [subtypSize p_t_t', 1] @-}
lem_weaken_subtype :: Env -> Env -> WFEnv -> Type -> Kind -> WFType 
      -> Type -> Kind -> WFType -> Subtype -> Vname -> Type -> Subtype
lem_weaken_subtype g g' p_env_wf t k p_env_t t' k' p_env_t' 
                       p_t_t'@(SBase env z1 b p1 z2 p2 w pf_wenv_ent_p2) x_ t_x
    = lem_weaken_subtype_sbase g g' p_env_wf t k p_env_t t' k' p_env_t' p_t_t' x_ t_x 
lem_weaken_subtype g g' p_env_wf ft1 k1 p_env_ft1 ft2 k2 p_env_ft2 
                       p_ft1_ft2@(SFunc env z1 s1 z2 s2 p_env_s2_s1 t1 t2 w p_wenv_t1_t2) x_ t_x
    = lem_weaken_subtype_sfunc g g' p_env_wf ft1 k1 p_env_ft1 ft2 k2 p_env_ft2 p_ft1_ft2 x_ t_x
lem_weaken_subtype g g' p_env_wf t k p_env_t t2 k2 p_env_t2
                   p_t_t2@(SWitn env v_z t_z p_env_vz_tz _t z t' p_env_t_t'vz) x_ t_x 
    = lem_weaken_subtype_switn g g' p_env_wf t k p_env_t t2 k2 p_env_t2 p_t_t2 x_ t_x
lem_weaken_subtype g g' p_env_wf t1 k1 p_env_t1 t' k' p_env_t'
                   p_t1_t'@(SBind env z t_z t _t' z' p_z'env_t_t') x_ t_x
    = lem_weaken_subtype_sbind g g' p_env_wf t1 k1 p_env_t1 t' k' p_env_t' p_t1_t' x_ t_x
lem_weaken_subtype g g' p_env_wf t1 k1 p_env_t1 t2 k2 p_env_tw p_t1_t2@(SPoly {}) x_ t_x
    = lem_weaken_subtype_spoly g g' p_env_wf t1 k1 p_env_t1 t2 k2 p_env_tw p_t1_t2 x_ t_x

{-@ lem_weaken_tv_subtype :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE g g'))
      -> t:Type  -> k:Kind  -> ProofOf(WFType (concatE g g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE g g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' }
      -> { a:Vname | not (in_env a g) && not (in_env a g') } -> k_a:Kind
      -> ProofOf(Subtype (concatE (ConsT a k_a g) g') t t') / [subtypSize p_t_t'] @-}
lem_weaken_tv_subtype :: Env -> Env -> WFEnv -> Type -> Kind -> WFType 
      -> Type -> Kind -> WFType -> Subtype -> Vname -> Kind -> Subtype
lem_weaken_tv_subtype g g' p_env_wf t k p_env_t t' k' p_env_t' 
                       (SBase env z1 b p1 z2 p2 w pf_wenv_ent_p2) a_ k_a
    = undefined {- -}
lem_weaken_tv_subtype g g' p_env_wf ft1 k1 p_env_ft1 ft2 k2 p_env_ft2 
                       (SFunc env z1 s1 z2 s2 p_env_s2_s1 t1 t2 w p_wenv_t1_t2) a_ k_a
    = undefined {-i
-}
lem_weaken_tv_subtype g g' p_env_wf t k p_env_t t2 k2 p_env_t2
                   (SWitn env v_z t_z p_env_vz_tz _t z t' p_env_t_t'vz) a_ k_a
    = undefined {-case p_env_t2 of
-}
lem_weaken_tv_subtype g g' p_env_wf t1 k1 p_env_t1 t' k' p_env_t'
                   (SBind env z t_z t _t' z' p_z'env_t_t') a_ k_a
    = undefined {- case p_env_t1 of 
-}
lem_weaken_tv_subtype g g' p_env_wf t1 k1 p_env_t1 t2 k2 p_env_tw (SPoly {}) a k_a
    = undefined
