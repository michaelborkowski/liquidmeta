{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasWeakenTypTV where

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
import SystemFLemmasFTyping2
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst
import LemmasChangeVarWF
import LemmasChangeVarEnt
import LemmasWeakenWF
import LemmasWeakenWFTV
import LemmasWeakenEnt
import LemmasWellFormedness
import LemmasTyping
import SubstitutionWFAgain
import LemmasChangeVarTyp
import LemmasWeakenTyp

{-@ reflect foo48 @-}
foo48 x = Just x
foo48 :: a -> Maybe a

-----------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
-----------------------------------------------------------

{-@ lem_weaken_tv_typ_tvar1 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTVar1 p_e_t }
        -> { a:Vname | (not (in_env a g)) && (not (in_env a g')) } -> k_a:Kind
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (ConsT a k_a g) g') 
                                                        e t) } / [typSize p_e_t, 0] @-}
lem_weaken_tv_typ_tvar1 :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> Vname -> Kind -> HasType  
lem_weaken_tv_typ_tvar1 g g' p_env_wf e t p_y_t@(TVar1 gg y_ t_y k_y p_gg_ty) a_ k_a
    = case g' of     -- env == concatE g (Cons y t_y g'')
        (Empty)           -> TVar3 (Cons y t_y gg) y t p_y_t a k_a 
          where
            a = a_ ? lem_in_env_concat g g' a_
                   ? lem_fv_bound_in_env g (FV y) t p_y_t p_env_wf a_
                   ? lem_free_bound_in_env g t Star p_g_t a_
            y = y_ ? lem_in_env_concat gg Empty y_
                   ? lem_free_bound_in_env gg t_y k_y p_gg_ty y_
            (WFEBind _gg p_gg_wf _y _ty k_y p_gg_ty) = p_env_wf
            p_g_t  = lem_typing_wf g (FV y) t p_y_t p_env_wf
        (Cons _y _ty g'') -> TVar1 (concatE (ConsT a_ k_a g) g'') y t_y k_y p_gag_ty  
          where
            a = a_ ? lem_in_env_concat g g' a_
            y = y_ ? lem_in_env_concat g g'' y_
            (WFEBind _gg p_gg_wf _y _ty _ky _) = p_env_wf
            p_gag_ty = lem_weaken_tv_wf' g g'' p_gg_wf t_y k_y p_gg_ty a_ k_a
-- (g; g' == _g, z:t_z) |- y : t_y

{-@ lem_weaken_tv_typ_tvar2 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTVar2 p_e_t }
        -> { a:Vname | (not (in_env a g)) && (not (in_env a g')) } -> k_a:Kind
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (ConsT a k_a g) g') 
                                                        e t) } / [typSize p_e_t, 0] @-}
lem_weaken_tv_typ_tvar2 :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> Vname -> Kind -> HasType
lem_weaken_tv_typ_tvar2 g g' p_env_wf e t p_y_ty@(TVar2 gg y t_y p_gg_y_ty z_ t_z) a_ k_a
    = case g' of
        (Empty)           -> TVar3 (concatE g g') y t_y p_y_ty a k_a
          where
            a = a_ ? lem_in_env_concat g g' a_ 
                   ? lem_in_env_concat gg (Cons z_ t_z Empty) a_
                   ? lem_free_bound_in_env gg t_y Star p_gg_ty a_
            (WFEBind _gg p_gg_wf _ _ _ _) = p_env_wf
            p_gg_ty = lem_typing_wf gg (FV y) t_y p_gg_y_ty p_gg_wf
        (Cons _z _tz g'') -> TVar2 (concatE (ConsT a k_a g) g'') 
                                   (y `withProof` lem_in_env_concat g g'' y
                                      `withProof` lem_in_env_concat (ConsT a k_a g) g'' y)  
                                   t_y p_gag_y_ty z t_z      
          where
            a = a_ ? lem_in_env_concat gg (Cons z t_z Empty) a_
            z = z_ ? lem_in_env_concat g g'' z_
            (WFEBind _gg p_gg_wf _ _ _ _) = p_env_wf 
            p_gag_y_ty = lem_weaken_tv_typ g g'' p_gg_wf e t p_gg_y_ty a k_a

{-@ lem_weaken_tv_typ_tvar3 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTVar3 p_e_t }
        -> { a:Vname | (not (in_env a g)) && (not (in_env a g')) } -> k_a:Kind
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (ConsT a k_a g) g') 
                                                        e t) } / [typSize p_e_t, 0] @-}
lem_weaken_tv_typ_tvar3 :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> Vname -> Kind -> HasType
lem_weaken_tv_typ_tvar3 g g' p_env_wf e t p_z_tz@(TVar3 gg z t_z p_z_t a'_ k_a') a_ k_a
    = case g' of
        (Empty)           -> TVar3 (concatE g g') z t_z p_z_tz a k_a
          where
            a = a_ ? lem_in_env_concat g g' a_
                   ? lem_in_env_concat gg (ConsT a'_ k_a' Empty) a_
                   ? lem_free_bound_in_env gg t_z Star p_gg_tz a_
            (WFEBindT _ p_gg_wf _ _) = p_env_wf
            p_gg_tz = lem_typing_wf gg (FV z) t_z p_z_t p_gg_wf
        (ConsT _a' _ g'') -> TVar3 (concatE (ConsT a k_a g) g'')
                                 (z `withProof` lem_in_env_concat g g'' z
                                    `withProof` lem_in_env_concat (ConsT a k_a g) g'' z)
                                 t (lem_weaken_tv_typ g g'' p_env'_wf (FV z) t p_z_t a k_a)
                                 a' k_a'        
          where
            a  = a_  ? lem_in_env_concat g (ConsT a' k_a' g'') a_
            a' = a'_ ? lem_in_env_concat g g'' a'_
            (WFEBindT env' p_env'_wf _ _) = p_env_wf

{-@ lem_weaken_tv_typ_tabs :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTAbs p_e_t }
        -> { a:Vname | (not (in_env a g)) && (not (in_env a g')) } -> k_a:Kind
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (ConsT a k_a g) g') 
                                                        e t) } / [typSize p_e_t, 0] @-}
lem_weaken_tv_typ_tabs :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> Vname -> Kind -> HasType          
lem_weaken_tv_typ_tabs g g' p_env_wf e t p_e_t@(TAbs env y t_y k_y p_gg'_ty e' t' y' p_y'_e'_t') a k_a
    = TAbs (concatE (ConsT a k_a g) g') y t_y k_y p_gag'_ty e' t' y'' p_y''a_e'_t'
        where
            p_env_t      = lem_typing_wf env e t p_e_t p_env_wf
            p_gag'_ty    = lem_weaken_tv_wf' g g' p_env_wf t_y k_y p_gg'_ty a k_a
            y''_         = fresh_var (concatE (ConsT a k_a g) g')
            y''          = y''_ ? lem_in_env_concat g g' y''_
                                ? lem_in_env_concat (ConsT a k_a g) g' y''_
                                ? lem_fv_bound_in_env (concatE g g') e t p_e_t p_env_wf y''_
                                ? lem_free_bound_in_env env t Star p_env_t y''_
            p_y'env_wf   = WFEBind env p_env_wf y'  t_y k_y p_gg'_ty
            p_y''env_wf  = WFEBind env p_env_wf y'' t_y k_y p_gg'_ty
            p_y''_e'_t'  = lem_change_var_typ (concatE g g') y' t_y Empty p_y'env_wf 
                                     (unbind y y' e') (unbindT y y' t') p_y'_e'_t' y'' 
                                     ? lem_subFV_unbind   y y' (FV y'') e' 
                                     ? lem_tsubFV_unbindT y y' (FV y'') t'
            p_y''a_e'_t' = lem_weaken_tv_typ g (Cons y'' t_y g') p_y''env_wf (unbind y y'' e') 
                                     (unbindT y y'' t') p_y''_e'_t' a k_a

{-@ lem_weaken_tv_typ_tapp :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTApp p_e_t }
        -> { a:Vname | (not (in_env a g)) && (not (in_env a g')) } -> k_a:Kind
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (ConsT a k_a g) g') 
                                                        e t) } / [typSize p_e_t, 0] @-}
lem_weaken_tv_typ_tapp :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> Vname -> Kind -> HasType          
lem_weaken_tv_typ_tapp g g' p_env_wf e t (TApp env e1 z s s' p_env_e1_ss' e2 p_env_e2_s) a k_a
    = TApp (concatE (ConsT a k_a g) g') e1 z s s' p_env'_e1_ss' e2 p_env'_e2_s
        where
          p_env'_e1_ss' = lem_weaken_tv_typ g g' p_env_wf e1 (TFunc z s s') p_env_e1_ss' a k_a
          p_env'_e2_s   = lem_weaken_tv_typ g g' p_env_wf e2 s              p_env_e2_s   a k_a

{-@ lem_weaken_tv_typ_tabst :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTAbsT p_e_t }
        -> { a:Vname | (not (in_env a g)) && (not (in_env a g')) } -> k_a:Kind
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (ConsT a k_a g) g') 
                                                        e t) } / [typSize p_e_t, 0] @-}
lem_weaken_tv_typ_tabst :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> Vname -> Kind -> HasType 
lem_weaken_tv_typ_tabst g g' p_env_wf e t 
                     p_e_t@(TAbsT env a1 k1 e' t' k_t' a' p_a'g_e'_t' p_a'g_t') a k_a
    = TAbsT (concatE (ConsT a k_a g) g') a1 k1 e' t' k_t' a'' p_a''a_e'_t' p_a''a_t'
        where
          p_env_t      = lem_typing_wf env e t p_e_t p_env_wf
          a''_         = fresh_var (concatE (ConsT a k_a g) g')
          a''          = a''_ ? lem_in_env_concat g g' a''_
                              ? lem_in_env_concat (ConsT a k_a g) g' a''_
                              ? lem_fv_bound_in_env env e t p_e_t p_env_wf a''_
                              ? lem_free_bound_in_env env t Star p_env_t a''_
          p_a'env_wf   = WFEBindT env p_env_wf a'  k1
          p_a''env_wf  = WFEBindT env p_env_wf a'' k1
          p_a''_e'_t'  = lem_change_tvar_typ (concatE g g') a' k1 Empty p_a'env_wf
                              (unbind_tv a1 a' e') (unbind_tvT a1 a' t') p_a'g_e'_t' a''
                                  ? lem_chgFTV_unbind_tv a1 a' a''
                                        (e' ? lem_fv_bound_in_env env e t p_e_t p_env_wf a')
                                  ? lem_tchgFTV_unbind_tvT a1 a' a''
                                        (t' ? lem_free_bound_in_env env t Star p_env_t a')
          p_a''a_e'_t' = lem_weaken_tv_typ g (ConsT a'' k1 g') p_a''env_wf 
                              (unbind_tv a1 a'' e') (unbind_tvT a1 a'' t') p_a''_e'_t' a k_a
          p_a''g_t'    = lem_change_tvar_wf' (concatE g g') a' k1 Empty p_a'env_wf 
                              (unbind_tvT a1 a' t') k_t' p_a'g_t' a''
                              ? lem_tchgFTV_unbind_tvT a1 a' a''
                                    (t' ? lem_free_bound_in_env env t Star p_env_t a')
          p_a''a_t'    = lem_weaken_tv_wf' g (ConsT a'' k1 g') p_a''env_wf
                              (unbind_tvT a1 a'' t') k_t' p_a''g_t' a k_a

{-@ lem_weaken_tv_typ_tappt :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTAppT p_e_t }
        -> { a:Vname | (not (in_env a g)) && (not (in_env a g')) } -> k_a:Kind
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (ConsT a k_a g) g') 
                                                        e t) } / [typSize p_e_t, 0] @-}
lem_weaken_tv_typ_tappt :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> Vname -> Kind -> HasType 
lem_weaken_tv_typ_tappt g g' p_env_wf e t p_e_t@(TAppT env e' a1 k1 s p_e'_a1s t' p_env_t') a k_a
    = TAppT (concatE (ConsT a k_a g) g') e' a1 k1 s p_env'_e'_a1s t' p_env'_t'
        where
          p_env'_e'_a1s = lem_weaken_tv_typ g g' p_env_wf e' (TPoly a1 k1 s) p_e'_a1s a k_a
          p_env'_t'     = lem_weaken_tv_wf' g g' p_env_wf t' k1 p_env_t' a k_a

{-@ lem_weaken_tv_typ_tlet :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTLet p_e_t }
        -> { a:Vname | (not (in_env a g)) && (not (in_env a g')) } -> k_a:Kind
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (ConsT a k_a g) g') 
                                                        e t) } / [typSize p_e_t, 0] @-}
lem_weaken_tv_typ_tlet :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> Vname -> Kind -> HasType
lem_weaken_tv_typ_tlet g g' p_env_wf e t 
               p_e_t@(TLet env e_y t_y p_env_ey_ty y e' t' k' p_env_t' y' p_y'env_e'_t') a k_a
    = TLet (concatE (ConsT a k_a g) g') e_y t_y p_env'_ey_ty y e' t' k' p_env'_t' y'' p_y''env'_e'_t'
        where
          p_env_t         = lem_typing_wf env e t p_e_t p_env_wf
          p_env_ty        = lem_typing_wf env e_y t_y p_env_ey_ty p_env_wf
          p_env'_t'       = lem_weaken_tv_wf' g g' p_env_wf t' k' p_env_t' a k_a
          y''_            = fresh_var (concatE (ConsT a k_a g) g') 
          y''             = y''_ ? lem_in_env_concat g g' y''_
                                 ? lem_in_env_concat (ConsT a k_a g) g' y''_
                                 ? lem_fv_bound_in_env (concatE g g') e t p_e_t p_env_wf y''_
                                 ? lem_free_bound_in_env env t Star p_env_t y''_
          p_y'env_wf      = WFEBind env p_env_wf y'  t_y Star p_env_ty
          p_y''env_wf     = WFEBind env p_env_wf y'' t_y Star p_env_ty
          p_env'_ey_ty    = lem_weaken_tv_typ g g' p_env_wf e_y t_y p_env_ey_ty a k_a
          p_y''env_e'_t'  = lem_change_var_typ (concatE g g') y' t_y Empty p_y'env_wf (unbind y y' e') 
                                               (unbindT y y' t') p_y'env_e'_t' y''
                                               ? lem_subFV_unbind   y y' (FV y'') e' 
                                               ? lem_tsubFV_unbindT y y' (FV y'') t'
          p_y''env'_e'_t' = lem_weaken_tv_typ g (Cons y'' t_y g') p_y''env_wf (unbind y y'' e') 
                                           (unbindT y y'' t') p_y''env_e'_t' a k_a

{-@ lem_weaken_tv_typ_tann :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTAnn p_e_t }
        -> { a:Vname | (not (in_env a g)) && (not (in_env a g')) } -> k_a:Kind
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (ConsT a k_a g) g') 
                                                        e t) } / [typSize p_e_t, 0] @-}
lem_weaken_tv_typ_tann :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> Vname -> Kind -> HasType 
lem_weaken_tv_typ_tann g g' p_env_wf e t (TAnn env e' _t p_env_e'_t) a k_a
    = TAnn (concatE (ConsT a k_a g) g') e' t p_env'_e'_t
        where
          p_env'_e'_t = lem_weaken_tv_typ g g' p_env_wf e' t p_env_e'_t a k_a

{-@ lem_weaken_tv_typ :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t }
        -> { a:Vname | (not (in_env a g)) && (not (in_env a g')) } -> k_a:Kind
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (ConsT a k_a g) g') 
                                                        e t) } / [typSize p_e_t, 1] @-}
lem_weaken_tv_typ :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> Vname -> Kind -> HasType 
lem_weaken_tv_typ g g' p_env_wf e t (TBC _g b) a k_a = TBC  (concatE (ConsT a k_a g) g') b
lem_weaken_tv_typ g g' p_env_wf e t (TIC _g n) a k_a = TIC  (concatE (ConsT a k_a g) g') n
lem_weaken_tv_typ g g' p_env_wf e t p_e_t@(TVar1 {}) a k_a
  = lem_weaken_tv_typ_tvar1 g g' p_env_wf e t p_e_t  a k_a
lem_weaken_tv_typ g g' p_env_wf e t p_e_t@(TVar2 {}) a k_a
  = lem_weaken_tv_typ_tvar2 g g' p_env_wf e t p_e_t  a k_a
lem_weaken_tv_typ g g' p_env_wf e t p_e_t@(TVar3 {}) a k_a
  = lem_weaken_tv_typ_tvar3 g g' p_env_wf e t p_e_t  a k_a
lem_weaken_tv_typ g g' p_env_wf e t (TPrm _ c) a k_a  = TPrm (concatE (ConsT a k_a g) g') c
lem_weaken_tv_typ g g' p_env_wf e t p_e_t@(TAbs {}) a k_a
  = lem_weaken_tv_typ_tabs g g' p_env_wf e t p_e_t  a k_a
lem_weaken_tv_typ g g' p_env_wf e t p_e_t@(TApp {}) a k_a
  = lem_weaken_tv_typ_tapp g g' p_env_wf e t p_e_t  a k_a
lem_weaken_tv_typ g g' p_env_wf e t p_e_t@(TAbsT {}) a k_a
  = lem_weaken_tv_typ_tabst g g' p_env_wf e t p_e_t  a k_a
lem_weaken_tv_typ g g' p_env_wf e t p_e_t@(TAppT {}) a k_a
  = lem_weaken_tv_typ_tappt g g' p_env_wf e t p_e_t  a k_a
lem_weaken_tv_typ g g' p_env_wf e t p_e_t@(TLet {}) a k_a
  = lem_weaken_tv_typ_tlet g g' p_env_wf e t p_e_t  a k_a
lem_weaken_tv_typ g g' p_env_wf e t p_e_t@(TAnn {}) a k_a
  = lem_weaken_tv_typ_tann g g' p_env_wf e t p_e_t  a k_a
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


{-@ lem_weaken_tv_subtype_sbase :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE g g'))
      -> t:Type  -> k:Kind  -> ProofOf(WFType (concatE g g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE g g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' && isSBase p_t_t' }
      -> { a:Vname | not (in_env a g) && not (in_env a g') } -> k_a:Kind
      -> ProofOf(Subtype (concatE (ConsT a k_a g) g') t t') / [subtypSize p_t_t', 0] @-}
lem_weaken_tv_subtype_sbase :: Env -> Env -> WFEnv -> Type -> Kind -> WFType 
      -> Type -> Kind -> WFType -> Subtype -> Vname -> Kind -> Subtype
lem_weaken_tv_subtype_sbase g g' p_env_wf t k p_env_t t' k' p_env_t' 
                       (SBase env z1 b p1 z2 p2 w pf_wenv_ent_p2) a_ k_a
    = SBase env' z1 b p1 z2 p2 w' pf_w'env'_ent_p2 
        where
          a                = a_ ? lem_in_env_concat g g' a_
          env'             = concatE (ConsT a k_a g) g'
          w'               = fresh_var (concatE (ConsT a k_a g) g')
          p_wenv_wf        = WFEBind env p_env_wf w t k p_env_t
          p_w'env_wf       = WFEBind env p_env_wf 
                                 (w' ? lem_in_env_concat g g' w'
                                     ? lem_in_env_concat (ConsT a k_a g) g' w')
                                 t k p_env_t
          pf_w'env_ent_p2  = lem_change_var_ent (concatE g g') w t Empty p_wenv_wf
                                 (unbind 0 w p2 ? lem_free_subset_binds env t' k' p_env_t') 
                                 pf_wenv_ent_p2 
                                 (w' ? lem_free_bound_in_env env t' k' p_env_t' w')
                                 ? lem_subFV_unbind 0 w (FV w') p2
          pf_w'env'_ent_p2 = lem_weaken_tv_ent g (Cons w' t g') 
                                 p_w'env_wf (unbind 0 w' p2) pf_w'env_ent_p2 a k_a

{-@ lem_weaken_tv_subtype_sfunc :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE g g'))
      -> t:Type  -> k:Kind  -> ProofOf(WFType (concatE g g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE g g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' && isSFunc p_t_t' }
      -> { a:Vname | not (in_env a g) && not (in_env a g') } -> k_a:Kind
      -> ProofOf(Subtype (concatE (ConsT a k_a g) g') t t') / [subtypSize p_t_t', 0] @-}
lem_weaken_tv_subtype_sfunc :: Env -> Env -> WFEnv -> Type -> Kind -> WFType 
      -> Type -> Kind -> WFType -> Subtype -> Vname -> Kind -> Subtype
lem_weaken_tv_subtype_sfunc g g' p_env_wf ft1 k1 p_env_ft1 ft2 k2 p_env_ft2 
                       (SFunc env z1 s1 z2 s2 p_env_s2_s1 t1 t2 w p_wenv_t1_t2) a_ k_a
    = SFunc env' z1 s1 z2 s2 p_env'_s2_s1 t1 t2 w' p_w'env'_t1_t2
        where
          (WFFunc _ _ _ k_s1 p_env_s1 _ k_t1 w1 p_w1'env_t1)
                           = lem_wffunc_for_wf_tfunc (concatE g g') z1 s1 t1 k1 p_env_ft1
          (WFFunc _ _ _ k_s2 p_env_s2 _ k_t2 w2 p_w2env_t2)
                           = lem_wffunc_for_wf_tfunc (concatE g g') z2 s2 t2 k2 p_env_ft2
          a              = a_ ? lem_in_env_concat g g' a_
          env'           = concatE (ConsT a k_a g) g'
          w'_            = fresh_var (concatE (ConsT a k_a g) g') 
          w'             = w'_ ? lem_in_env_concat g g' w'_
                               ? lem_in_env_concat (ConsT a k_a g) g' w'_
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
          p_env'_s2_s1   = lem_weaken_tv_subtype g g' p_env_wf s2 k_s2 p_env_s2 s1 k_s1
                                                 p_env_s1 p_env_s2_s1 a k_a
          p_w'env_t1_t2  = lem_change_var_subtype env w s2 Empty p_wenv_wf
                                   (unbindT z1 w t1) k_t1 p_wenv_t1 (unbindT z2 w t2) k_t2 p_wenv_t2
                                   p_wenv_t1_t2 
                                   ( w' ? lem_free_bound_in_env env ft1 k1 p_env_ft1 w'
                                        ? lem_free_bound_in_env env ft2 k2 p_env_ft2 w' )
                                   ? lem_tsubFV_unbindT z1 w (FV w') t1
                                   ? lem_tsubFV_unbindT z2 w (FV w') t2
          p_w'env'_t1_t2 = lem_weaken_tv_subtype g (Cons w' s2 g') p_w'env_wf
                                   (unbindT z1 w' t1) k_t1 p_w'env_t1 (unbindT z2 w' t2) k_t2
                                   p_w'env_t2 p_w'env_t1_t2 a k_a

{-@ lem_weaken_tv_subtype_switn :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE g g'))
      -> t:Type  -> k:Kind  -> ProofOf(WFType (concatE g g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE g g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' && isSWitn p_t_t' }
      -> { a:Vname | not (in_env a g) && not (in_env a g') } -> k_a:Kind
      -> ProofOf(Subtype (concatE (ConsT a k_a g) g') t t') / [subtypSize p_t_t', 0] @-}
lem_weaken_tv_subtype_switn :: Env -> Env -> WFEnv -> Type -> Kind -> WFType 
      -> Type -> Kind -> WFType -> Subtype -> Vname -> Kind -> Subtype
lem_weaken_tv_subtype_switn g g' p_env_wf t k p_env_t t2 k2 p_env_t2
                   (SWitn env v_z t_z p_env_vz_tz _t z t' p_env_t_t'vz) a_ k_a
    = SWitn env' v_z t_z p_env'_vz_tz t z t' p_env'_t_t'vz
        where
          (WFExis _ _ _ k_z p_env_tz _ k' z' p_z'env_t')
                        = lem_wfexis_for_wf_texists (concatE g g') z t_z t' k2 p_env_t2
          a             = a_ ? lem_in_env_concat g g' a_
          env'          = concatE (ConsT a k_a g) g'
          p_z'env_wf    = WFEBind env p_env_wf z' t_z k_z p_env_tz
          p_env_t'vz    = lem_subst_wf' (concatE g g') Empty z' v_z t_z p_env_vz_tz p_z'env_wf 
                                        (unbindT z z' t') k' p_z'env_t'
          p_env'_vz_tz  = lem_weaken_tv_typ g g' p_env_wf v_z t_z p_env_vz_tz a k_a
                                         ? lem_tsubFV_unbindT z z' v_z t'
          p_env'_t_t'vz = lem_weaken_tv_subtype g g' p_env_wf t k p_env_t
                                             (tsubBV z v_z t') k' p_env_t'vz p_env_t_t'vz a k_a

{-@ lem_weaken_tv_subtype_sbind :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE g g'))
      -> t:Type  -> k:Kind  -> ProofOf(WFType (concatE g g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE g g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' && isSBind p_t_t' }
      -> { a:Vname | not (in_env a g) && not (in_env a g') } -> k_a:Kind
      -> ProofOf(Subtype (concatE (ConsT a k_a g) g') t t') / [subtypSize p_t_t', 0] @-}
lem_weaken_tv_subtype_sbind :: Env -> Env -> WFEnv -> Type -> Kind -> WFType 
      -> Type -> Kind -> WFType -> Subtype -> Vname -> Kind -> Subtype
lem_weaken_tv_subtype_sbind g g' p_env_wf t1 k1 p_env_t1 t' k' p_env_t'
                   (SBind env z t_z t _t' z' p_z'env_t_t') a_ k_a
    = SBind env' z t_z t t' z'' p_z''env'_t_t'
        where
          (WFExis _ _ _ k_z p_env_tz _ k w p_wenv_t)
                         = lem_wfexis_for_wf_texists (concatE g g') z t_z t k1 p_env_t1
          a              = a_ ? lem_in_env_concat g g' a_
          z''_           = fresh_var (concatE (ConsT a k_a g) g') 
          z''            = z''_ ? lem_in_env_concat g g' z''_
                                ? lem_in_env_concat (ConsT a k_a g) g' z''_
                                ? lem_free_bound_in_env env t1 k1 p_env_t1 z''_
                                ? lem_free_bound_in_env env t' k' p_env_t' z''_
          env'           = concatE (ConsT a k_a g) g'
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
          p_z''env'_t_t' = lem_weaken_tv_subtype g (Cons z'' t_z g') p_z''env_wf
                                   (unbindT z z'' t) k p_z''env_t t' k' p_z''env_t' 
                                   p_z''env_t_t' a k_a

{-@ lem_weaken_tv_subtype_spoly :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE g g'))
      -> t:Type  -> k:Kind  -> ProofOf(WFType (concatE g g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE g g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' && isSPoly p_t_t' }
      -> { a:Vname | not (in_env a g) && not (in_env a g') } -> k_a:Kind
      -> ProofOf(Subtype (concatE (ConsT a k_a g) g') t t') / [subtypSize p_t_t', 0] @-}
lem_weaken_tv_subtype_spoly :: Env -> Env -> WFEnv -> Type -> Kind -> WFType 
      -> Type -> Kind -> WFType -> Subtype -> Vname -> Kind -> Subtype
lem_weaken_tv_subtype_spoly g g' p_env_wf t1 Star p_env_t1 t2 Star p_env_t2
                         (SPoly env a1 k' t1' a2 t2' a1' p_a1'g_t1'_t2') a k_a
    = SPoly (concatE (ConsT a k_a g) g') a1 k' t1' a2 t2' a1'' p_a1''a_t1'_t2'
        where
          (WFPoly _ _ _ _ k_t1' aa1 p_aa1env_t1')
                          = lem_wfpoly_for_wf_tpoly env a1 k' t1' p_env_t1
          (WFPoly _ _ _ _ k_t2' aa2 p_aa2env_t2')
                          = lem_wfpoly_for_wf_tpoly env a2 k' t2' p_env_t2
          a1''_           = fresh_var (concatE (ConsT a k_a g) g') 
          a1''            = a1''_ ? lem_in_env_concat g g' a1''_
                                  ? lem_in_env_concat (ConsT a k_a g) g' a1''_
                                  ? lem_free_bound_in_env env t1 Star p_env_t1 a1''_
                                  ? lem_free_bound_in_env env t2 Star p_env_t2 a1''_
          p_aa1env_wf     = WFEBindT env p_env_wf aa1  k'
          p_aa2env_wf     = WFEBindT env p_env_wf aa2  k'
          p_a1'env_wf     = WFEBindT env p_env_wf a1'  k'
          p_a1''env_wf    = WFEBindT env p_env_wf a1'' k'
          p_a1'env_t1'    = lem_change_tvar_wf' (concatE g g') aa1 k' Empty p_aa1env_wf
                                  (unbind_tvT a1 aa1 t1') k_t1' p_aa1env_t1' a1'
                                  ? lem_tchgFTV_unbind_tvT a1 aa1 a1' t1'
          p_a1'env_t2'    = lem_change_tvar_wf' (concatE g g') aa2 k' Empty p_aa2env_wf
                                  (unbind_tvT a2 aa2 t2') k_t2' p_aa2env_t2' a1'
                                  ? lem_tchgFTV_unbind_tvT a2 aa2 a1' t2'
          p_a1''env_t1'   = lem_change_tvar_wf' (concatE g g') aa1 k' Empty p_aa1env_wf
                                  (unbind_tvT a1 aa1 t1') k_t1' p_aa1env_t1' a1''
                                  ? lem_tchgFTV_unbind_tvT a1 aa1 a1'' t1'
          p_a1''env_t2'   = lem_change_tvar_wf' (concatE g g') aa2 k' Empty p_aa2env_wf
                                  (unbind_tvT a2 aa2 t2') k_t2' p_aa2env_t2' a1''
                                  ? lem_tchgFTV_unbind_tvT a2 aa2 a1'' t2'
          p_a1''_t1'_t2'  = lem_change_tvar_subtype (concatE g g') a1' k' Empty p_a1'env_wf
                                  (unbind_tvT a1 a1' t1') k_t1' p_a1'env_t1'
                                  (unbind_tvT a2 a1' t2') k_t2' p_a1'env_t2' p_a1'g_t1'_t2' a1''
                                  ? lem_tchgFTV_unbind_tvT a1 a1' a1'' t1'
                                  ? lem_tchgFTV_unbind_tvT a2 a1' a1'' t2'
          p_a1''a_t1'_t2' = lem_weaken_tv_subtype g (ConsT a1'' k' g') p_a1''env_wf
                                  (unbind_tvT a1 a1'' t1') k_t1' p_a1''env_t1'
                                  (unbind_tvT a2 a1'' t2') k_t2' p_a1''env_t2' p_a1''_t1'_t2' a k_a
lem_weaken_tv_subtype_spoly g g' p_env_wf t1 Base p_env_t1 t2 k2 p_env_t2 
                         (SPoly env a1 k' t1' a2 t2' a1' p_a1'g_t1'_t2') a_ k_a
    = impossible ("by lemma" ? lem_wf_tpoly_star env a1 k' t1' p_env_t1)
lem_weaken_tv_subtype_spoly g g' p_env_wf t1 k1 p_env_t1 t2 Base p_env_t2 
                         (SPoly env a1 k' t1' a2 t2' a1' p_a1'g_t1'_t2') a_ k_a
    = impossible ("by lemma" ? lem_wf_tpoly_star env a2 k' t2' p_env_t2)

{-@ lem_weaken_tv_subtype :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE g g'))
      -> t:Type  -> k:Kind  -> ProofOf(WFType (concatE g g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE g g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' }
      -> { a:Vname | not (in_env a g) && not (in_env a g') } -> k_a:Kind
      -> ProofOf(Subtype (concatE (ConsT a k_a g) g') t t') / [subtypSize p_t_t', 1] @-}
lem_weaken_tv_subtype :: Env -> Env -> WFEnv -> Type -> Kind -> WFType 
      -> Type -> Kind -> WFType -> Subtype -> Vname -> Kind -> Subtype
lem_weaken_tv_subtype g g' p_env_wf t k p_env_t t' k' p_env_t' 
                      p_t_t'@(SBase env z1 b p1 z2 p2 w pf_wenv_ent_p2) a_ k_a
    = lem_weaken_tv_subtype_sbase g g' p_env_wf t k p_env_t t' k' p_env_t' p_t_t' a_ k_a
lem_weaken_tv_subtype g g' p_env_wf ft1 k1 p_env_ft1 ft2 k2 p_env_ft2 
                      p_t_t'@(SFunc env z1 s1 z2 s2 p_env_s2_s1 t1 t2 w p_wenv_t1_t2) a_ k_a
    = lem_weaken_tv_subtype_sfunc g g' p_env_wf ft1 k1 p_env_ft1 ft2 k2 p_env_ft2 p_t_t' a_ k_a
lem_weaken_tv_subtype g g' p_env_wf t k p_env_t t2 k2 p_env_t2
                      p_t_t'@(SWitn env v_z t_z p_env_vz_tz _t z t' p_env_t_t'vz) a_ k_a
    = lem_weaken_tv_subtype_switn g g' p_env_wf t k p_env_t t2 k2 p_env_t2 p_t_t' a_ k_a
lem_weaken_tv_subtype g g' p_env_wf t1 k1 p_env_t1 t' k' p_env_t'
                      p_t_t'@(SBind env z t_z t _t' z' p_z'env_t_t') a_ k_a
    = lem_weaken_tv_subtype_sbind g g' p_env_wf t1 k1 p_env_t1 t' k' p_env_t' p_t_t' a_ k_a
lem_weaken_tv_subtype g g' p_env_wf t1 k1 p_env_t1 t2 k2 p_env_tw p_t_t'@(SPoly {}) a k_a
    = lem_weaken_tv_subtype_spoly g g' p_env_wf t1 k1 p_env_t1 t2 k2 p_env_tw p_t_t' a k_a
