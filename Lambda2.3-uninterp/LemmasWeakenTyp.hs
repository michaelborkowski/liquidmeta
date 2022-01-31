{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasWeakenTyp where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
--import BasicPropsSubstitution
import BasicPropsEnvironments
--import BasicPropsWellFormedness
--import SystemFLemmasWeaken
--import SystemFLemmasSubstitution
import Typing
--import BasicPropsCSubst
import LemmasWeakenWF
--import LemmasWeakenEnt
--import LemmasWellFormedness
--import LemmasTyping
--import SubstitutionWFAgain

{-@ reflect foo47 @-}
foo47 x = Just x
foo47 :: a -> Maybe a

-----------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
-----------------------------------------------------------

--        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
{-@ lem_weaken_typ_tvar1 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTVar1 p_e_t }
        -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) } -> t_x:Type 
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (Cons x t_x g) g') e t) } 
           / [esize e, envsize g', 0] @-}
lem_weaken_typ_tvar1 :: Env -> Env {-> WFEnv-} -> Expr -> Type -> HasType -> Vname -> Type -> HasType
lem_weaken_typ_tvar1 g g' {-p_env_wf-} e t p_y_t@(TVar1 gg y t_y k_y p_gg_ty) x_ t_x
    = case g' of     -- env == concatE g (Cons y t_y g'')
        (Empty)           -> TVar2 (Cons y t_y gg) y t p_y_t x t_x   
          where
            x = x_ -- ? lem_free_bound_in_env g t Star p_g_t x_
--            (WFEBind _gg p_gg_wf _y _ty k_y p_gg_ty) = p_env_wf
--            p_g_t  = lem_typing_wf g (FV y) t p_y_t p_env_wf
        (Cons _y _ty g'') -> TVar1 (concatE (Cons x t_x g) g'') y t_y k_y p_gxg_ty        
          where
            x = x_ -- ? lem_in_env_concat g g' x_
--            (WFEBind _gg p_gg_wf _y _ty _ky _) = p_env_wf
            p_gxg_ty = lem_weaken_wf g g'' {-p_gg_wf-} t_y k_y p_gg_ty x t_x
-- (g; g' == _g, z:t_z) |- y : t_y

{-@ lem_weaken_typ_tvar2 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTVar2 p_e_t }
        -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) } -> t_x:Type 
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (Cons x t_x g) g') e t) } 
           / [esize e, envsize g', 0] @-}
lem_weaken_typ_tvar2 :: Env -> Env {-> WFEnv-} -> Expr -> Type -> HasType -> Vname -> Type -> HasType
lem_weaken_typ_tvar2 g g' {-p_env_wf-} e t p_y_ty@(TVar2 gg y t_y p_gg_y_ty z t_z) x_ t_x
    = case g' of
        (Empty)           -> TVar2 (concatE g g') y t_y p_y_ty x t_x 
          where
            x = x_ -- ? lem_free_bound_in_env gg t_y Star p_gg_ty x_
--            (WFEBind _gg p_gg_wf _ _ _ _) = p_env_wf
--            p_gg_ty = lem_typing_wf gg (FV y) t_y p_gg_y_ty p_gg_wf
        (Cons _z _tz g'') -> TVar2 (concatE (Cons x t_x g) g'') 
                                   (y `withProof` lem_in_env_concat g g'' y)
                                   t_y p_gxg_y_ty z t_z                                       
          where
            x = x_ -- ? lem_in_env_concat gg (Cons z t_z Empty) x_
--            (WFEBind _gg p_gg_wf _ _ _ _) = p_env_wf 
            p_gxg_y_ty = lem_weaken_typ g g'' {-p_gg_wf-} e t p_gg_y_ty x t_x

{-@ lem_weaken_typ_tvar3 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTVar3 p_e_t }
        -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) } -> t_x:Type 
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (Cons x t_x g) g') e t) } 
           / [esize e, envsize g', 0] @-}
lem_weaken_typ_tvar3 :: Env -> Env {-> WFEnv-} -> Expr -> Type -> HasType -> Vname -> Type -> HasType
lem_weaken_typ_tvar3 g g' {-p_env_wf-} e t p_z_tz@(TVar3 gg z t_z p_z_t a' k_a') x_ t_x 
    = case g' of
        (Empty)           -> TVar2 (concatE g g') z t_z p_z_tz x t_x
          where
            x = x_ -- ? lem_free_bound_in_env gg t_z Star p_gg_tz x_
--            (WFEBindT _gg p_gg_wf _ _) = p_env_wf
--            p_gg_tz = lem_typing_wf gg (FV z) t_z p_z_t p_gg_wf
        (ConsT _a' _ g'') -> TVar3 (concatE (Cons x t_x g) g'')
                                 (z `withProof` lem_in_env_concat g g'' z)
                                 t (lem_weaken_typ g g'' {-p_env'_wf-} (FV z) t p_z_t x t_x)
                                 a' k_a'                                                     
          where
            x  = x_  -- ? lem_in_env_concat g (ConsT a' k_a' g'') x_
--            (WFEBindT env' p_env'_wf _ _) = p_env_wf

{-@ lem_weaken_typ_tabs :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTAbs p_e_t }
        -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) } -> t_x:Type 
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (Cons x t_x g) g') e t) } 
           / [esize e, envsize g', 0] @-}
lem_weaken_typ_tabs :: Env -> Env {-> WFEnv-} -> Expr -> Type -> HasType -> Vname -> Type -> HasType          
lem_weaken_typ_tabs g g' {-p_env_wf-} e t p_e_t@(TAbs env t_y k_y p_gg'_ty e' t' nms mk_p_y_e'_t') x t_x
    = TAbs (concatE (Cons x t_x g) g') t_y k_y p_gxg'_ty e' t' nms' mk_p_yx_e'_t'
        where
--            p_env_t      = lem_typing_wf env e t p_e_t p_env_wf
            p_gxg'_ty    = lem_weaken_wf g g' {-p_env_wf-} t_y k_y p_gg'_ty x t_x 
--            y''_         = fresh_var (concatE (Cons x t_x g) g')
--            y''          = y''_ ? lem_in_env_concat g g' y''_
--                                ? lem_in_env_concat (Cons x t_x g) g' y''_
--                                ? lem_fv_bound_in_env (concatE g g') e t p_e_t p_env_wf y''_
--                                ? lem_free_bound_in_env env t Star p_env_t y''_
--            p_y''env_wf  = WFEBind env p_env_wf y'' t_y k_y p_gg'_ty
            {-@ mk_p_yx_e'_t' :: { y:Vname | NotElem y nms' }
                  -> ProofOf(HasType (Cons y t_y (concatE (Cons x t_x g) g'))
                                     (unbind y e') (unbindT y t')) @-}
            mk_p_yx_e'_t' y = lem_weaken_typ g (Cons y t_y g') {-p_y''env_wf-} (unbind y e') 
                                     (unbindT y t') (mk_p_y_e'_t' y) x t_x
            nms'            = x:(unionEnv nms (concatE g g'))

{-@ lem_weaken_typ_tapp :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTApp p_e_t }
        -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) } -> t_x:Type 
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (Cons x t_x g) g') e t) } 
           / [esize e, envsize g', 0] @-}
lem_weaken_typ_tapp :: Env -> Env {-> WFEnv-} -> Expr -> Type -> HasType -> Vname -> Type -> HasType
lem_weaken_typ_tapp g g' {-p_env_wf-} e t (TApp env e1 s s' p_env_e1_ss' e2 p_env_e2_s) x t_x 
    = TApp (concatE (Cons x t_x g) g') e1 s s' p_env'_e1_ss' e2 p_env'_e2_s
        where
          p_env'_e1_ss' = lem_weaken_typ g g' {-p_env_wf-} e1 (TFunc s s') p_env_e1_ss' x t_x
          p_env'_e2_s   = lem_weaken_typ g g' {-p_env_wf-} e2 s            p_env_e2_s   x t_x

{-@ lem_weaken_typ_tabst :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTAbsT p_e_t }
        -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) } -> t_x:Type 
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (Cons x t_x g) g') e t) } 
           / [esize e, envsize g', 0] @-}
lem_weaken_typ_tabst :: Env -> Env {-> WFEnv-} -> Expr -> Type -> HasType -> Vname -> Type -> HasType
lem_weaken_typ_tabst g g' {-p_env_wf-} e t 
                     p_e_t@(TAbsT env k1 e' t' nms mk_p_ag_e'_t') x t_x 
    = TAbsT (concatE (Cons x t_x g) g') k1 e' t' nms' mk_p_ax_e'_t'
        where
          {-@ mk_p_ax_e'_t' :: { a:Vname | NotElem a nms' }
                -> ProofOf(HasType (ConsT a k1 (concatE (Cons x t_x g) g'))
                                     (unbind_tv a e') (unbind_tvT a t')) @-}
          mk_p_ax_e'_t' a = lem_weaken_typ g (ConsT a k1 g') --p_a''env_wf 
                                (unbind_tv a e') (unbind_tvT a t') (mk_p_ag_e'_t' a) x t_x
          nms'              = x:(unionEnv nms (concatE g g'))

{-@ lem_weaken_typ_tappt :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTAppT p_e_t }
        -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) } -> t_x:Type 
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (Cons x t_x g) g') e t) } 
           / [esize e, envsize g', 0] @-}
lem_weaken_typ_tappt :: Env -> Env {-> WFEnv-} -> Expr -> Type -> HasType -> Vname -> Type -> HasType
lem_weaken_typ_tappt g g' {-p_env_wf-} e t p_e_t@(TAppT env e' k1 s p_e'_a1s t' p_env_t') x t_x 
    = TAppT (concatE (Cons x t_x g) g') e' k1 s p_env'_e'_a1s t' p_env'_t'
        where
          p_env'_e'_a1s = lem_weaken_typ g g' {-p_env_wf-} e' (TPoly k1 s) p_e'_a1s x t_x
          p_env'_t'     = lem_weaken_wf  g g' {-p_env_wf-} t' k1 p_env_t' x t_x

{-@ lem_weaken_typ_tlet :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTLet p_e_t }
        -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) } -> t_x:Type 
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (Cons x t_x g) g') e t) } 
           / [esize e, envsize g', 0] @-}
lem_weaken_typ_tlet :: Env -> Env {-> WFEnv-} -> Expr -> Type -> HasType -> Vname -> Type -> HasType
lem_weaken_typ_tlet g g' {-p_env_wf-} e t 
               p_e_t@(TLet env e_y t_y p_env_ey_ty e' t' k' p_env_t' nms mk_p_yenv_e'_t') x t_x
    = TLet (concatE (Cons x t_x g) g') e_y t_y p_env'_ey_ty e' t' k' p_env'_t' nms' mk_p_yenv'_e'_t'
        where
          p_env'_ey_ty       = lem_weaken_typ g g' {-p_env_wf-} e_y t_y p_env_ey_ty x t_x
          p_env'_t'          = lem_weaken_wf g g' {-p_env_wf-} t' k' p_env_t' x t_x
          {-@ mk_p_yenv'_e'_t' :: { y:Vname | NotElem y nms' }
                -> ProofOf(HasType (Cons y t_y (concatE (Cons x t_x g) g'))
                                   (unbind y e') (unbindT y t')) @-}
          mk_p_yenv'_e'_t' y = lem_weaken_typ g (Cons y t_y g') {-p_y''env_wf-} (unbind y e') 
                                              (unbindT y t') (mk_p_yenv_e'_t' y) x t_x 
          nms'               = x:(unionEnv nms (concatE g g'))

{-@ lem_weaken_typ_tann :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTAnn p_e_t }
        -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) } -> t_x:Type 
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (Cons x t_x g) g') e t) } 
           / [esize e, envsize g', 0] @-}
lem_weaken_typ_tann :: Env -> Env {-> WFEnv-} -> Expr -> Type -> HasType -> Vname -> Type -> HasType 
lem_weaken_typ_tann g g' {-p_env_wf-} e t (TAnn env e' _t p_env_e'_t) x t_x
    = TAnn (concatE (Cons x t_x g) g') e' t p_env'_e'_t
        where
          p_env'_e'_t = lem_weaken_typ g g' {-p_env_wf-} e' t p_env_e'_t x t_x

{-@ lem_weaken_typ_tsub :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTSub p_e_t }
        -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) } -> t_x:Type 
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (Cons x t_x g) g') e t) } 
           / [esize e, envsize g', 0] @-}
lem_weaken_typ_tsub :: Env -> Env {-> WFEnv-} -> Expr -> Type -> HasType -> Vname -> Type -> HasType
lem_weaken_typ_tsub g g' {-p_env_wf-} e t (TSub env _e s p_env_e_s _t k p_env_t p_env_s_t) x t_x
    = TSub (concatE (Cons x t_x g) g') e s p_env'_e_s t k p_env'_t p_env'_s_t 
        where
--          p_env_s    = lem_typing_wf      env e s p_env_e_s p_env_wf
          p_env'_e_s = lem_weaken_typ     g g' {-p_env_wf-} e s p_env_e_s x t_x
          p_env'_t   = lem_weaken_wf      g g' {-p_env_wf-} t k p_env_t x t_x 
          p_env'_s_t = lem_weaken_subtype g g' {-p_env_wf-} s {-Star p_env_s-} t {-k p_env_t-}
                                          p_env_s_t x t_x

--        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
{-@ lem_weaken_typ :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t }
        -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) } -> t_x:Type 
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (Cons x t_x g) g') e t) } 
           / [esize e, envsize g', 1] @-}
lem_weaken_typ :: Env -> Env {-> WFEnv-} -> Expr -> Type -> HasType -> Vname -> Type -> HasType 
lem_weaken_typ g g' {-p_env_wf-} e t (TBC _g b)      x t_x = TBC  (concatE (Cons x t_x g) g') b
lem_weaken_typ g g' {-p_env_wf-} e t (TIC _g n)      x t_x = TIC  (concatE (Cons x t_x g) g') n
lem_weaken_typ g g' {-p_env_wf-} e t p_y_t@(TVar1 gg y t_y k_y p_gg_ty) x_ t_x -- env == concatE g (Cons y t_y g'') 
    = lem_weaken_typ_tvar1 g g' {-p_env_wf-} e t p_y_t x_ t_x
lem_weaken_typ g g' {-p_env_wf-} e t p_y_ty@(TVar2 gg y t_y p_gg_y_ty z t_z) x_ t_x
    = lem_weaken_typ_tvar2 g g' {-p_env_wf-} e t p_y_ty x_ t_x
lem_weaken_typ g g'{- p_env_wf-} e t p_y_ty@(TVar3 {}) x t_x 
    = lem_weaken_typ_tvar3 g g' {-p_env_wf-} e t p_y_ty x t_x
lem_weaken_typ g g' {-p_env_wf-} e t (TPrm _g c)     x t_x = TPrm (concatE (Cons x t_x g) g') c
lem_weaken_typ g g' {-p_env_wf-} e t p_e_t@(TAbs {}) x t_x
    = lem_weaken_typ_tabs g g' {-p_env_wf-} e t p_e_t x t_x
lem_weaken_typ g g' {-p_env_wf-} e t p_e_t@(TApp {}) x t_x 
    = lem_weaken_typ_tapp g g' {-p_env_wf-} e t p_e_t x t_x
lem_weaken_typ g g' {-p_env_wf-} e t p_e_t@(TAbsT {}) x t_x 
    = lem_weaken_typ_tabst g g' {-p_env_wf-} e t p_e_t x t_x
lem_weaken_typ g g' {-p_env_wf-} e t p_e_t@(TAppT {}) x t_x 
    = lem_weaken_typ_tappt g g' {-p_env_wf-} e t p_e_t x t_x
lem_weaken_typ g g' {-p_env_wf-} e t p_e_t@(TLet {}) x t_x
    = lem_weaken_typ_tlet g g' {-p_env_wf-} e t p_e_t x t_x
lem_weaken_typ g g' {-p_env_wf-} e t p_e_t@(TAnn env e' _t p_env_e'_t) x t_x
    = lem_weaken_typ_tann g g' {-p_env_wf-} e t p_e_t x t_x
lem_weaken_typ g g' {-p_env_wf-} e t p_e_t@(TSub {}) x t_x
    = lem_weaken_typ_tsub g g' {-p_env_wf-} e t p_e_t x t_x

--      -> ProofOf(WFEnv (concatE g g'))
--      -> t:Type  -> k:Kind  -> ProofOf(WFType (concatE g g') t k) 
--      -> t':Type -> k':Kind -> ProofOf(WFType (concatE g g') t' k')
--      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (Cons x t_x g) g') t t' &&
--                     subtypSize' p_t_t' == subtypSize' p'_t_t' } / [tsize t', envsize g', 0] @-}
{-@ lem_weaken_subtype_sbase :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> t:Type -> t':Type
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t'&& isSBase p_t_t' }
      -> { x:Vname | not (in_env x g) && not (in_env x g') } -> t_x:Type
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (Cons x t_x g) g') t t' }
       / [tsize t', envsize g', 0] @-}
lem_weaken_subtype_sbase :: Env -> Env {-> WFEnv-} -> Type {-> Kind -> WFType -}
      -> Type {-> Kind -> WFType-} -> Subtype -> Vname -> Type -> Subtype
lem_weaken_subtype_sbase g g' {-p_env_wf-} t {-k p_env_t-} t' {-k' p_env_t'-}
                       (SBase env b p1 p2 nms mk_pf_yenv_p1_p2) x t_x
    = SBase env' b p1 p2 nms' mk_pf_yenv'_p1_p2 
        where
--          x                = x_ ? lem_in_env_concat g g' x_
          env'             = concatE (Cons x t_x g) g'
          {-@ mk_pf_yenv'_p1_p2 :: { y:Vname | NotElem y nms' }
                -> ProofOf(Implies (Cons y (TRefn b PEmpty) (concatE (Cons x t_x g) g')) 
                                   (unbindP y p1) (unbindP y p2)) @-}
          mk_pf_yenv'_p1_p2 y = IWeak g (Cons y (TRefn b PEmpty) g') 
                                      (unbindP y p1) (unbindP y p2) (mk_pf_yenv_p1_p2 y) x t_x
          nms'                = x:(unionEnv nms (concatE g g'))
--        p_wenv_wf        = WFEBind env p_env_wf w t k p_env_t

{-@ lem_weaken_subtype_sfunc :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> t:Type -> t':Type
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' && isSFunc p_t_t' }
      -> { x:Vname | not (in_env x g) && not (in_env x g') } -> t_x:Type
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (Cons x t_x g) g') t t' }
       / [tsize t', envsize g', 0] @-}
lem_weaken_subtype_sfunc :: Env -> Env {-> WFEnv-} -> Type {-> Kind -> WFType -}
      -> Type {-> Kind -> WFType-} -> Subtype -> Vname -> Type -> Subtype
lem_weaken_subtype_sfunc g g' {-p_env_wf-} ft1 {-k1 p_env_ft1-} ft2 {-k2 p_env_ft2 -}
                       (SFunc env s1 s2 p_env_s2_s1 t1 t2 nms mk_p_wenv_t1_t2) x t_x
    = SFunc env' s1 s2 p_env'_s2_s1 t1 t2 nms' mk_p_wenv'_t1_t2
        where
          env'           = concatE (Cons x t_x g) g'
          p_env'_s2_s1   = lem_weaken_subtype g g' {-p_env_wf-} s2 {-k_s2 p_env_s2-} s1 {-k_s1
                                              p_env_s1-} p_env_s2_s1 x t_x
          {-@ mk_p_wenv'_t1_t2 :: { w:Vname | NotElem w nms' }
                -> ProofOf(Subtype (Cons w s2 (concatE (Cons x t_x g) g')) 
                                   (unbindT w t1) (unbindT w t2)) @-}
          mk_p_wenv'_t1_t2 w = lem_weaken_subtype g (Cons w s2 g') --p_w'env_wf
                                   (unbindT w t1) {-k_t1 p_wenv_t1-} (unbindT w t2) {-k_t2
                                   p_wenv_t2-} (mk_p_wenv_t1_t2 w) x t_x
          nms'               = x:(unionEnv nms (concatE g g'))
{-          (WFFunc _ _ _ k_s1 p_env_s1 _ k_t1 w1 p_w1'env_t1)
                           = lem_wffunc_for_wf_tfunc (concatE g g') z1 s1 t1 k1 p_env_ft1
          (WFFunc _ _ _ k_s2 p_env_s2 _ k_t2 w2 p_w2env_t2)
                           = lem_wffunc_for_wf_tfunc (concatE g g') z2 s2 t2 k2 p_env_ft2
--          x              = x_ ? lem_in_env_concat g g' x_
          p_w'env_wf     = WFEBind env p_env_wf w' s2 k_s2 p_env_s2
          p_w1env_t1     = lem_subtype_in_env_wf env Empty w1 s2 s1 p_env_s2_s1 
                                                 (unbindT z1 w1 t1) k_t1 p_w1'env_t1
-}

{-@ lem_weaken_subtype_switn :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> t:Type -> t':Type
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' && isSWitn p_t_t' }
      -> { x:Vname | not (in_env x g) && not (in_env x g') } -> t_x:Type
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (Cons x t_x g) g') t t' }
       / [tsize t', envsize g', 0] @-}
lem_weaken_subtype_switn :: Env -> Env {-> WFEnv-} -> Type {-> Kind -> WFType-}
      -> Type {-> Kind -> WFType-} -> Subtype -> Vname -> Type -> Subtype
lem_weaken_subtype_switn g g' {-p_env_wf-} t {-k p_env_t-} t2 {-k2 p_env_t2-}
                   (SWitn env v_z t_z p_env_vz_tz _t t' p_env_t_t'vz) x t_x 
    = SWitn env' v_z t_z p_env'_vz_tz t t' p_env'_t_t'vz
        where
          env'          = concatE (Cons x t_x g) g'
          p_env'_vz_tz  = lem_weaken_typ g g' {-p_env_wf-} v_z t_z p_env_vz_tz x t_x
--                                         ? lem_tsubFV_unbindT z z' v_z t'
          p_env'_t_t'vz = lem_weaken_subtype g g' {-p_env_wf-} t {-k p_env_t-}
                                             (tsubBV v_z t') {-k' p_env_t'vz-} p_env_t_t'vz x t_x
{-          (WFExis _ _ _ k_z p_env_tz _ k' z' p_z'env_t')
                        = lem_wfexis_for_wf_texists (concatE g g') z t_z t' k2 p_env_t2
          p_env_t'vz    = lem_subst_wf (concatE g g') Empty z' v_z t_z p_env_vz_tz
                                       (unbindT z z' t') k' p_z'env_t'-}

{-@ lem_weaken_subtype_sbind :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> t:Type -> t':Type
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' && isSBind p_t_t' }
      -> { x:Vname | not (in_env x g) && not (in_env x g') } -> t_x:Type
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (Cons x t_x g) g') t t' }
       / [tsize t', envsize g', 0] @-}
lem_weaken_subtype_sbind :: Env -> Env {-> WFEnv-} -> Type {-> Kind -> WFType -}
      -> Type {-> Kind -> WFType-} -> Subtype -> Vname -> Type -> Subtype
lem_weaken_subtype_sbind g g' {-p_env_wf-} t1 {-k1 p_env_t1-} t' {-k' p_env_t'-}
                   (SBind env t_z t _t' nms mk_p_zenv_t_t') x t_x
    = SBind env' t_z t t' nms' mk_p_zenv'_t_t'
        where
          env'           = concatE (Cons x t_x g) g'
          {-@ mk_p_zenv'_t_t' :: { z:Vname | NotElem z nms'}
                -> ProofOf(Subtype (Cons z t_z (concatE (Cons x t_x g) g')) (unbindT z t) t') @-}
          mk_p_zenv'_t_t' z = lem_weaken_subtype g (Cons z t_z g') {-p_z''env_wf-}
                                   (unbindT z t) {-k p_z''env_t-} t' {-k' p_z''env_t' -}
                                   (mk_p_zenv_t_t' z) x t_x
          nms'              = x:(unionEnv nms (concatE g g'))
{-          (WFExis _ _ _ k_z p_env_tz _ k w p_wenv_t)
                         = lem_wfexis_for_wf_texists (concatE g g') z t_z t k1 p_env_t1
          p_z''env_wf    = WFEBind env p_env_wf z'' t_z k_z p_env_tz
          p_z''env_t'    = lem_weaken_wf' env Empty p_env_wf t' k' p_env_t' z'' t_z
-}
{-@ lem_weaken_subtype_spoly :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> t:Type -> t':Type
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' && isSPoly p_t_t' }
      -> { x:Vname | not (in_env x g) && not (in_env x g') } -> t_x:Type
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (Cons x t_x g) g') t t' }
       / [tsize t', envsize g', 0] @-}
lem_weaken_subtype_spoly :: Env -> Env {-> WFEnv-} -> Type {-> Kind -> WFType -}
      -> Type {-> Kind -> WFType-} -> Subtype -> Vname -> Type -> Subtype
lem_weaken_subtype_spoly g g' {-p_env_wf-} t1 {-Star p_env_t1-} t2 {-Star p_env_t2 -}
                         (SPoly env k' t1' t2' nms mk_p_a1g_t1'_t2') x t_x
    = SPoly (concatE (Cons x t_x g) g') k' t1' t2' nms' mk_p_a1x_t1'_t2'
        where
          {-@ mk_p_a1x_t1'_t2' :: { a1:Vname | NotElem a1 nms' }
                -> ProofOf(Subtype (ConsT a1 k' (concatE (Cons x t_x g) g')) 
                                   (unbind_tvT a1 t1') (unbind_tvT a1 t2')) @-}
          mk_p_a1x_t1'_t2' a1 = lem_weaken_subtype g (ConsT a1 k' g') {-p_a1''env_wf-}
                                  (unbind_tvT a1 t1') {-k_t1' p_a1''env_t1'-}
                                  (unbind_tvT a1 t2') {-k_t2' p_a1''env_t2'-} 
                                  (mk_p_a1g_t1'_t2' a1) x t_x
          nms'              = x:(unionEnv nms (concatE g g'))
{-
          (WFPoly _ _ _ _ k_t1' aa1 p_aa1env_t1')
                          = lem_wfpoly_for_wf_tpoly env a1 k' t1' p_env_t1
          (WFPoly _ _ _ _ k_t2' aa2 p_aa2env_t2')
                          = lem_wfpoly_for_wf_tpoly env a2 k' t2' p_env_t2
          p_a1''env_wf    = WFEBindT env p_env_wf a1'' k'
-}
{-lem_weaken_subtype_spoly g g' p_env_wf t1 Base p_env_t1 t2 k2 p_env_t2 
                         (SPoly env a1 k' t1' a2 t2' a1' p_a1'g_t1'_t2') x_ t_x
    = impossible ("by lemma" ? lem_wf_tpoly_star env k' t1' p_env_t1)
lem_weaken_subtype_spoly g g' p_env_wf t1 k1 p_env_t1 t2 Base p_env_t2 
                         (SPoly env a1 k' t1' a2 t2' a1' p_a1'g_t1'_t2') x_ t_x
    = impossible ("by lemma" ? lem_wf_tpoly_star env k' t2' p_env_t2)
-}
--      -> ProofOf(WFEnv (concatE g g'))
--      -> t:Type  -> k:Kind  -> ProofOf(WFType (concatE g g') t k) 
--      -> t':Type -> k':Kind -> ProofOf(WFType (concatE g g') t' k')
{-@ lem_weaken_subtype :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> t:Type -> t':Type -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' }
      -> { x:Vname | not (in_env x g) && not (in_env x g') } -> t_x:Type
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (Cons x t_x g) g') t t' }
       / [tsize t', envsize g', 1] @-}
lem_weaken_subtype :: Env -> Env {-> WFEnv-} -> Type {-> Kind -> WFType-} 
      -> Type {-> Kind -> WFType-} -> Subtype -> Vname -> Type -> Subtype
lem_weaken_subtype g g' {-p_env_wf-} t {-k p_env_t-} t' {-k' p_env_t'-}  p_t_t'@(SBase {}) x_ t_x
    = lem_weaken_subtype_sbase g g' {-p_env_wf-} t {-k p_env_t-} t' {-k' p_env_t'-} p_t_t' x_ t_x 
lem_weaken_subtype g g' {-p_env_wf-} ft1 {-k1 p_env_ft1-} ft2 {-k2 p_env_ft2-}  p_ft1_ft2@(SFunc {}) x_ t_x
    = lem_weaken_subtype_sfunc g g' {-p_env_wf-} ft1 {-k1 p_env_ft1-} ft2 {-k2 p_env_ft2-} p_ft1_ft2 x_ t_x
lem_weaken_subtype g g' {-p_env_wf-} t {-k p_env_t-} t2 {-k2 p_env_t2-}    p_t_t2@(SWitn {}) x_ t_x 
    = lem_weaken_subtype_switn g g' {-p_env_wf-} t {-k p_env_t-} t2 {-k2 p_env_t2-} p_t_t2 x_ t_x
lem_weaken_subtype g g' {-p_env_wf-} t1 {-k1 p_env_t1-} t' {-k' p_env_t'-} p_t1_t'@(SBind {}) x_ t_x
    = lem_weaken_subtype_sbind g g' {-p_env_wf-} t1 {-k1 p_env_t1-} t' {-k' p_env_t'-} p_t1_t' x_ t_x
lem_weaken_subtype g g' {-p_env_wf-} t1 {-k1 p_env_t1-} t2 {-k2 p_env_tw-} p_t1_t2@(SPoly {}) x_ t_x
    = lem_weaken_subtype_spoly g g' {-p_env_wf-} t1 {-k1 p_env_t1-} t2 {-k2 p_env_tw-} p_t1_t2 x_ t_x
