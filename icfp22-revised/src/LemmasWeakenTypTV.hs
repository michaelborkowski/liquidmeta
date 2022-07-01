{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasWeakenTypTV where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof,(?))
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import BasicPropsEnvironments
import Typing
import LemmasWeakenWFTV
import LemmasWeakenTyp

-----------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
-----------------------------------------------------------

{-@ lem_weaken_tv_typ_tvar1 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTVar1 p_e_t }
        -> { a:Vname | (not (in_env a g)) && (not (in_env a g')) } -> k_a:Kind
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (ConsT a k_a g) g') e t }
         / [ typSize p_e_t, 0 ] @-}
lem_weaken_tv_typ_tvar1 :: Env -> Env ->  Expr -> Type -> HasType -> Vname -> Kind -> HasType  
lem_weaken_tv_typ_tvar1 g g' {-p_env_wf-} e t p_y_t@(TVar1 gg y t_y k_y p_gg_ty) a k_a
    = case g' of     -- env == concatE g (Cons y t_y g'')
        (Empty)           -> TVar3 (Cons y t_y gg) y t p_y_t a k_a 
        (Cons _y _ty g'') -> TVar1 (concatE (ConsT a k_a g) g'') y t_y k_y p_gag_ty  
          where
            p_gag_ty = lem_weaken_tv_wf g g'' {-p_gg_wf-} t_y k_y p_gg_ty a k_a
-- (g; g' == _g, z:t_z) |- y : t_y

{-@ lem_weaken_tv_typ_tvar2 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTVar2 p_e_t }
        -> { a:Vname | (not (in_env a g)) && (not (in_env a g')) } -> k_a:Kind
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (ConsT a k_a g) g') e t }
         / [ typSize p_e_t, 0 ] @-}
lem_weaken_tv_typ_tvar2 :: Env -> Env {-> WFEnv-} -> Expr -> Type -> HasType -> Vname -> Kind -> HasType
lem_weaken_tv_typ_tvar2 g g' {-p_env_wf-} e t p_y_ty@(TVar2 gg y t_y p_gg_y_ty z t_z) a k_a
    = case g' of
        (Empty)           -> TVar3 (concatE g g') y t_y p_y_ty a k_a
        (Cons _z _tz g'') -> TVar2 (concatE (ConsT a k_a g) g'') 
                                   (y `withProof` lem_in_env_concat g g'' y)
                                   t_y p_gag_y_ty z t_z      
          where
            p_gag_y_ty = lem_weaken_tv_typ g g'' {-p_gg_wf-} e t p_gg_y_ty a k_a

{-@ lem_weaken_tv_typ_tvar3 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTVar3 p_e_t }
        -> { a:Vname | (not (in_env a g)) && (not (in_env a g')) } -> k_a:Kind
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (ConsT a k_a g) g') e t }
         / [ typSize p_e_t, 0 ] @-}
lem_weaken_tv_typ_tvar3 :: Env -> Env {-> WFEnv-} -> Expr -> Type -> HasType -> Vname -> Kind -> HasType
lem_weaken_tv_typ_tvar3 g g' {-p_env_wf-} e t p_z_tz@(TVar3 gg z t_z p_z_t a' k_a') a k_a
    = case g' of
        (Empty)           -> TVar3 (concatE g g') z t_z p_z_tz a k_a
        (ConsT _a' _ g'') -> TVar3 (concatE (ConsT a k_a g) g'')
                                 (z `withProof` lem_in_env_concat g g'' z)
                                 t (lem_weaken_tv_typ g g'' {-p_env'_wf-} (FV z) t p_z_t a k_a)
                                 a' k_a'        

{-@ lem_weaken_tv_typ_tabs :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTAbs p_e_t }
        -> { a:Vname | (not (in_env a g)) && (not (in_env a g')) } -> k_a:Kind
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (ConsT a k_a g) g') e t }
         / [ typSize p_e_t, 0 ] @-}
lem_weaken_tv_typ_tabs :: Env -> Env {-> WFEnv-} -> Expr -> Type -> HasType -> Vname -> Kind -> HasType
lem_weaken_tv_typ_tabs g g' {-p_env_wf-} e t p_e_t@(TAbs env t_y k_y p_gg'_ty e' t' nms mk_p_y_e'_t') a k_a
    = TAbs (concatE (ConsT a k_a g) g') t_y k_y p_gag'_ty e' t'  nms' mk_p_ya_e'_t'
        where
            p_gag'_ty    = lem_weaken_tv_wf g g' t_y k_y p_gg'_ty a k_a
            {-@ mk_p_ya_e'_t' :: { y:Vname | NotElem y nms' }
                  -> { pf:HasType | propOf pf == HasType (Cons y t_y (concatE (ConsT a k_a g) g'))
                                                   (unbind y e') (unbindT y t') } @-}
            mk_p_ya_e'_t' y = lem_weaken_tv_typ g (Cons y t_y g') {-p_y''env_wf-} (unbind y e')
                                     (unbindT y t') (mk_p_y_e'_t' y) a k_a
            nms'            = a:(unionEnv nms (concatE g g'))

{-@ lem_weaken_tv_typ_tapp :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTApp p_e_t }
        -> { a:Vname | (not (in_env a g)) && (not (in_env a g')) } -> k_a:Kind
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (ConsT a k_a g) g') e t }
         / [ typSize p_e_t, 0 ] @-}
lem_weaken_tv_typ_tapp :: Env -> Env {-> WFEnv-} -> Expr -> Type -> HasType -> Vname -> Kind -> HasType
lem_weaken_tv_typ_tapp g g' {-p_env_wf-} e t (TApp env e1 s s' p_env_e1_ss' e2 p_env_e2_s) a k_a
    = TApp (concatE (ConsT a k_a g) g') e1 s s' p_env'_e1_ss' e2 p_env'_e2_s
        where
          p_env'_e1_ss' = lem_weaken_tv_typ g g' {-p_env_wf-} e1 (TFunc s s') p_env_e1_ss' a k_a
          p_env'_e2_s   = lem_weaken_tv_typ g g' {-p_env_wf-} e2 s            p_env_e2_s   a k_a

{-@ lem_weaken_tv_typ_tabst :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTAbsT p_e_t }
        -> { a:Vname | (not (in_env a g)) && (not (in_env a g')) } -> k_a:Kind
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (ConsT a k_a g) g') e t }
         / [ typSize p_e_t, 0 ] @-}
lem_weaken_tv_typ_tabst :: Env -> Env {-> WFEnv-} -> Expr -> Type -> HasType -> Vname -> Kind -> HasType
lem_weaken_tv_typ_tabst g g' {-p_env_wf-} e t 
                     p_e_t@(TAbsT env k1 e' t' nms mk_p_a'g_e'_t') a k_a
    = TAbsT (concatE (ConsT a k_a g) g') k1 e' t'  nms' mk_p_a'a_e'_t'
        where
          {-@ mk_p_a'a_e'_t' :: { a':Vname | NotElem a' nms' }
                -> { pf:HasType | propOf pf == HasType (ConsT a' k1 (concatE (ConsT a k_a g) g'))
                                                 (unbind_tv a' e') (unbind_tvT a' t') } @-}
          mk_p_a'a_e'_t' a' = lem_weaken_tv_typ g (ConsT a' k1 g') --p_a''env_wf
                                (unbind_tv a' e') (unbind_tvT a' t') (mk_p_a'g_e'_t' a') a k_a
          nms'              = a:(unionEnv nms (concatE g g'))

{-@ lem_weaken_tv_typ_tappt :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTAppT p_e_t }
        -> { a:Vname | (not (in_env a g)) && (not (in_env a g')) } -> k_a:Kind
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (ConsT a k_a g) g') e t }
         / [ typSize p_e_t, 0 ] @-}
lem_weaken_tv_typ_tappt :: Env -> Env {-> WFEnv-} -> Expr -> Type -> HasType -> Vname -> Kind -> HasType 
lem_weaken_tv_typ_tappt g g' {-p_env_wf-} e t p_e_t@(TAppT env e' k1 s p_e'_a1s t' p_env_t') a k_a
    = TAppT (concatE (ConsT a k_a g) g') e' k1 s p_env'_e'_a1s t' p_env'_t'
        where
          p_env'_e'_a1s = lem_weaken_tv_typ g g' {-p_env_wf-} e' (TPoly k1 s) p_e'_a1s a k_a
          p_env'_t'     = lem_weaken_tv_wf  g g' {-p_env_wf-} t' k1 p_env_t' a k_a

{-@ lem_weaken_tv_typ_tlet :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTLet p_e_t }
        -> { a:Vname | (not (in_env a g)) && (not (in_env a g')) } -> k_a:Kind
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (ConsT a k_a g) g') e t }
         / [ typSize p_e_t, 0 ] @-}
lem_weaken_tv_typ_tlet :: Env -> Env {-> WFEnv-} -> Expr -> Type -> HasType -> Vname -> Kind -> HasType
lem_weaken_tv_typ_tlet g g' {-p_env_wf-} e t 
               p_e_t@(TLet env e_y t_y p_env_ey_ty e' t' k' p_env_t' nms mk_p_yenv_e'_t') a k_a
    = TLet (concatE (ConsT a k_a g) g') e_y t_y p_env'_ey_ty 
           e' t' k' p_env'_t' nms' mk_p_yenv'_e'_t'
        where
          p_env'_ey_ty    = lem_weaken_tv_typ g g' {-p_env_wf-} e_y t_y p_env_ey_ty a k_a
          p_env'_t'       = lem_weaken_tv_wf  g g' {-p_env_wf-} t' k' p_env_t' a k_a
          {-@ mk_p_yenv'_e'_t' :: { y:Vname | NotElem y nms' }
                -> { pf:HasType | propOf pf == HasType (Cons y t_y (concatE (ConsT a k_a g) g'))
                                                 (unbind y e') (unbindT y t') }@-}
          mk_p_yenv'_e'_t' y = lem_weaken_tv_typ g (Cons y t_y g') {-p_y''env_wf-} (unbind y e')
                                              (unbindT y t') (mk_p_yenv_e'_t' y) a k_a
          nms'               = a:(unionEnv nms (concatE g g'))

{-@ lem_weaken_tv_typ_tann :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t && isTAnn p_e_t }
        -> { a:Vname | (not (in_env a g)) && (not (in_env a g')) } -> k_a:Kind
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (ConsT a k_a g) g') e t }
         / [ typSize p_e_t, 0 ] @-}
lem_weaken_tv_typ_tann :: Env -> Env {-> WFEnv-} -> Expr -> Type -> HasType -> Vname -> Kind -> HasType 
lem_weaken_tv_typ_tann g g' {-p_env_wf-} e t (TAnn env e' _t p_env_e'_t) a k_a
    = TAnn (concatE (ConsT a k_a g) g') e' t p_env'_e'_t
        where
          p_env'_e'_t = lem_weaken_tv_typ g g' {-p_env_wf-} e' t p_env_e'_t a k_a

{-@ lem_weaken_tv_typ :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t }
        -> { a:Vname | (not (in_env a g)) && (not (in_env a g')) } -> k_a:Kind
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (ConsT a k_a g) g') e t }
         / [ typSize p_e_t, 1 ] @-}
lem_weaken_tv_typ :: Env -> Env {-> WFEnv-} -> Expr -> Type -> HasType -> Vname -> Kind -> HasType 
lem_weaken_tv_typ g g' {-p_env_wf-} e t (TBC _g b) a k_a = TBC  (concatE (ConsT a k_a g) g') b
lem_weaken_tv_typ g g' {-p_env_wf-} e t (TIC _g n) a k_a = TIC  (concatE (ConsT a k_a g) g') n
lem_weaken_tv_typ g g' {-p_env_wf-} e t p_e_t@(TVar1 {}) a k_a
  = lem_weaken_tv_typ_tvar1 g g' {-p_env_wf-} e t p_e_t  a k_a
lem_weaken_tv_typ g g' {-p_env_wf-} e t p_e_t@(TVar2 {}) a k_a
  = lem_weaken_tv_typ_tvar2 g g' {-p_env_wf-} e t p_e_t  a k_a
lem_weaken_tv_typ g g' {-p_env_wf-} e t p_e_t@(TVar3 {}) a k_a
  = lem_weaken_tv_typ_tvar3 g g' {-p_env_wf-} e t p_e_t  a k_a
lem_weaken_tv_typ g g' {-p_env_wf-} e t (TPrm _ c) a k_a  = TPrm (concatE (ConsT a k_a g) g') c
lem_weaken_tv_typ g g' {-p_env_wf-} e t p_e_t@(TAbs {}) a k_a
  = lem_weaken_tv_typ_tabs g g' {-p_env_wf-} e t p_e_t  a k_a
lem_weaken_tv_typ g g' {-p_env_wf-} e t p_e_t@(TApp {}) a k_a
  = lem_weaken_tv_typ_tapp g g' {-p_env_wf-} e t p_e_t  a k_a
lem_weaken_tv_typ g g' {-p_env_wf-} e t p_e_t@(TAbsT {}) a k_a
  = lem_weaken_tv_typ_tabst g g' {-p_env_wf-} e t p_e_t  a k_a
lem_weaken_tv_typ g g' {-p_env_wf-} e t p_e_t@(TAppT {}) a k_a
  = lem_weaken_tv_typ_tappt g g' {-p_env_wf-} e t p_e_t  a k_a
lem_weaken_tv_typ g g' {-p_env_wf-} e t p_e_t@(TLet {}) a k_a
  = lem_weaken_tv_typ_tlet g g' {-p_env_wf-} e t p_e_t  a k_a
lem_weaken_tv_typ g g' {-p_env_wf-} e t p_e_t@(TAnn {}) a k_a
  = lem_weaken_tv_typ_tann g g' {-p_env_wf-} e t p_e_t  a k_a
lem_weaken_tv_typ g g' {-p_env_wf-} e t (TSub env _e s p_e_s _t k p_env_t p_s_t) a k_a
  = TSub (concatE (ConsT a k_a g) g') e s p_env'_e_s t k p_env'_t p_env'_s_t
      where
        p_env'_e_s = lem_weaken_tv_typ     g g' e s p_e_s a k_a
        p_env'_t   = lem_weaken_tv_wf      g g' t k p_env_t a k_a
        p_env'_s_t = lem_weaken_tv_subtype g g' s t  p_s_t a k_a

{-@ lem_weaken_many_typ :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> e:Expr -> t:Type -> ProofOf(HasType g e t) 
      -> ProofOf(HasType (concatE g g') e t) @-}
lem_weaken_many_typ :: Env -> Env {-> WFEnv-} -> Expr -> Type -> HasType -> HasType
lem_weaken_many_typ g Empty           {-p_g_wf-}    e t p_g_e_t = p_g_e_t
lem_weaken_many_typ g (Cons x t_x g') {-p_xenv_wf-} e t p_g_e_t 
  = lem_weaken_typ (concatE g g') Empty {-p_env_wf-} e t p_gg'_e_t x t_x
      where
        p_gg'_e_t = lem_weaken_many_typ g g' {-p_env_wf-} e t p_g_e_t 
lem_weaken_many_typ g (ConsT a k_a g') {-p_aenv_wf-} e t p_g_e_t 
  = lem_weaken_tv_typ (concatE g g') Empty {-p_env_wf-} e t p_gg'_e_t a k_a
      where
        p_gg'_e_t = lem_weaken_many_typ g g' {-p_env_wf-} e t p_g_e_t


{-@ lem_weaken_tv_subtype_sbase :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> t:Type  -> t':Type 
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' && isSBase p_t_t' }
      -> { a:Vname | not (in_env a g) && not (in_env a g') } -> k_a:Kind
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (ConsT a k_a g) g') t t' } 
       / [ subtypSize p_t_t', 0 ] @-}
lem_weaken_tv_subtype_sbase :: Env -> Env {-> WFEnv-} -> Type {-> Kind -> WFType -}
      -> Type {-> Kind -> WFType-} -> Subtype -> Vname -> Kind -> Subtype
lem_weaken_tv_subtype_sbase g g'  t  t' (SBase env b p1 p2 nms mk_pf_yenv_p1_p2) a k_a
    = SBase env' b p1 p2 nms' mk_pf_yenv'_p1_p2 
        where
          env'             = concatE (ConsT a k_a g) g'
          {-@ mk_pf_yenv'_p1_p2 :: { y:Vname | NotElem y nms' }
                -> ProofOf(Implies (Cons y (TRefn b PEmpty) (concatE (ConsT a k_a g) g'))
                                   (unbindP y p1) (unbindP y p2)) @-}
          mk_pf_yenv'_p1_p2 y = IWeakTV g (Cons y (TRefn b PEmpty) g')
                                      (unbindP y p1) (unbindP y p2) (mk_pf_yenv_p1_p2 y) a k_a
          nms'                = a:(unionEnv nms (concatE g g'))

{-@ lem_weaken_tv_subtype_sfunc :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> t:Type  -> t':Type 
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' && isSFunc p_t_t' }
      -> { a:Vname | not (in_env a g) && not (in_env a g') } -> k_a:Kind
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (ConsT a k_a g) g') t t' }
       / [ subtypSize p_t_t', 0 ] @-}
lem_weaken_tv_subtype_sfunc :: Env -> Env {-> WFEnv-} -> Type {-> Kind -> WFType -}
      -> Type {-> Kind -> WFType-} -> Subtype -> Vname -> Kind -> Subtype
lem_weaken_tv_subtype_sfunc g g' {-p_env_wf-} ft1 {-k1 p_env_ft1-} ft2 {-k2 p_env_ft2 -}
                       (SFunc env s1 s2 p_env_s2_s1 t1 t2 nms mk_p_wenv_t1_t2) a k_a
    = SFunc env' s1 s2 p_env'_s2_s1 t1 t2 nms' mk_p_wenv'_t1_t2
        where
          env'           = concatE (ConsT a k_a g) g'
          p_env'_s2_s1   = lem_weaken_tv_subtype g g' s2 s1  p_env_s2_s1 a k_a
          {-@ mk_p_wenv'_t1_t2 :: { w:Vname | NotElem w nms' }
                -> { pf:Subtype | propOf pf == Subtype (Cons w s2 (concatE (ConsT a k_a g) g'))
                                                       (unbindT w t1) (unbindT w t2) } @-}
          mk_p_wenv'_t1_t2 w = lem_weaken_tv_subtype g (Cons w s2 g') --p_w'env_wf
                                   (unbindT w t1) {-k_t1 p_wenv_t1-} (unbindT w t2) {-k_t2
                                   p_wenv_t2-} (mk_p_wenv_t1_t2 w) a k_a
          nms'               = a:(unionEnv nms (concatE g g'))

{-@ lem_weaken_tv_subtype_switn :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> t:Type  -> t':Type 
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' && isSWitn p_t_t' }
      -> { a:Vname | not (in_env a g) && not (in_env a g') } -> k_a:Kind
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (ConsT a k_a g) g') t t' }
       / [ subtypSize p_t_t', 0 ] @-}
lem_weaken_tv_subtype_switn :: Env -> Env {-> WFEnv-} -> Type {-> Kind -> WFType -}
      -> Type {-> Kind -> WFType-} -> Subtype -> Vname -> Kind -> Subtype
lem_weaken_tv_subtype_switn g g' {-p_env_wf-} t {-k p_env_t-} t2 {-k2 p_env_t2-}
                   (SWitn env v_z t_z p_env_vz_tz _t t' p_env_t_t'vz) a k_a
    = SWitn env' v_z t_z p_env'_vz_tz t t' p_env'_t_t'vz
        where
          env'          = concatE (ConsT a k_a g) g'
          p_env'_vz_tz  = lem_weaken_tv_typ g g' {-p_env_wf-} v_z t_z p_env_vz_tz a k_a
          p_env'_t_t'vz = lem_weaken_tv_subtype g g' {-p_env_wf-} t {-k p_env_t-}
                                             (tsubBV v_z t') {-k' p_env_t'vz-} p_env_t_t'vz a k_a

{-@ lem_weaken_tv_subtype_sbind :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> t:Type  -> t':Type 
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' && isSBind p_t_t' }
      -> { a:Vname | not (in_env a g) && not (in_env a g') } -> k_a:Kind
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (ConsT a k_a g) g') t t' }
       / [ subtypSize p_t_t', 0 ] @-}
lem_weaken_tv_subtype_sbind :: Env -> Env {-> WFEnv-} -> Type {-> Kind -> WFType -}
      -> Type {-> Kind -> WFType-} -> Subtype -> Vname -> Kind -> Subtype
lem_weaken_tv_subtype_sbind g g'  t1  t' (SBind env t_z t _t' nms mk_p_zenv_t_t') a k_a
    = SBind env' t_z t t' nms' mk_p_zenv'_t_t'
        where
          env'           = concatE (ConsT a k_a g) g'
          {-@ mk_p_zenv'_t_t' :: { z:Vname | NotElem z nms'}
                -> { pf:Subtype | propOf pf == Subtype (Cons z t_z (concatE (ConsT a k_a g) g'))
                                                       (unbindT z t) t' } @-}
          mk_p_zenv'_t_t' z = lem_weaken_tv_subtype g (Cons z t_z g') {-p_z''env_wf-}
                                   (unbindT z t) {-k p_z''env_t-} t' {-k' p_z''env_t' -}
                                   (mk_p_zenv_t_t' z) a k_a
          nms'              = a:(unionEnv nms (concatE g g'))

{-@ lem_weaken_tv_subtype_spoly :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> t:Type  -> t':Type 
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' && isSPoly p_t_t' }
      -> { a:Vname | not (in_env a g) && not (in_env a g') } -> k_a:Kind
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (ConsT a k_a g) g') t t' }
       / [ subtypSize p_t_t', 0 ] @-}
lem_weaken_tv_subtype_spoly :: Env -> Env {-> WFEnv-} -> Type {-> Kind -> WFType -}
      -> Type {-> Kind -> WFType-} -> Subtype -> Vname -> Kind -> Subtype
lem_weaken_tv_subtype_spoly g g' {-p_env_wf-} t1 {-Star p_env_t1-} t2 {-Star p_env_t2-}
                         (SPoly env k' t1' t2' nms mk_p_a1g_t1'_t2') a k_a
    = SPoly (concatE (ConsT a k_a g) g') k' t1' t2' nms' mk_p_a1a_t1'_t2'
        where
          {-@ mk_p_a1a_t1'_t2' :: { a1:Vname | NotElem a1 nms' }
                -> { pf:Subtype | propOf pf == Subtype (ConsT a1 k' (concatE (ConsT a k_a g) g'))
                                                       (unbind_tvT a1 t1') (unbind_tvT a1 t2') } @-}
          mk_p_a1a_t1'_t2' a1 = lem_weaken_tv_subtype g (ConsT a1 k' g') {-p_a1''env_wf-}
                                  (unbind_tvT a1 t1') (unbind_tvT a1 t2') 
                                  (mk_p_a1g_t1'_t2' a1) a k_a
          nms'              = a:(unionEnv nms (concatE g g'))

{-@ lem_weaken_tv_subtype :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> t:Type  -> t':Type 
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' }
      -> { a:Vname | not (in_env a g) && not (in_env a g') } -> k_a:Kind
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (ConsT a k_a g) g') t t' }
       / [ subtypSize p_t_t', 1 ] @-}
lem_weaken_tv_subtype :: Env -> Env {-> WFEnv-} -> Type {-> Kind -> WFType -}
      -> Type {-> Kind -> WFType-} -> Subtype -> Vname -> Kind -> Subtype
lem_weaken_tv_subtype g g' t  t' p_t_t'@(SBase {}) a_ k_a
    = lem_weaken_tv_subtype_sbase g g' {-p_env_wf-} t {-k p_env_t-} t' {-k' p_env_t'-} p_t_t' a_ k_a
lem_weaken_tv_subtype g g' ft1  ft2  p_t_t'@(SFunc {}) a_ k_a
    = lem_weaken_tv_subtype_sfunc g g' ft1 ft2  p_t_t' a_ k_a
lem_weaken_tv_subtype g g' t  t2 p_t_t'@(SWitn {}) a_ k_a
    = lem_weaken_tv_subtype_switn g g' {-p_env_wf-} t {-k p_env_t-} t2 {-k2 p_env_t2-} p_t_t' a_ k_a
lem_weaken_tv_subtype g g' t1 t' p_t_t'@(SBind {}) a_ k_a
    = lem_weaken_tv_subtype_sbind g g' {-p_env_wf-} t1 {-k1 p_env_t1-} t' {-k' p_env_t'-} p_t_t' a_ k_a
lem_weaken_tv_subtype g g' t1 t2 {-k2 p_env_tw-} p_t_t'@(SPoly {}) a k_a
    = lem_weaken_tv_subtype_spoly g g' {-p_env_wf-} t1 {-k1 p_env_t1-} t2 {-k2 p_env_tw-} p_t_t' a k_a

{-@ lem_weaken_many_subtype :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> s:Type -> t:Type -> ProofOf(Subtype g s t) 
      -> ProofOf(Subtype (concatE g g') s t) @-}
lem_weaken_many_subtype :: Env -> Env -> Type -> Type -> Subtype -> Subtype
lem_weaken_many_subtype g Empty             s  t  p_g_s_t = p_g_s_t
lem_weaken_many_subtype g (Cons x t_x g')   s  t  p_g_s_t 
  = lem_weaken_subtype (concatE g g') Empty s  t  p_g'g_s_t x t_x
      where
        p_g'g_s_t = lem_weaken_many_subtype g g' {-p_env_wf-} s {-k_s p_g_s-} t {-k_t p_g_t-} p_g_s_t 
lem_weaken_many_subtype g (ConsT a k_a g') {-p_aenv_wf-} s {-k_s p_g_s-} t {-k_t p_g_t-} p_g_s_t 
  = lem_weaken_tv_subtype (concatE g g') Empty {-p_env_wf-} s {-k_s p_g'g_s-} t {-k_t p_g'g_t-} p_g'g_s_t a k_a
      where
        p_g'g_s_t = lem_weaken_many_subtype g g' {-p_env_wf-} s {-k_s p_g_s-} t {-k_t p_g_t-} p_g_s_t
