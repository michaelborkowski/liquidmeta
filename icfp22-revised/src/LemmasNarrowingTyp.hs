{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasNarrowingTyp where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof,(?))
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import BasicPropsSubstitution
import BasicPropsEnvironments
import WellFormedness
import BasicPropsWellFormedness
import SystemFLemmasSubstitution
import Typing
import LemmasWeakenWF
import LemmasWellFormedness
import LemmasTyping
import LemmasSubtyping
import LemmasWeakenTyp
import SubstitutionLemmaWF
import LemmasExactness

{-@ lem_narrow_typ_tvar1 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
        -> k_sx:Kind -> ProofOf(WFType g s_x k_sx) -> t_x:Type 
        -> { p_sx_tx:Subtype | propOf p_sx_tx == Subtype g s_x t_x } 
        -> ProofOf(WFEnv g ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t  == HasType (concatE (Cons x t_x g) g') e t && isTVar1 p_e_t }
        -> {p'_e_t:HasType | propOf p'_e_t == HasType (concatE (Cons x s_x g) g') e t } @-}
lem_narrow_typ_tvar1 :: Env -> Env -> Vname -> Type -> Kind -> WFType -> Type -> Subtype -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_narrow_typ_tvar1 g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf e t p_e_t@(TVar1 _env z t' k' p_env_t')
   = case g' of                                              -- t == self t'  (FV z) k'
      (Empty)           -> p_z_tx                            -- t == self t_x (FV z) k'
        where                                                -- z:t_x, G |- (FV z) : self t_x (FV z) k'
          p_g_sx_k'   = case (k_sx, k') of
                          (Star, Base) -> lem_sub_pullback_wftype g p_g_wf s_x t'
                                                                  p_sx_tx p_g_sx p_env_t'
                          (Base, Star) -> WFKind g s_x  p_g_sx
                          (_   , _   ) -> p_g_sx
          p_z_self_sx = TVar1 g z s_x k' p_g_sx_k'
          p_env'_wf   = WFEBind g p_g_wf x s_x k_sx p_g_sx
          p_env'_sx   = lem_weaken_wf g Empty  s_x k_sx p_g_sx   x s_x
          p_env'_t'   = lem_weaken_wf g Empty  t_x k'   p_env_t' x s_x
          p_xg_sx_tx  = lem_weaken_subtype g Empty s_x  t_x  p_sx_tx x s_x
          p_xg_sx_tx' = lem_exact_subtype (Cons x s_x g) p_env'_wf s_x k_sx p_env'_sx t_x 
                                          p_xg_sx_tx k' p_env'_t' (FV z) 
                                          (FTVar1 (erase_env g) z (erase t_x)
                                              ? lem_erase_subtype g s_x t_x p_sx_tx)
          p_xsxg_t    = lem_selfify_wf (Cons x s_x g) t' k' p_env'_t' (FV z) 
                             (FTVar1 (erase_env g) z (erase t_x) ? lem_erase_subtype g s_x t_x p_sx_tx)
          p_z_tx      = TSub (Cons x s_x g) (FV z) (self s_x (FV z) k') p_z_self_sx 
                             (self t_x (FV z) k') k' p_xsxg_t p_xg_sx_tx'
      (Cons _z _ g'')  -> TVar1 (concatE (Cons x s_x g) g'')  
                                (z ? lem_in_env_concat g g'' z) t' k' p_env'_t'
        where
          p_env'_t'   = lem_narrow_wf g g'' x s_x t_x p_sx_tx t' k' p_env_t' 

{-@ lem_narrow_typ :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
        -> k_sx:Kind -> ProofOf(WFType g s_x k_sx) -> t_x:Type 
        -> { p_sx_tx:Subtype | propOf p_sx_tx == Subtype g s_x t_x } 
        -> ProofOf(WFEnv  g ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t }
        -> {p'_e_t:HasType | propOf p'_e_t == HasType (concatE (Cons x s_x g) g') e t }
         / [typSize p_e_t, 1] @-}
lem_narrow_typ :: Env -> Env -> Vname -> Type -> Kind -> WFType -> Type -> Subtype -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf e t (TBC _env b) 
  = TBC (concatE (Cons x s_x g) g') b 
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf e t (TIC _env n) 
  = TIC (concatE (Cons x s_x g) g') n 
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf e t p_e_t@(TVar1 {}) 
  = lem_narrow_typ_tvar1 g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf e t p_e_t
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf e _t (TVar2 env' z_ t p_z_t w_ t_w) 
  = case g' of             -- g''=Emp so x=w and p_z_t :: HasType(g (FV z) t)
        (Empty)           -> TVar2 g z_ t p_z_t w_ s_x
        (Cons _w _tw g'') -> TVar2 (concatE (Cons x s_x g) g'') z t p'_z_t w t_w 
          where
            z      = z_ ? lem_in_env_concat (Cons x s_x g) g'' z_
                        ? lem_in_env_concat (Cons x t_x g) g'' z_
            w      = w_ ? lem_in_env_concat g g'' w_
            p'_z_t = lem_narrow_typ g g'' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf (FV z) t p_z_t
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf e t (TVar3 env_ z_ _t p_z_t a_ k_a) 
  = case g' of 
        (Empty)            -> impossible "x <> a"
        (ConsT _a _ka g'') -> TVar3 (concatE (Cons x s_x g) g'') z t p'_z_t a k_a
          where
            z      = z_ ? lem_in_env_concat (Cons x s_x g) g'' z_
                        ? lem_in_env_concat (Cons x t_x g) g'' z_
            a      = a_ ? lem_in_env_concat g g'' a_
            p'_z_t = lem_narrow_typ g g'' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf (FV z) t p_z_t
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf e t (TPrm _en c) 
  = TPrm (concatE (Cons x s_x g) g') c 
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf e t 
               (TAbs env_ t_z k_z p_env_tz e' t' nms mk_p_yenv_e'_t') 
  = TAbs (concatE (Cons x s_x g) g') t_z k_z p_env'_tz e' t' nms' mk_p_yenv'_e'_t'
      where
        {-@ mk_p_yenv'_e'_t' :: { y:Vname | NotElem y nms' }
              -> { pf:HasType | propOf pf == HasType (Cons y t_z (concatE (Cons x s_x g) g'))
                                                     (unbind y e') (unbindT y t') } @-}
        mk_p_yenv'_e'_t' y = lem_narrow_typ g (Cons y t_z g') x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf
                                         (unbind y e') (unbindT y t') (mk_p_yenv_e'_t' y)
        p_env'_tz          = lem_narrow_wf g g' x s_x t_x p_sx_tx t_z k_z p_env_tz
        nms'               = unionEnv nms (concatE (Cons x s_x g) g')
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf e t 
               (TApp env_ e' t_z t' p_env_e'_tzt' e_z p_env_ez_tz) 
  = TApp (concatE (Cons x s_x g) g') e' t_z t' p_env'_e'_tzt' e_z p_env'_ez_tz
      where
        p_env'_e'_tzt' = lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf
                                        e' (TFunc t_z t') p_env_e'_tzt'
        p_env'_ez_tz   = lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf 
                                        e_z t_z p_env_ez_tz
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf e t 
               (TAbsT env k e' t' nms mk_p_aenv_e'_t')
  = TAbsT (concatE (Cons x s_x g) g') k e' t' nms' mk_p_aenv'_e'_t'
      where
        {-@ mk_p_aenv'_e'_t' :: { a:Vname | NotElem a nms' }
              -> { pf:HasType | propOf pf == HasType (ConsT a k (concatE (Cons x s_x g) g'))
                                                     (unbind_tv a e') (unbind_tvT a t') } @-}
        mk_p_aenv'_e'_t' a = lem_narrow_typ g (ConsT a k g') x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf
                                        (unbind_tv a e') (unbind_tvT a t') (mk_p_aenv_e'_t' a)
        nms'               = unionEnv nms (concatE (Cons x s_x g) g')
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf e t 
               (TAppT env e' k s p_e'_as t' p_env_t') 
  = TAppT (concatE (Cons x s_x g) g') e' k s p_env'_e'_as t' p_env'_t'
      where
        p_env'_e'_as = lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf
                                      e' (TPoly k s) p_e'_as
        p_env'_t'    = lem_narrow_wf g g' x s_x t_x p_sx_tx t' k p_env_t'
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf e t 
               (TLet env_ e_z t_z p_env_ez_tz e' t_ k p_env_t nms mk_p_yenv_e'_t) 
  = TLet (concatE (Cons x s_x g) g') e_z t_z p_env'_ez_tz e' t k p_env'_t nms' mk_p_yenv'_e'_t
      where
        {-@ mk_p_yenv'_e'_t :: { y:Vname | NotElem y nms' }
              -> { pf:HasType | propOf pf == HasType (Cons y t_z (concatE (Cons x s_x g) g'))
                                                     (unbind y e') (unbindT y t) } @-}
        mk_p_yenv'_e'_t y = lem_narrow_typ g (Cons y t_z g') x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf
                                           (unbind y e') (unbindT y t) (mk_p_yenv_e'_t y)
        p_env'_ez_tz      = lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf 
                                           e_z t_z p_env_ez_tz
        p_env'_t          = lem_narrow_wf g g' x s_x t_x p_sx_tx t k p_env_t
        nms'              = unionEnv nms (concatE (Cons x s_x g) g')
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf e t (TAnn env_ e' t_ p_env_e'_t) 
  = TAnn (concatE (Cons x s_x g) g') e' t p_env'_e'_t
      where
        p_env'_e'_t = lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf e' t p_env_e'_t
lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf e t 
               (TSub env_ e_ s p_env_e_s t_ k p_env_t p_env_s_t) 
  = TSub (concatE (Cons x s_x g) g') e s p_env'_e_s t k p_env'_t p_env'_s_t
      where
        p_env'_e_s = lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf e s p_env_e_s
        p_env'_t   = lem_narrow_wf  g g' x s_x t_x p_sx_tx t k p_env_t
        p_env'_s_t = lem_narrow_sub g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf 
                                    s {-Star p_env_s-} t {-k p_env_t-} p_env_s_t 

{-@ lem_narrow_sub_sbase :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
        -> k_sx:Kind -> ProofOf(WFType g s_x k_sx) -> t_x:Type  
        -> { p_sx_tx:Subtype | propOf p_sx_tx == Subtype g s_x t_x } 
        -> ProofOf(WFEnv g) -> s:Type  -> t:Type 
        -> { p_s_t:Subtype  | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t && isSBase p_s_t }
        -> { p'_s_t:Subtype | propOf p'_s_t == (Subtype (concatE (Cons x s_x g) g') s t) }
         / [ subtypSize p_s_t, 0] @-}
lem_narrow_sub_sbase :: Env -> Env -> Vname -> Type -> Kind -> WFType -> Type -> Subtype -> WFEnv
                    -> Type {-> Kind -> WFType-} -> Type {-> Kind -> WFType-} -> Subtype -> Subtype
lem_narrow_sub_sbase g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf s {-k_s p_env_s-} t {-k_t p_env_t-}
                     (SBase env b p1 p2 nms mk_imp_p1_p2) -- p_env_s_t
  = SBase (concatE (Cons x s_x g) g') b p1 p2 nms' mk_imp'_p1_p2
      where
        {-@ mk_imp'_p1_p2 :: { y:Vname | NotElem y nms' }
              -> ProofOf(Implies (Cons y (TRefn b PEmpty) (concatE (Cons x s_x g) g'))
                                 (unbindP y p1) (unbindP y p2)) @-}
        mk_imp'_p1_p2 y = INarrow g (Cons y (TRefn b PEmpty) g') x s_x t_x p_sx_tx
                                    (unbindP y p1) (unbindP y p2) (mk_imp_p1_p2 y)
        nms'            = unionEnv nms (concatE (Cons x s_x g) g')

{-@ lem_narrow_sub_sfunc :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
        -> k_sx:Kind -> ProofOf(WFType g s_x k_sx) -> t_x:Type  
        -> { p_sx_tx:Subtype | propOf p_sx_tx == Subtype g s_x t_x } 
        -> ProofOf(WFEnv g) -> s:Type  -> t:Type 
        -> { p_s_t:Subtype  | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t && isSFunc p_s_t }
        -> { p'_s_t:Subtype | propOf p'_s_t == (Subtype (concatE (Cons x s_x g) g') s t) }
         / [ subtypSize p_s_t, 0] @-}
lem_narrow_sub_sfunc :: Env -> Env -> Vname -> Type -> Kind -> WFType -> Type -> Subtype -> WFEnv
                    -> Type {-> Kind -> WFType-} -> Type {-> Kind -> WFType-} -> Subtype -> Subtype
lem_narrow_sub_sfunc g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf ty1 {-ky1 p_env_ty1-} ty2 {-ky2 p_env_ty2-}
                     (SFunc env s1 s2 p_s2_s1 t1 t2 nms mk_p_yenv_t1_t2) 
  = SFunc (concatE (Cons x s_x g) g') s1 s2 p_env'_s2_s1 t1 t2 nms' mk_p_yenv'_t1_t2 
      where   
        {-@ mk_p_yenv'_t1_t2 :: { y:Vname | NotElem y nms' }
              -> { pf:Subtype | propOf pf == Subtype (Cons y s2 (concatE (Cons x s_x g) g'))
                                                     (unbindT y t1) (unbindT y t2) } @-}
        mk_p_yenv'_t1_t2 y = lem_narrow_sub g (Cons y s2 g') x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf
                                       (unbindT y t1) (unbindT y t2) (mk_p_yenv_t1_t2 y)
        p_env'_s2_s1  = lem_narrow_sub g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf s2 s1 p_s2_s1
        nms'               = unionEnv nms (concatE (Cons x s_x g) g')

{-@ lem_narrow_sub_switn :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
        -> k_sx:Kind -> ProofOf(WFType g s_x k_sx) -> t_x:Type  
        -> { p_sx_tx:Subtype | propOf p_sx_tx == Subtype g s_x t_x } 
        -> ProofOf(WFEnv g) -> s:Type  -> t:Type 
        -> { p_s_t:Subtype  | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t && isSWitn p_s_t }
        -> { p'_s_t:Subtype | propOf p'_s_t == (Subtype (concatE (Cons x s_x g) g') s t) }
         / [ subtypSize p_s_t, 0] @-}
lem_narrow_sub_switn :: Env -> Env -> Vname -> Type -> Kind -> WFType -> Type -> Subtype -> WFEnv
                    -> Type {-> Kind -> WFType-} -> Type {-> Kind -> WFType-} -> Subtype -> Subtype
lem_narrow_sub_switn g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf t {-k p_env_t-} t2 {-k2 p_env_t2-}
               (SWitn env v_z t_z p_env_vz_tz _t t' p_env_t_t'vz) 
  = SWitn (concatE (Cons x s_x g) g') v_z t_z p_env'_vz_tz t t' p_env'_t_t'vz  
      where
        p_env'_vz_tz  = lem_narrow_typ g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf 
                                       v_z t_z p_env_vz_tz
        p_env'_t_t'vz = lem_narrow_sub g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf t {-k p_env_t-}
                                       (tsubBV v_z t') {-k' p_env_t'vz-} p_env_t_t'vz  

{-@ lem_narrow_sub_sbind :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
        -> k_sx:Kind -> ProofOf(WFType g s_x k_sx) -> t_x:Type  
        -> { p_sx_tx:Subtype | propOf p_sx_tx == Subtype g s_x t_x } 
        -> ProofOf(WFEnv g) -> s:Type  -> t:Type 
        -> { p_s_t:Subtype  | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t && isSBind p_s_t }
        -> { p'_s_t:Subtype | propOf p'_s_t == (Subtype (concatE (Cons x s_x g) g') s t) }
         / [ subtypSize p_s_t, 0] @-}
lem_narrow_sub_sbind :: Env -> Env -> Vname -> Type -> Kind -> WFType -> Type -> Subtype -> WFEnv
                    -> Type {-> Kind -> WFType-} -> Type {-> Kind -> WFType-} -> Subtype -> Subtype
lem_narrow_sub_sbind g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf t1 {-k1 p_env_t1-} t' {-k' p_env_t'-}
                     (SBind env t_z t _t' nms mk_p_wenv_t_t') 
  = SBind (concatE (Cons x s_x g) g') t_z t t' nms' mk_p_wenv'_t_t'
      where
        {-@ mk_p_wenv'_t_t' :: { y:Vname | NotElem y nms' }
              -> { pf:Subtype | propOf pf == Subtype (Cons y t_z (concatE (Cons x s_x g) g'))
                                                     (unbindT y t) t' } @-}
        mk_p_wenv'_t_t' w = lem_narrow_sub g (Cons w t_z g') x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf
                                (unbindT w t) {-k p_wenv_t-} t' {-k' p_wenv_t'-} (mk_p_wenv_t_t' w)
        nms'               = unionEnv nms (concatE (Cons x s_x g) g')

{-@ lem_narrow_sub_spoly :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
        -> k_sx:Kind -> ProofOf(WFType g s_x k_sx) -> t_x:Type  
        -> { p_sx_tx:Subtype | propOf p_sx_tx == Subtype g s_x t_x } 
        -> ProofOf(WFEnv g) -> s:Type  -> t:Type 
        -> { p_s_t:Subtype  | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t && isSPoly p_s_t }
        -> { p'_s_t:Subtype | propOf p'_s_t == (Subtype (concatE (Cons x s_x g) g') s t) }
         / [ subtypSize p_s_t, 0] @-}
lem_narrow_sub_spoly :: Env -> Env -> Vname -> Type -> Kind -> WFType -> Type -> Subtype -> WFEnv
                    -> Type {-> Kind -> WFType-} -> Type {-> Kind -> WFType-} -> Subtype -> Subtype
lem_narrow_sub_spoly g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf t1 {-k1 p_env_t1-} t2 {-k2 p_env_t2-}
                     (SPoly env k t1' t2' nms mk_p_env_t1'_t2') 
  = SPoly (concatE (Cons x s_x g) g') k t1' t2' nms' mk_p_env'_t1'_t2'
      where
        {-@ mk_p_env'_t1'_t2' :: { a:Vname | NotElem a nms' }
              -> { pf:Subtype | propOf pf == Subtype (ConsT a k (concatE (Cons x s_x g) g'))
                                                     (unbind_tvT a t1') (unbind_tvT a t2') } @-}
        mk_p_env'_t1'_t2' a = lem_narrow_sub g (ConsT a k g') x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf 
                                  (unbind_tvT a t1') (unbind_tvT a t2') (mk_p_env_t1'_t2' a)
        nms'               = unionEnv nms (concatE (Cons x s_x g) g')

{-@ lem_narrow_sub :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
        -> k_sx:Kind -> ProofOf(WFType g s_x k_sx) -> t_x:Type  
        -> { p_sx_tx:Subtype | propOf p_sx_tx == Subtype g s_x t_x } 
        -> ProofOf(WFEnv g) -> s:Type  -> t:Type 
        -> { p_s_t:Subtype  | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t }
        -> { p'_s_t:Subtype | propOf p'_s_t == (Subtype (concatE (Cons x s_x g) g') s t) }
         / [ subtypSize p_s_t, 1] @-}
lem_narrow_sub :: Env -> Env -> Vname -> Type -> Kind -> WFType -> Type -> Subtype -> WFEnv
                    -> Type -> Type -> Subtype -> Subtype
lem_narrow_sub g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf s t p_s_t@(SBase {}) -- p_env_s_t
  = lem_narrow_sub_sbase g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf s t p_s_t
lem_narrow_sub g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf ty1 ty2 p_ty1_ty2@(SFunc {}) 
  = lem_narrow_sub_sfunc g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf ty1 ty2 p_ty1_ty2
lem_narrow_sub g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf t t2 p_t_t2@(SWitn {}) 
  = lem_narrow_sub_switn g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf t t2 p_t_t2
lem_narrow_sub g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf t1 t' p_t1_t'@(SBind {}) 
  = lem_narrow_sub_sbind g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf t1 t' p_t1_t'
lem_narrow_sub g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf t1 t2 p_t1_t2@(SPoly {}) 
  = lem_narrow_sub_spoly g g' x s_x k_sx p_g_sx t_x p_sx_tx p_g_wf t1 t2 p_t1_t2
