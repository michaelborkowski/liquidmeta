{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SubstitutionLemmaTyp where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import LocalClosure
import Semantics
import SystemFWellFormedness
import SystemFTyping
import BasicPropsSubstitution            
import BasicPropsEnvironments
import WellFormedness                    
import BasicPropsWellFormedness
import Typing
import LemmasWeakenWF          
import LemmasWellFormedness
import SubstitutionLemmaWF
import LemmasTyping
import LemmasWeakenTyp
import LemmasWeakenTypTV
import LemmasExactness

{-@ lem_subst_typ_tvar1 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> { p_vx_tx:HasType | propOf p_vx_tx == HasType g v_x t_x }
        -> ProofOf(WFEnv g) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t  == HasType (concatE (Cons x t_x g) g') e t && isTVar1 p_e_t}
        -> {p'_e_t:HasType | propOf p'_e_t == HasType (concatE g (esubFV x v_x g')) 
                                                      (subFV x v_x e) (tsubFV x v_x t) &&
                             sizeOf p'_e_t <= (sizeOf p_e_t) + 2 * (sizeOf p_vx_tx) } 
         / [sizeOf p_e_t, 0] @-}
lem_subst_typ_tvar1 :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_typ_tvar1 g g' x v_x t_x p_vx_tx p_g_wf e t (TVar1 _env z t' k' p_env_t) 
  = case g' of          -- empty case: e = FV z = FV x and t = self t' x = self t_x x
      (Empty)           -> case k' of 
          Base -> lem_exact_type g v_x t_x p_vx_tx Base p_env_t p_g_wf 
                                   ? lem_free_bound_in_env g t_x Star p_g_tx x
                                   ? lem_tsubFV_notin x v_x t_x 
                                   ? lem_tsubFV_self x v_x t_x (FV z) Base
          Star -> p_vx_tx ? lem_free_bound_in_env g t_x Star p_g_tx x
                          ? lem_tsubFV_notin x v_x t_x 
        where
          p_g_tx = lem_typing_wf g v_x t_x p_vx_tx p_g_wf
      (Cons _z _ g'')  -> TVar1 (concatE g (esubFV x v_x g''))  -- z <> x, t = self t' (FV z)
                                (z ? lem_in_env_esub g'' x v_x z
                                   ? lem_in_env_concat g g'' z )
                                (tsubFV x v_x t') k' p_env'_t'vx
                                   ? lem_tsubFV_self2 x v_x t' z k'
        where
          p_vx_er_tx  = lem_typing_hasftype g v_x t_x p_vx_tx p_g_wf
          p_env'_t'vx = lem_subst_wf g g'' x v_x t_x p_vx_er_tx t' k' p_env_t

{-@ lem_subst_typ_tvar2 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> { p_vx_tx:HasType | propOf p_vx_tx == HasType g v_x t_x }
        -> ProofOf(WFEnv g ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t  == HasType (concatE (Cons x t_x g) g') e t && isTVar2 p_e_t}
        -> {p'_e_t:HasType | propOf p'_e_t == HasType (concatE g (esubFV x v_x g')) 
                                                      (subFV x v_x e) (tsubFV x v_x t) &&
                             sizeOf p'_e_t <= (sizeOf p_e_t) + 2 * (sizeOf p_vx_tx) } 
         / [sizeOf p_e_t, 0] @-}
lem_subst_typ_tvar2 :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_typ_tvar2 g g' x v_x t_x p_vx_tx p_g_wf e t (TVar2 n env_ z _t p_z_t w_ t_w) 
    = case g' of             -- g'' = Empty so x = w and p_z_t :: HasFType(g (FV z) t)
        (Empty)           -> case (x == z) of
            (True)  -> impossible "it is"
            (False) -> p_z_t ? lem_tsubFV_notin x v_x (t 
                                   ? lem_free_bound_in_env g t Star p_g_t x)
                where
                  p_g_t = lem_typing_wf g (FV z) t p_z_t p_g_wf
        (Cons _w _tw g'') -> case (x == z) of
            (True)  -> lem_weaken_typ (concatE g (esubFV x v_x g'')) Empty 
                                      v_x (tsubFV x v_x t) p_gg''_vx_tx w (tsubFV x v_x t_w)
                         where
                           w = w_ ? lem_in_env_esub g'' x v_x w_
                                  ? lem_in_env_concat g g'' w_
                           p_gg''_vx_tx = lem_subst_typ g g'' x v_x t_x p_vx_tx p_g_wf
                                                        e t p_z_t
            (False) -> TVar2 (typSize p_z_tvx) (concatE g (esubFV x v_x g'')) --z
                             (z ? lem_in_env_esub g'' x v_x z
                                ? lem_in_env_concat (Cons x t_x g) g'' z) 
                             (tsubFV x v_x t) p_z_tvx w (tsubFV x v_x t_w)
                         where
                           w = w_ ? lem_in_env_esub g'' x v_x w_
                                  ? lem_in_env_concat g g'' w_
                           p_z_tvx = lem_subst_typ g g'' x v_x t_x p_vx_tx
                                                   p_g_wf e t p_z_t

{-@ lem_subst_typ_tvar3 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> { p_vx_tx:HasType | propOf p_vx_tx == HasType g v_x t_x }
        -> ProofOf(WFEnv  g ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t  == HasType (concatE (Cons x t_x g) g') e t && isTVar3 p_e_t}
        -> {p'_e_t:HasType | propOf p'_e_t == HasType (concatE g (esubFV x v_x g')) 
                                                      (subFV x v_x e) (tsubFV x v_x t) &&
                             sizeOf p'_e_t <= (sizeOf p_e_t) + 2 * (sizeOf p_vx_tx) } 
         / [sizeOf p_e_t, 0] @-}
lem_subst_typ_tvar3 :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_typ_tvar3 g g' x v_x t_x p_vx_tx p_g_wf e t (TVar3 n env_ z _t p_z_t a_ k_a) 
    = case g' of             -- g'' = Empty so x = w and p_z_t :: HasFType(g (FV z) t)
        (Empty)            -> impossible "a != x" -- case (x == z) of
        (ConsT _ _ka g'') -> case (x == z) of
            (True)  -> lem_weaken_tv_typ (concatE g (esubFV x v_x g'')) Empty 
                                         v_x (tsubFV x v_x t) p_gg''_vx_tx a k_a
                         where
                           a = a_ ? lem_in_env_esub g'' x v_x a_
                                  ? lem_in_env_concat g g'' a_
                           p_gg''_vx_tx = lem_subst_typ g g'' x v_x t_x p_vx_tx p_g_wf
                                                        e t p_z_t
            (False) -> TVar3 (typSize p_z_tvx) (concatE g (esubFV x v_x g'')) --z
                             (z ? lem_in_env_esub g'' x v_x z
                                ? lem_in_env_concat (Cons x t_x g) g'' z) 
                             (tsubFV x v_x t) p_z_tvx a k_a
                         where
                           a = a_ ? lem_in_env_esub g'' x v_x a_
                                  ? lem_in_env_concat g g'' a_
                           p_z_tvx = lem_subst_typ g g'' x v_x t_x p_vx_tx
                                                   p_g_wf e t p_z_t

{-@ lem_subst_typ_tabs :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> { p_vx_tx:HasType | propOf p_vx_tx == HasType g v_x t_x }
        -> ProofOf(WFEnv  g ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t  == HasType (concatE (Cons x t_x g) g') e t && isTAbs p_e_t}
        -> {p'_e_t:HasType | propOf p'_e_t == HasType (concatE g (esubFV x v_x g')) 
                                                      (subFV x v_x e) (tsubFV x v_x t) &&
                             sizeOf p'_e_t <= (sizeOf p_e_t) + 2 * (sizeOf p_vx_tx) } 
         / [sizeOf p_e_t, 0] @-}
lem_subst_typ_tabs :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_typ_tabs g g' x v_x t_x p_vx_tx p_g_wf e t 
                   (TAbs n env_ t_z k_z p_env_tz e' t' nms mk_p_yenv_e'_t') 
  = TAbs n' (concatE g (esubFV x v_x g')) (tsubFV x v_x t_z) k_z p_g'g_tzvx
         (subFV x v_x e') (tsubFV x v_x t') nms' mk_p_yg'g_e'vx_t'vx
      where
        p_vx_er_tx       = lem_typing_hasftype g v_x t_x p_vx_tx p_g_wf
        p_g'g_tzvx       = lem_subst_wf g g' x v_x t_x p_vx_er_tx t_z k_z p_env_tz
        {-@ mk_p_yg'g_e'vx_t'vx :: { y:Vname | NotElem y nms' } 
              -> { pf:HasType | propOf pf == 
                      HasType (Cons y (tsubFV x v_x t_z) (concatE g (esubFV x v_x g'))) 
                              (unbind y (subFV x v_x e')) (unbindT y (tsubFV x v_x t')) && 
                                sizeOf pf <= n + 2 * (sizeOf p_vx_tx) } @-}
        mk_p_yg'g_e'vx_t'vx y = lem_subst_typ g (Cons y t_z g') x v_x t_x p_vx_tx p_g_wf
                                         (unbind y e') (unbindT y t') (mk_p_yenv_e'_t' y)
                                         ? lem_commute_subFV_unbind    x 
                                               (v_x ? lem_typ_islc g v_x t_x p_vx_tx p_g_wf) y e'
                                         ? lem_commute_tsubFV_unbindT  x 
                                               (v_x ? lem_typ_islc g v_x t_x p_vx_tx p_g_wf) y t' 
        nms'                  = unionEnv nms (concatE (Cons x t_x g) g')
        n'                    =  n + 2 * (typSize p_vx_tx)

{-@ lem_subst_typ_tapp :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> { p_vx_tx:HasType | propOf p_vx_tx == HasType g v_x t_x }
        -> ProofOf(WFEnv   g ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t  == HasType (concatE (Cons x t_x g) g') e t && isTApp p_e_t}
        -> {p'_e_t:HasType | propOf p'_e_t == HasType (concatE g (esubFV x v_x g')) 
                                                      (subFV x v_x e) (tsubFV x v_x t) &&
                             sizeOf p'_e_t <= (sizeOf p_e_t) + 2 * (sizeOf p_vx_tx) } 
         / [sizeOf p_e_t, 0] @-}
lem_subst_typ_tapp :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_typ_tapp g g' x v_x t_x p_vx_tx p_g_wf e t 
                   (TApp n env_ e' t_z t' p_env_e'_tzt' e_z p_env_ez_tz) 
  = TApp n' (concatE g (esubFV x v_x g')) (subFV x v_x e') (tsubFV x v_x t_z) (tsubFV x v_x t') 
         p_g'g_e'vx_tzt'vx (subFV x v_x e_z)  p_g'g_ezvx_tzvx         
      where
        p_g'g_e'vx_tzt'vx = lem_subst_typ g g' x v_x t_x p_vx_tx p_g_wf e' 
                                          (TFunc t_z t') p_env_e'_tzt'
        p_g'g_ezvx_tzvx   = lem_subst_typ g g' x v_x t_x p_vx_tx p_g_wf e_z t_z p_env_ez_tz 
        n'                = max (typSize p_g'g_e'vx_tzt'vx) (typSize p_g'g_ezvx_tzvx)

{-@ lem_subst_typ_tabst :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> { p_vx_tx:HasType | propOf p_vx_tx == HasType g v_x t_x }
        -> ProofOf(WFEnv  g ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t  == HasType (concatE (Cons x t_x g) g') e t && isTAbsT p_e_t}
        -> {p'_e_t:HasType | propOf p'_e_t == HasType (concatE g (esubFV x v_x g')) 
                                                      (subFV x v_x e) (tsubFV x v_x t) &&
                             sizeOf p'_e_t <= (sizeOf p_e_t) + 2 * (sizeOf p_vx_tx) } 
         / [sizeOf p_e_t, 0] @-}
lem_subst_typ_tabst :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_typ_tabst g g' x v_x t_x p_vx_tx p_g_wf e t 
                    p_e_t@(TAbsT n env k e' t' nms mk_p_a'env_e'_t') 
  = TAbsT n' (concatE g (esubFV x v_x g')) k (subFV x v_x e') (tsubFV x v_x t') nms'
          mk_p_a'env'_e'_t'
      where
        {-@ mk_p_a'env'_e'_t' :: { a':Vname | NotElem a' nms' }
              -> { pf:HasType | propOf pf ==
                      HasType (ConsT a' k (concatE g (esubFV x v_x g')))
                              (unbind_tv a' (subFV x v_x e')) (unbind_tvT a' (tsubFV x v_x t')) &&
                                sizeOf pf <= n + 2 * (sizeOf p_vx_tx) } @-}
        mk_p_a'env'_e'_t' a' = lem_subst_typ g (ConsT (a' ? lem_in_env_concat g g' a') k g') 
                                 x v_x t_x p_vx_tx p_g_wf 
                                 (unbind_tv a' e') (unbind_tvT a' t') (mk_p_a'env_e'_t' a')
                                 ? lem_commute_subFV_unbind_tv x
                                     (v_x ? lem_typ_islc g v_x t_x p_vx_tx p_g_wf) a' e'
                                 ? lem_commute_tsubFV_unbind_tvT x
                                     (v_x ? lem_typ_islc g v_x t_x p_vx_tx p_g_wf) a' t'
        nms'                 = unionEnv nms (concatE (Cons x t_x g) g')
        n'                   =  n + 2 * (typSize p_vx_tx)
          
{-@ lem_subst_typ_tappt :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> { p_vx_tx:HasType | propOf p_vx_tx == HasType g v_x t_x }
        -> ProofOf(WFEnv g ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t  == HasType (concatE (Cons x t_x g) g') e t && isTAppT p_e_t}
        -> {p'_e_t:HasType | propOf p'_e_t == HasType (concatE g (esubFV x v_x g')) 
                                                      (subFV x v_x e) (tsubFV x v_x t) &&
                             sizeOf p'_e_t <= (sizeOf p_e_t) + 2 * (sizeOf p_vx_tx) } 
         / [sizeOf p_e_t, 0] @-}
lem_subst_typ_tappt :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_typ_tappt g g' x v_x t_x p_vx_tx p_g_wf e t 
                    p_e_t@(TAppT n env e' k1 s p_e'_a1s t' p_env_t')
  = TAppT n' (concatE g (esubFV x v_x g')) (subFV x v_x e') k1 (tsubFV x v_x s) p_env'_e'_a1s
          (tsubFV x v_x t') p_env'_t'
          ? lem_commute_tsubFV_tsubBTV t' x (v_x ? lem_typ_islc g v_x t_x p_vx_tx p_g_wf) s
          ? toProof ( tdepth (tsubFV x v_x (tsubBTV t' s)) === tdepth (tsubBTV t' s)  ) 
      where
        p_vx_er_tx    = lem_typing_hasftype g v_x t_x p_vx_tx p_g_wf
        p_env'_e'_a1s = lem_subst_typ g g' x v_x t_x p_vx_tx p_g_wf e' (TPoly k1 s) p_e'_a1s
        p_env'_t'     = lem_subst_wf  g g' x v_x t_x p_vx_er_tx t' k1 p_env_t'
        n'            = n + 2*(typSize p_vx_tx)
                      
 
{-@ lem_subst_typ_tlet :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> { p_vx_tx:HasType | propOf p_vx_tx == HasType g v_x t_x }
        -> ProofOf(WFEnv   g ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t  == HasType (concatE (Cons x t_x g) g') e t && isTLet p_e_t}
        -> {p'_e_t:HasType | propOf p'_e_t == HasType (concatE g (esubFV x v_x g')) 
                                                      (subFV x v_x e) (tsubFV x v_x t) &&
                             sizeOf p'_e_t <= (sizeOf p_e_t) + 2 * (sizeOf p_vx_tx) } 
         / [sizeOf p_e_t, 0] @-}
lem_subst_typ_tlet :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_typ_tlet g g' x v_x t_x p_vx_tx p_g_wf e t 
                   (TLet n env_ e_z t_z p_env_ez_tz e' t_ k p_env_t nms mk_p_yenv_e'_t) 
  = TLet n' (concatE g (esubFV x v_x g')) (subFV x v_x e_z) (tsubFV x v_x t_z) p_g'g_ezvx_tzvx
         (subFV x v_x e') (tsubFV x v_x t) k p_g'g_t'vx nms' mk_p_yg'g_e'vx_tvx
      where
        p_vx_er_tx       = lem_typing_hasftype g v_x t_x p_vx_tx p_g_wf
        p_g'g_ezvx_tzvx  = lem_subst_typ g g' x v_x t_x p_vx_tx p_g_wf e_z t_z p_env_ez_tz
        p_g'g_t'vx       = lem_subst_wf  g g' x v_x t_x p_vx_er_tx t k p_env_t
        {-@ mk_p_yg'g_e'vx_tvx :: { y:Vname | NotElem y nms' } 
              -> { pf:HasType | propOf pf == 
                      HasType (Cons y (tsubFV x v_x t_z) (concatE g (esubFV x v_x g'))) 
                              (unbind y (subFV x v_x e')) (unbindT y (tsubFV x v_x t)) && 
                                sizeOf pf <= n + 2 * (sizeOf p_vx_tx) } @-}
        mk_p_yg'g_e'vx_tvx y = lem_subst_typ g (Cons (y ? lem_in_env_concat g g' y) t_z g') 
                                         x v_x t_x p_vx_tx p_g_wf 
                                         (unbind y e') (unbindT y t) (mk_p_yenv_e'_t y)
                                         ? lem_commute_subFV_unbind    x
                                               (v_x ? lem_typ_islc g v_x t_x p_vx_tx p_g_wf) y e'
                                         ? lem_commute_tsubFV_unbindT  x 
                                               (v_x ? lem_typ_islc g v_x t_x p_vx_tx p_g_wf) y t
        nms'                 = unionEnv nms (concatE (Cons x t_x g) g')
        n'                   = n + 2 * (typSize p_vx_tx)

{-@ lem_subst_typ_tsub :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> { p_vx_tx:HasType | propOf p_vx_tx == HasType g v_x t_x }
        -> ProofOf(WFEnv   g ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t  == HasType (concatE (Cons x t_x g) g') e t && isTSub p_e_t}
        -> {p'_e_t:HasType | propOf p'_e_t == HasType (concatE g (esubFV x v_x g')) 
                                                      (subFV x v_x e) (tsubFV x v_x t) &&
                             sizeOf p'_e_t <= (sizeOf p_e_t) + 2 * (sizeOf p_vx_tx) } 
         / [sizeOf p_e_t, 0] @-}
lem_subst_typ_tsub :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_typ_tsub g g' x v_x t_x p_vx_tx p_g_wf e t 
                   (TSub n env_ e_ s p_env_e_s t_ k p_env_t p_env_s_t)
  = TSub n' (concatE g (esubFV x v_x g')) (subFV x v_x e) (tsubFV x v_x s) p_g'g_e_s
         (tsubFV x v_x t) k p_g'g_t p_g'g_s_t
      where
        p_vx_er_tx = lem_typing_hasftype g v_x t_x p_vx_tx p_g_wf
        p_g'g_e_s  = lem_subst_typ g g' x v_x t_x p_vx_tx p_g_wf e s p_env_e_s
        p_g'g_t    = lem_subst_wf  g g' x v_x t_x p_vx_er_tx t k p_env_t
        p_g'g_s_t  = lem_subst_sub g g' x v_x t_x p_vx_tx p_g_wf s  t  p_env_s_t
        n'         = max (typSize p_g'g_e_s) (subtypSize p_g'g_s_t)

{-@ lem_subst_typ :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> { p_vx_tx:HasType | propOf p_vx_tx == HasType g v_x t_x }
        -> ProofOf(WFEnv  g  ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t  == HasType (concatE (Cons x t_x g) g') e t }
        -> {p'_e_t:HasType | propOf p'_e_t == HasType (concatE g (esubFV x v_x g')) 
                                                      (subFV x v_x e) (tsubFV x v_x t) &&
                             sizeOf p'_e_t <= (sizeOf p_e_t) + 2 * (sizeOf p_vx_tx) } 
         / [sizeOf p_e_t, 1] @-}
lem_subst_typ :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_typ g g' x v_x t_x p_vx_tx p_g_wf e t (TBC _env b) 
  = TBC (concatE g (esubFV x v_x g')) b ? lem_tsubFV_tybc x v_x b
lem_subst_typ g g' x v_x t_x p_vx_tx p_g_wf e t (TIC _env n) 
  = TIC (concatE g (esubFV x v_x g')) n ? lem_tsubFV_tyic x v_x n 
lem_subst_typ g g' x v_x t_x p_vx_tx p_g_wf e t p_e_t@(TVar1 {})  
  = lem_subst_typ_tvar1 g g' x v_x t_x p_vx_tx p_g_wf e t p_e_t
lem_subst_typ g g' x v_x t_x p_vx_tx p_g_wf e t p_e_t@(TVar2 {})
  = lem_subst_typ_tvar2 g g' x v_x t_x p_vx_tx p_g_wf e t p_e_t
lem_subst_typ g g' x v_x t_x p_vx_tx p_g_wf e t p_e_t@(TVar3 {})
  = lem_subst_typ_tvar3 g g' x v_x t_x p_vx_tx p_g_wf e t p_e_t
lem_subst_typ g g' x v_x t_x p_vx_tx p_g_wf e t (TPrm _en c) 
  = TPrm (concatE g (esubFV x v_x g')) c ? lem_tsubFV_ty x v_x c 
lem_subst_typ g g' x v_x t_x p_vx_tx p_g_wf e t p_e_t@(TAbs {}) 
  = lem_subst_typ_tabs g g' x v_x t_x p_vx_tx p_g_wf e t p_e_t  
lem_subst_typ g g' x v_x t_x p_vx_tx p_g_wf e t p_e_t@(TApp {}) 
  = lem_subst_typ_tapp g g' x v_x t_x p_vx_tx p_g_wf e t p_e_t
lem_subst_typ g g' x v_x t_x p_vx_tx p_g_wf e t p_e_t@(TAbsT {}) 
  = lem_subst_typ_tabst g g' x v_x t_x p_vx_tx p_g_wf e t p_e_t
lem_subst_typ g g' x v_x t_x p_vx_tx p_g_wf e t p_e_t@(TAppT {}) 
  = lem_subst_typ_tappt g g' x v_x t_x p_vx_tx p_g_wf e t p_e_t
lem_subst_typ g g' x v_x t_x p_vx_tx p_g_wf e t p_e_t@(TLet {}) 
  = lem_subst_typ_tlet g g' x v_x t_x p_vx_tx p_g_wf e t p_e_t
lem_subst_typ g g' x v_x t_x p_vx_tx p_g_wf e t (TAnn n env_ e' t_ p_env_e'_t) 
  = TAnn n' (concatE g (esubFV x v_x g')) (subFV x v_x e') (tsubFV x v_x t) p_g'g_e'_t
      where
        p_g'g_e'_t = lem_subst_typ g g' x v_x t_x p_vx_tx p_g_wf e' t p_env_e'_t
        n'         = n + 2 * (typSize p_vx_tx)
lem_subst_typ g g' x v_x t_x p_vx_tx p_g_wf e t p_e_t@(TSub {}) 
  = lem_subst_typ_tsub g g' x v_x t_x p_vx_tx p_g_wf e t p_e_t

{-@ lem_subst_sub_sbase :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> { p_vx_tx:HasType | propOf p_vx_tx == HasType g v_x t_x }
        -> ProofOf(WFEnv  g ) -> s:Type -> t:Type
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t && isSBase p_s_t }
        -> {p'_s_t:Subtype | propOf p'_s_t == Subtype (concatE g (esubFV x v_x g')) 
                                                         (tsubFV x v_x s) (tsubFV x v_x t)  &&
                             sizeOf p'_s_t <= (sizeOf p_s_t) + 2 * (sizeOf p_vx_tx)} 
         / [ sizeOf p_s_t, 0 ] @-}
lem_subst_sub_sbase :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Type {-> Kind -> WFType-} -> Type {-> Kind -> WFType-} -> Subtype -> Subtype
lem_subst_sub_sbase g g' x v_x t_x p_vx_tx p_g_wf s {-k_s p_env_s-} t {-k_t p_env_t -}
              (SBase env b ps qs nms mk_imp_ps_qs) -- p_env_s_t
  = SBase (concatE g (esubFV x v_x g')) b (psubFV x v_x ps) (psubFV x v_x qs) nms'
          mk_imp_ps'_qs'
      where
        {-@ mk_imp_ps'_qs' :: { y:Vname | NotElem y nms' }
              -> ProofOf(Implies (Cons y (TRefn b PEmpty) (concatE g (esubFV x v_x g')))
                                 (unbindP y (psubFV x v_x ps)) (unbindP y (psubFV x v_x qs))) @-}
        mk_imp_ps'_qs' y = ISub g (Cons y (TRefn b PEmpty) g') x v_x t_x p_vx_tx 
                                (unbindP y ps) (unbindP y qs) (mk_imp_ps_qs y)
                                ? lem_commute_psubFV_unbindP x 
                                    (v_x ? lem_typ_islc g v_x t_x p_vx_tx p_g_wf) y ps
                                ? lem_commute_psubFV_unbindP x 
                                    (v_x ? lem_typ_islc g v_x t_x p_vx_tx p_g_wf) y qs
                                ? toProof ( tsubFV x v_x (TRefn b PEmpty) 
                                        === TRefn b (psubFV x v_x PEmpty) === TRefn b PEmpty )
        nms'             = x:(unionEnv nms (concatE g g'))

{-@ lem_subst_sub_sfunc :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> { p_vx_tx:HasType | propOf p_vx_tx == HasType g v_x t_x }
        -> ProofOf(WFEnv  g ) -> s:Type -> t:Type
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t && isSFunc p_s_t }
        -> {p'_s_t:Subtype | propOf p'_s_t == Subtype (concatE g (esubFV x v_x g')) 
                                                         (tsubFV x v_x s) (tsubFV x v_x t)  &&
                             sizeOf p'_s_t <= (sizeOf p_s_t) + 2 * (sizeOf p_vx_tx) } 
         / [ sizeOf p_s_t, 0 ] @-}
lem_subst_sub_sfunc :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Type {-> Kind -> WFType-} -> Type {-> Kind -> WFType-} -> Subtype -> Subtype
lem_subst_sub_sfunc g g' x v_x t_x p_vx_tx p_g_wf ty1 {-ky1 p_env_ty1-} ty2 {-ky2 p_env_ty2-}
              (SFunc n env s1 s2 p_s2_s1 t1 t2 nms mk_p_yenv_t1_t2) 
  = SFunc n' (concatE g (esubFV x v_x g')) (tsubFV x v_x s1)  (tsubFV x v_x s2)
          p_s2vx_s1vx (tsubFV x v_x t1) (tsubFV x v_x t2) nms' mk_p_yg'g_t1vx_t2vx
          ? toProof (tsubFV x v_x (TFunc s1 t1) === TFunc (tsubFV x v_x s1) (tsubFV x v_x t1) )
          ? toProof (tsubFV x v_x (TFunc s2 t2) === TFunc (tsubFV x v_x s2) (tsubFV x v_x t2) )
      where 
        {-@ mk_p_yg'g_t1vx_t2vx :: { y:Vname | NotElem y nms' }
              -> { pf:Subtype | propOf pf == 
                      Subtype (Cons y (tsubFV x v_x s2) (concatE g (esubFV x v_x g')))
                              (unbindT y (tsubFV x v_x t1)) (unbindT y (tsubFV x v_x t2)) &&
                                sizeOf pf <= n + 2 * (sizeOf p_vx_tx) } @-}
        mk_p_yg'g_t1vx_t2vx y = lem_subst_sub g (Cons y s2 g') x v_x t_x p_vx_tx p_g_wf
                                         (unbindT y t1) (unbindT y t2) (mk_p_yenv_t1_t2 y)
                                         ? lem_commute_tsubFV_unbindT  x
                                               (v_x ? lem_typ_islc g v_x t_x p_vx_tx p_g_wf) y t1
                                         ? lem_commute_tsubFV_unbindT  x 
                                               (v_x ? lem_typ_islc g v_x t_x p_vx_tx p_g_wf) y t2 
        p_s2vx_s1vx      = lem_subst_sub g g' x v_x t_x p_vx_tx p_g_wf s2 s1 p_s2_s1 
        nms'             = x:(unionEnv  nms  (concatE g g'))
        n'               = n + 2 * (typSize p_vx_tx)
 
{-@ lem_subst_sub_switn :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> { p_vx_tx:HasType | propOf p_vx_tx == HasType g v_x t_x }
        -> ProofOf(WFEnv  g ) -> s:Type -> t:Type
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t && isSWitn p_s_t }
        -> {p'_s_t:Subtype | propOf p'_s_t == Subtype (concatE g (esubFV x v_x g')) 
                                                         (tsubFV x v_x s) (tsubFV x v_x t)  &&
                             sizeOf p'_s_t <= (sizeOf p_s_t) + 2 * (sizeOf p_vx_tx) } 
         / [ sizeOf p_s_t, 0 ] @-}
lem_subst_sub_switn :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Type {-> Kind -> WFType-} -> Type {-> Kind -> WFType-} -> Subtype -> Subtype
lem_subst_sub_switn g g' x v_x t_x p_vx_tx p_g_wf t {-k p_env_t-} t2 {-k2 p_env_t2-}
              (SWitn n env v_z t_z p_env_vz_tz _t t' p_env_t_t'vz)
  = SWitn n' (concatE g (esubFV x v_x g')) (subFV x v_x v_z) (tsubFV x v_x t_z) p_g'g_vzvx_tzvx
          (tsubFV x v_x t) (tsubFV x v_x t') p_g'g_tvx_t'vzvx
      where
        p_g'g_vzvx_tzvx  = lem_subst_typ g g' x v_x t_x p_vx_tx p_g_wf v_z t_z p_env_vz_tz
        p_g'g_tvx_t'vzvx = lem_subst_sub g g' x v_x t_x p_vx_tx p_g_wf t {-k p_env_t -}
                                         (tsubBV v_z t') {-k' p_env_t'vz-} p_env_t_t'vz
                                         ? lem_commute_tsubFV_tsubBV v_z x 
                                             (v_x ? lem_typ_islc g v_x t_x p_vx_tx p_g_wf) t'
        n'               = max (typSize p_g'g_vzvx_tzvx) (subtypSize p_g'g_tvx_t'vzvx)

{-@ lem_subst_sub_sbind :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> { p_vx_tx:HasType | propOf p_vx_tx == HasType g v_x t_x }
        -> ProofOf(WFEnv  g ) -> s:Type -> t:Type
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t && isSBind p_s_t }
        -> {p'_s_t:Subtype | propOf p'_s_t == Subtype (concatE g (esubFV x v_x g')) 
                                                         (tsubFV x v_x s) (tsubFV x v_x t)  &&
                             sizeOf p'_s_t <= (sizeOf p_s_t) + 2 * (sizeOf p_vx_tx)} 
         / [ sizeOf p_s_t, 0 ] @-}
lem_subst_sub_sbind :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Type {-> Kind -> WFType-} -> Type {-> Kind -> WFType-} -> Subtype -> Subtype
lem_subst_sub_sbind g g' x v_x t_x p_vx_tx p_g_wf t1 {-k1 p_env_t1-} t' {-k' p_env_t'-}
              (SBind n env t_z t _t' nms mk_p_wenv_t_t') 
  = SBind n' (concatE g (esubFV x v_x g')) (tsubFV x v_x t_z) (tsubFV x v_x t) 
          (tsubFV x v_x t' ? lem_islct_at_tsubFV 0 0 x 
                                 (v_x ? lem_typ_islc g v_x t_x p_vx_tx p_g_wf) t')
          nms' mk_p_wenv'_tvx_t'vx
      where 
        {-@ mk_p_wenv'_tvx_t'vx :: { w:Vname | NotElem w nms'}
               -> { pf:Subtype | propOf pf ==
                       Subtype (Cons w (tsubFV x v_x t_z) (concatE g (esubFV x v_x g')))
                               (unbindT w (tsubFV x v_x t)) (tsubFV x v_x t') &&
                                 sizeOf pf <= n + 2 * (sizeOf p_vx_tx) } @-}
        mk_p_wenv'_tvx_t'vx w = lem_subst_sub g (Cons w t_z g') x v_x t_x p_vx_tx p_g_wf
                                         (unbindT w t)  t'  (mk_p_wenv_t_t' w)
                                         ? lem_commute_tsubFV_unbindT x 
                                             (v_x ? lem_typ_islc g v_x t_x p_vx_tx p_g_wf) w t
        nms'             = x:(unionEnv nms (concatE g g'))
        n'               = n + 2 * (typSize p_vx_tx)

{-@ lem_subst_sub_spoly :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> { p_vx_tx:HasType | propOf p_vx_tx == HasType g v_x t_x }
        -> ProofOf(WFEnv  g ) -> s:Type -> t:Type
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t && isSPoly p_s_t }
        -> {p'_s_t:Subtype | propOf p'_s_t == Subtype (concatE g (esubFV x v_x g')) 
                                                         (tsubFV x v_x s) (tsubFV x v_x t)  &&
                             sizeOf p'_s_t <= (sizeOf p_s_t) + 2 * (sizeOf p_vx_tx) } 
         / [ sizeOf p_s_t, 0 ] @-}
lem_subst_sub_spoly :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Type {-> Kind -> WFType-} -> Type {-> Kind -> WFType-} -> Subtype -> Subtype
lem_subst_sub_spoly g g' x v_x t_x p_vx_tx p_g_wf t1 {-k1@Star p_env_t1-} t2 {-k2@Star p_env_t2-}
                    (SPoly n env k' t1' t2' nms mk_p_a1env_t1'_t2') 
  = SPoly n' (concatE g (esubFV x v_x g')) k' (tsubFV x v_x t1') (tsubFV x v_x t2')
          nms' mk_p_a1g'g_t1'vx_t2'vx
      where
        {-@ mk_p_a1g'g_t1'vx_t2'vx :: { a1:Vname | NotElem a1 nms' }
              -> { pf:Subtype | propOf pf ==
                      Subtype (ConsT a1 k' (concatE g (esubFV x v_x g')))
                        (unbind_tvT a1 (tsubFV x v_x t1')) (unbind_tvT a1 (tsubFV x v_x t2')) &&
                                sizeOf pf <= n + 2 * (sizeOf p_vx_tx) } @-}
        mk_p_a1g'g_t1'vx_t2'vx a1 = lem_subst_sub g (ConsT (a1 ? lem_in_env_concat g g' a1) k' g') 
                                      x v_x t_x p_vx_tx p_g_wf
                                      (unbind_tvT a1 t1') (unbind_tvT a1 t2') 
                                      (mk_p_a1env_t1'_t2' a1)
                                      ? lem_commute_tsubFV_unbind_tvT x 
                                          (v_x ? lem_typ_islc g v_x t_x p_vx_tx p_g_wf) a1 t1'
                                      ? lem_commute_tsubFV_unbind_tvT x 
                                          (v_x ? lem_typ_islc g v_x t_x p_vx_tx p_g_wf) a1 t2'
        nms'             = unionEnv nms (concatE (Cons x t_x g) g')
        n'               = n + 2 * (typSize p_vx_tx)

{-@ lem_subst_sub :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> { p_vx_tx:HasType | propOf p_vx_tx == HasType g v_x t_x }
        -> ProofOf(WFEnv  g)  -> s:Type -> t:Type
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t }
        -> {p'_s_t:Subtype | propOf p'_s_t == Subtype (concatE g (esubFV x v_x g')) 
                                                         (tsubFV x v_x s) (tsubFV x v_x t)  &&
                             sizeOf p'_s_t <= (sizeOf p_s_t) + 2 * (sizeOf p_vx_tx)} 
         / [ sizeOf p_s_t, 1 ] @-}
lem_subst_sub :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Type {-> Kind -> WFType-} -> Type {-> Kind -> WFType-} -> Subtype -> Subtype
lem_subst_sub g g' x v_x t_x p_vx_tx p_g_wf s {-k_s p_env_s-} t {-k_t p_env_t-} p_s_t@(SBase {}) 
    = lem_subst_sub_sbase g g' x v_x t_x p_vx_tx p_g_wf s {-k_s p_env_s-} t {-k_t p_env_t-} p_s_t
lem_subst_sub g g' x v_x t_x p_vx_tx p_g_wf ty1  ty2  p_ty1_ty2@(SFunc {}) 
    = lem_subst_sub_sfunc g g' x v_x t_x p_vx_tx p_g_wf ty1 ty2  p_ty1_ty2
lem_subst_sub g g' x v_x t_x p_vx_tx p_g_wf t {-k p_env_t-} t2 {-k2 p_env_t2-} p_t_t2@(SWitn {}) 
    = lem_subst_sub_switn g g' x v_x t_x p_vx_tx p_g_wf t {-k p_env_t-} t2 {-k2 p_env_t2-} p_t_t2
lem_subst_sub g g' x v_x t_x p_vx_tx p_g_wf t1 {-k1 p_env_t1-} t' {-k' p_env_t'-} p_t1_t'@(SBind {}) 
    = lem_subst_sub_sbind g g' x v_x t_x p_vx_tx p_g_wf t1 {-k1 p_env_t1-} t' {-k' p_env_t'-} p_t1_t'
lem_subst_sub g g' x v_x t_x p_vx_tx p_g_wf t1 {-k1 p_env_t1-} t2 {-k2 p_env_t2-} p_t1_t2@(SPoly {}) 
    = lem_subst_sub_spoly g g' x v_x t_x p_vx_tx p_g_wf t1 {-k1 p_env_t1-} t2 {-k2 p_env_t2-} p_t1_t2
