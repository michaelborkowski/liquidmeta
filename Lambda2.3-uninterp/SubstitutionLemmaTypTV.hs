{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SubstitutionLemmaTypTV where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import LocalClosure
import Strengthenings
import Semantics
import SystemFWellFormedness
import SystemFTyping
import BasicPropsSubstitution
import BasicPropsEnvironments
import WellFormedness
import BasicPropsWellFormedness
import Typing
--import LemmasWeakenWF
import LemmasWeakenWFTV
import LemmasWellFormedness
import SubstitutionLemmaWFTV
import LemmasTyping
import LemmasWeakenTyp
import LemmasWeakenTypTV
import LemmasSubtyping
import LemmasExactness

--        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) -> e:Expr -> t:Type 
{-@ lem_subst_tv_typ_tvar1 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv g ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t  == HasType (concatE (ConsT a k_a g) g') e t && isTVar1 p_e_t }
        -> {p'_e_t:HasType | propOf p'_e_t == HasType (concatE g (esubFTV a t_a g')) 
                                                      (subFTV a t_a e) (tsubFTV a t_a t) &&
                             sizeOf p'_e_t <= sizeOf p_e_t + 2 * tdepth t_a + 0 }
         / [sizeOf p_e_t, 0] @-}
lem_subst_tv_typ_tvar1 :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_tv_typ_tvar1 g g' a t_a k_a p_g_ta p_g_wf e t (TVar1 _env z t' k' p_env_t') 
  = case g' of          -- empty case: e = FV z = FV x and t = self t' x = self t_x x
      (Empty)          -> impossible "a <> z"
      (Cons _z _ g'')  -> TVar1 (concatE g (esubFTV a t_a g''))  -- z <> a, t = self t' (FV z)
                                (z ? lem_in_env_esubFTV g'' a t_a z
                                   ? lem_in_env_concat g g'' z)
                                (tsubFTV a t_a t') k' p_env'_t'ta
                                ? lem_tsubFTV_self a t_a t' (FV z) k'
        where
          p_env'_t'ta = lem_subst_tv_wf' g g'' a t_a k_a p_g_ta p_g_wf t' k' p_env_t'

{-@ lem_subst_tv_typ_tvar2 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv g ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTVar2 p_e_t }
        -> {p'_e_t:HasType | propOf p'_e_t == HasType (concatE g (esubFTV a t_a g')) 
                                                      (subFTV a t_a e) (tsubFTV a t_a t) &&
                             sizeOf p'_e_t <= sizeOf p_e_t + 2 * tdepth t_a + 0 }
         / [sizeOf p_e_t, 0] @-}
lem_subst_tv_typ_tvar2 :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_tv_typ_tvar2 g g' a t_a k_a p_g_ta p_g_wf e t p_env_z_t@(TVar2 n env_ z _t p_z_t w_ t_w) 
    = case g' of             
        (Empty)           -> impossible "a <> w"
        (Cons _w _tw g'') -> case (a == z) of
            (True)  -> impossible ("by lemma" ? lem_tvar_v_in_env (concatE (ConsT a k_a g) g')
                                                                  z t p_env_z_t )
            (False) -> TVar2 (typSize p_z_tta) (concatE g (esubFTV a t_a g'')) 
                             (z ? lem_in_env_esubFTV g'' a t_a z
                                ? lem_in_env_concat (ConsT a k_a g) g'' z)
                             (tsubFTV a t_a t) p_z_tta w (tsubFTV a t_a t_w)
                         where
                           w = w_ ? lem_in_env_esubFTV g'' a t_a w_
                                  ? lem_in_env_concat g g'' w_
                           p_z_tta = lem_subst_tv_typ g g'' a t_a k_a p_g_ta 
                                                      p_g_wf e t p_z_t

{-@ lem_subst_tv_typ_tvar3 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv g ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTVar3 p_e_t }
        -> {p'_e_t:HasType | propOf p'_e_t == HasType (concatE g (esubFTV a t_a g')) 
                                                      (subFTV a t_a e) (tsubFTV a t_a t) &&
                             sizeOf p'_e_t <= sizeOf p_e_t + 2 * tdepth t_a + 0 }
         / [sizeOf p_e_t, 0] @-}
lem_subst_tv_typ_tvar3 :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_tv_typ_tvar3 g g' a t_a k_a p_g_ta p_g_wf e t p_env_z_t@(TVar3 n env_ z _t p_z_t a'_ k_a') 
    = case g' of             -- g'' = Empty so a = a' and p_z_t :: HasFType(g (FV z) t)
        (Empty)            -> case (a == z) of
            (True)  -> impossible ("by lemma" ? lem_tvar_v_in_env (concatE (ConsT a k_a g) g')
                                                                  z t p_env_z_t)
            (False) -> p_z_t ? lem_free_bound_in_env g t Star p_g_t a
                             ? lem_tsubFTV_notin a t_a t   --  ? toProof ( e === (FV z) )
                         where
                           p_g_t = lem_typing_wf g (FV z) t p_z_t p_g_wf
        (ConsT _ _ka g'') -> case (a == z) of
            (True)  -> impossible ("by lemma" ? lem_tvar_v_in_env (concatE (ConsT a k_a g) g')
                                                                  z t p_env_z_t )
            (False) -> TVar3 (typSize p_z_tvta) (concatE g (esubFTV a t_a g'')) --z
                             (z ? lem_in_env_esubFTV g'' a t_a z
                                ? lem_in_env_concat (ConsT a k_a g) g'' z)
                             (tsubFTV a t_a t) p_z_tvta a' k_a'
                         where
                           a' = a'_ ? lem_in_env_esubFTV g'' a t_a a'_
                                    ? lem_in_env_concat g g'' a'_
                           p_z_tvta = lem_subst_tv_typ g g'' a t_a k_a p_g_ta 
                                                       p_g_wf e t p_z_t

{-@ lem_subst_tv_typ_tabs :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv g ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTAbs p_e_t }
        -> {p'_e_t:HasType | propOf p'_e_t == HasType (concatE g (esubFTV a t_a g')) 
                                                      (subFTV a t_a e) (tsubFTV a t_a t) &&
                             sizeOf p'_e_t <= sizeOf p_e_t + 2 * tdepth t_a + 0 }
         / [sizeOf p_e_t, 0] @-}
lem_subst_tv_typ_tabs :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_tv_typ_tabs g g' a t_a k_a p_g_ta p_g_wf e t 
                      (TAbs n env_ t_z k_z p_env_tz e' t' nms mk_p_yenv_e'_t') 
  = TAbs n' (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t_z) k_z p_g'g_tzta
         (subFTV a t_a e') (tsubFTV a t_a t') nms' mk_p_yg'g_e'ta_t'ta
      where
        p_g'g_tzta       = lem_subst_tv_wf' g g' a t_a k_a p_g_ta p_g_wf t_z k_z p_env_tz
        {-@ mk_p_yg'g_e'ta_t'ta :: { y:Vname | NotElem y nms' }
              -> { pf:HasType | propOf pf ==
                      HasType (Cons y (tsubFTV a t_a t_z) (concatE g (esubFTV a t_a g')))
                              (unbind y (subFTV a t_a e')) (unbindT y (tsubFTV a t_a t')) &&
                                sizeOf pf <= n + 2 * tdepth t_a + 0 } @-}
        mk_p_yg'g_e'ta_t'ta y = lem_subst_tv_typ g (Cons y t_z g') a t_a k_a p_g_ta p_g_wf
                                         (unbind y e') (unbindT y t') (mk_p_yenv_e'_t' y)
                                         ? lem_commute_subFTV_unbind   a
                                               (t_a ? lem_wftype_islct g t_a k_a p_g_ta) y e'
                                         ? lem_commute_tsubFTV_unbindT a
                                               (t_a ? lem_wftype_islct g t_a k_a p_g_ta) y t'
        nms'                  = unionEnv nms (concatE (ConsT a k_a g) g')
        n'                    = n + 2 * tdepth t_a + 0

{-@ lem_subst_tv_typ_tapp :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv g ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTApp p_e_t }
        -> {p'_e_t:HasType | propOf p'_e_t == HasType (concatE g (esubFTV a t_a g')) 
                                                      (subFTV a t_a e) (tsubFTV a t_a t) &&
                             sizeOf p'_e_t <= sizeOf p_e_t + 2 * tdepth t_a + 0 }
         / [sizeOf p_e_t, 0] @-}
lem_subst_tv_typ_tapp :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_tv_typ_tapp g g' a t_a k_a p_g_ta p_g_wf e t 
                      (TApp n env_ e' t_z t' p_env_e'_tzt' e_z p_env_ez_tz) 
  = TApp n' (concatE g (esubFTV a t_a g')) (subFTV a t_a e') (tsubFTV a t_a t_z) (tsubFTV a t_a t') 
         p_g'g_e'ta_tzt'ta (subFTV a t_a e_z)  p_g'g_ezta_tzta
      where
        p_g'g_e'ta_tzt'ta = lem_subst_tv_typ g g' a t_a k_a p_g_ta p_g_wf e' 
                                             (TFunc t_z t') p_env_e'_tzt'
        p_g'g_ezta_tzta   = lem_subst_tv_typ g g' a t_a k_a p_g_ta p_g_wf e_z t_z p_env_ez_tz 
        n'                = max (typSize p_g'g_e'ta_tzt'ta) (typSize p_g'g_ezta_tzta)

{-@ lem_subst_tv_typ_tabst :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv g ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTAbsT p_e_t }
        -> {p'_e_t:HasType | propOf p'_e_t == HasType (concatE g (esubFTV a t_a g')) 
                                                      (subFTV a t_a e) (tsubFTV a t_a t) &&
                             sizeOf p'_e_t <= sizeOf p_e_t + 2 * tdepth t_a + 0 }
         / [sizeOf p_e_t, 0] @-}
lem_subst_tv_typ_tabst :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_tv_typ_tabst g g' a t_a k_a p_g_ta p_g_wf e t 
                    p_e_t@(TAbsT n env k e' t' nms mk_p_a'env_e'_t') 
  = TAbsT n' (concatE g (esubFTV a t_a g')) k (subFTV a t_a e') (tsubFTV a t_a t') nms'
          mk_p_a'env'_e'_t'
      where
        {-@ mk_p_a'env'_e'_t' :: { a':Vname | NotElem a' nms' }
              -> { pf:HasType | propOf pf ==
                      HasType (ConsT a' k (concatE g (esubFTV a t_a g')))
                              (unbind_tv a' (subFTV a t_a e')) (unbind_tvT a' (tsubFTV a t_a t')) &&
                                sizeOf pf <= n + 2 * tdepth t_a + 0 } @-}
        mk_p_a'env'_e'_t' a' = lem_subst_tv_typ g (ConsT (a' ? lem_in_env_concat g g' a') k g')
                                 a t_a k_a p_g_ta p_g_wf
                                 (unbind_tv a' e') (unbind_tvT a' t') (mk_p_a'env_e'_t' a')
                                 ? lem_commute_subFTV_unbind_tv a
                                     (t_a ? lem_wftype_islct g t_a k_a p_g_ta) a' e'
                                 ? lem_commute_tsubFTV_unbind_tvT a
                                     (t_a ? lem_wftype_islct g t_a k_a p_g_ta) a' t'
        nms'                 = unionEnv nms (concatE (ConsT a k_a g) g')
        n'                   = n + 2 * tdepth t_a + 0
          
{-@ lem_subst_tv_typ_tappt :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv g ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTAppT p_e_t }
        -> {p'_e_t:HasType | propOf p'_e_t == HasType (concatE g (esubFTV a t_a g')) 
                                                      (subFTV a t_a e) (tsubFTV a t_a t) &&
                             sizeOf p'_e_t <= sizeOf p_e_t + 2 * tdepth t_a + 0 }
         / [sizeOf p_e_t, 0] @-}
lem_subst_tv_typ_tappt :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_tv_typ_tappt g g' a t_a k_a p_g_ta p_g_wf e t 
                    p_e_t@(TAppT n env e' k1 s p_e'_a1s t' p_env_t')
  = TAppT n' (concatE g (esubFTV a t_a g')) (subFTV a t_a e') k1 (tsubFTV a t_a s) p_env'_e'_a1s
          (tsubFTV a t_a t') p_env'_t'
          ? lem_commute_tsubFTV_tsubBTV t' a (t_a ? lem_wftype_islct g t_a k_a p_g_ta) s
          ? toProof ( tdepth (tsubFTV a t_a (tsubBTV t' s)) <= tdepth t_a + tdepth (tsubBTV t' s) )
      where
        p_env'_e'_a1s = lem_subst_tv_typ g g' a t_a k_a p_g_ta p_g_wf e' (TPoly k1 s) p_e'_a1s
        p_env'_t'     = lem_subst_tv_wf' g g' a t_a k_a p_g_ta p_g_wf t' k1 p_env_t'
        n'            = n + 2 * tdepth t_a + 0

{-@ lem_subst_tv_typ_tlet :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv g ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTLet p_e_t }
        -> {p'_e_t:HasType | propOf p'_e_t == HasType (concatE g (esubFTV a t_a g')) 
                                                      (subFTV a t_a e) (tsubFTV a t_a t) &&
                             sizeOf p'_e_t <= sizeOf p_e_t + 2 * tdepth t_a + 0 }
         / [sizeOf p_e_t, 0] @-}
lem_subst_tv_typ_tlet :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_tv_typ_tlet g g' a t_a k_a p_g_ta p_g_wf e t 
                      (TLet n env_ e_z t_z p_env_ez_tz e' t_ k p_env_t nms mk_p_yenv_e'_t) 
  = TLet n' (concatE g (esubFTV a t_a g')) (subFTV a t_a e_z) (tsubFTV a t_a t_z) p_g'g_ezta_tzta
         (subFTV a t_a e') (tsubFTV a t_a t) k p_g'g_t'ta nms' mk_p_yg'g_e'ta_tta
      where
        {-@ mk_p_yg'g_e'ta_tta :: { y:Vname | NotElem y nms' }
              -> { pf:HasType | propOf pf ==
                      HasType (Cons y (tsubFTV a t_a t_z) (concatE g (esubFTV a t_a g')))
                              (unbind y (subFTV a t_a e')) (unbindT y (tsubFTV a t_a t)) &&
                                sizeOf pf <= n + 2 * tdepth t_a + 0 } @-}
        mk_p_yg'g_e'ta_tta y = lem_subst_tv_typ g (Cons (y ? lem_in_env_concat g g' y) t_z g')
                                         a t_a k_a p_g_ta p_g_wf
                                         (unbind y e') (unbindT y t) (mk_p_yenv_e'_t y)
                                         ? lem_commute_subFTV_unbind a
                                               (t_a ? lem_wftype_islct g t_a k_a p_g_ta) y e'
                                         ? lem_commute_tsubFTV_unbindT a
                                               (t_a ? lem_wftype_islct g t_a k_a p_g_ta) y t
        p_g'g_ezta_tzta      = lem_subst_tv_typ g g' a t_a k_a p_g_ta p_g_wf e_z t_z p_env_ez_tz
        p_g'g_t'ta           = lem_subst_tv_wf' g g' a t_a k_a p_g_ta p_g_wf t k p_env_t
        nms'                 = unionEnv nms (concatE (ConsT a k_a g) g')
        n'                   = n + 2 * tdepth t_a + 0

{-@ lem_subst_tv_typ_tsub :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv g ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTSub p_e_t }
        -> {p'_e_t:HasType | propOf p'_e_t == HasType (concatE g (esubFTV a t_a g')) 
                                                      (subFTV a t_a e) (tsubFTV a t_a t) &&
                             sizeOf p'_e_t <= sizeOf p_e_t + 2 * tdepth t_a + 0 }
         / [sizeOf p_e_t, 0] @-}
lem_subst_tv_typ_tsub :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_tv_typ_tsub g g' a t_a k_a p_g_ta p_g_wf e t 
                      (TSub n env_ e_ s p_env_e_s t_ k p_env_t p_env_s_t) 
  = TSub n' (concatE g (esubFTV a t_a g')) (subFTV a t_a e) (tsubFTV a t_a s) p_g'g_e_s
         (tsubFTV a t_a t) k p_g'g_t p_g'g_s_t
      where
        p_g'g_e_s  = lem_subst_tv_typ g g' a t_a k_a p_g_ta p_g_wf e s p_env_e_s
        p_g'g_t    = lem_subst_tv_wf' g g' a t_a k_a p_g_ta p_g_wf t k p_env_t
        p_g'g_s_t  = lem_subst_tv_sub g g' a t_a k_a p_g_ta p_g_wf s {-Star p_env_s-} t {-k p_env_t-} p_env_s_t
        n'         = n + 2 * tdepth t_a + 0

{-@ lem_subst_tv_typ :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv g ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t }
        -> {p'_e_t:HasType | propOf p'_e_t == HasType (concatE g (esubFTV a t_a g')) 
                                                      (subFTV a t_a e) (tsubFTV a t_a t) &&
                             sizeOf p'_e_t <= sizeOf p_e_t + 2 * tdepth t_a + 0 }
         / [sizeOf p_e_t, 1] @-}
lem_subst_tv_typ :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_g_wf e t (TBC _env b)
  = TBC (concatE g (esubFTV a t_a g')) b ? lem_tsubFTV_tybc a t_a b
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_g_wf e t (TIC _env n)
  = TIC (concatE g (esubFTV a t_a g')) n ? lem_tsubFTV_tyic a t_a n
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_g_wf e t p_e_t@(TVar1 {}) 
  = lem_subst_tv_typ_tvar1 g g' a t_a k_a p_g_ta p_g_wf e t p_e_t
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_g_wf e t p_e_t@(TVar2 {}) 
  = lem_subst_tv_typ_tvar2 g g' a t_a k_a p_g_ta p_g_wf e t p_e_t
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_g_wf e t p_e_t@(TVar3 {}) 
  = lem_subst_tv_typ_tvar3 g g' a t_a k_a p_g_ta p_g_wf e t p_e_t
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_g_wf e t (TPrm _env c)
  = TPrm (concatE g (esubFTV a t_a g')) c ? lem_tsubFTV_ty a t_a c
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_g_wf e t p_e_t@(TAbs {})
  = lem_subst_tv_typ_tabs g g' a t_a k_a p_g_ta p_g_wf e t p_e_t
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_g_wf e t p_e_t@(TApp {}) 
  = lem_subst_tv_typ_tapp g g' a t_a k_a p_g_ta p_g_wf e t p_e_t
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_g_wf e t p_e_t@(TAbsT {}) 
  = lem_subst_tv_typ_tabst g g' a t_a k_a p_g_ta p_g_wf e t p_e_t
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_g_wf e t p_e_t@(TAppT {}) 
  = lem_subst_tv_typ_tappt g g' a t_a k_a p_g_ta p_g_wf e t p_e_t
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_g_wf e t p_e_t@(TLet {})
  = lem_subst_tv_typ_tlet g g' a t_a k_a p_g_ta p_g_wf e t p_e_t
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_g_wf e t (TAnn n env_ e' t_ p_env_e'_t) 
  = TAnn n' (concatE g (esubFTV a t_a g')) (subFTV a t_a e') (tsubFTV a t_a t) p_env'_e'ta_tta
      where
        p_env'_e'ta_tta = lem_subst_tv_typ g g' a t_a k_a p_g_ta p_g_wf e' t p_env_e'_t
        n'              = typSize p_env'_e'ta_tta
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_g_wf e t p_e_t@(TSub {}) 
  = lem_subst_tv_typ_tsub g g' a t_a k_a p_g_ta p_g_wf e t p_e_t


{-@ lem_subst_tv_sub_sbase_ftv :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
      -> { a:Vname | (not (in_env a g)) && not (in_env a g') } 
      -> b':Basic -> qs:Preds -> k_a:Kind -> ProofOf(WFType g (TRefn b' qs) k_a) 
      -> ProofOf(WFEnv g ) -> p1:Preds -> p2:Preds  
      -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (ConsT a k_a g) g') 
                                             (TRefn (FTV a) p1) (TRefn (FTV a) p2) && isSBase p_s_t }
      -> {p'_s_t:Subtype | propOf p'_s_t == Subtype (concatE g (esubFTV a (TRefn b' qs) g')) 
                                                    (tsubFTV a (TRefn b' qs) (TRefn (FTV a) p1))
                                                    (tsubFTV a (TRefn b' qs) (TRefn (FTV a) p2)) &&
                           sizeOf p'_s_t <= sizeOf p_s_t + 0 } @-} -- / [subtypSize p_s_t, 0] @- }
lem_subst_tv_sub_sbase_ftv :: Env -> Env -> Vname -> Basic -> Preds -> Kind -> WFType -> WFEnv
      -> Preds {-> Kind -> WFType-} -> Preds {-> Kind -> WFType-} -> Subtype -> Subtype
lem_subst_tv_sub_sbase_ftv g g' a b' qs k_a p_g_ta p_g_wf p1 {-k_s p_env_s-} p2 {-k_t p_env_t -}
                       (SBase env b _p1 _p2 nms mk_imp_p1_p2) 
  = SBase (concatE g (esubFTV a t_a g')) b' (strengthen (psubFTV a t_a p1) qs)
          (strengthen (psubFTV a t_a p2) qs) 
          nms' mk_imp_p1taq_p2taq
      where 
        t_a              = TRefn b' qs
        {-@ mk_imp_p1taq_p2taq  :: { y:Vname | NotElem y nms' }
              -> ProofOf(Implies (Cons y (TRefn b' PEmpty) (concatE g (esubFTV a t_a g')))
                                 (unbindP y (strengthen (psubFTV a t_a p1) qs))
                                 (unbindP y (strengthen (psubFTV a t_a p2) qs)) ) @-}
        mk_imp_p1taq_p2taq y  = IStren y b' qs (concatE g (esubFTV a t_a g'))
                                       (unbindP y (psubFTV a t_a p1)) 
                                       (unbindP y (psubFTV a t_a p2)) imp_p1ta_p2ta
                                       ? lem_unbindP_strengthen y (psubFTV a t_a p1) qs
                                       ? lem_unbindP_strengthen y (psubFTV a t_a p2) qs
          where
            imp_p1ta_p2ta  = ISubTV g (Cons y (TRefn (FTV a) PEmpty) g') a t_a k_a p_g_ta 
                                    (unbindP y p1) (unbindP y p2) (mk_imp_p1_p2 y)  
                                    ? lem_commute_psubFTV_unbindP a
                                        (t_a ? lem_wftype_islct g t_a k_a p_g_ta) y p1
                                    ? lem_commute_psubFTV_unbindP a
                                        (t_a ? lem_wftype_islct g t_a k_a p_g_ta) y p2
                                    ? toProof ( tsubFTV a t_a (TRefn (FTV a) PEmpty)
                                            === push (psubFTV a t_a PEmpty) t_a 
                                            === push PEmpty t_a === t_a )
        nms'                  = a:(unionEnv nms (concatE g g'))

{-@ lem_subst_tv_sub_sbase :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv g ) -> s:Type  -> t:Type 
        -> { p_s_t:Subtype | propOf p_s_t  == Subtype (concatE (ConsT a k_a g) g') s t && isSBase p_s_t }
        -> {p'_s_t:Subtype | propOf p'_s_t == Subtype (concatE g (esubFTV a t_a g')) 
                                                      (tsubFTV a t_a s) (tsubFTV a t_a t) &&
                             sizeOf p'_s_t <= sizeOf p_s_t + 2 * tdepth t_a + 0 } / [subtypSize p_s_t, 0] @-}
lem_subst_tv_sub_sbase :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Type {-> Kind -> WFType-} -> Type {-> Kind -> WFType-} -> Subtype -> Subtype
lem_subst_tv_sub_sbase g g' a t_a k_a p_g_ta p_g_wf s {-k_s p_env_s-} t {-k_t p_env_t -}
                       p_s_t@(SBase env b p1 p2 nms mk_imp_p1_p2) = case b of
  (FTV a1) | a1 == a -> case t_a of -- b' could be FTV here
    (TRefn b' qs)   -> lem_subst_tv_sub_sbase_ftv g g' a b' qs k_a p_g_ta p_g_wf 
                                                  p1 {-k_s p_env_s-} p2 {-k_t p_env_t-} p_s_t
    (TFunc  t_x t') -> lem_sub_refl (concatE g (esubFTV a t_a g')) t_a k_a p_env'_ta
                           ? toProof ( tsubFTV a t_a (TRefn (FTV a) p1)
                                   === push (psubFTV a t_a p1) (TFunc t_x t') === TFunc t_x t' )
                           ? toProof ( tsubFTV a t_a (TRefn (FTV a) p2)
                                   === push (psubFTV a t_a p2) (TFunc t_x t') === TFunc t_x t' )
      where
        p_env'_ta = lem_weaken_many_wf g (esubFTV a t_a g')  t_a k_a p_g_ta 
    (TPoly   k0 t') -> lem_sub_refl (concatE g (esubFTV a t_a g')) t_a k_a p_env'_ta 
                           ? toProof ( tsubFTV a t_a (TRefn (FTV a) p1)
                                   === push (psubFTV a t_a p1) (TPoly k0 t') === TPoly k0 t' )
                           ? toProof ( tsubFTV a t_a (TRefn (FTV a) p2)
                                   === push (psubFTV a t_a p2) (TPoly k0 t') === TPoly k0 t' )
      where
        p_env'_ta = lem_weaken_many_wf g (esubFTV a t_a g')  t_a k_a p_g_ta 
  _                  -> SBase (concatE g (esubFTV a t_a g')) b (psubFTV a t_a p1) 
                              (psubFTV a t_a p2) nms' mk_imp_p1ta_p2ta
    where
      {-@ mk_imp_p1ta_p2ta  :: { y:Vname | NotElem y nms' }
            -> ProofOf(Implies (Cons y (TRefn b PEmpty) (concatE g (esubFTV a t_a g')))
                               (unbindP y (psubFTV a t_a p1)) (unbindP y (psubFTV a t_a p2))) @-}
      mk_imp_p1ta_p2ta y = ISubTV g (Cons y (TRefn b PEmpty) g') a t_a k_a p_g_ta
                                  (unbindP y p1) (unbindP y p2) (mk_imp_p1_p2 y)
                                  ? lem_commute_psubFTV_unbindP a
                                        (t_a ? lem_wftype_islct g t_a k_a p_g_ta) y p1
                                  ? lem_commute_psubFTV_unbindP a
                                        (t_a ? lem_wftype_islct g t_a k_a p_g_ta) y p2
                                  ? toProof ( tsubFTV a t_a (TRefn b PEmpty)
                                          === TRefn b (psubFTV a t_a PEmpty) === TRefn b PEmpty )
      nms'             = a:(unionEnv nms (concatE g g'))

{-@ lem_subst_tv_sub_sfunc :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv g ) -> s:Type  -> t:Type 
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (ConsT a k_a g) g') s t && isSFunc p_s_t }
        -> {p'_s_t:Subtype | propOf p'_s_t == Subtype (concatE g (esubFTV a t_a g')) 
                                                      (tsubFTV a t_a s) (tsubFTV a t_a t) &&
                             sizeOf p'_s_t <= sizeOf p_s_t + 2 * tdepth t_a + 0 } / [subtypSize p_s_t, 0] @-}
lem_subst_tv_sub_sfunc :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Type {-> Kind -> WFType-} -> Type {-> Kind -> WFType-} -> Subtype -> Subtype
lem_subst_tv_sub_sfunc g g' a t_a k_a p_g_ta p_g_wf ty1 {-ky1 p_env_ty1-} ty2 {-ky2 p_env_ty2-}
                       (SFunc n env s1 s2 p_s2_s1 t1 t2 nms mk_p_yenv_t1_t2) 
  = SFunc n' (concatE g (esubFTV a t_a g')) (tsubFTV a t_a s1)  (tsubFTV a t_a s2)
          p_s2ta_s1ta (tsubFTV a t_a t1) (tsubFTV a t_a t2) nms' mk_p_yg'g_t1ta_t2ta
      where 
        {-@ mk_p_yg'g_t1ta_t2ta :: { y:Vname | NotElem y nms' }
              -> { pf:Subtype | propOf pf ==
                      Subtype (Cons y (tsubFTV a t_a s2) (concatE g (esubFTV a t_a g')))
                              (unbindT y (tsubFTV a t_a t1)) (unbindT y (tsubFTV a t_a t2)) &&
                                sizeOf pf <= n + 2 * tdepth t_a + 0 } @-}
        mk_p_yg'g_t1ta_t2ta y = lem_subst_tv_sub g (Cons y s2 g') a t_a k_a p_g_ta p_g_wf
                                            (unbindT y t1) {-k_t1 p_yenv_t1 -}
                                            (unbindT y t2) {-k_t2 p_yenv_t2 -} (mk_p_yenv_t1_t2 y)
                                            ? lem_commute_tsubFTV_unbindT a
                                                  (t_a ? lem_wftype_islct g t_a k_a p_g_ta) y t1
                                            ? lem_commute_tsubFTV_unbindT a
                                                  (t_a ? lem_wftype_islct g t_a k_a p_g_ta) y t2
        p_s2ta_s1ta      = lem_subst_tv_sub g g' a t_a k_a p_g_ta p_g_wf 
                                            s2 {-k_s2 p_env_s2-} s1 {-k_s1 p_env_s1-} p_s2_s1 
        nms'             = a:(unionEnv nms (concatE g g'))
        n'               = n + 2 * tdepth t_a + 0

{-@ lem_subst_tv_sub_switn :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv g ) -> s:Type  -> t:Type 
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (ConsT a k_a g) g') s t && isSWitn p_s_t}
        -> {p'_s_t:Subtype | propOf p'_s_t == Subtype (concatE g (esubFTV a t_a g')) 
                                                      (tsubFTV a t_a s) (tsubFTV a t_a t) &&
                             sizeOf p'_s_t <= sizeOf p_s_t + 2 * tdepth t_a + 0 } / [subtypSize p_s_t, 0] @-}
lem_subst_tv_sub_switn :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Type {-> Kind -> WFType-} -> Type {-> Kind -> WFType-} -> Subtype -> Subtype
lem_subst_tv_sub_switn g g' a t_a k_a p_g_ta p_g_wf t {-k p_env_t-} t2 {-k2 p_env_t2-}
                       (SWitn n env v_z t_z p_env_vz_tz _t t' p_env_t_t'vz)
  = SWitn n' (concatE g (esubFTV a t_a g')) (subFTV a t_a v_z) (tsubFTV a t_a t_z) p_g'g_vzta_tzta
          (tsubFTV a t_a t) (tsubFTV a t_a t') p_g'g_tta_t'vzta
      where
        p_g'g_vzta_tzta  = lem_subst_tv_typ g g' a t_a k_a p_g_ta p_g_wf v_z t_z p_env_vz_tz
        p_g'g_tta_t'vzta = lem_subst_tv_sub g g' a t_a k_a p_g_ta p_g_wf t {-k p_env_t -}
                              (tsubBV v_z t') {-k' p_env_t'vz-} p_env_t_t'vz
                              ? lem_commute_tsubFTV_tsubBV v_z a 
                                    (t_a ? lem_wftype_islct g t_a k_a p_g_ta) t'
        n'               = n + 2 * tdepth t_a + 0

{-@ lem_subst_tv_sub_sbind :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv g ) -> s:Type  -> t:Type 
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (ConsT a k_a g) g') s t && isSBind p_s_t }
        -> {p'_s_t:Subtype | propOf p'_s_t == Subtype (concatE g (esubFTV a t_a g')) 
                                                      (tsubFTV a t_a s) (tsubFTV a t_a t) &&
                             sizeOf p'_s_t <= sizeOf p_s_t + 2 * tdepth t_a + 0 } / [subtypSize p_s_t, 0] @-}
lem_subst_tv_sub_sbind :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Type {-> Kind -> WFType-} -> Type {-> Kind -> WFType-} -> Subtype -> Subtype
lem_subst_tv_sub_sbind g g' a t_a k_a p_g_ta p_g_wf t1 {-k1 p_env_t1-} t' {-k' p_env_t'-}
                       (SBind n env t_z t _t' nms mk_p_wenv_t_t') 
  = SBind n' (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t_z) (tsubFTV a t_a t) 
          (tsubFTV a t_a t' ? lem_islct_at_tsubFTV 0 0 a
                                 (t_a ? lem_wftype_islct g t_a k_a p_g_ta) t')
          nms' mk_p_wenv'_tta_t'ta
      where 
        {-@ mk_p_wenv'_tta_t'ta :: { w:Vname | NotElem w nms'}
              -> { pf:Subtype | propOf pf ==
                      Subtype (Cons w (tsubFTV a t_a t_z) (concatE g (esubFTV a t_a g')))
                              (unbindT w (tsubFTV a t_a t)) (tsubFTV a t_a t') &&
                                sizeOf pf <= n + 2 * tdepth t_a + 0 } @-}
        mk_p_wenv'_tta_t'ta w = lem_subst_tv_sub g (Cons w t_z g') a t_a k_a p_g_ta p_g_wf
                                         (unbindT w t) {-k p_wenv_t-} t' {-k' p_wenv_t'-} 
                                         (mk_p_wenv_t_t' w)
                                         ? lem_commute_tsubFTV_unbindT a
                                             (t_a ? lem_wftype_islct g t_a k_a p_g_ta) w t
        nms'                  = a:(unionEnv nms (concatE g g'))
        n'                    = n + 2 * tdepth t_a + 0

{-@ lem_subst_tv_sub_spoly :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv g ) -> s:Type  -> t:Type 
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (ConsT a k_a g) g') s t && isSPoly p_s_t }
        -> {p'_s_t:Subtype | propOf p'_s_t == Subtype (concatE g (esubFTV a t_a g')) 
                                                      (tsubFTV a t_a s) (tsubFTV a t_a t) &&
                             sizeOf p'_s_t <= sizeOf p_s_t + 2 * tdepth t_a + 0 } / [subtypSize p_s_t, 0] @-}
lem_subst_tv_sub_spoly :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Type {-> Kind -> WFTypr-} -> Type {-> Kind -> WFType-} -> Subtype -> Subtype
lem_subst_tv_sub_spoly g g' a t_a k_a p_g_ta p_g_wf t1 {-k1 p_env_t1-} t2 {-k2 p_env_t2 -}
                       (SPoly n env k' t1' t2' nms mk_p_a1env_t1'_t2') 
  = SPoly n' (concatE g (esubFTV a t_a g')) k' (tsubFTV a t_a t1') (tsubFTV a t_a t2')
          nms' mk_p_a1g'g_t1'ta_t2'ta
      where
        {-@ mk_p_a1g'g_t1'ta_t2'ta :: { a1:Vname | NotElem a1 nms' }
              -> { pf:Subtype | propOf pf ==
                      Subtype (ConsT a1 k' (concatE g (esubFTV a t_a g')))
                              (unbind_tvT a1 (tsubFTV a t_a t1')) (unbind_tvT a1 (tsubFTV a t_a t2')) &&
                                sizeOf pf <= n + 2 * tdepth t_a + 0 } @-}
        mk_p_a1g'g_t1'ta_t2'ta a1 = lem_subst_tv_sub g (ConsT a1 k' g') a t_a k_a p_g_ta p_g_wf
                                      (unbind_tvT a1 t1') {-k_t1' p_a1'env_t1'-}
                                      (unbind_tvT a1 t2') {-k_t2' p_a1'env_t2'-} (mk_p_a1env_t1'_t2' a1)
                                      ? lem_commute_tsubFTV_unbind_tvT a
                                          (t_a ? lem_wftype_islct g t_a k_a p_g_ta) a1 t1'
                                      ? lem_commute_tsubFTV_unbind_tvT a 
                                          (t_a ? lem_wftype_islct g t_a k_a p_g_ta) a1 t2'
        nms'                  = a:(unionEnv nms (concatE g g'))
        n'                    = n + 2 * tdepth t_a + 0

{-@ lem_subst_tv_sub :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv g ) -> s:Type  -> t:Type 
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (ConsT a k_a g) g') s t }
        -> {p'_s_t:Subtype | propOf p'_s_t == Subtype (concatE g (esubFTV a t_a g')) 
                                                      (tsubFTV a t_a s) (tsubFTV a t_a t) &&
                             sizeOf p'_s_t <= sizeOf p_s_t + 2 * tdepth t_a + 0 } / [subtypSize p_s_t, 1] @-}
lem_subst_tv_sub :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Type {-> Kind -> WFType-} -> Type {-> Kind -> WFType-} -> Subtype -> Subtype
lem_subst_tv_sub g g' a t_a k_a p_g_ta p_g_wf s {-k_s p_env_s-} t {-k_t p_env_t-} p_t_t'@(SBase {}) 
  = lem_subst_tv_sub_sbase g g' a t_a k_a p_g_ta p_g_wf s {-k_s p_env_s-} t {-k_t p_env_t-} p_t_t'
lem_subst_tv_sub g g' a t_a k_a p_g_ta p_g_wf ty1 {-ky1 p_env_ty1-} ty2 {-ky2 p_env_ty2-}
                 p_t_t'@(SFunc {}) 
  = lem_subst_tv_sub_sfunc g g' a t_a k_a p_g_ta p_g_wf ty1 {-ky1 p_env_ty1-} ty2 {-ky2 p_env_ty2-} p_t_t'
lem_subst_tv_sub g g' a t_a k_a p_g_ta p_g_wf t {-k p_env_t-} t2 {-k2 p_env_t2-} p_t_t'@(SWitn {}) 
  = lem_subst_tv_sub_switn g g' a t_a k_a p_g_ta p_g_wf t {-k p_env_t-} t2 {-k2 p_env_t2-} p_t_t'
lem_subst_tv_sub g g' a t_a k_a p_g_ta p_g_wf t1 {-k1 p_env_t1-} t' {-k' p_env_t'-} p_t_t'@(SBind {}) 
  = lem_subst_tv_sub_sbind g g' a t_a k_a p_g_ta p_g_wf t1 {-k1 p_env_t1-} t' {-k' p_env_t'-} p_t_t'
lem_subst_tv_sub g g' a t_a k_a p_g_ta p_g_wf t1 {-k1 p_env_t1-} t2 {-k2 p_env_t2-} p_t_t'@(SPoly {})
  = lem_subst_tv_sub_spoly g g' a t_a k_a p_g_ta p_g_wf t1 {-k1 p_env_t1-} t2 {-k2 p_env_t2-} p_t_t'
