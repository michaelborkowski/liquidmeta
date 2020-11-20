{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SubstitutionLemmaWFTV where

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
import SystemFLemmasWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasSubstitution
import Typing
import SystemFAlphaEquivalence
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

{-@ reflect foo49 @-}
foo49 x = Just x
foo49 :: a -> Maybe a

-- -- -- -- -- -- -- -- -- -- -- ---
-- Part of the Substitution Lemma --
-- -- -- -- -- -- -- -- -- -- -- ---
 
{-@ lem_subst_tv_wf_wfrefn :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:Type
          -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
          -> ProofOf(WFFE (concatF (FConsT a k_a (erase_env g)) (erase_env g')) )
          -> { t:Type | same_binders t_a t || isTrivial t } -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (ConsT a k_a g) g') t k && isWFRefn p_env_t}
          -> ProofOf(WFType (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k) / [wftypSize p_env_t, 0] @-}
lem_subst_tv_wf_wfrefn :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFFE 
                    -> Type -> Kind -> WFType -> WFType
lem_subst_tv_wf_wfrefn g g' a t_a k_a p_g_ta p_env_wf t k p_env_t@(WFRefn env z b p_env_b p y_ p_env'_p_bl)
  = case b of                                                -- t = TRefn b z p
      (FTV a'_) | (a == a'_) -> case k_a of                    -- t = TRefn (FTV a) z p
        Base -> if p == Bc True then p_gg'ta_ta else
                    lem_push_wf (concatE g (esubFTV a t_a g')) t_a Base p_gg'ta_ta
                            z (subFTV a t_a p ? lem_same_bindersE_subFTV t_a a 
                                                  (t_a ? lem_same_binders_refl t_a t) 
                                      p) y pf_pta_bl 
          where
            y          = y_ ? lem_in_env_esubFTV g' a t_a y_
                            ? lem_in_env_concat g  g' y_
                            ? lem_in_env_concat (ConsT a k_a g) g' y_
                            ? lem_free_bound_in_env g t_a k_a p_g_ta y_
            p_er_g_ta  = lem_erase_wftype  g t_a k_a p_g_ta
            p_g'tag_wf = lem_subst_tv_wffe (erase_env g) (erase_env g') a (erase t_a) k_a 
                                             p_er_g_ta p_env_wf ? lem_erase_esubFTV a t_a g'
            p_gg'ta_ta = lem_weaken_many_wf g (esubFTV a t_a g') p_g'tag_wf t_a k_a p_g_ta
                                              ? lem_tsubFTV_trivial a t_a 1 
            p_env_er_b = lem_erase_wftype env (TRefn b 1 (Bc True)) Base p_env_b
            p_g_er_ta  = lem_erase_wftype g t_a k_a p_g_ta
            p_er_yenv_wf = WFFBind (erase_env env) (p_env_wf ? lem_erase_concat (ConsT a k_a g) g') 
                                   y (FTBasic b) Base p_env_er_b 
            pf_pta_bl  = lem_subst_tv_ftyp (erase_env g) (FCons y (FTBasic b) (erase_env g'))
                           (a ? lem_in_env_concatF (erase_env g) (erase_env g') a
                              ? lem_in_env_concatF (erase_env g) (FCons y (FTBasic b) (erase_env g')) a)
                           t_a k_a p_g_er_ta p_er_yenv_wf (unbind z y p) (FTBasic TBool) 
                           (p_env'_p_bl ? lem_erase_concat (ConsT a k_a g) g')
                           ? lem_commute_subFTV_unbind a (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta)
                               z y p
                           ? lem_erase_concat g (esubFTV a t_a g')
                           ? lem_erase_esubFTV a t_a g'  
        Star -> impossible ("by lemma" ? lem_kind_for_tv g g' a k_a
                                       ? lem_wf_ftv_kind (concatE (ConsT a k_a g) g') a k p_env_b)
  {- FTV a'_ -} | otherwise  -> WFRefn (concatE g (esubFTV a t_a g')) z (FTV a') p_gg'_b (subFTV a t_a p)
                                     y p_ygg'_pta_bl 
          where
            y             = y_ ? lem_in_env_esubFTV g' a t_a y_
                               ? lem_in_env_concat g  g' y_
                               ? lem_in_env_concat (ConsT a k_a g) g' y_
                               ? lem_free_bound_in_env g t_a k_a p_g_ta y_
            a'            = a'_ ? lem_in_env_esubFTV g' a t_a a'_
                                ? lem_in_env_concat g g' a'_
                                ? lem_in_env_concat (ConsT a k_a g) g' a'_
                                ? lem_in_env_concat g (esubFTV a t_a g') a'_
            p_gg'_b       = lem_subst_tv_wf g g' a t_a k_a p_g_ta p_env_wf 
                                            (TRefn (FTV a') 1 (Bc True)) Base p_env_b
            p_ag_wf       = lem_truncate_wffe (FConsT a k_a (erase_env g)) (erase_env g') p_env_wf
            (WFFBindT _ p_g_wf _ _) = p_ag_wf
            p_env_er_b    = lem_erase_wftype env (TRefn b 1 (Bc True)) Base p_env_b
            p_g_er_ta     = lem_erase_wftype g t_a k_a p_g_ta
            p_er_yenv_wf  = WFFBind (erase_env env) (p_env_wf ? lem_erase_concat (ConsT a k_a g) g')
                                    y (FTBasic b) Base p_env_er_b 
            p_ygg'_pta_bl = lem_subst_tv_ftyp (erase_env g) (FCons y (FTBasic b) (erase_env g')) 
                               (a ? lem_in_env_concatF (erase_env g) (erase_env g') a
                                  ? lem_in_env_concatF (erase_env g) (FCons y (FTBasic b) (erase_env g')) a)
                               t_a k_a p_g_er_ta p_er_yenv_wf (unbind z y p) (FTBasic TBool)
                               (p_env'_p_bl ? lem_erase_concat (ConsT a k_a g) g')
                               ? lem_commute_subFTV_unbind a (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta)
                                   z y p
                               ? lem_erase_concat g (esubFTV a t_a g')
                               ? lem_erase_esubFTV a t_a g'
      (BTV a')             -> impossible ("by lemma" ? lem_btv_not_wf env a' 1 (Bc True) Base p_env_b)
      _                    -> WFRefn (concatE g (esubFTV a t_a g')) z b p_gg'_b (subFTV a t_a p) 
                                     y p_ygg'_pta_bl 
        where
          y             = y_ ? lem_in_env_esubFTV g' a t_a y_
                             ? lem_in_env_concat g  g' y_
                             ? lem_in_env_concat (ConsT a k_a g) g' y_
                             ? lem_free_bound_in_env g t_a k_a p_g_ta y_
          p_gg'_b       = WFBase (concatE g (esubFTV a t_a g')) b
          p_ag_wf       = lem_truncate_wffe (FConsT a k_a (erase_env g)) (erase_env g') p_env_wf
          (WFFBindT _ p_g_wf _ _) = p_ag_wf
          p_env_er_b    = lem_erase_wftype env (TRefn b 1 (Bc True)) Base p_env_b
          p_g_er_ta     = lem_erase_wftype g t_a k_a p_g_ta
          p_er_yenv_wf  = WFFBind (erase_env env) (p_env_wf ? lem_erase_concat (ConsT a k_a g) g')
                                  y (FTBasic b) Base p_env_er_b 
          p_ygg'_pta_bl = lem_subst_tv_ftyp (erase_env g) (FCons y (FTBasic b) (erase_env g')) 
                             (a ? lem_in_env_concatF (erase_env g) (erase_env g') a
                                ? lem_in_env_concatF (erase_env g) (FCons y (FTBasic b) (erase_env g')) a)
                             t_a k_a p_g_er_ta p_er_yenv_wf (unbind z y p) (FTBasic TBool)
                             (p_env'_p_bl ? lem_erase_concat (ConsT a k_a g) g')
                             ? lem_commute_subFTV_unbind a (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta)
                                 z y p
                             ? lem_erase_concat g (esubFTV a t_a g')
                             ? lem_erase_esubFTV a t_a g'

{-@ lem_subst_tv_wf_wfvar :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:Type
          -> k_a:Kind -> ProofOf(WFType g t_a k_a)
          -> ProofOf(WFFE (concatF (FConsT a k_a (erase_env g)) (erase_env g')) )
          -> { t:Type | same_binders t_a t || isTrivial t } -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (ConsT a k_a g) g') t k && isWFVar p_env_t }
          -> ProofOf(WFType (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k) / [wftypSize p_env_t, 0] @-}
lem_subst_tv_wf_wfvar :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFFE 
                           -> Type -> Kind -> WFType -> WFType
lem_subst_tv_wf_wfvar g g' a t_a k_a p_g_ta p_env_wf t k (WFVar1 _env' a' k_a') 
  = case g' of
      Empty {- a == a' -}  -> p_g_ta ? lem_tsubFTV_trivial a t_a 1
      (ConsT _a' _ka' g'') -> WFVar1 (concatE g (esubFTV a t_a g''))
                                     (a' ? lem_in_env_esubFTV g'' a t_a a'
                                         ? lem_in_env_concat g g'' a'
                                         ? lem_in_env_concat (ConsT a k_a g) g'' a') k_a'
lem_subst_tv_wf_wfvar g g' a t_a k_a p_g_ta p_env_wf t k p_g_t@(WFVar2 _env' a'_ k_a' p_env'_a' y_ t_y) 
  = case g' of 
      Empty             -> impossible "a <> y"
      (Cons _y _ty g'') -> case ( a == a'_ ) of 
        True -> case ( k_a , k) of
          (Base, Star) -> WFKind (concatE g (esubFTV a t_a g')) t_a p_env''_ta
            where
              p_er_g_ta  = lem_erase_wftype  g t_a k_a p_g_ta
              p_g'tag_wf = lem_subst_tv_wffe (erase_env g) (erase_env g') a (erase t_a) k_a 
                                             p_er_g_ta p_env_wf ? lem_erase_esubFTV a t_a g'
              p_env''_ta = lem_weaken_many_wf g (esubFTV a t_a g') p_g'tag_wf t_a k_a p_g_ta
                                              ? lem_tsubFTV_trivial a t_a 1 
          (Star, Base) -> impossible ("by lemma" ? lem_kind_for_tv g g' a k_a
                                                 ? lem_wf_ftv_kind (concatE (ConsT a k_a g) g') a k p_g_t)
          _            -> lem_weaken_many_wf g (esubFTV a t_a g') p_g'tag_wf t_a k_a p_g_ta
                                             ? lem_tsubFTV_trivial a t_a 1
            where
              p_er_g_ta  = lem_erase_wftype  g t_a k_a p_g_ta
              p_g'tag_wf = lem_subst_tv_wffe (erase_env g) (erase_env g') a (erase t_a) k_a 
                                             p_er_g_ta p_env_wf ? lem_erase_esubFTV a t_a g' 
        False -> WFVar2 (concatE g (esubFTV a t_a g'')) a' k_a' p_gg''_a' y (tsubFTV a t_a t_y)
          where
            (WFFBind _ p_env'_wf _ _ _ _) = p_env_wf
            a'        = a'_ ? lem_in_env_esubFTV g'' a t_a a'_
                            ? lem_in_env_concat g g'' a'_
                            ? lem_in_env_concat (ConsT a k_a g) g'' a'_
                            ? lem_in_env_concat g (esubFTV a t_a g'') a'_
            y         = y_ ? lem_in_env_esubFTV g'' a t_a y_
                           ? lem_in_env_concat g g'' y_
                           ? lem_in_env_concat (ConsT a k_a g) g'' y_
                           ? lem_free_bound_in_env g t_a k_a p_g_ta y_
            p_gg''_a' = lem_subst_tv_wf g g'' a t_a k_a p_g_ta p_env'_wf 
                                        (TRefn (FTV a') 1 (Bc True)) k_a' p_env'_a'
lem_subst_tv_wf_wfvar g g' a t_a k_a p_g_ta p_env_wf t k p_g_t@(WFVar3 _env' a'_ k_a' p_env'_a' a1_ k_a1) 
  = case g' of
      Empty {- a == a1 -} -> p_env'_a'
      (ConsT _a1 _k1 g'') -> case ( a == a'_ ) of 
        True -> case ( k_a , k) of
          (Base, Star) -> WFKind (concatE g (esubFTV a t_a g')) t_a p_env''_ta
            where
              p_er_g_ta  = lem_erase_wftype  g t_a k_a p_g_ta
              p_g'tag_wf = lem_subst_tv_wffe (erase_env g) (erase_env g') a (erase t_a) k_a 
                                             p_er_g_ta p_env_wf ? lem_erase_esubFTV a t_a g'
              p_env''_ta = lem_weaken_many_wf g (esubFTV a t_a g') p_g'tag_wf t_a k_a p_g_ta
                                              ? lem_tsubFTV_trivial a t_a 1 
          (Star, Base) -> impossible ("by lemma" ? lem_kind_for_tv g g' a k_a
                                                 ? lem_wf_ftv_kind (concatE (ConsT a k_a g) g') a k p_g_t)
          _            -> lem_weaken_many_wf g (esubFTV a t_a g') p_g'tag_wf t_a k_a p_g_ta
                                             ? lem_tsubFTV_trivial a t_a 1
            where
              p_er_g_ta  = lem_erase_wftype  g t_a k_a p_g_ta
              p_g'tag_wf = lem_subst_tv_wffe (erase_env g) (erase_env g') a (erase t_a) k_a 
                                             p_er_g_ta p_env_wf ? lem_erase_esubFTV a t_a g' 
        False -> WFVar3 (concatE g (esubFTV a t_a g'')) a' k_a' p_gg''_a' a1 k_a1
          where
            (WFFBindT _ p_env'_wf _ _) = p_env_wf
            a'        = a'_ ? lem_in_env_esubFTV g'' a t_a a'_
                            ? lem_in_env_concat g g'' a'_
                            ? lem_in_env_concat (ConsT a k_a g) g'' a'_
                            ? lem_in_env_concat g (esubFTV a t_a g'') a'_
            a1        = a1_ ? lem_in_env_esubFTV g'' a t_a a1_
                            ? lem_in_env_concat g g'' a1_
                            ? lem_in_env_concat (ConsT a k_a g) g'' a1_
                            ? lem_free_bound_in_env g t_a k_a p_g_ta a1_
            p_gg''_a' = lem_subst_tv_wf g g'' a t_a k_a p_g_ta p_env'_wf 
                                        (TRefn (FTV a') 1 (Bc True)) k_a' p_env'_a' 

{-@ lem_subst_tv_wf_wffunc :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:Type
          -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
          -> ProofOf(WFFE (concatF (FConsT a k_a (erase_env g)) (erase_env g')) )  
          -> { t:Type | same_binders t_a t } -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (ConsT a k_a g) g') t k && isWFFunc p_env_t }
          -> ProofOf(WFType (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k) / [wftypSize p_env_t, 0] @-}
lem_subst_tv_wf_wffunc :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFFE 
                           -> Type -> Kind -> WFType -> WFType
lem_subst_tv_wf_wffunc g g' a t_a k_a p_g_ta p_env_wf t k (WFFunc env z t_z k_z p_env_tz t' k' y_ p_yenv_t')  
  = WFFunc (concatE g (esubFTV a t_a g')) z (tsubFTV a t_a t_z) k_z p_g'g_tzta
           (tsubFTV a t_a t') k' y p_yg'g_t'ta
      where
        y           = y_ ? lem_in_env_esubFTV g' a t_a y_ 
                         ? lem_in_env_concat g g' y_ 
                         ? lem_in_env_concat (ConsT a k_a g) g' y_
                         ? lem_free_bound_in_env g t_a k_a p_g_ta y_
        p_er_env_tz = lem_erase_wftype env t_z k_z p_env_tz ? lem_erase_concat (ConsT a k_a g) g'
        p_yenv_wf   = WFFBind (concatF (FConsT a k_a (erase_env g)) (erase_env g')) p_env_wf 
                              y (erase t_z) k_z p_er_env_tz
        p_g'g_tzta  = lem_subst_tv_wf g g'              a t_a k_a p_g_ta p_env_wf  t_z k_z p_env_tz
        p_yg'g_t'ta = lem_subst_tv_wf g (Cons y t_z g') a t_a k_a p_g_ta p_yenv_wf 
                         (unbindT z y t' ? lem_same_binders_tsubBV t_a z (FV y) t') k' p_yenv_t' 
                         ? lem_commute_tsubFTV_unbindT a (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta)
                               z y t' 

{-@ lem_subst_tv_wf_wfexis :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:Type
          -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
          -> ProofOf(WFFE (concatF (FConsT a k_a (erase_env g)) (erase_env g')) )  
          -> { t:Type | same_binders t_a t || isTrivial t } -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (ConsT a k_a g) g') t k && isWFExis p_env_t }
          -> ProofOf(WFType (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k) / [wftypSize p_env_t, 0] @-}
lem_subst_tv_wf_wfexis :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFFE 
                           -> Type -> Kind -> WFType -> WFType
lem_subst_tv_wf_wfexis g g' a t_a k_a p_g_ta p_env_wf t k (WFExis env z t_z k_z p_env_tz t' k' y_ p_yenv_t')  
  = WFExis (concatE g (esubFTV a t_a g')) z (tsubFTV a t_a t_z) k_z p_g'g_tzta
           (tsubFTV a t_a t') k' y p_yg'g_t'ta
      where
        y           = y_ ? lem_in_env_esubFTV g' a t_a y_ 
                         ? lem_in_env_concat g g' y_ 
                         ? lem_in_env_concat (ConsT a k_a g) g' y_
                         ? lem_free_bound_in_env g t_a k_a p_g_ta y_
        p_er_env_tz = lem_erase_wftype env t_z k_z p_env_tz ? lem_erase_concat (ConsT a k_a g) g'
        p_yenv_wf   = WFFBind (concatF (FConsT a k_a (erase_env g)) (erase_env g')) p_env_wf 
                              y (erase t_z) k_z p_er_env_tz
        p_g'g_tzta  = lem_subst_tv_wf g g'              a t_a k_a p_g_ta p_env_wf  t_z k_z p_env_tz
        p_yg'g_t'ta = lem_subst_tv_wf g (Cons y t_z g') a t_a k_a p_g_ta p_yenv_wf 
                         (unbindT z y t' ? lem_same_binders_tsubBV t_a z (FV y) t') k'
                         (p_yenv_t' {-? lem_erase_concat (Cons x t_x g) g'-})
                         ? lem_commute_tsubFTV_unbindT a (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta)
                               z y t'

{-@ lem_subst_tv_wf_wfpoly :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:Type
          -> k_a:Kind -> ProofOf(WFType g t_a k_a)
          -> ProofOf(WFFE (concatF (FConsT a k_a (erase_env g)) (erase_env g')) )
          -> { t:Type | same_binders t_a t || isTrivial t } -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (ConsT a k_a g) g') t k && isWFPoly p_env_t }
          -> ProofOf(WFType (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k) / [wftypSize p_env_t, 0] @-}
lem_subst_tv_wf_wfpoly :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFFE 
                              -> Type -> Kind -> WFType -> WFType
lem_subst_tv_wf_wfpoly g g' a t_a k_a p_g_ta p_env_wf t k (WFPoly _env a1 k_a1 t' k_t' a1'_ p_a1'env_t') 
  = WFPoly (concatE g (esubFTV a t_a g')) a1 k_a1 (tsubFTV a t_a t') k_t' a1' p_a1'gg'_t'
      where
        a1'         = a1'_ ? lem_in_env_esubFTV g' a t_a a1'_
                           ? lem_in_env_concat g  g' a1'_
                           ? lem_in_env_concat (ConsT a k_a g) g' a1'_
                           ? lem_free_bound_in_env g t_a k_a p_g_ta a1'_
        p_a1'env_wf = WFFBindT (concatF (FConsT a k_a (erase_env g)) (erase_env g')) p_env_wf a1' k_a1
                               ? lem_erase_concat (ConsT a k_a g) g'
        p_a1'gg'_t' = lem_subst_tv_wf g (ConsT a1' k_a1 g') a t_a k_a p_g_ta p_a1'env_wf
                          (unbind_tvT a1 a1' t' ? lem_same_binders_unbind_tvT t_a a1 a1' t') 
                          k_t' p_a1'env_t'
                          ? lem_commute_tsubFTV_unbind_tvT a (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta)
                               a1 a1' t'

{-@ lem_subst_tv_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:Type
          -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
          -> ProofOf(WFFE (concatF (FConsT a k_a (erase_env g)) (erase_env g')) ) 
          -> { t:Type | same_binders t_a t || isTrivial t } -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (ConsT a k_a g) g') t k }
          -> ProofOf(WFType (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k) / [wftypSize p_env_t, 1] @-}
lem_subst_tv_wf :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFFE 
                    -> Type -> Kind -> WFType -> WFType
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_env_wf t k (WFBase _env b)
  = WFBase (concatE g (esubFTV a t_a g')) b
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_env_wf t k p_e_t@(WFRefn {})
  = lem_subst_tv_wf_wfrefn g g' a t_a k_a p_g_ta p_env_wf t k p_e_t
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_env_wf t k p_e_t@(WFVar1 {})
  = lem_subst_tv_wf_wfvar g g' a t_a k_a p_g_ta p_env_wf t k p_e_t
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_env_wf t k p_e_t@(WFVar2 {})
  = lem_subst_tv_wf_wfvar g g' a t_a k_a p_g_ta p_env_wf t k p_e_t
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_env_wf t k p_e_t@(WFVar3 {})
  = lem_subst_tv_wf_wfvar g g' a t_a k_a p_g_ta p_env_wf t k p_e_t
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_env_wf t k p_e_t@(WFFunc {})
  = lem_subst_tv_wf_wffunc g g' a t_a k_a p_g_ta p_env_wf t k p_e_t
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_env_wf t k p_e_t@(WFExis {})
  = lem_subst_tv_wf_wfexis g g' a t_a k_a p_g_ta p_env_wf t k p_e_t
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_env_wf t k p_e_t@(WFPoly {})
  = lem_subst_tv_wf_wfpoly g g' a t_a k_a p_g_ta p_env_wf t k p_e_t
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_env_wf t k (WFKind _env _t p_env_t_base)
  = WFKind (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) p_gg'_tta_base
      where
        p_gg'_tta_base = lem_subst_tv_wf g g' a t_a k_a p_g_ta p_env_wf t Base p_env_t_base

-- the legacy version of TV substitution in WFType that takes WFEnv as a parameter
{-@ lem_subst_tv_wf' :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:Type
          -> k_a:Kind -> ProofOf(WFType g t_a k_a) -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) 
          -> { t:Type | same_binders t_a t || isTrivial t } -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (ConsT a k_a g) g') t k }
          -> ProofOf(WFType (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k) / [wftypSize p_env_t, 1] @-}
lem_subst_tv_wf' :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv 
                    -> Type -> Kind -> WFType -> WFType
lem_subst_tv_wf' g g' a t_a k_a p_g_ta p_env_wf t k p_e_t
  = lem_subst_tv_wf g g' a t_a k_a p_g_ta p_er_env_wf t k p_e_t 
      where
        p_er_env_wf = lem_erase_env_wfenv (concatE (ConsT a k_a g) g') p_env_wf
                                          ? lem_erase_concat (ConsT a k_a g) g'

-----------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
-----------------------------------------------------------

{-@ lem_witness_sub :: g:Env -> v_x:Value -> t_x:Type -> ProofOf(HasType g v_x t_x) 
        -> ProofOf(WFEnv g) -> x:Vname -> t':Type -> k':Kind 
        -> { y:Vname | not (in_env y g) && not (Set_mem y (free t')) && not (Set_mem y (freeTV t')) }
        -> ProofOf(WFType (Cons y t_x g) (unbindT x y t') k')
        -> ProofOf(Subtype g (tsubBV x v_x t') (TExists x t_x t')) @-}
lem_witness_sub :: Env -> Expr -> Type -> HasType -> WFEnv -> Vname -> Type -> Kind
                       -> Vname -> WFType -> Subtype
lem_witness_sub g v_x t_x p_vx_tx p_g_wf x t' k' y p_yg_t' 
  = SWitn g v_x t_x p_vx_tx (tsubBV x v_x t') x t' p_t'vx_t'vx
      where
      p_g_tx      = lem_typing_wf g v_x t_x p_vx_tx p_g_wf
      p_yg_wf     = WFEBind g p_g_wf y t_x Star p_g_tx
      p_g_t'vx    = lem_subst_wf' g Empty y v_x t_x p_vx_tx p_yg_wf (unbindT x y t') k' p_yg_t'
                                  ? lem_tsubFV_unbindT x y v_x t'
      p_t'vx_t'vx = lem_sub_refl g (tsubBV x v_x t') k' p_g_t'vx p_g_wf
