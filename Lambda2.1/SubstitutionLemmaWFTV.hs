{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SubstitutionLemmaWFTV where

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
import LemmasWeakenWFTV
import LemmasWellFormedness
import SubstitutionLemmaWF

{-@ reflect foo42 @-}
foo42 x = Just x
foo42 :: a -> Maybe a

-- -- -- -- -- -- -- -- -- -- -- ---
-- Part of the Substitution Lemma --
-- -- -- -- -- -- -- -- -- -- -- ---
 
{-@ lem_subst_tv_wf_wfrefn :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFFE (concatF (FConsT a k_a (erase_env g)) (erase_env g')) )
        -> t:Type -> k:Kind
        -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (ConsT a k_a g) g') t k && isWFRefn p_env_t}
        -> ProofOf(WFType (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k) / [wftypSize p_env_t, 0] @-}
lem_subst_tv_wf_wfrefn :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFFE 
                    -> Type -> Kind -> WFType -> WFType
lem_subst_tv_wf_wfrefn g g' a t_a k_a p_g_ta p_env_wf t k p_env_t@(WFRefn env z b tt p_env_b p y_ p_env'_p_bl)
  = case b of                                                -- t = TRefn b z p
      (FTV a'_) | (a == a'_) -> case k_a of                    -- t = TRefn (FTV a) z p
        Base -> if p == Bc True then p_gg'ta_ta else
                    lem_push_wf (concatE g (esubFTV a t_a g')) t_a {-Base-} p_gg'ta_ta
                            0 (subFTV a t_a p) y pf_pta_bl 
          where
            y          = y_ ? lem_in_env_esubFTV g' a t_a y_
                            ? lem_in_env_concat g  g' y_
                            ? lem_in_env_concat (ConsT a k_a g) g' y_
                            ? lem_free_bound_in_env g t_a k_a p_g_ta y_
            p_er_g_ta  = lem_erase_wftype  g t_a k_a p_g_ta
            p_g'tag_wf = lem_subst_tv_wffe (erase_env g) (erase_env g') a (erase t_a) k_a 
                                             p_er_g_ta p_env_wf ? lem_erase_esubFTV a t_a g'
            p_gg'ta_ta = lem_weaken_many_wf g (esubFTV a t_a g') p_g'tag_wf t_a k_a p_g_ta
                                            ? lem_subFTV_notin a t_a (tt ? lem_trivial_nofv tt)
            p_env_er_b = lem_erase_wftype env (TRefn b z tt) Base p_env_b
            p_g_er_ta  = lem_erase_wftype g t_a k_a p_g_ta
            p_er_yenv_wf = WFFBind (erase_env env) (p_env_wf ? lem_erase_concat (ConsT a k_a g) g') 
                                   y (FTBasic b) Base p_env_er_b 
            pf_pta_bl  = lem_subst_tv_ftyp (erase_env g) (FCons y (FTBasic b) (erase_env g'))
                           (a ? lem_in_env_concatF (erase_env g) (erase_env g') a
                              ? lem_in_env_concatF (erase_env g) (FCons y (FTBasic b) (erase_env g')) a)
                           t_a k_a p_g_er_ta p_er_yenv_wf (unbind 0 y p) (FTBasic TBool) 
                           (p_env'_p_bl ? lem_erase_concat (ConsT a k_a g) g')
                           ? lem_commute_subFTV_unbind a (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta)
                               0 y p
                           ? lem_erase_concat g (esubFTV a t_a g')
                           ? lem_erase_esubFTV a t_a g'  
        Star -> impossible ("by lemma" ? lem_kind_for_tv g g' a k_a
                                       ? lem_wf_ftv_kind (concatE (ConsT a k_a g) g') a tt k p_env_b)
  {- FTV a'_ -} | otherwise  -> WFRefn (concatE g (esubFTV a t_a g')) z (FTV a') tt p_gg'_b (subFTV a t_a p)
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
                                            (TRefn (FTV a') z tt) Base p_env_b
                                            ? lem_subFTV_notin a t_a (tt ? lem_trivial_nofv tt)
            p_ag_wf       = lem_truncate_wffe (FConsT a k_a (erase_env g)) (erase_env g') p_env_wf
            (WFFBindT _ p_g_wf _ _) = p_ag_wf
            p_env_er_b    = lem_erase_wftype env (TRefn b z tt) Base p_env_b
            p_g_er_ta     = lem_erase_wftype g t_a k_a p_g_ta
            p_er_yenv_wf  = WFFBind (erase_env env) (p_env_wf ? lem_erase_concat (ConsT a k_a g) g')
                                    y (FTBasic b) Base p_env_er_b 
            p_ygg'_pta_bl = lem_subst_tv_ftyp (erase_env g) (FCons y (FTBasic b) (erase_env g')) 
                               (a ? lem_in_env_concatF (erase_env g) (erase_env g') a
                                  ? lem_in_env_concatF (erase_env g) (FCons y (FTBasic b) (erase_env g')) a)
                               t_a k_a p_g_er_ta p_er_yenv_wf (unbind 0 y p) (FTBasic TBool)
                               (p_env'_p_bl ? lem_erase_concat (ConsT a k_a g) g')
                               ? lem_commute_subFTV_unbind a (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta)
                                   0 y p
                               ? lem_erase_concat g (esubFTV a t_a g')
                               ? lem_erase_esubFTV a t_a g'
      (BTV a')             -> impossible ("by lemma" ? lem_btv_not_wf env a' z tt Base p_env_b)
      _                    -> WFRefn (concatE g (esubFTV a t_a g')) z b tt p_gg'_b (subFTV a t_a p) 
                                     y p_ygg'_pta_bl ? lem_subFTV_notin a t_a (tt ? lem_trivial_nofv tt)
        where
          y             = y_ ? lem_in_env_esubFTV g' a t_a y_
                             ? lem_in_env_concat g  g' y_
                             ? lem_in_env_concat (ConsT a k_a g) g' y_
                             ? lem_free_bound_in_env g t_a k_a p_g_ta y_
          p_gg'_b       = WFBase (concatE g (esubFTV a t_a g')) b 
                                 tt ? lem_subFTV_notin a t_a (tt ? lem_trivial_nofv tt)
          p_ag_wf       = lem_truncate_wffe (FConsT a k_a (erase_env g)) (erase_env g') p_env_wf
          (WFFBindT _ p_g_wf _ _) = p_ag_wf
          p_env_er_b    = lem_erase_wftype env (TRefn b z tt) Base p_env_b
          p_g_er_ta     = lem_erase_wftype g t_a k_a p_g_ta
          p_er_yenv_wf  = WFFBind (erase_env env) (p_env_wf ? lem_erase_concat (ConsT a k_a g) g')
                                  y (FTBasic b) Base p_env_er_b 
          p_ygg'_pta_bl = lem_subst_tv_ftyp (erase_env g) (FCons y (FTBasic b) (erase_env g')) 
                             (a ? lem_in_env_concatF (erase_env g) (erase_env g') a
                                ? lem_in_env_concatF (erase_env g) (FCons y (FTBasic b) (erase_env g')) a)
                             t_a k_a p_g_er_ta p_er_yenv_wf (unbind 0 y p) (FTBasic TBool)
                             (p_env'_p_bl ? lem_erase_concat (ConsT a k_a g) g')
                             ? lem_commute_subFTV_unbind a (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta)
                                 0 y p
                             ? lem_erase_concat g (esubFTV a t_a g')
                             ? lem_erase_esubFTV a t_a g'

{-@ lem_subst_tv_wf_wfvar :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
          -> k_a:Kind -> ProofOf(WFType g t_a k_a)
          -> ProofOf(WFFE (concatF (FConsT a k_a (erase_env g)) (erase_env g')) )
          -> t:Type -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (ConsT a k_a g) g') t k && isWFVar p_env_t }
          -> ProofOf(WFType (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k) / [wftypSize p_env_t, 0] @-}
lem_subst_tv_wf_wfvar :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFFE 
                           -> Type -> Kind -> WFType -> WFType
lem_subst_tv_wf_wfvar g g' a t_a k_a p_g_ta p_env_wf t k (WFVar1 _env' a' tt k_a') 
  = case g' of
      Empty {- a == a' -}  -> p_g_ta ? lem_subFTV_notin a t_a (tt ? lem_trivial_nofv tt)
      (ConsT _a' _ka' g'') -> WFVar1 (concatE g (esubFTV a t_a g''))
                                     (a' ? lem_in_env_esubFTV g'' a t_a a'
                                         ? lem_in_env_concat g g'' a'
                                         ? lem_in_env_concat (ConsT a k_a g) g'' a') 
                                     (tt ? lem_subFTV_notin a t_a (tt ? lem_trivial_nofv tt)) k_a'
lem_subst_tv_wf_wfvar g g' a t_a k_a p_g_ta p_env_wf t k p_g_t@(WFVar2 _env' a'_ tt k_a' p_env'_a' y_ t_y) 
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
                                              ? lem_subFTV_notin a t_a (tt ? lem_trivial_nofv tt)
          (Star, Base) -> impossible ("by lemma" ? lem_kind_for_tv g g' a k_a
                                                 ? lem_wf_ftv_kind (concatE (ConsT a k_a g) g') a tt k p_g_t)
          _            -> lem_weaken_many_wf g (esubFTV a t_a g') p_g'tag_wf t_a k_a p_g_ta
                                             ? lem_subFTV_notin a t_a (tt ? lem_trivial_nofv tt)
            where
              p_er_g_ta  = lem_erase_wftype  g t_a k_a p_g_ta
              p_g'tag_wf = lem_subst_tv_wffe (erase_env g) (erase_env g') a (erase t_a) k_a 
                                             p_er_g_ta p_env_wf ? lem_erase_esubFTV a t_a g' 
        False -> WFVar2 (concatE g (esubFTV a t_a g'')) a' tt k_a' p_gg''_a' y (tsubFTV a t_a t_y)
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
                                        (TRefn (FTV a') Z tt) k_a' p_env'_a'
                                        ? lem_subFTV_notin a t_a (tt ? lem_trivial_nofv tt)
lem_subst_tv_wf_wfvar g g' a t_a k_a p_g_ta p_env_wf t k p_g_t@(WFVar3 _env' a'_ tt k_a' p_env'_a' a1_ k_a1) 
  = case g' of
      Empty {- a == a1 -} -> p_env'_a' ? lem_subFTV_notin a t_a (tt ? lem_trivial_nofv tt)
      (ConsT _a1 _k1 g'') -> case ( a == a'_ ) of 
        True -> case ( k_a , k) of
          (Base, Star) -> WFKind (concatE g (esubFTV a t_a g')) t_a p_env''_ta
            where
              p_er_g_ta  = lem_erase_wftype  g t_a k_a p_g_ta
              p_g'tag_wf = lem_subst_tv_wffe (erase_env g) (erase_env g') a (erase t_a) k_a 
                                             p_er_g_ta p_env_wf ? lem_erase_esubFTV a t_a g'
              p_env''_ta = lem_weaken_many_wf g (esubFTV a t_a g') p_g'tag_wf t_a k_a p_g_ta
                                              ? lem_subFTV_notin a t_a (tt ? lem_trivial_nofv tt)
          (Star, Base) -> impossible ("by lemma" ? lem_kind_for_tv g g' a k_a
                                                 ? lem_wf_ftv_kind (concatE (ConsT a k_a g) g') a tt k p_g_t)
          _            -> lem_weaken_many_wf g (esubFTV a t_a g') p_g'tag_wf t_a k_a p_g_ta
                                             ? lem_subFTV_notin a t_a (tt ? lem_trivial_nofv tt)
            where
              p_er_g_ta  = lem_erase_wftype  g t_a k_a p_g_ta
              p_g'tag_wf = lem_subst_tv_wffe (erase_env g) (erase_env g') a (erase t_a) k_a 
                                             p_er_g_ta p_env_wf ? lem_erase_esubFTV a t_a g' 
        False -> WFVar3 (concatE g (esubFTV a t_a g'')) a' tt k_a' p_gg''_a' a1 k_a1
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
                                        (TRefn (FTV a') Z tt) k_a' p_env'_a' 
                                        ? lem_subFTV_notin a t_a (tt ? lem_trivial_nofv tt)

{-@ lem_subst_tv_wf_wffunc :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
          -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
          -> ProofOf(WFFE (concatF (FConsT a k_a (erase_env g)) (erase_env g')) )  
          -> t:Type -> k:Kind
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
                         (unbindT z y t') k' p_yenv_t' 
                         ? lem_commute_tsubFTV_unbindT a (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta)
                               z y t' 

{-@ lem_subst_tv_wf_wfexis :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
          -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
          -> ProofOf(WFFE (concatF (FConsT a k_a (erase_env g)) (erase_env g')) )  
          -> t:Type -> k:Kind
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
                         (unbindT z y t') k' (p_yenv_t' {-? lem_erase_concat (Cons x t_x g) g'-})
                         ? lem_commute_tsubFTV_unbindT a (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta)
                               z y t'

{-@ lem_subst_tv_wf_wfpoly :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
          -> k_a:Kind -> ProofOf(WFType g t_a k_a)
          -> ProofOf(WFFE (concatF (FConsT a k_a (erase_env g)) (erase_env g')) )
          -> t:Type -> k:Kind
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
                          (unbind_tvT a1 a1' t') k_t' p_a1'env_t'
                          ? lem_commute_tsubFTV_unbind_tvT a (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta)
                               a1 a1' t'

{-@ lem_subst_tv_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
          -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
          -> ProofOf(WFFE (concatF (FConsT a k_a (erase_env g)) (erase_env g')) ) 
          -> t:Type -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (ConsT a k_a g) g') t k }
          -> ProofOf(WFType (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k) / [wftypSize p_env_t, 1] @-}
lem_subst_tv_wf :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFFE 
                    -> Type -> Kind -> WFType -> WFType
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_env_wf t k (WFBase _env b tt)
  = WFBase (concatE g (esubFTV a t_a g')) b tt ? lem_subFTV_notin a t_a (tt ? lem_trivial_nofv tt)
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
