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
import SystemFLemmasSubstitution
import Typing
import LemmasWeakenWFTV
import LemmasWellFormedness

{-@ reflect foo42 @-}
foo42 x = Just x
foo42 :: a -> Maybe a

-- -- -- -- -- -- -- -- -- -- -- ---
-- Part of the Substitution Lemma --
-- -- -- -- -- -- -- -- -- -- -- ---

--        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
--        -> ProofOf(WFFE (concatF (FConsT a k_a (erase_env g)) (erase_env g')) )
{-@ lem_subst_tv_wf_wfrefn :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) -> ProofOf(WFFE (erase_env g))
        -> t:Type -> k:Kind
        -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (ConsT a k_a g) g') t k && isWFRefn p_env_t}
        -> ProofOf(WFType (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k) 
         / [tsize t, envsize g', ksize k, 0] @-}
lem_subst_tv_wf_wfrefn :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFFE 
                    -> Type -> Kind -> WFType -> WFType
lem_subst_tv_wf_wfrefn g g' a t_a k_a p_g_ta p_erg_wf t k (WFRefn env b p_env_b ps nms mk_p_env'_p_bl)
  = case b of                                   -- t = TRefn b       ps
      (FTV a'_) | (a == a'_) -> case k_a of     -- t = TRefn (FTV a) ps
        Base -> lem_push_wf (concatE g (esubFTV a t_a g')) t_a {-Base-} p_gg'ta_ta
                            (psubFTV a t_a ps) nms' mk_pf_pta_bl 
          where
            p_gg'ta_ta = lem_weaken_many_wf g (esubFTV a t_a g') t_a k_a p_g_ta
                                            ? lem_psubFTV_notin a t_a PEmpty
--            p_env_er_b = lem_erase_wftype env (TRefn b PEmpty) Base p_env_b
            p_g_er_ta  = lem_erase_wftype g t_a k_a p_g_ta
            {-@ mk_pf_pta_bl :: { y:Vname | NotElem y nms' }
                  -> ProofOf(PHasFType (FCons y (erase t_a) (erase_env (concatE g (esubFTV a t_a g'))))
                                       (unbindP y (psubFTV a t_a ps))) @-}
            mk_pf_pta_bl y = lem_subst_tv_pftyp (erase_env g) (FCons y (FTBasic b) (erase_env g')
                                                                 ? lem_in_env_concat g g' y)
                               a (t_a ? lem_free_subset_binds g t_a k_a p_g_ta
                                      ? lem_wftype_islct g t_a k_a p_g_ta)
                               k_a p_g_er_ta p_erg_wf (unbindP y ps) 
                               (mk_p_env'_p_bl y ? lem_erase_concat (ConsT a k_a g) g')
                               ? lem_commute_psubFTV_unbindP a 
                                   (t_a ? lem_wftype_islct g t_a k_a p_g_ta) y ps
                               ? lem_erase_concat g (esubFTV a t_a g')
                               ? lem_erase_esubFTV a t_a g'  
                               ? lem_erase_tsubFTV a t_a (TRefn b PEmpty)
--              where
--                p_er_yenv_wf = WFFBind (erase_env env) (p_env_wf ? lem_erase_concat (ConsT a k_a g) g') 
--                                       y (FTBasic b) Base p_env_er_b 
            nms'           = a:(unionEnv nms (concatE (ConsT a k_a g) g'))
        Star -> impossible ("by lemma" ? lem_kind_for_tv g g' a k_a
                                       ? lem_wf_ftv_kind (concatE (ConsT a k_a g) g') a k p_env_b)
      (BTV a')             -> impossible ("by lemma" ? lem_btv_not_wf env a' PEmpty Base p_env_b)
      _                    -> WFRefn (concatE g (esubFTV a t_a g')) b p_gg'_b (psubFTV a t_a ps) 
                                     nms' mk_p_ygg'_pta_bl -- ? lem_psubFTV_notin a t_a PEmpty
        where
          p_gg'_b       = lem_subst_tv_wf g g' a t_a k_a p_g_ta p_erg_wf 
                                          (TRefn b PEmpty) Base p_env_b  ? lem_psubFTV_notin a t_a PEmpty
--          p_env_er_b    = lem_erase_wftype env (TRefn b PEmpty) Base p_env_b
          p_g_er_ta     = lem_erase_wftype g t_a k_a p_g_ta
          {-@ mk_p_ygg'_pta_bl :: { y:Vname | NotElem y nms' }
                -> ProofOf(PHasFType (FCons y (FTBasic b) (erase_env (concatE g (esubFTV a t_a g'))))
                                     (unbindP y (psubFTV a t_a ps))) @-}
          mk_p_ygg'_pta_bl y = lem_subst_tv_pftyp (erase_env g) (FCons y (FTBasic b) (erase_env g')
                                                                 ? lem_in_env_concat g g' y)
                               a (t_a ? lem_free_subset_binds g t_a k_a p_g_ta
                                      ? lem_wftype_islct g t_a k_a p_g_ta)
                               k_a p_g_er_ta p_erg_wf (unbindP y ps) 
                               (mk_p_env'_p_bl y ? lem_erase_concat (ConsT a k_a g) g')
                               ? lem_commute_psubFTV_unbindP a 
                                   (t_a ? lem_wftype_islct g t_a k_a p_g_ta) y ps
                               ? lem_erase_concat g (esubFTV a t_a g')
                               ? lem_erase_esubFTV a t_a g'  
                               ? lem_erase_tsubFTV a t_a (TRefn b PEmpty)
--              where
--                p_er_yenv_wf = WFFBind (erase_env env) (p_env_wf ? lem_erase_concat (ConsT a k_a g) g') 
--                                       y (FTBasic b) Base p_env_er_b 
          nms'               = a:(unionEnv nms (concatE (ConsT a k_a g) g'))

{-@ lem_subst_tv_wf_wfvar :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
          -> k_a:Kind -> ProofOf(WFType g t_a k_a) -> ProofOf(WFFE (erase_env g))
          -> t:Type -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (ConsT a k_a g) g') t k && isWFVar p_env_t }
          -> ProofOf(WFType (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k) 
           / [tsize t, envsize g', ksize k, 0] @-}
lem_subst_tv_wf_wfvar :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFFE 
                           -> Type -> Kind -> WFType -> WFType
lem_subst_tv_wf_wfvar g g' a t_a k_a p_g_ta p_g_wf t k (WFVar1 _env' a' k_a') 
  = case g' of
      Empty {- a == a' -}  -> p_g_ta ? lem_tsubFTV_ftv a t_a 
      (ConsT _a' _ka' g'') -> WFVar1 (concatE g (esubFTV a t_a g''))
                                     (a' ? lem_in_env_esubFTV g'' a t_a a'
                                         ? lem_in_env_concat g g'' a') k_a'
                                     ? lem_psubFTV_notin a t_a PEmpty 
lem_subst_tv_wf_wfvar g g' a t_a k_a p_g_ta p_g_wf t k p_g_t@(WFVar2 _env' a'_ k_a' p_env'_a' y t_y) 
  = case g' of 
      Empty             -> impossible "a <> y"
      (Cons _y _ty g'') -> case ( a == a'_ ) of 
        True -> case ( k_a , k ) of
          (Base, Star) -> WFKind (concatE g (esubFTV a t_a g')) t_a p_env''_tta
                                 ? lem_tsubFTV_ftv a t_a
            where
              p_env''_tta = lem_weaken_many_wf g (esubFTV a t_a g') t_a k_a p_g_ta 
          (Star, Base) -> impossible ("by lemma" ? lem_kind_for_tv g g' a k_a
                                        ? lem_wf_ftv_kind (concatE (ConsT a k_a g) g') a k p_g_t)
          _            -> lem_weaken_many_wf g (esubFTV a t_a g') t_a k_a p_g_ta
                                             ? lem_tsubFTV_ftv a t_a
        False -> WFVar2 (concatE g (esubFTV a t_a g'')) a' k_a' p_gg''_a' y (tsubFTV a t_a t_y)
          where
--            (WFFBind _ p_env'_wf _ _ _ _) = p_env_wf
            a'        = a'_ ? lem_in_env_esubFTV g'' a t_a a'_
                            ? lem_in_env_concat (ConsT a k_a g) g'' a'_
                            ? lem_in_env_concat g (esubFTV a t_a g'') a'_
            p_gg''_a' = lem_subst_tv_wf g g'' a t_a k_a p_g_ta p_g_wf 
                                        (TRefn (FTV a') PEmpty) k_a' p_env'_a'
                                        ? lem_psubFTV_notin a t_a PEmpty
lem_subst_tv_wf_wfvar g g' a t_a k_a p_g_ta p_g_wf t k p_g_t@(WFVar3 _env' a'_ k_a' p_env'_a' a1 k_a1) 
  = case g' of
      Empty {- a == a1 -} -> p_env'_a' ? lem_psubFTV_notin a t_a PEmpty
      (ConsT _a1 _k1 g'') -> case ( a == a'_ ) of 
        True -> case ( k_a , k ) of
          (Base, Star) -> WFKind (concatE g (esubFTV a t_a g')) t_a p_env''_tta
                                 ? lem_tsubFTV_ftv a t_a
            where
              p_env''_tta = lem_weaken_many_wf g (esubFTV a t_a g') t_a k_a p_g_ta
          (Star, Base) -> impossible ("by lemma" ? lem_kind_for_tv g g' a k_a
                                        ? lem_wf_ftv_kind (concatE (ConsT a k_a g) g') a k p_g_t)
          _            -> lem_weaken_many_wf g (esubFTV a t_a g') t_a k_a p_g_ta
                                             ? lem_tsubFTV_ftv a t_a
        False -> WFVar3 (concatE g (esubFTV a t_a g'')) a' k_a' p_gg''_a' a1 k_a1
          where
--            (WFFBindT _ p_env'_wf _ _) = p_env_wf
            a'        = a'_ ? lem_in_env_esubFTV g'' a t_a a'_
                            ? lem_in_env_concat (ConsT a k_a g) g'' a'_
                            ? lem_in_env_concat g (esubFTV a t_a g'') a'_
            p_gg''_a' = lem_subst_tv_wf g g'' a t_a k_a p_g_ta p_g_wf 
                                        (TRefn (FTV a') PEmpty) k_a' p_env'_a' 
                                        ? lem_psubFTV_notin a t_a PEmpty

{-@ lem_subst_tv_wf_wffunc :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
          -> k_a:Kind -> ProofOf(WFType g t_a k_a) -> ProofOf(WFFE (erase_env g))
          -> t:Type -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (ConsT a k_a g) g') t k && isWFFunc p_env_t }
          -> ProofOf(WFType (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k) 
           / [tsize t, envsize g', ksize k, 0] @-}
lem_subst_tv_wf_wffunc :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFFE 
                           -> Type -> Kind -> WFType -> WFType
lem_subst_tv_wf_wffunc g g' a t_a k_a p_g_ta p_g_wf t k (WFFunc env t_z k_z p_env_tz t' k' nms mk_p_yenv_t')  
  = WFFunc (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t_z) k_z p_g'g_tzta
           (tsubFTV a t_a t') k' nms' mk_p_yg'g_t'ta
      where
        p_g'g_tzta  = lem_subst_tv_wf g g'    a t_a k_a p_g_ta p_g_wf  t_z k_z p_env_tz
        {-@ mk_p_yg'g_t'ta :: { y:Vname | NotElem y nms' }
              -> ProofOf(WFType (Cons y (tsubFTV a t_a t_z) (concatE g (esubFTV a t_a g')))
                                (unbindT y (tsubFTV a t_a t')) k') @-}
        mk_p_yg'g_t'ta y = lem_subst_tv_wf g (Cons y t_z g') a t_a k_a p_g_ta p_g_wf
                               (unbindT y t') k' (mk_p_yenv_t' y)
                               ? lem_commute_tsubFTV_unbindT a
                                   (t_a ? lem_wftype_islct g t_a k_a p_g_ta) y t'
--          where
--            p_er_env_tz  = lem_erase_wftype env t_z k_z p_env_tz 
--                                            ? lem_erase_concat (ConsT a k_a g) g'
--            p_yenv_wf    = WFFBind (concatF (FConsT a k_a (erase_env g)) (erase_env g')) p_env_wf
--                                   y (erase t_z) k_z p_er_env_tz
        nms'             = a:(unionEnv nms (concatE g g'))

{-@ lem_subst_tv_wf_wfexis :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
          -> k_a:Kind -> ProofOf(WFType g t_a k_a) -> ProofOf(WFFE (erase_env g))
          -> t:Type -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (ConsT a k_a g) g') t k && isWFExis p_env_t }
          -> ProofOf(WFType (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k) 
           / [tsize t, envsize g', ksize k, 0] @-}
lem_subst_tv_wf_wfexis :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFFE 
                           -> Type -> Kind -> WFType -> WFType
lem_subst_tv_wf_wfexis g g' a t_a k_a p_g_ta p_g_wf t k (WFExis env t_z k_z p_env_tz t' k' nms mk_p_yenv_t')  
  = WFExis (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t_z) k_z p_g'g_tzta
           (tsubFTV a t_a t') k' nms' mk_p_yg'g_t'ta
      where
        p_g'g_tzta  = lem_subst_tv_wf g g'    a t_a k_a p_g_ta p_g_wf  t_z k_z p_env_tz
        {-@ mk_p_yg'g_t'ta :: { y:Vname | NotElem y nms' }
              -> ProofOf(WFType (Cons y (tsubFTV a t_a t_z) (concatE g (esubFTV a t_a g')))
                                (unbindT y (tsubFTV a t_a t')) k') @-}
        mk_p_yg'g_t'ta y = lem_subst_tv_wf g (Cons y t_z g') a t_a k_a p_g_ta p_g_wf
                               (unbindT y t') k' (mk_p_yenv_t' y)
                               ? lem_commute_tsubFTV_unbindT a
                                   (t_a ? lem_wftype_islct g t_a k_a p_g_ta) y t'
--          where
--            p_er_env_tz  = lem_erase_wftype env t_z k_z p_env_tz 
--                                            ? lem_erase_concat (ConsT a k_a g) g'
--            p_yenv_wf    = WFFBind (concatF (FConsT a k_a (erase_env g)) (erase_env g')) p_env_wf
--                                   y (erase t_z) k_z p_er_env_tz
        nms'             = a:(unionEnv nms (concatE g g'))

{-@ lem_subst_tv_wf_wfpoly :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
          -> k_a:Kind -> ProofOf(WFType g t_a k_a) -> ProofOf(WFFE (erase_env g))
          -> t:Type -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (ConsT a k_a g) g') t k && isWFPoly p_env_t }
          -> ProofOf(WFType (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k) 
           / [tsize t, envsize g', ksize k, 0] @-}
lem_subst_tv_wf_wfpoly :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFFE 
                              -> Type -> Kind -> WFType -> WFType
lem_subst_tv_wf_wfpoly g g' a t_a k_a p_g_ta p_g_wf t k (WFPoly _env k_a1 t' k_t' nms mk_p_a1env_t') 
  = WFPoly (concatE g (esubFTV a t_a g')) k_a1 (tsubFTV a t_a t') k_t' nms' mk_p_a1gg'_t'
      where
        {-@ mk_p_a1gg'_t' :: { a1:Vname | NotElem a1 nms' }
              -> ProofOf(WFType (ConsT a1 k_a1 (concatE g (esubFTV a t_a g')))
                                (unbind_tvT a1 (tsubFTV a t_a t')) k_t') @-}
        mk_p_a1gg'_t' a1 = lem_subst_tv_wf g (ConsT a1 k_a1 g') a t_a k_a p_g_ta p_g_wf
                               (unbind_tvT a1 t') k_t' (mk_p_a1env_t' a1)
                               ? lem_commute_tsubFTV_unbind_tvT a
                                   (t_a ? lem_wftype_islct g t_a k_a p_g_ta) a1 t'
--          where
--            p_a1env_wf   = WFFBindT (concatF (FConsT a k_a (erase_env g)) (erase_env g')) 
--                                    p_env_wf a1 k_a1
        nms'             = a:(unionEnv nms (concatE g g'))

{-@ lem_subst_tv_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
          -> k_a:Kind -> ProofOf(WFType g t_a k_a) -> ProofOf(WFFE (erase_env g))
          -> t:Type -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (ConsT a k_a g) g') t k }
          -> ProofOf(WFType (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k) 
           / [tsize t, envsize g', ksize k, 1] @-}
lem_subst_tv_wf :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFFE 
                    -> Type -> Kind -> WFType -> WFType
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_g_wf t k (WFBase _env b)
  = WFBase (concatE g (esubFTV a t_a g')) b ? lem_psubFTV_notin a t_a PEmpty 
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_g_wf t k p_e_t@(WFRefn {})
  = lem_subst_tv_wf_wfrefn g g' a t_a k_a p_g_ta p_g_wf t k p_e_t
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_g_wf t k p_e_t@(WFVar1 {})
  = lem_subst_tv_wf_wfvar g g' a t_a k_a p_g_ta p_g_wf t k p_e_t
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_g_wf t k p_e_t@(WFVar2 {})
  = lem_subst_tv_wf_wfvar g g' a t_a k_a p_g_ta p_g_wf t k p_e_t
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_g_wf t k p_e_t@(WFVar3 {})
  = lem_subst_tv_wf_wfvar g g' a t_a k_a p_g_ta p_g_wf t k p_e_t
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_g_wf t k p_e_t@(WFFunc {})
  = lem_subst_tv_wf_wffunc g g' a t_a k_a p_g_ta p_g_wf t k p_e_t
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_g_wf t k p_e_t@(WFExis {})
  = lem_subst_tv_wf_wfexis g g' a t_a k_a p_g_ta p_g_wf t k p_e_t
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_g_wf t k p_e_t@(WFPoly {})
  = lem_subst_tv_wf_wfpoly g g' a t_a k_a p_g_ta p_g_wf t k p_e_t
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_g_wf t k (WFKind _env _t p_env_t_base)
  = WFKind (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) p_gg'_tta_base
      where
        p_gg'_tta_base = lem_subst_tv_wf g g' a t_a k_a p_g_ta p_g_wf t Base p_env_t_base

-- this version takes WFEnv
{-@ lem_subst_tv_wf' :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) -> ProofOf(WFEnv g)
        -> t:Type -> k:Kind
        -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (ConsT a k_a g) g') t k }
        -> ProofOf(WFType (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k) @-}
lem_subst_tv_wf' :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Type -> Kind -> WFType -> WFType
lem_subst_tv_wf' g g' a t_a k_a p_g_ta p_g_wf t k p_e_t
  = lem_subst_tv_wf g g' a t_a k_a p_g_ta p_er_g_wf t k p_e_t
      where
        p_er_g_wf = lem_erase_env_wfenv g p_g_wf
--                                          ? lem_erase_concat (ConsT a k_a g) g'
