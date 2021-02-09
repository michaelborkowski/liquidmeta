{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SubstitutionLemmaTypTV where

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
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import Entailments
import LemmasChangeVarWF
import LemmasWeakenWF
import LemmasWeakenWFTV
import LemmasWellFormedness
import LemmasTyping
import LemmasSubtyping
import LemmasChangeVarTyp
import LemmasWeakenTyp
import LemmasWeakenTypTV
import SubstitutionWFAgain
import DenotationsSelfify
import PrimitivesSemantics
import PrimitivesDenotations
import DenotationsSoundness
import LemmasExactness
import SubstitutionLemmaWFEnv
import SubstitutionLemmaEnt
import SubstitutionLemmaEntTV
import EntailmentsExtra

{-@ reflect foo68 @-}
foo68 x = Just x
foo68 :: a -> Maybe a

{-@ lem_subst_tv_typ_tvar1 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTVar1 p_e_t }
        -> ProofOf(HasType (concatE g (esubFTV a t_a g')) (subFTV a t_a e) (tsubFTV a t_a t)) 
               / [typSize p_e_t, 0] @-}
lem_subst_tv_typ_tvar1 :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_tv_typ_tvar1 g g' a t_a k_a p_g_ta p_env_wf e t (TVar1 _env z t' k' p_env_t') 
  = case g' of          -- empty case: e = FV z = FV x and t = self t' x = self t_x x
      (Empty)          -> impossible "a <> z"
      (Cons _z _ g'')  -> TVar1 (concatE g (esubFTV a t_a g''))  -- z <> a, t = self t' (FV z)
                                (z ? lem_in_env_esubFTV g'' a t_a z
                                   ? lem_in_env_concat g g'' z
                                   ? lem_in_env_concat (ConsT a k_a g) g'' z)          
                                (tsubFTV a t_a t') k' p_env'_t'ta
                                ? lem_tsubFTV_self a t_a t' (FV z) k'
        where
          (WFEBind _ p_g''g_wf _z _tz k_z p_g_tz) = p_env_wf
          p_env'_t'ta = lem_subst_tv_wf' g g'' a t_a k_a p_g_ta p_g''g_wf t' k' p_env_t'

{-@ lem_subst_tv_typ_tvar2 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTVar2 p_e_t }
        -> ProofOf(HasType (concatE g (esubFTV a t_a g')) (subFTV a t_a e) (tsubFTV a t_a t)) 
               / [typSize p_e_t, 0] @-}
lem_subst_tv_typ_tvar2 :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_tv_typ_tvar2 g g' a t_a k_a p_g_ta p_env_wf e t p_env_z_t@(TVar2 env_ z _t p_z_t w_ t_w) 
    = case g' of             
        (Empty)           -> impossible "a <> w"
        (Cons _w _tw g'') -> case (a == z) of
            (True)  -> impossible ("by lemma" ? lem_tvar_v_in_env (concatE (ConsT a k_a g) g')
                                                                z t p_env_z_t
                                              ? lem_binds_invariants (concatE (ConsT a k_a g) g''))
            (False) -> TVar2 (concatE g (esubFTV a t_a g'')) 
                             (z ? lem_in_env_esubFTV g'' a t_a z
                                ? lem_in_env_concat g g'' z
                                ? lem_in_env_concat (ConsT a k_a g) g'' z) 
                             (tsubFTV a t_a t) p_z_tta w (tsubFTV a t_a t_w)
                         where
                           (WFEBind _gg'' p_gg''_wf _ _ _ _) = p_env_wf
                           w = w_ ? lem_in_env_esubFTV g'' a t_a w_
                                  ? lem_in_env_concat g g'' w_
                                  ? lem_in_env_concat (ConsT a k_a g) g'' w_
                                  ? lem_free_bound_in_env g t_a k_a p_g_ta w_
                           p_z_tta = lem_subst_tv_typ g g'' a t_a k_a p_g_ta 
                                                      p_gg''_wf e t p_z_t

{-@ lem_subst_tv_typ_tvar3 :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTVar3 p_e_t }
        -> ProofOf(HasType (concatE g (esubFTV a t_a g')) (subFTV a t_a e) (tsubFTV a t_a t)) 
               / [typSize p_e_t, 0] @-}
lem_subst_tv_typ_tvar3 :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_tv_typ_tvar3 g g' a t_a k_a p_g_ta p_env_wf e t p_env_z_t@(TVar3 env_ z _t p_z_t a'_ k_a') 
    = case g' of             -- g'' = Empty so a = a' and p_z_t :: HasFType(g (FV z) t)
        (Empty)            -> case (a == z) of
            (True)  -> impossible ("by lemma" ? lem_tvar_v_in_env (concatE (ConsT a k_a g) g')
                                                                z t p_env_z_t)
            (False) -> p_z_t ? lem_free_bound_in_env g t Star p_g_t a
                             ? lem_tsubFTV_notin a t_a t   --  ? toProof ( e === (FV z) )
                         where
                           (WFEBindT g_ p_g_wf _ _) = p_env_wf
                           p_g_t = lem_typing_wf g (FV z) t p_z_t p_g_wf
        (ConsT _ _ka g'') -> case (a == z) of
            (True)  -> impossible ("by lemma" ? lem_tvar_v_in_env (concatE (ConsT a k_a g) g')
                                                                z t p_env_z_t
                                              ? lem_binds_invariants (concatE (ConsT a k_a g) g''))
            (False) -> TVar3 (concatE g (esubFTV a t_a g'')) --z
                             (z ? lem_in_env_esubFTV g'' a t_a z
                                ? lem_in_env_concat g g'' z
                                ? lem_in_env_concat (ConsT a k_a g) g'' z) 
                             (tsubFTV a t_a t) p_z_tvta a' k_a'
                         where
                           (WFEBindT _gg'' p_gg''_wf _ _) = p_env_wf
                           a' = a'_ ? lem_in_env_esubFTV g'' a t_a a'_
                                    ? lem_in_env_concat g g'' a'_
                                    ? lem_in_env_concat (ConsT a k_a g) g'' a'_
                                    ? lem_free_bound_in_env g t_a k_a p_g_ta a'_
                           p_z_tvta = lem_subst_tv_typ g g'' a t_a k_a p_g_ta 
                                                       p_gg''_wf e t p_z_t

{-@ lem_subst_tv_typ_tabs :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTAbs p_e_t }
        -> ProofOf(HasType (concatE g (esubFTV a t_a g')) (subFTV a t_a e) (tsubFTV a t_a t)) 
               / [typSize p_e_t, 0] @-}
lem_subst_tv_typ_tabs :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_tv_typ_tabs g g' a t_a k_a p_g_ta p_env_wf e t 
                      (TAbs env_ z t_z k_z p_env_tz e' t' y_ p_yenv_e'_t') 
  = TAbs (concatE g (esubFTV a t_a g')) z (tsubFTV a t_a t_z) k_z p_g'g_tzta
         (subFTV a t_a e') (tsubFTV a t_a t') y p_yg'g_e'ta_t'ta
      where
        y                = y_  ? lem_in_env_esubFTV g' a t_a y_ 
                               ? lem_in_env_concat g  g' y_ 
                               ? lem_in_env_concat (ConsT a k_a g) g' y_
                               ? lem_free_bound_in_env g t_a k_a p_g_ta y_
        p_yenv_wf        = WFEBind (concatE (ConsT a k_a g) g') p_env_wf y t_z k_z p_env_tz
        p_g'g_tzta       = lem_subst_tv_wf' g g' a t_a k_a p_g_ta p_env_wf t_z k_z p_env_tz
        p_yg'g_e'ta_t'ta = lem_subst_tv_typ g (Cons y t_z g') a t_a k_a p_g_ta p_yenv_wf
                               (unbind z y e') (unbindT z y t') p_yenv_e'_t'
                               ? lem_commute_subFTV_unbind a 
                                     (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta) z y e'
                               ? lem_commute_tsubFTV_unbindT a 
                                     (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta) z y t'

{-@ lem_subst_tv_typ_tapp :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTApp p_e_t }
        -> ProofOf(HasType (concatE g (esubFTV a t_a g')) (subFTV a t_a e) (tsubFTV a t_a t)) 
               / [typSize p_e_t, 0] @-}
lem_subst_tv_typ_tapp :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_tv_typ_tapp g g' a t_a k_a p_g_ta p_env_wf e t 
                      (TApp env_ e' z t_z t' p_env_e'_tzt' e_z p_env_ez_tz) 
  = TApp (concatE g (esubFTV a t_a g')) (subFTV a t_a e') z (tsubFTV a t_a t_z) (tsubFTV a t_a t') 
         p_g'g_e'ta_tzt'ta (subFTV a t_a e_z)  p_g'g_ezta_tzta
      where
        p_g'g_e'ta_tzt'ta = lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e' 
                                             (TFunc z t_z t') p_env_e'_tzt'
        p_g'g_ezta_tzta   = lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e_z t_z p_env_ez_tz 

{-@ lem_subst_tv_typ_tabst :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTAbsT p_e_t }
        -> ProofOf(HasType (concatE g (esubFTV a t_a g')) (subFTV a t_a e) (tsubFTV a t_a t)) 
               / [typSize p_e_t, 0] @-}
lem_subst_tv_typ_tabst :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_tv_typ_tabst g g' a t_a k_a p_g_ta p_env_wf e t 
                    p_e_t@(TAbsT env a1 k e' t' k_t' a'_ p_a'env_e'_t' p_a'env_t') 
  = TAbsT (concatE g (esubFTV a t_a g')) a1 k (subFTV a t_a e') (tsubFTV a t_a t') k_t' a'
          p_a'env'_e'_t' p_a'env'_t'
      where
        p_env_t        = lem_typing_wf env e t p_e_t p_env_wf
        a'             = a'_ ? lem_in_env_esubFTV g' a t_a a'_
                             ? lem_in_env_concat g  g' a'_
                             ? lem_in_env_concat (ConsT a k_a g) g' a'_
                             ? lem_free_bound_in_env g t_a k_a p_g_ta a'_
        p_a'env_wf     = WFEBindT env p_env_wf a' k
        p_a'env'_e'_t' = lem_subst_tv_typ g (ConsT a' k g') a t_a k_a p_g_ta p_a'env_wf 
                             (unbind_tv a1 a' e') (unbind_tvT a1 a' t') p_a'env_e'_t'
                             ? lem_commute_subFTV_unbind_tv a
                                   (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta) a1 a' e'
                             ? lem_commute_tsubFTV_unbind_tvT a
                                   (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta) a1 a' t'
        p_a'env'_t'    = lem_subst_tv_wf' g (ConsT a' k g') a t_a k_a p_g_ta p_a'env_wf
                             (unbind_tvT a1 a' t') k_t' p_a'env_t'
                             ? lem_commute_tsubFTV_unbind_tvT a
                                   (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta) a1 a' t'
          
{-@ lem_subst_tv_typ_tappt :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTAppT p_e_t }
        -> ProofOf(HasType (concatE g (esubFTV a t_a g')) (subFTV a t_a e) (tsubFTV a t_a t)) 
               / [typSize p_e_t, 0] @-}
lem_subst_tv_typ_tappt :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_tv_typ_tappt g g' a t_a k_a p_g_ta p_env_wf e t 
                    p_e_t@(TAppT env e' a1 k1 s p_e'_a1s t' p_env_t')
  = TAppT (concatE g (esubFTV a t_a g')) (subFTV a t_a e') a1 k1 (tsubFTV a t_a s) p_env'_e'_a1s
          (tsubFTV a t_a t') p_env'_t'
          ? lem_commute_tsubFTV_tsubBTV a1 t' a (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta) s
      where
        p_env'_e'_a1s = lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e' (TPoly a1 k1 s) p_e'_a1s
        p_env'_t'     = lem_subst_tv_wf' g g' a t_a k_a p_g_ta p_env_wf t' k1 p_env_t'
 
{-@ lem_subst_tv_typ_tlet :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTLet p_e_t }
        -> ProofOf(HasType (concatE g (esubFTV a t_a g')) (subFTV a t_a e) (tsubFTV a t_a t)) 
               / [typSize p_e_t, 0] @-}
lem_subst_tv_typ_tlet :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_tv_typ_tlet g g' a t_a k_a p_g_ta p_env_wf e t (TLet env_ e_z t_z p_env_ez_tz z e' t_ k
                                                        p_env_t y_ p_yenv_e'_t) 
  = TLet (concatE g (esubFTV a t_a g')) (subFTV a t_a e_z) (tsubFTV a t_a t_z) p_g'g_ezta_tzta z
         (subFTV a t_a e') (tsubFTV a t_a t) k p_g'g_t'ta y p_yg'g_e'ta_tta
      where
        y                = y_  ? lem_in_env_esubFTV g' a t_a y_ 
                               ? lem_in_env_concat g  g' y_ 
                               ? lem_in_env_concat (ConsT a k_a g) g' y_
                               ? lem_free_bound_in_env g t_a k_a p_g_ta y_
        p_env_tz         = lem_typing_wf env_ e_z t_z p_env_ez_tz p_env_wf
        p_yenv_wf        = WFEBind (concatE (ConsT a k_a g) g') p_env_wf y t_z Star p_env_tz
        p_g'g_ezta_tzta  = lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e_z t_z p_env_ez_tz
        p_g'g_t'ta       = lem_subst_tv_wf' g g' a t_a k_a p_g_ta p_env_wf t k p_env_t
        p_yg'g_e'ta_tta  = lem_subst_tv_typ g (Cons y t_z g') a t_a k_a p_g_ta p_yenv_wf 
                                         (unbind z y e') (unbindT z y t) p_yenv_e'_t
                                         ? lem_commute_subFTV_unbind a
                                               (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta) z y e'
                                         ? lem_commute_tsubFTV_unbindT a
                                               (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta) z y t

{-@ lem_subst_tv_typ_tsub :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTSub p_e_t }
        -> ProofOf(HasType (concatE g (esubFTV a t_a g')) (subFTV a t_a e) (tsubFTV a t_a t)) 
               / [typSize p_e_t, 0] @-}
lem_subst_tv_typ_tsub :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_tv_typ_tsub g g' a t_a k_a p_g_ta p_env_wf e t 
                      (TSub env_ e_ s p_env_e_s t_ k p_env_t p_env_s_t) 
  = TSub (concatE g (esubFTV a t_a g')) (subFTV a t_a e) (tsubFTV a t_a s) p_g'g_e_s
         (tsubFTV a t_a t) k p_g'g_t p_g'g_s_t
      where
        p_g'g_e_s  = lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e s p_env_e_s
        p_g'g_t    = lem_subst_tv_wf' g g' a t_a k_a p_g_ta p_env_wf t k p_env_t
        p_env_s    = lem_typing_wf (concatE (ConsT a k_a g) g') e s p_env_e_s p_env_wf
        p_g'g_s_t  = lem_subst_tv_sub g g' a t_a k_a p_g_ta p_env_wf s Star p_env_s t k p_env_t p_env_s_t

{-@ lem_subst_tv_typ :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t }
        -> ProofOf(HasType (concatE g (esubFTV a t_a g')) (subFTV a t_a e) (tsubFTV a t_a t)) 
               / [typSize p_e_t, 1] @-}
lem_subst_tv_typ :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t (TBC _env b)
  = TBC (concatE g (esubFTV a t_a g')) b ? lem_tsubFTV_tybc a t_a b
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t (TIC _env n)
  = TIC (concatE g (esubFTV a t_a g')) n ? lem_tsubFTV_tyic a t_a n
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t p_e_t@(TVar1 {}) 
  = lem_subst_tv_typ_tvar1 g g' a t_a k_a p_g_ta p_env_wf e t p_e_t
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t p_e_t@(TVar2 {}) 
  = lem_subst_tv_typ_tvar2 g g' a t_a k_a p_g_ta p_env_wf e t p_e_t
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t p_e_t@(TVar3 {}) 
  = lem_subst_tv_typ_tvar3 g g' a t_a k_a p_g_ta p_env_wf e t p_e_t
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t (TPrm _env c)
  = TPrm (concatE g (esubFTV a t_a g')) c ? lem_tsubFTV_ty a t_a c
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t p_e_t@(TAbs {})
  = lem_subst_tv_typ_tabs g g' a t_a k_a p_g_ta p_env_wf e t p_e_t
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t p_e_t@(TApp {}) 
  = lem_subst_tv_typ_tapp g g' a t_a k_a p_g_ta p_env_wf e t p_e_t
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t p_e_t@(TAbsT {}) 
  = lem_subst_tv_typ_tabst g g' a t_a k_a p_g_ta p_env_wf e t p_e_t
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t p_e_t@(TAppT {}) 
  = lem_subst_tv_typ_tappt g g' a t_a k_a p_g_ta p_env_wf e t p_e_t
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t p_e_t@(TLet {})
  = lem_subst_tv_typ_tlet g g' a t_a k_a p_g_ta p_env_wf e t p_e_t
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t (TAnn env_ e' t_ p_env_e'_t) 
  = TAnn (concatE g (esubFTV a t_a g')) (subFTV a t_a e') (tsubFTV a t_a t) p_env'_e'ta_tta
      where
        p_env'_e'ta_tta = lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e' t p_env_e'_t
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t p_e_t@(TSub {}) 
  = lem_subst_tv_typ_tsub g g' a t_a k_a p_g_ta p_env_wf e t p_e_t


{-@ lem_subst_tv_sub_sbase :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) 
        -> s:Type -> k_s:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') s k_s)
        -> t:Type -> k_t:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') t k_t)
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (ConsT a k_a g) g') s t && isSBase p_s_t }
        -> ProofOf(Subtype (concatE g (esubFTV a t_a g')) (tsubFTV a t_a s) (tsubFTV a t_a t)) 
               / [subtypSize p_s_t, 0] @-}
lem_subst_tv_sub_sbase :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Type -> Kind -> WFType -> Type -> Kind -> WFType -> Subtype -> Subtype
lem_subst_tv_sub_sbase g g' a t_a k_a p_g_ta p_env_wf s k_s p_env_s t k_t p_env_t 
                       p_s_t@(SBase env z1 b p1 z2 p2 y_ ent_yenv_p2) = case b of
  (FTV a1) | a1 == a -> case t_a of -- b' could be FTV here
    (TRefn b' z q_)   -> lem_subst_tv_sub_sbase_ftv g g' a b' z q k_a p_g_ta p_env_wf 
                                                   z1 p1 k_s p_env_s z2 p2 k_t p_env_t p_s_t
      where 
        q = q_ ? lem_refn_is_pred (TRefn b' z q_) b' z q_
    (TFunc x t_x t') -> lem_sub_refl (concatE g (esubFTV a t_a g')) t_a k_a p_env'_ta p_env'_wf
      where
        p_env'_wf = lem_subst_tv_wfenv g g' a t_a k_a p_g_ta p_env_wf
        p_env'_ta = lem_weaken_many_wf' g (esubFTV a t_a g') p_env'_wf t_a k_a p_g_ta 
    (TPoly a0 k0 t') -> lem_sub_refl (concatE g (esubFTV a t_a g')) t_a k_a p_env'_ta p_env'_wf
      where
        p_env'_wf = lem_subst_tv_wfenv g g' a t_a k_a p_g_ta p_env_wf
        p_env'_ta = lem_weaken_many_wf' g (esubFTV a t_a g') p_env'_wf t_a k_a p_g_ta 
  _                  -> SBase (concatE g (esubFTV a t_a g')) z1 b (subFTV a t_a p1) 
                              z2 (subFTV a t_a p2) y ent_yenv'_p2ta
    where
      y                = y_  ? lem_in_env_esubFTV g' a t_a y_ 
                             ? lem_in_env_concat g  g' y_ 
                             ? lem_in_env_concat (ConsT a k_a g) g' y_
                             ? lem_free_bound_in_env g t_a k_a p_g_ta y_
      (w_, p_wenv_p2_bl) = lem_ftyp_for_wf_trefn env b z2 p2 k_t p_env_t
      w                = w_  ? lem_in_env_concat g  g' w_ 
                             ? lem_in_env_concat (ConsT a k_a g) g' w_
      p_wenv_wf        = WFEBind env p_env_wf w (TRefn b z1 p1) k_s p_env_s
      p_yenv_wf        = WFEBind env p_env_wf y (TRefn b z1 p1) k_s p_env_s
      p_er_wenv_wf     = lem_erase_env_wfenv (Cons w (TRefn b z1 p1) env) p_wenv_wf
      p_yenv_p2_bl     = lem_change_var_ftyp (erase_env env) w (FTBasic b) FEmpty p_er_wenv_wf
                                             (unbind 0 w p2) (FTBasic TBool) p_wenv_p2_bl y
                                             ? lem_subFV_unbind 0 w (FV y) p2
      ent_yenv'_p2ta   = lem_subst_tv_ent g (Cons y (TRefn b z1 p1) g') a t_a k_a p_g_ta p_yenv_wf
                             (unbind 0 y p2 ? lem_fv_subset_bindsF (FCons y (FTBasic b) (erase_env env)) 
                                 (unbind 0 y p2) (FTBasic TBool) p_yenv_p2_bl)
                             ent_yenv_p2 
                             ? lem_commute_subFTV_unbind a
                                   (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta) 0 y p2 

{-@ lem_subst_tv_sub_sfunc :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) 
        -> s:Type -> k_s:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') s k_s)
        -> t:Type -> k_t:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') t k_t)
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (ConsT a k_a g) g') s t && isSFunc p_s_t }
        -> ProofOf(Subtype (concatE g (esubFTV a t_a g')) (tsubFTV a t_a s) (tsubFTV a t_a t)) 
               / [subtypSize p_s_t, 0] @-}
lem_subst_tv_sub_sfunc :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Type -> Kind -> WFType -> Type -> Kind -> WFType -> Subtype -> Subtype
lem_subst_tv_sub_sfunc g g' a t_a k_a p_g_ta p_env_wf ty1 ky1 p_env_ty1 ty2 ky2 p_env_ty2
                       (SFunc env x1 s1 x2 s2 p_s2_s1 t1 t2 y_ p_yenv_t1_t2) 
  = SFunc (concatE g (esubFTV a t_a g')) x1 (tsubFTV a t_a s1) x2 (tsubFTV a t_a s2)
          p_s2ta_s1ta (tsubFTV a t_a t1) (tsubFTV a t_a t2) y p_yg'g_t1ta_t2ta
      where 
        y                = y_  ? lem_in_env_esubFTV g' a t_a y_ 
                               ? lem_in_env_concat g  g' y_ 
                               ? lem_in_env_concat (ConsT a k_a g) g' y_
                               ? lem_free_bound_in_env g t_a k_a p_g_ta  y_
        (WFFunc _ _ _s1 k_s1 p_env_s1 _ k_t1 w1 p_w1env_t1) 
                         = lem_wffunc_for_wf_tfunc (concatE (ConsT a k_a g) g') x1 s1 t1 ky1 p_env_ty1
        (WFFunc _ _ _s2 k_s2 p_env_s2 _ k_t2 w2 p_w2env_t2)
                         = lem_wffunc_for_wf_tfunc (concatE (ConsT a k_a g) g') x2 s2 t2 ky2 p_env_ty2
        p_w1s1env_wf     = WFEBind env p_env_wf w1 s1 k_s1 p_env_s1
        p_w2env_wf       = WFEBind env p_env_wf w2 s2 k_s2 p_env_s2
        _p_yenv_t1       = lem_change_var_wf' (concatE (ConsT a k_a g) g') w1 s1 Empty p_w1s1env_wf
                                              (unbindT x1 w1 t1) k_t1 p_w1env_t1 y
                                              `withProof` lem_tsubFV_unbindT x1 w1 (FV y) t1
        p_yenv_t1        = lem_subtype_in_env_wf (concatE (ConsT a k_a g) g') Empty y s2 s1 
                                             p_s2_s1 (unbindT x1 y t1) k_t1 _p_yenv_t1
        p_yenv_t2        = lem_change_var_wf' (concatE (ConsT a k_a g) g') w2 s2 Empty p_w2env_wf
                                              (unbindT x2 w2 t2) k_t2 p_w2env_t2 y
                                              `withProof` lem_tsubFV_unbindT x2 w2 (FV y) t2
        p_s2ta_s1ta      = lem_subst_tv_sub g g' a t_a k_a p_g_ta p_env_wf 
                                            s2 k_s2 p_env_s2 s1 k_s1 p_env_s1 p_s2_s1 
        p_yenv_wf        = WFEBind (concatE (ConsT a k_a g) g') p_env_wf y s2 k_s2 p_env_s2
        p_yg'g_t1ta_t2ta = lem_subst_tv_sub g (Cons y s2 g') a t_a k_a p_g_ta p_yenv_wf
                                            (unbindT x1 y t1) k_t1 p_yenv_t1 
                                            (unbindT x2 y t2) k_t2 p_yenv_t2 p_yenv_t1_t2
                                            ? lem_commute_tsubFTV_unbindT a
                                                  (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta) x1 y t1
                                            ? lem_commute_tsubFTV_unbindT a
                                                  (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta) x2 y t2

{-@ lem_subst_tv_sub_switn :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) 
        -> s:Type -> k_s:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') s k_s)
        -> t:Type -> k_t:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') t k_t)
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (ConsT a k_a g) g') s t && isSWitn p_s_t}
        -> ProofOf(Subtype (concatE g (esubFTV a t_a g')) (tsubFTV a t_a s) (tsubFTV a t_a t)) 
               / [subtypSize p_s_t, 0] @-}
lem_subst_tv_sub_switn :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Type -> Kind -> WFType -> Type -> Kind -> WFType -> Subtype -> Subtype
lem_subst_tv_sub_switn g g' a t_a k_a p_g_ta p_env_wf t k p_env_t t2 k2 p_env_t2
                       (SWitn env v_z t_z p_env_vz_tz _t z t' p_env_t_t'vz)
  = SWitn (concatE g (esubFTV a t_a g')) (subFTV a t_a v_z) (tsubFTV a t_a t_z) p_g'g_vzta_tzta
          (tsubFTV a t_a t) z (tsubFTV a t_a t') p_g'g_tta_t'vzta
      where
        (WFExis _ _ _ k_z p_env_tz _ k' y p_yenv_t') 
                         = lem_wfexis_for_wf_texists (concatE (ConsT a k_a g) g') z t_z t' k2 p_env_t2
        p_g'g_vzta_tzta  = lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf v_z t_z p_env_vz_tz
        p_yenv_wf        = WFEBind env p_env_wf y t_z k_z p_env_tz
        p_env_t'vz       = lem_subst_wf' (concatE (ConsT a k_a g) g') Empty y v_z t_z p_env_vz_tz 
                              p_yenv_wf (unbindT z y t') k' p_yenv_t' 
                              ? lem_tsubFV_unbindT z y v_z t'
        p_g'g_tta_t'vzta = lem_subst_tv_sub g g' a t_a k_a p_g_ta p_env_wf t k p_env_t 
                              (tsubBV z v_z t') k' p_env_t'vz p_env_t_t'vz
                              ? lem_commute_tsubFTV_tsubBV z v_z a 
                                    (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta) t'

{-@ lem_subst_tv_sub_sbind :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) 
        -> s:Type -> k_s:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') s k_s)
        -> t:Type -> k_t:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') t k_t)
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (ConsT a k_a g) g') s t && isSBind p_s_t }
        -> ProofOf(Subtype (concatE g (esubFTV a t_a g')) (tsubFTV a t_a s) (tsubFTV a t_a t)) 
               / [subtypSize p_s_t, 0] @-}
lem_subst_tv_sub_sbind :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Type -> Kind -> WFType -> Type -> Kind -> WFType -> Subtype -> Subtype
lem_subst_tv_sub_sbind g g' a t_a k_a p_g_ta p_env_wf t1 k1 p_env_t1 t' k' p_env_t'
                       (SBind env z t_z t _t' w_ p_wenv_t_t') 
  = SBind (concatE g (esubFTV a t_a g')) z (tsubFTV a t_a t_z) (tsubFTV a t_a t) (tsubFTV a t_a t')
          w p_wenv'_tta_t'ta
      where 
        w                = w_ ? lem_in_env_esubFTV g' a t_a w_
                              ? lem_in_env_concat g g' w_
                              ? lem_in_env_concat (ConsT a k_a g) g' w_
                              ? lem_free_bound_in_env g t_a k_a p_g_ta w_
        (WFExis _ _ _ k_z p_env_tz _ k y p_yenv_t) 
                         = lem_wfexis_for_wf_texists (concatE (ConsT a k_a g) g') z t_z t k1 p_env_t1
        p_wenv_wf        = WFEBind (concatE (ConsT a k_a g) g') p_env_wf w t_z k_z p_env_tz
        p_yenv_wf        = WFEBind (concatE (ConsT a k_a g) g') p_env_wf y t_z k_z p_env_tz
        p_wenv_t         = lem_change_var_wf' env y t_z Empty p_yenv_wf (unbindT z y t) k p_yenv_t w
                                              ? lem_tsubFV_unbindT z y (FV w) t
        p_wenv_t'        = lem_weaken_wf'     env Empty p_env_wf t' k' p_env_t' w t_z
        p_wenv'_tta_t'ta = lem_subst_tv_sub g (Cons w t_z g') a t_a k_a p_g_ta p_wenv_wf
                                         (unbindT z w t) k p_wenv_t t' k' p_wenv_t' p_wenv_t_t'
                                         ? lem_commute_tsubFTV_tsubBV z (FV w) a
                                             (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta) t

{-@ lem_subst_tv_sub_spoly :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) 
        -> s:Type -> k_s:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') s k_s)
        -> t:Type -> k_t:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') t k_t)
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (ConsT a k_a g) g') s t && isSPoly p_s_t }
        -> ProofOf(Subtype (concatE g (esubFTV a t_a g')) (tsubFTV a t_a s) (tsubFTV a t_a t)) 
               / [subtypSize p_s_t, 0] @-}
lem_subst_tv_sub_spoly :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Type -> Kind -> WFType -> Type -> Kind -> WFType -> Subtype -> Subtype
lem_subst_tv_sub_spoly g g' a t_a k_a p_g_ta p_env_wf t1 k1@Star p_env_t1 t2 k2@Star p_env_t2 
                       (SPoly env a1 k' t1' a2 t2' a1'_ p_a1'env_t1'_t2') 
  = SPoly (concatE g (esubFTV a t_a g')) a1 k' (tsubFTV a t_a t1') a2 (tsubFTV a t_a t2')
          a1' p_a1'g'g_t1'ta_t2'ta
      where
        (WFPoly _ _ _ _ k_t1' aa1 p_aa1env_t1')  
                             = lem_wfpoly_for_wf_tpoly env a1 k' t1' p_env_t1
        (WFPoly _ _ _ _ k_t2' aa2 p_aa2env_t2')
                             = lem_wfpoly_for_wf_tpoly env a2 k' t2' p_env_t2
        a1'                  = a1'_ ? lem_in_env_esubFTV g' a t_a a1'_
                                    ? lem_in_env_concat g  g' a1'_
                                    ? lem_in_env_concat (ConsT a k_a g) g' a1'_
                                    ? lem_free_bound_in_env g t_a k_a p_g_ta a1'_
        p_aa1env_wf          = WFEBindT env p_env_wf aa1  k'
        p_aa2env_wf          = WFEBindT env p_env_wf aa2  k'
        p_a1'env_wf          = WFEBindT env p_env_wf a1'  k'
        p_a1'env_t1'         = lem_change_tvar_wf' (concatE (ConsT a k_a g) g') aa1 k' Empty p_aa1env_wf
                                   (unbind_tvT a1 aa1 t1') k_t1' p_aa1env_t1' a1'
                                   ? lem_tchgFTV_unbind_tvT a1 aa1 a1' t1'
        p_a1'env_t2'         = lem_change_tvar_wf' (concatE (ConsT a k_a g) g') aa2 k' Empty p_aa2env_wf
                                   (unbind_tvT a2 aa2 t2') k_t2' p_aa2env_t2' a1'
                                   ? lem_tchgFTV_unbind_tvT a2 aa2 a1' t2'
        p_a1'g'g_t1'ta_t2'ta = lem_subst_tv_sub g (ConsT a1' k' g') a t_a k_a p_g_ta p_a1'env_wf
                                   (unbind_tvT a1 a1' t1') k_t1' p_a1'env_t1'
                                   (unbind_tvT a2 a1' t2') k_t2' p_a1'env_t2' p_a1'env_t1'_t2'
                                   ? lem_commute_tsubFTV_unbind_tvT a
                                         (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta) a1 a1' t1'
                                   ? lem_commute_tsubFTV_unbind_tvT a 
                                         (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta) a2 a1' t2'
lem_subst_tv_sub_spoly g g' a t_a k_a p_g_ta p_env_wf t1 Base p_env_t1 t2 k2   p_env_t2 
                    (SPoly env a1 k' t1' a2 t2' a1'_ p_a1'env_t1'_t2') 
  = impossible ("by lemma" ? lem_wf_tpoly_star env a1 k' t1' p_env_t1)
lem_subst_tv_sub_spoly g g' a t_a k_a p_g_ta p_env_wf t1 k1   p_env_t1 t2 Base p_env_t2 
                    (SPoly env a1 k' t1' a2 t2' a1'_ p_a1'env_t1'_t2') 
  = impossible ("by lemma" ? lem_wf_tpoly_star env a2 k' t2' p_env_t2)

{-@ lem_subst_tv_sub :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) 
        -> s:Type -> k_s:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') s k_s)
        -> t:Type -> k_t:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') t k_t)
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (ConsT a k_a g) g') s t }
        -> ProofOf(Subtype (concatE g (esubFTV a t_a g')) (tsubFTV a t_a s) (tsubFTV a t_a t)) / [subtypSize p_s_t, 1] @-}
lem_subst_tv_sub :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Type -> Kind -> WFType -> Type -> Kind -> WFType -> Subtype -> Subtype
lem_subst_tv_sub g g' a t_a k_a p_g_ta p_env_wf s k_s p_env_s t k_t p_env_t 
                 p_t_t'@(SBase env z1 b p1 z2 p2 y_ ent_yenv_p2) 
  = lem_subst_tv_sub_sbase g g' a t_a k_a p_g_ta p_env_wf s k_s p_env_s t k_t p_env_t p_t_t'
lem_subst_tv_sub g g' a t_a k_a p_g_ta p_env_wf ty1 ky1 p_env_ty1 ty2 ky2 p_env_ty2
                 p_t_t'@(SFunc env_ x1 s1 x2 s2 p_s2_s1 t1 t2 y_ p_yenv_t1_t2) 
  = lem_subst_tv_sub_sfunc g g' a t_a k_a p_g_ta p_env_wf ty1 ky1 p_env_ty1 ty2 ky2 p_env_ty2 p_t_t'
lem_subst_tv_sub g g' a t_a k_a p_g_ta p_env_wf t k p_env_t t2 k2 p_env_t2
                 p_t_t'@(SWitn env v_z t_z p_env_vz_tz _t z t' p_env_t_t'vz) 
  = lem_subst_tv_sub_switn g g' a t_a k_a p_g_ta p_env_wf t k p_env_t t2 k2 p_env_t2 p_t_t'
lem_subst_tv_sub g g' a t_a k_a p_g_ta p_env_wf t1 k1 p_env_t1 t' k' p_env_t'
                 p_t_t'@(SBind env z t_z t _t' w_ p_wenv_t_t') 
  = lem_subst_tv_sub_sbind g g' a t_a k_a p_g_ta p_env_wf t1 k1 p_env_t1 t' k' p_env_t' p_t_t'
lem_subst_tv_sub g g' a t_a k_a p_g_ta p_env_wf t1 k1 p_env_t1 t2 k2 p_env_t2 p_t_t'@(SPoly {})
  = lem_subst_tv_sub_spoly g g' a t_a k_a p_g_ta p_env_wf t1 k1 p_env_t1 t2 k2 p_env_t2 p_t_t'
