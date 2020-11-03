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
import LemmasWellFormedness
import LemmasTyping
import LemmasSubtyping
import LemmasChangeVarTyp
import LemmasWeakenTyp
import SubstitutionLemmaWF
import DenotationsSelfify
import DenotationsSoundnessSub
import PrimitivesSemantics
import PrimitivesDenotations
import DenotationsSoundnessTyp
import LemmasExactness
import SubstitutionLemmaEnt

{-@ reflect foo54b @-}
foo54b x = Just x
foo54b :: a -> Maybe a

{-@ lem_subst_tv_typ_tvar :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:Type
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTVar p_e_t}
        -> ProofOf(HasType (concatE g (esubFTV a t_a g')) (subFTV a t_a e) (tsubFTV a t_a t)) / [typSize p_e_t] @-}
lem_subst_tv_typ_tvar :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_tv_typ_tvar g g' a t_a k_a p_g_ta p_env_wf e t (TVar1 _env z t') 
  = case g' of          -- empty case: e = FV z = FV x and t = self t' x = self t_x x
      (Empty)           -> impossible "a <> z" {-lem_exact_type g v_x t_x p_vx_tx 
                                   ? lem_free_bound_in_env g t_x k_x p_g_tx x
                                   ? lem_tsubFV_self x v_x t_x z
                                   ? toProof (tsubFV x v_x t_x === t_x)
        where
          (WFEBind _g p_g_wf _x _tx k_x p_g_tx) = p_env_wf-}
      (Cons _z _ g'')  -> TVar1 (concatE g (esubFTV a t_a g''))  -- z <> x, t = self t' (FV z)
                                (z ? lem_in_env_esubFTV g'' a t_a z
                                   ? lem_in_env_concat g g'' z
                                   ? lem_in_env_concat (ConsT a k_a g) g'' z)          
                                (tsubFTV a t_a t') -- ? lem_tsubFV_self2 x v_x t' z do i need new lemma?
lem_subst_tv_typ_tvar g g' a t_a k_a p_g_ta p_env_wf e t (TVar2 env_ z _t p_z_t w_ t_w) 
    = case g' of             -- g'' = Empty so x = w and p_z_t :: HasFType(g (FV z) t)
        (Empty)            -> impossible " "
        (Cons  _w _tw g'') -> case (a == z) of 
            True   -> impossible "a <> z"
            False  -> TVar2 (concatE g (esubFTV a t_a g'')) --z
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
{-            (True)  -> lem_weaken_typ (concatE g (esubFV x v_x g'')) Empty p_env'_wf
                                      v_x (tsubFV x v_x t) p_gg''_vx_tx w (tsubFV x v_x t_w)
                                      ? toProof ( e === (FV x) )
                         where
                           (WFEBind _gg'' p_gg''_wf _ _ _ _) = p_env_wf
                           w = w_ ? lem_in_env_esub g'' x v_x w_
                                  ? lem_in_env_concat g g'' w_
                                  ? lem_in_env_concat (Cons x t_x g) g'' w_
                                  ? lem_fv_bound_in_env g v_x t_x p_vx_tx w_
                           p_env'_wf    = lem_subst_wfenv g g'' x v_x t_x p_vx_tx p_gg''_wf
                           p_gg''_vx_tx = lem_subst_typ g g'' x v_x t_x p_vx_tx p_gg''_wf
                                                        e t p_z_t -}
lem_subst_tv_typ_tvar g g' a t_a k_a p_g_ta p_env_wf e t p_e_t = undefined
{-
lem_subst_typ_tvar g g' a t_a k_a p_g_ta p_env_wf e t (TVar3 env_ z _t p_z_t a'_ k_a') 
    = case g' of             -- g'' = Empty so a = a' and p_z_t :: HasFType(g (FV z) t)
        (Empty)            -> case (a == z) of
            (True)  -> impossible "it is"
            (False) -> p_z_t ? toProof ( tsubFTV a t_a t === t )
                             ? lem_free_bound_in_env g t Star p_g_t a
                             ? toProof ( e === (FV z) )
                         where
                           (WFEBindT g_ p_g_wf _ _) = p_env_wf
                           p_g_t = lem_typing_wf g (FV z) t p_z_t p_g_wf
        (ConsT _a' _  g'') -> case (a == z) of
            (True)  -> impossible "" {-lem_weaken_tv_typ (concatE g (esubFV x v_x g'')) Empty p_env'_wf
                                         v_x (tsubFV x v_x t) p_gg''_vx_tx a k_a
                                         ? toProof ( e === (FV x) )
                         where
                           (WFEBindT _gg'' p_gg''_wf _ _) = p_env_wf
                           a = a_ ? lem_in_env_esub g'' x v_x a_
                                  ? lem_in_env_concat g g'' a_
                                  ? lem_in_env_concat (Cons x t_x g) g'' a_
                                  ? lem_fv_bound_in_env g v_x t_x p_vx_tx a_
                           p_env'_wf    = lem_subst_wfenv g g'' x v_x t_x p_vx_tx p_gg''_wf
                           p_gg''_vx_tx = lem_subst_typ g g'' x v_x t_x p_vx_tx p_gg''_wf
                                                        e t p_z_t -}
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
-}
{-@ lem_subst_tv_typ :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:Type
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t }
        -> ProofOf(HasType (concatE g (esubFTV a t_a g')) (subFTV a t_a e) (tsubFTV a t_a t)) / [typSize p_e_t] @-}
lem_subst_tv_typ :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t (TBC _env b)
  = TBC (concatE g (esubFTV a t_a g')) b ? lem_tsubFTV_tybc a t_a b
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t (TIC _env n)
  = TIC (concatE g (esubFTV a t_a g')) n ? lem_tsubFTV_tyic a t_a n
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t p_e_t@(TVar1 {}) 
  = lem_subst_tv_typ_tvar g g' a t_a k_a p_g_ta p_env_wf e t p_e_t
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t p_e_t@(TVar2 {}) 
  = lem_subst_tv_typ_tvar g g' a t_a k_a p_g_ta p_env_wf e t p_e_t
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t p_e_t@(TVar3 {}) 
  = lem_subst_tv_typ_tvar g g' a t_a k_a p_g_ta p_env_wf e t p_e_t
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t (TPrm _env c)
  = TPrm (concatE g (esubFTV a t_a g')) c ? lem_tsubFTV_ty a t_a c
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t (TAbs {}) = undefined
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t (TApp {}) = undefined
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t (TAbsT {}) = undefined
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t (TAppT {}) = undefined
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t (TLet {}) = undefined
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t (TAnn {}) = undefined
lem_subst_tv_typ g g' a t_a k_a p_g_ta p_env_wf e t (TSub {}) = undefined

{-@ lem_subst_tv_sub :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:Type
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) 
        -> s:Type -> k_s:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') s k_s)
        -> t:Type -> k_t:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') t k_t)
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (ConsT a k_a g) g') s t }
        -> ProofOf(Subtype (concatE g (esubFTV a t_a g')) (tsubFTV a t_a s) (tsubFTV a t_a t)) / [subtypSize p_s_t] @-}
lem_subst_tv_sub :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                    -> Type -> Kind -> WFType -> Type -> Kind -> WFType -> Subtype -> Subtype
lem_subst_tv_sub g g' a t_a k_a p_g_ta p_env_wf s k_s p_env_s t k_t p_env_t 
              (SBase env z1 b p1 z2 p2 y_ ent_yenv_p2) = undefined
lem_subst_tv_sub g g' a t_a k_a p_g_ta p_env_wf ty1 ky1 p_env_ty1 ty2 ky2 p_env_ty2
              (SFunc env_ x1 s1 x2 s2 p_s2_s1 t1 t2 y_ p_yenv_t1_t2) = undefined 
lem_subst_tv_sub g g' a t_a k_a p_g_ta p_env_wf t k p_env_t t2 k2 p_env_t2
              (SWitn env v_z t_z p_env_vz_tz _t z t' p_env_t_t'vz) = undefined 
lem_subst_tv_sub g g' a t_a k_a p_g_ta p_env_wf t1 k1 p_env_t1 t' k' p_env_t'
              (SBind env z t_z t _t' w_ p_wenv_t_t') = undefined 
lem_subst_tv_sub g g' a t_a k_a p_g_ta p_env_wf t1 k1 p_env_t1 t2 k2 p_env_t2 (SPoly {}) = undefined 
