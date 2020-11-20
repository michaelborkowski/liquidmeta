{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module DenotationsSelfify where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import SameBinders
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import PrimitivesFTyping
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasFTyping
import Typing
import SystemFAlphaEquivalence
import BasicPropsCSubst
import BasicPropsDenotes
import PrimitivesSemantics -- this module has moved "up" in the order
import LemmasWeakenWF
import SubstitutionLemmaWF
import SubstitutionLemmaWFTV

{-@ reflect foo50 @-}
foo50 x = Just x
foo50 :: a -> Maybe a

{-@ lem_equals_evals :: e:Expr -> v:Value -> ProofOf(EvalsTo e v) -> b:Basic 
        -> ProofOf(HasFType FEmpty v (FTBasic b))
        -> ProofOf(EvalsTo (App (App (equals b) v) e) (Bc True)) @-}
lem_equals_evals :: Expr -> Expr -> EvalsTo -> Basic -> HasFType -> EvalsTo
lem_equals_evals e v ev_e_v TBool p_v_b = case v of
  (Bc w)  -> AddStep (App (App (equals TBool) v) e) (App (App (Prim Eqv) v) e) step_one
                           (Bc True) ev_eqv_tt
    where
      st_eql_eqv = EPrimT Eql (TRefn TBool 1 (Bc True)) -- equals b ~> Prim Eqv
      step_app   = EApp1 (equals TBool) (Prim Eqv) st_eql_eqv v
      step_one   = EApp1 (App (equals TBool) v) (App (Prim Eqv) v) step_app e
      ev_eqv_tt  = lemma_eqv_semantics v w (Refl v) e w ev_e_v
  _       -> impossible ("by lemma" ? lem_bool_values v p_v_b)
lem_equals_evals e v ev_e_v TInt  p_v_b = case v of
  (Ic n) -> AddStep (App (App (equals TInt) v) e) (App (App (Prim Eq) v) e) step_one
                    (Bc True) ev_eq_tt
    where
      st_eql_eqv = EPrimT Eql (TRefn TInt 1 (Bc True)) -- equals b ~> Prim Eq
      step_app   = EApp1 (equals TInt) (Prim Eq) st_eql_eqv v
      step_one   = EApp1 (App (equals TInt) v) (App (Prim Eq) v) step_app e
      ev_eq_tt   = lemma_eq_semantics v n (Refl v) e n ev_e_v
  _      -> impossible ("by lemma" ? lem_int_values v p_v_b)
lem_equals_evals e v ev_e_v b     p_v_b = impossible ("by lemma" ? lem_base_types_star b p_emp_b)
    where
      p_emp_b = lem_ftyping_wfft FEmpty v (FTBasic b) p_v_b WFFEmpty

--- Lemma 7 in the paper version
{-@ lem_denotations_selfify :: t:Type -> k:Kind 
        -> { e:Expr | Set_emp (freeBV e) } -> v:Value -> ProofOf(EvalsTo e v) -> ProofOf(Denotes t v)
        -> ProofOf(Denotes (self t e k) v) @-}
lem_denotations_selfify :: Type -> Kind {-> WFType-} -> Expr -> Expr
                                -> EvalsTo -> Denotes -> Denotes
lem_denotations_selfify (TRefn b z p)      Base {-p_emp_t-} e v ev_e_v den_t_v = case den_t_v of
  (DRefn _b _z _p _v p_v_b ev_pv_tt) -> DRefn b z (selfify p b z e) v p_v_b ev_selfpv_tt
      where           -- (subBV x v p) ~>* tt          -- (subBV x v (selfify p b z e)) ~>* tt
        ev_rhs_tt    = lem_equals_evals e v ev_e_v b p_v_b 
        ev_selfpv_tt = lemma_and_semantics (subBV z v p) True ev_pv_tt 
                           (subBV z v (App (App (equals b) (BV z)) e) ? lem_subBV_notin z v (equals b)
                                                                      ? lem_subBV_notin z v e) 
                           True ev_rhs_tt
lem_denotations_selfify (TFunc z t_z t')   k    {-p_emp_t-} e v ev_e_v den_t_v = den_t_v
lem_denotations_selfify (TExists z t_z t') Base {-p_emp_t-} e v ev_e_v den_t_v = case den_t_v of
  (DExis _z _tz _t' _v s eqv_ert'_s p_v_s v_z den_tz_vz den_t'vz_v) 
    -> DExis z t_z (self t' e Base) v s eqv_ert'_s p_v_s v_z den_tz_vz den_selft'vz_v
         where 
           den_selft'vz_v = lem_denotations_selfify (tsubBV z v_z t') Base {-p_emp_t'vz -}
                                                    e v ev_e_v den_t'vz_v
               ? lem_tsubBV_self z v_z t' e Base
lem_denotations_selfify (TPoly a k_a t')   k    {-p_emp_t-} e v ev_e_v den_t_v = den_t_v
lem_denotations_selfify t                  Star {-p_emp_t-} e v ev_e_v den_t_v = den_t_v


--- used in Lemma 8
{-@ lem_denote_ctsubst_refn_var :: g:Env -> a:Vname -> x:Vname -> p:Pred -> th:CSub
        -> ProofOf(DenotesEnv g th) -> v:Value -> ProofOf(Denotes (ctsubst th (TRefn (FTV a) x p)) v)
        -> (Denotes,EvalsTo)<{\pf ev -> propOf pf == Denotes (csubst_tv th a) v && 
                                        propOf ev == EvalsTo (subBV x v (csubst th p)) (Bc True) }> @-} 
lem_denote_ctsubst_refn_var :: Env -> Vname -> Vname -> Pred -> CSub -> DenotesEnv -> Expr
                                   -> Denotes -> (Denotes, EvalsTo)
lem_denote_ctsubst_refn_var g a x p th den_g_th v den_thap_v = undefined

{-@ lem_denote_ctsubst_refn_var' :: g:Env -> a:Vname -> x:Vname -> p:Pred -> th:CSub
        -> ProofOf(DenotesEnv g th) -> v:Value -> ProofOf(Denotes (csubst_tv th a) v)
        -> ProofOf(EvalsTo (subBV x v (csubst th p)) (Bc True))
        -> ProofOf(Denotes (ctsubst th (TRefn (FTV a) x p)) v) @-}
lem_denote_ctsubst_refn_var' :: Env -> Vname -> Vname -> Pred -> CSub -> DenotesEnv -> Expr
                                    -> Denotes -> EvalsTo -> Denotes
lem_denote_ctsubst_refn_var' g a x p th den_g_th v den_tha_v ev_thpv_tt = undefined


{-@ lem_ctsubst_wf :: g:Env -> t:Type -> k:Kind -> ProofOf(WFType g t k) -> ProofOf (WFEnv g) 
        -> { th:CSub | same_binders_cs th t } -> ProofOf(DenotesEnv g th)  
        -> ProofOf(WFType Empty (ctsubst th t) k) @-}
lem_ctsubst_wf :: Env -> Type -> Kind -> WFType -> WFEnv -> CSub -> DenotesEnv -> WFType
lem_ctsubst_wf Empty            t k p_g_t p_g_wf th den_g_th = case den_g_th of
  (DEmp)                                           -> p_g_t ? lem_binds_env_th Empty th den_g_th
lem_ctsubst_wf (Cons x t_x g')  t k p_g_t p_g_wf th den_g_th = case den_g_th of
  (DExt  g' th' den_g'_th' _x _tx v_x den_th'tx_vx) -> p_emp_tht
    where
      (s_x, p_emp_sx) = get_ftyp_from_den (ctsubst th' t_x) v_x den_th'tx_vx -- ? lem_erase_ctsubst th' t_x
      p_g'_sx        = lem_weaken_many_ftyp FEmpty (erase_env g') 
                           (p_er_g'_wf ? lem_empty_concatF (erase_env g'))
                           v_x s_x p_emp_sx -- (erase (ctsubst th' t_x)) p_emp_vx_th'tx 
      (WFEBind _ p_g'_wf _ _ k_x p_g'_tx) = p_g_wf
      p_er_g'_wf     = lem_erase_env_wfenv g' p_g'_wf
      p_g'_th'tx     = lem_ctsubst_wf g' t_x k_x p_g'_tx p_g'_wf th' den_g'_th'
--      p_x'g'_wf      = WFEBind g' p_g'_wf x (ctsubst th' t_x) k_x p_g'_th'tx
      p_g'_tvx       = undefined {- fix this line
                       lem_subst_wf g' Empty x v_x (unerase s_x) p_g'_sx p_g'_wf t k p_g_t
                       -}
      p_emp_tht      = lem_ctsubst_wf g' (tsubFV x v_x t) k p_g'_tvx p_g'_wf 
                                      (th' ? lem_same_binders_cs x v_x th' t) den_g'_th'
lem_ctsubst_wf (ConsT a k_a g') t k p_g_t p_g_wf th den_g_th = case den_g_th of
  (DExtT g' th' den_g'_th' _a _ka t_a p_emp_ta) -> p_emp_tht
    where
      p_g'_ta        = lem_weaken_many_wf' Empty g' (p_g'_wf ? lem_empty_concatE g') t_a k_a p_emp_ta
      (WFEBindT _ p_g'_wf _ _) = p_g_wf
      p_g'_tta       = lem_subst_tv_wf' g' Empty a t_a k_a p_g'_ta p_g_wf t k p_g_t
      p_emp_tht      = lem_ctsubst_wf g' (tsubFTV a t_a t) k p_g'_tta p_g'_wf 
                                      (th' ? lem_same_binders_cs_tv a t_a th' t) den_g'_th'
