{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module DenotationsSelfify where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Strengthenings
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import PrimitivesFTyping
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasFTyping2
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import BasicPropsEraseTyping
import PrimitivesSemantics -- this module has moved "up" in the order
import LemmasWeakenWF
import LemmasWeakenWFTV
import LemmasWellFormedness
import SubstitutionLemmaWF
import SubstitutionLemmaWFTV
import SubstitutionWFAgain

{-@ reflect foo50 @-}
foo50 :: a -> Maybe a
foo50 x = Just x

{-@ lem_equals_evals :: b:Basic -> z:RVname -> p:Pred -> e:Expr -> v:Value 
        -> ProofOf(EvalsTo e v) -> ProofOf(HasFType FEmpty v (FTBasic b))
        -> ProofOf(EvalsTo (App (App (AppT (Prim Eql) (TRefn b z p)) v) e) 
                           (Bc True)) @-}
lem_equals_evals :: Basic -> RVname -> Expr -> Expr -> Expr -> EvalsTo -> HasFType -> EvalsTo 
lem_equals_evals TBool z p e v ev_e_v p_v_b = case v of -- b in {Bool,Int} is implicit here
  (Bc w)  -> AddStep (App (App (AppT (Prim Eql) (TRefn TBool z p)) v) e) (App (App (Prim Eqv) v) e) step_one
                           (Bc True) ev_eqv_tt
    where
      st_eql_eqv = EPrimT Eql (TRefn TBool z p) -- equals b ~> Prim Eqv
      step_app   = EApp1 (AppT (Prim Eql) (TRefn TBool z p)) (Prim Eqv) st_eql_eqv v
      step_one   = EApp1 (App (AppT (Prim Eql) (TRefn TBool z p)) v) (App (Prim Eqv) v) step_app e
      ev_eqv_tt  = lemma_eqv_semantics v w (Refl v) e w ev_e_v
  _       -> impossible ("by lemma" ? lem_bool_values v p_v_b)
lem_equals_evals TInt  z p e v ev_e_v p_v_b = case v of
  (Ic n) -> AddStep (App (App (AppT (Prim Eql) (TRefn TInt z p)) v) e) (App (App (Prim Eq) v) e) step_one
                    (Bc True) ev_eq_tt
    where
      st_eql_eqv = EPrimT Eql (TRefn TInt z p) -- equals b ~> Prim Eq
      step_app   = EApp1 (AppT (Prim Eql) (TRefn TInt z p)) (Prim Eq) st_eql_eqv v
      step_one   = EApp1 (App (AppT (Prim Eql) (TRefn TInt z p)) v) (App (Prim Eq) v) step_app e
      ev_eq_tt   = lemma_eq_semantics v n (Refl v) e n ev_e_v
  _      -> impossible ("by lemma" ? lem_int_values v p_v_b)
lem_equals_evals b     z p e v ev_e_v p_v_b = impossible ("by lemma" ? lem_base_types_star b p_emp_b)
    where
      p_emp_b = lem_ftyping_wfft FEmpty v (FTBasic b) p_v_b WFFEmpty

--- Lemma 7 in the paper version
{-@ lem_denotations_selfify :: t:Type -> k:Kind -> ProofOf(WFType Empty t k)
        -> { e:Term | Set_emp (freeBV e) } -> ProofOf(HasFType FEmpty e (erase t))
        -> v:Value -> ProofOf(EvalsTo e v) -> ProofOf(Denotes t v)
        -> ProofOf(Denotes (self t e k) v) @-}
lem_denotations_selfify :: Type -> Kind -> WFType -> Expr -> HasFType -> Expr
                                -> EvalsTo -> Denotes -> Denotes
lem_denotations_selfify (TRefn b z p_)     Base p_emp_t e p_e_t v ev_e_v den_t_v = case den_t_v of
  (DRefn _b _z _p _v p_v_b ev_pv_tt) -> DRefn b z (strengthen (eqlPred (TRefn b z p) e) p) 
                                              v p_v_b ev_selfpv_tt
                           ? lem_subBV_strengthen 0 v (eqlPred (TRefn b z p) e) p{--}
      where           -- (subBV x v p) ~>* tt          -- (subBV x v (selfify p b z e)) ~>* tt
        y_           = fresh_var Empty
        y            = y_ ? lem_free_bound_in_env Empty (TRefn b z p) Base p_emp_t y_
        {- @ ev_rhs_tt :: ProofOf(EvalsTo (subBV 0 v (eqlPred (TRefn b z p) e)) (Bc True) ) @-}
        ev_rhs_tt    = lem_equals_evals b z (subFV 0 v p) e v ev_e_v p_v_b 
                                                        ? lem_subBV_notin 0 v (Prim Eql)
                                                        ? lem_subBV_notin 0 v e 
        p_eqlte_b    = lem_eqlPred_ftyping Empty b z (p ? lem_refn_is_pred (TRefn b z p) b z p)
                           p_emp_t WFFEmpty y e p_e_t 
        p_emp_er_t   = lem_erase_wftype Empty (TRefn b z p) Base p_emp_t
        p_y_wf       = WFFBind FEmpty WFFEmpty y (FTBasic b) Base p_emp_er_t
        {- @ p_eqltev_b :: ProofOf(HasFType FEmpty (subBV 0 v (eqlPred (TRefn b z p) e)) (FTBasic TBool)) @-}
        p_eqltev_b   = lem_subst_ftyp FEmpty FEmpty y v (FTBasic b) p_v_b p_y_wf
                                      (unbind 0 y (eqlPred (TRefn b z p) e)) (FTBasic TBool)
                                      p_eqlte_b ? lem_subFV_unbind 0 y v (eqlPred (TRefn b z p) e)
                                      ? lem_empty_concatF FEmpty
        {-@ ev_selfpv_tt :: ProofOf(EvalsTo (strengthen (subBV 0 v (eqlPred (TRefn b z p) e)) (subBV 0 v p)) (Bc True)) @-}
        ev_selfpv_tt = undefined {- this one diverges!
                           lemma_strengthen_semantics 
                           (subBV 0 v (eqlPred (TRefn b z p) e)) --(selfify p b z e) 
                           True ev_rhs_tt (subBV 0 v p) True ev_pv_tt p_eqltev_b -}
        p            = p_ ? lem_refn_is_pred (TRefn b z p_) b z p_
lem_denotations_selfify (TFunc z t_z t')   k    p_emp_t e p_e_t v ev_e_v den_t_v = den_t_v
lem_denotations_selfify (TExists z t_z t') Base p_emp_t e p_e_t v ev_e_v den_t_v = case den_t_v of
  (DExis _z _tz _t' _v p_v_ert' v_z den_tz_vz den_t'vz_v) 
    -> DExis z t_z (self t' e Base) v p_v_ert' v_z den_tz_vz den_selft'vz_v
         where 
           p_vz_er_tz     = get_ftyp_from_den t_z v_z den_tz_vz
           (WFExis _ _ _ k_z p_g_tz _ k_t' y p_y_t')
                          = lem_wfexis_for_wf_texists Empty  z t_z t' Base p_emp_t 
           p_y_wf         = WFEBind Empty WFEEmpty y t_z k_z p_g_tz
           p_emp_t'vz     = lem_subst_wf Empty Empty y v_z t_z p_vz_er_tz p_y_wf 
                                         (unbindT z y t') k_t' p_y_t'
                                         ? lem_empty_concatE Empty
                                         ? lem_tsubFV_unbindT z y v_z t'
           den_selft'vz_v = lem_denotations_selfify (tsubBV z v_z t') k_t' p_emp_t'vz 
                                                    e (p_e_t ? lem_erase_tsubBV z v_z t')
                                                    v ev_e_v den_t'vz_v
                                                    ? lem_tsubBV_self z v_z t' e Base
lem_denotations_selfify (TPoly a k_a t')   k    p_emp_t e p_e_t v ev_e_v den_t_v = den_t_v
lem_denotations_selfify t                  Star p_emp_t e p_e_t v ev_e_v den_t_v = den_t_v


{--- used in Lemma 8
{-@ lem_denote_ctsubst_refn_var :: g:Env -> a:Vname -> x:RVname -> p:Pred -> th:CSub
        -> ProofOf(DenotesEnv g th) -> v:Value -> ProofOf(Denotes (ctsubst th (TRefn (FTV a) x p)) v)
        -> (Denotes,EvalsTo)<{\pf ev -> propOf pf == Denotes (csubst_tv th a) v && 
                                        propOf ev == EvalsTo (subBV 0 v (csubst th p)) (Bc True) }> @-} 
lem_denote_ctsubst_refn_var :: Env -> Vname -> RVname -> Pred -> CSub -> DenotesEnv -> Expr
                                   -> Denotes -> (Denotes, EvalsTo)
lem_denote_ctsubst_refn_var g a x p th den_g_th v den_thap_v = undefined

{-@ lem_denote_ctsubst_refn_var' :: g:Env -> a:Vname -> x:RVname -> p:Pred -> th:CSub
        -> ProofOf(DenotesEnv g th) -> v:Value -> ProofOf(Denotes (csubst_tv th a) v)
        -> ProofOf(EvalsTo (subBV 0 v (csubst th p)) (Bc True))
        -> ProofOf(Denotes (ctsubst th (TRefn (FTV a) x p)) v) @-}
lem_denote_ctsubst_refn_var' :: Env -> Vname -> RVname -> Pred -> CSub -> DenotesEnv -> Expr
                                    -> Denotes -> EvalsTo -> Denotes
lem_denote_ctsubst_refn_var' g a x p th den_g_th v den_tha_v ev_thpv_tt = undefined
-}
