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
import SystemFLemmasFTyping2
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import BasicPropsEraseTyping
import PrimitivesSemantics -- this module has moved "up" in the order
import LemmasWeakenWF
import LemmasWeakenWFTV
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
{-@ lem_denotations_selfify :: t:Type -> k:Kind 
        -> { e:Expr | Set_emp (freeBV e) } -> v:Value -> ProofOf(EvalsTo e v) -> ProofOf(Denotes t v)
        -> ProofOf(Denotes (self t e k) v) @-}
lem_denotations_selfify :: Type -> Kind {-> WFType-} -> Expr -> Expr
                                -> EvalsTo -> Denotes -> Denotes
lem_denotations_selfify (TRefn b z p)      Base {-p_emp_t-} e v ev_e_v den_t_v = undefined {-= case den_t_v of
  (DRefn _b _z _p _v p_v_b ev_pv_tt) -> DRefn b z (selfify p b z e) v p_v_b ev_selfpv_tt
      where           -- (subBV x v p) ~>* tt          -- (subBV x v (selfify p b z e)) ~>* tt
        ev_rhs_tt    = lem_equals_evals b z (subFV 0 v p) e v ev_e_v p_v_b 
        ev_selfpv_tt = lemma_and_semantics 
                           (subBV 0 v (selfify p b z e) ? lem_subBV_notin 0 v (Prim Eql)
                                                        ? lem_subBV_notin 0 v e) 
                           True ev_rhs_tt (subBV 0 v p) True ev_pv_tt
-}
lem_denotations_selfify (TFunc z t_z t')   k    {-p_emp_t-} e v ev_e_v den_t_v = den_t_v
lem_denotations_selfify (TExists z t_z t') Base {-p_emp_t-} e v ev_e_v den_t_v = case den_t_v of
  (DExis _z _tz _t' _v p_v_ert' v_z den_tz_vz den_t'vz_v) 
    -> DExis z t_z (self t' e Base) v p_v_ert' v_z den_tz_vz den_selft'vz_v
         where 
           den_selft'vz_v = lem_denotations_selfify (tsubBV z v_z t') Base {-p_emp_t'vz -}
                                                    e v ev_e_v den_t'vz_v
               ? lem_tsubBV_self z v_z t' e Base
lem_denotations_selfify (TPoly a k_a t')   k    {-p_emp_t-} e v ev_e_v den_t_v = den_t_v
lem_denotations_selfify t                  Star {-p_emp_t-} e v ev_e_v den_t_v = den_t_v


--- used in Lemma 8
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


-- should be?     -> { th:CSub | same_binders_cs th t } -> ProofOf(DenotesEnv g th)  
{-@ lem_ctsubst_wf :: g:Env -> t:Type -> k:Kind -> ProofOf(WFType g t k) -> ProofOf (WFEnv g) 
        -> th:CSub -> ProofOf(DenotesEnv g th)  
        -> ProofOf(WFType Empty (ctsubst th t) k) @-}
lem_ctsubst_wf :: Env -> Type -> Kind -> WFType -> WFEnv -> CSub -> DenotesEnv -> WFType
lem_ctsubst_wf Empty            t k p_g_t p_g_wf th den_g_th = case den_g_th of
  (DEmp)                                           -> p_g_t ? lem_binds_env_th Empty th den_g_th
lem_ctsubst_wf (Cons x t_x g')  t k p_g_t p_g_wf th den_g_th = case den_g_th of
  (DExt  g' th' den_g'_th' _x _tx v_x den_th'tx_vx) -> p_emp_tht
    where
      p_emp_vx_th'tx = get_ftyp_from_den (ctsubst th' t_x) v_x den_th'tx_vx ? lem_erase_ctsubst th' t_x
      p_g'_vx_th'tx  = lem_weaken_many_ftyp FEmpty (erase_env g') 
                           (p_er_g'_wf ? lem_empty_concatF (erase_env g'))
                           v_x (erase (ctsubst th' t_x)) p_emp_vx_th'tx 
      (WFEBind _ p_g'_wf _ _ k_x p_g'_tx) = p_g_wf
      p_er_g'_wf     = lem_erase_env_wfenv g' p_g'_wf
      p_g'_th'tx     = lem_ctsubst_wf g' t_x k_x p_g'_tx p_g'_wf th' den_g'_th'
--      p_x'g'_wf      = WFEBind g' p_g'_wf x (ctsubst th' t_x) k_x p_g'_th'tx
      p_g'_tvx       = undefined {- fix this line
                       lem_subst_wf g' Empty x v_x (unerase s_x) p_g'_sx p_g'_wf t k p_g_t
                       -}
      p_emp_tht      = lem_ctsubst_wf g' (tsubFV x v_x t) k p_g'_tvx p_g'_wf th' den_g'_th'
lem_ctsubst_wf (ConsT a k_a g') t k p_g_t p_g_wf th den_g_th = case den_g_th of
  (DExtT g' th' den_g'_th' _a _ka t_a p_emp_ta) -> p_emp_tht
    where
      p_g'_ta        = lem_weaken_many_wf' Empty g' (p_g'_wf ? lem_empty_concatE g') t_a k_a p_emp_ta
      (WFEBindT _ p_g'_wf _ _) = p_g_wf
      p_g'_tta       = undefined -- lem_subst_tv_wf' g' Empty a t_a k_a p_g'_ta p_g_wf t k p_g_t
      p_emp_tht      = lem_ctsubst_wf g' (tsubFTV a t_a t) k p_g'_tta p_g'_wf th' den_g'_th'
