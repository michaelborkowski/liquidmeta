{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SubstitutionLemmaEnt where

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
import PrimitivesSemantics
import LemmasWellFormedness
import LemmasTyping
import LemmasSubtyping
import SubstitutionLemmaWF
import SubstitutionWFAgain
import DenotationsSoundness

{-@ reflect foo61 @-}
foo61 x = Just x
foo61 :: a -> Maybe a

data AugmentedCSubP where
    AugmentedCSub :: Env -> Env -> Vname -> Expr -> Type -> CSub -> AugmentedCSubP

data AugmentedCSub where
    InsertInCS :: Env -> Env -> Vname -> Expr -> Type -> CSub -> CSub -> DenotesEnv
                      -> (Expr -> Proof) -> (Type -> Proof) -> AugmentedCSub

{-@ data AugmentedCSub where
      InsertInCS :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
          -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value -> t_x:Type 
          -> th':CSub -> th:CSub -> ProofOf(DenotesEnv (concatE (Cons x t_x g) g') th)
          -> ( p:Pred -> { pf:Proof | csubst th p  ==  csubst th'  (subFV x v_x p) } )
          -> ( t:Type -> { pf:Proof | ctsubst th t == ctsubst th' (tsubFV x v_x t) } )
          -> ProofOf(AugmentedCSub g g' x v_x t_x th') @-}

{-@ lem_add_var_csubst :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> ProofOf(HasType g v_x t_x)
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') )
        -> th':CSub -> ProofOf(DenotesEnv (concatE g (esubFV x v_x g')) th')
        -> ProofOf(AugmentedCSub g g' x v_x t_x th') / [envsize g'] @-}
lem_add_var_csubst :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                          -> CSub -> DenotesEnv -> AugmentedCSub
lem_add_var_csubst g Empty           x v_x_ t_x p_vx_tx p_env_wf zth' den_env'_th' 
  = case p_env_wf of -- env = Cons x t_x g
      (WFEBind _ p_g_wf _ _ _ _) -> case (lem_denote_sound_typ g v_x_ t_x p_vx_tx 
                                                               p_g_wf zth' den_env'_th') of
        (ValDen _ _ val ev_th'vx_val den_th'tx_val) 
          -> InsertInCS g Empty x v_x t_x zth' {-th-} 
                        (CCons x th'vx (zth' ? lem_binds_env_th g zth' den_env'_th'))
                        (DExt g zth' den_env'_th' x t_x th'vx  den_th'tx_th'vx) eq_func1 eq_func2
               where
                 {-@ v_x :: { v_x:Value | Set_sub (fv v_x)  (vbindsC zth') &&
                                          Set_sub (ftv v_x) (tvbindsC zth') && v_x == v_x_ } @-}
                 v_x   = v_x_ ? lem_binds_env_th g zth' den_env'_th'
                              ? lem_fv_subset_binds g v_x_ t_x p_vx_tx p_g_wf
                              ? lem_csubst_value zth' v_x_
                              ? lem_den_nofv (csubst zth' v_x_) (ctsubst zth' t_x) -- den_th'tx_th'vx
                                    (den_th'tx_val ? lem_value_refl (csubst zth' v_x_) val ev_th'vx_val) 
                 {-@ th'vx :: { v:Value | Set_emp (fv v) && v == csubst zth' v_x } @-}
                 th'vx :: Expr
                 th'vx_ = csubst zth' v_x {-? lem_csubst_value zth' v_x -}
                 th'vx  = th'vx_ ? lem_den_nofv (csubst zth' v_x) (ctsubst zth' t_x) -- den_th'tx_th'vx 
                                                (den_th'tx_val ? lem_value_refl th'vx_ val ev_th'vx_val) 
                                 ? lem_den_nobv (csubst zth' v_x) (ctsubst zth' t_x) -- den_th'tx_th'vx 
                                                (den_th'tx_val ? lem_value_refl th'vx_ val ev_th'vx_val) 
                 {-@ den_th'tx_th'vx :: ProofOf(Denotes (ctsubst zth' t_x) (csubst zth' v_x)) @-}
                 den_th'tx_th'vx :: Denotes
                 den_th'tx_th'vx = den_th'tx_val ? lem_value_refl th'vx val ev_th'vx_val
        {- @ eq_func1 :: p:Pred -> { pf:Proof | csubst th p == csubst zth' (subFV x v_x_ p) } @-}
                 eq_func1 :: Expr -> Proof   -- csubst th p
                 eq_func1 p = () ? lem_csubst_subFV   zth' x v_x  p 
                                 ? lem_binds_env_th g zth' den_env'_th'
        {- @ eq_func2 :: t:Type -> { pf:Proof | ctsubst th t == ctsubst zth' (tsubFV x v_x_ t) } @-}
                 eq_func2 :: Type -> Proof
                 eq_func2 t = () ? lem_ctsubst_tsubFV zth' x v_x  t
                                 ? lem_binds_env_th g zth' den_env'_th'
lem_add_var_csubst g (Cons z t_z g') x v_x_ t_x p_vx_tx p_zenv_wf zth' den_zenv'_zth'
  = case den_zenv'_zth' of   
      (DExt env' th' den_env'_th' _z tzvx v_z_ den_th'tzvx_vz)
        -> InsertInCS g (Cons z t_z g') x v_x_ t_x zth' zth den_zenv_zth eq_funcz1 eq_funcz2
             where
               v_z          = v_z_ ? lem_den_nofv v_z_ (ctsubst th' tzvx) den_th'tzvx_vz
                                   ? lem_den_nobv v_z_ (ctsubst th' tzvx) den_th'tzvx_vz 
               zth          = CCons z v_z (th ? lem_binds_env_th env th den_env_th) 
               den_zenv_zth = DExt env th den_env_th z t_z v_z den_thtz_vz
               den_thtz_vz  = den_th'tzvx_vz ? eq_func2 t_z
               (WFEBind _ p_env_wf _ _ _ _) = p_zenv_wf
               p_xg_wf = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
               (WFEBind _ p_g_wf _ _ _ _) = p_xg_wf 
               env          = concatE (Cons x t_x g) g'
               {-@ eq_func1 :: p:Pred -> { pf:Proof | csubst th p == csubst th' (subFV x v_x_ p) } @-}
               {-@ eq_func2 :: t:Type -> { pf:Proof | ctsubst th t == ctsubst th' (tsubFV x v_x_ t) } @-}
               eq_func1 :: Expr -> Proof
               eq_func2 :: Type -> Proof 
               (InsertInCS _ _ _ _ _ _ th den_env_th eq_func1 eq_func2)
                            = lem_add_var_csubst g g' x v_x_ t_x p_vx_tx p_env_wf th' den_env'_th'
               -- csubst zth p  ==  csubst zth'  (subFV x v_x p)
               {-@ eq_funcz1 :: p:Pred
                        -> { pf:Proof | csubst (CCons z v_z th) p == csubst zth' (subFV x v_x_ p) } @-}
               eq_funcz1 :: Expr -> Proof
               eq_funcz1 p = () --    ? toProof ( csubst zth' (subFV x v_x_ p) 
                                              ? lem_binds_env_th env' th' den_env'_th'
                                              ? toProof ( zth' === CCons z v_z th' )
--                                            === csubst th' (subFV z v_z (subFV x v_x_ p))
                                              ? lem_subFV_notin x v_x_ v_z
--                                            === csubst th' (subFV z (subFV x v_x_ v_z) (subFV x v_x_ p)) 
                                              ? lem_commute_subFV  z v_z x -- v_x_ p
                                                       (v_x_ ? lem_fv_bound_in_env g v_x_ t_x p_vx_tx p_g_wf z) p
--                                            === csubst th' (subFV x v_x_ (subFV z v_z p)) 
                                              ? eq_func1 (subFV z v_z p)
--                                            === csubst th (subFV z v_z p) ) 
               {-@ eq_funcz2 :: t:Type 
                        -> { pf:Proof | ctsubst (CCons z v_z th) t == ctsubst zth' (tsubFV x v_x_ t) } @-}
               eq_funcz2 :: Type -> Proof
               eq_funcz2 t = () --    ? toProof ( ctsubst zth' (tsubFV x v_x_ t) 
                                              ? lem_binds_env_th env' th' den_env'_th'
                                              ? toProof ( zth' === CCons z v_z th' )
--                                            === ctsubst th' (tsubFV z v_z (tsubFV x v_x_ t))
                                              ? lem_subFV_notin x v_x_ v_z
--                                            === ctsubst th' (tsubFV z (subFV x v_x_ v_z) (tsubFV x v_x_ t)) 
                                              ? lem_commute_tsubFV  z v_z x -- v_x_ p
                                                       (v_x_ ? lem_fv_bound_in_env g v_x_ t_x p_vx_tx p_g_wf z) t
--                                            === ctsubst th' (tsubFV x v_x_ (tsubFV z v_z t)) 
                                              ? eq_func2 (tsubFV z v_z t)
--                                            === ctsubst th (tsubFV z v_z t) )  
lem_add_var_csubst g (ConsT a k_a g') x v_x_ t_x p_vx_tx p_aenv_wf zth' den_aenv'_zth' 
  = case den_aenv'_zth' of   
      (DExtT env' th' den_env'_th' _a _ka {-tavx-} t_a p_emp_ta {-den_th'tzvx_vz-})
        -> InsertInCS g (ConsT a k_a g') x v_x_ t_x zth' ath den_aenv_ath eq_funca1 eq_funca2
             where
               ath          = CConsT a t_a (th ? lem_binds_env_th env th den_env_th) 
               den_aenv_ath = DExtT env th den_env_th a k_a t_a p_emp_ta --den_thtz_vz
               (WFEBindT _ p_env_wf _ _) = p_aenv_wf
               p_xg_wf = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
               (WFEBind _ p_g_wf _ _ _ _) = p_xg_wf 
               env          = concatE (Cons x t_x g) g'
               {-@ eq_func1 :: p:Pred -> { pf:Proof | csubst th p == csubst th' (subFV x v_x_ p) } @-}
               {-@ eq_func2 :: t:Type -> { pf:Proof | ctsubst th t == ctsubst th' (tsubFV x v_x_ t) } @-}
               eq_func1 :: Expr -> Proof
               eq_func2 :: Type -> Proof 
               (InsertInCS _ _ _ _ _ _ th den_env_th eq_func1 eq_func2)
                            = lem_add_var_csubst g g' x v_x_ t_x p_vx_tx p_env_wf th' den_env'_th'
               -- csubst zth p  ==  csubst zth'  (subFV x v_x p)
               {-@ eq_funca1 :: p:Pred
                        -> { pf:Proof | csubst (CConsT a t_a th) p == csubst zth' (subFV x v_x_ p) } @-}
               eq_funca1 :: Expr -> Proof
               eq_funca1 p = () --    ? toProof ( csubst zth' (subFV x v_x_ p) 
                                              ? lem_binds_env_th env' th' den_env'_th'
                                              ? toProof ( zth' === CConsT a t_a th' )
--                                            === csubst th' (subFTV a t_a (subFV x v_x_ p))
                                              ? lem_tsubFV_notin x v_x_ t_a
--                                            === csubst th' (subFTV a (tsubFV x v_x_ t_a) (subFV x v_x_ p)) 
                                              ? lem_commute_subFV_subFTV  a t_a x
                                                       (v_x_ ? lem_fv_bound_in_env g v_x_ t_x p_vx_tx p_g_wf a) p
--                                            === csubst th' (subFV x v_x_ (subFTV a t_a p)) 
                                              ? eq_func1  (subFTV a t_a p)
--                                            === csubst th (subFTV a t_a p) ) 
               {-@ eq_funca2 :: t:Type 
                        -> { pf:Proof | ctsubst (CConsT a t_a th) t == ctsubst zth' (tsubFV x v_x_ t) } @-}
               eq_funca2 :: Type -> Proof
               eq_funca2 t = () --    ? toProof ( ctsubst zth' (tsubFV x v_x_ t) 
                                              ? lem_binds_env_th env' th' den_env'_th'
                                              ? toProof ( zth' === CConsT a t_a th' )
--                                            === ctsubst th' (tsubFTV a t_a (tsubFV x v_x_ t))
                                              ? lem_tsubFV_notin x v_x_ t_a
--                                            === ctsubst th' (tsubFTV a (tsubFV x v_x_ t_a) (tsubFV x v_x_ t)) 
                                              ? lem_commute_tsubFV_tsubFTV  a t_a x 
                                                       (v_x_ ? lem_fv_bound_in_env g v_x_ t_x p_vx_tx p_g_wf a) t
--                                            === ctsubst th' (tsubFV x v_x_ (tsubFTV a t_a t)) 
                                              ? eq_func2 (tsubFTV a t_a t)
--                                            === ctsubst th (tsubFTV a t_a t) ) 
               _            = zth'

{-@ lem_subst_ent :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
            -> t_x:Type -> ProofOf(HasType g v_x t_x) 
            -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) 
            -> { p:Pred | Set_sub (Set_cup (fv p) (ftv p)) (binds (concatE (Cons x t_x g) g')) }
            -> ProofOf(Entails (concatE (Cons x t_x g) g') p) 
            -> ProofOf(Entails (concatE g (esubFV x v_x g')) (subFV x v_x p)) @-}
lem_subst_ent :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv -> Expr -> Entails -> Entails
lem_subst_ent g g' x v_x t_x p_vx_tx p_env_wf p (EntPred env _p evals_func)
  = EntPred (concatE g (esubFV x v_x g')) (subFV x v_x p) evals_func'
      where
        {-@ evals_func' :: th':CSub -> ProofOf(DenotesEnv (concatE g (esubFV x v_x g')) th')
                                -> ProofOf(EvalsTo (csubst th' (subFV x v_x p)) (Bc True)) @-}
        evals_func' :: CSub -> DenotesEnv -> EvalsTo  
        evals_func' th' den_env'_th' = evals_func th den_env_th ? eq_func p
          where
            (InsertInCS _ _ _ _ _ _ th den_env_th eq_func _) 
                = lem_add_var_csubst g g' x v_x t_x p_vx_tx p_env_wf th' den_env'_th'
