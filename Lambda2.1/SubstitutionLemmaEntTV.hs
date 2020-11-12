{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SubstitutionLemmaEntTV where

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
import DenotationsSoundnessTyp
--import LemmasExactness

{-@ reflect foo62 @-}
foo62 x = Just x
foo62 :: a -> Maybe a

{- CHECKED 
{-@ lem_subst_tv_wfenv :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:Type
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') )
        -> ProofOf(WFEnv (concatE g (esubFTV a t_a g')) ) / [envsize g'] @-}
lem_subst_tv_wfenv :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv -> WFEnv
lem_subst_tv_wfenv g Empty           a t_a k_a p_g_ta p_xg_wf  = case p_xg_wf of
  (WFEBind  _g p_g_wf _ _ _ _) -> p_g_wf
  (WFEBindT _g p_g_wf _ _)     -> p_g_wf
lem_subst_tv_wfenv g (Cons z t_z g') a t_a k_a p_g_ta p_env_wf = case p_env_wf of
  (WFEBind env' p_env'_wf _z _tz k_z p_env'_tz) 
    -> WFEBind env'' p_env''_wf z (tsubFTV a t_a t_z) k_z p_env''_tzta
      where
        env''        = concatE g (esubFTV a t_a g')
        p_env''_wf   = lem_subst_tv_wfenv g g' a t_a k_a p_g_ta p_env'_wf
        p_env''_tzta = lem_subst_tv_wf    g g' a t_a k_a p_g_ta p_env'_wf t_z k_z p_env'_tz
lem_subst_tv_wfenv g (ConsT a1 k1 g') a t_a k_a p_g_ta p_env_wf = case p_env_wf of
  (WFEBindT env' p_env'_wf _a1 _k1)          -> WFEBindT env'' p_env''_wf a1 k1
    where
      env''      = concatE g (esubFTV a t_a g')
      p_env''_wf = lem_subst_tv_wfenv g g' a t_a k_a p_g_ta p_env'_wf
-}

data TVAugmentedCSubP where
    TVAugmentedCSub :: Env -> Env -> Vname -> Type -> Kind -> CSub -> TVAugmentedCSubP

data TVAugmentedCSub where
    InsertTVInCS :: Env -> Env -> Vname -> Type -> Kind -> CSub -> CSub -> DenotesEnv
                      -> (Expr -> Proof) -> (Type -> Proof) -> TVAugmentedCSub

{-@ data TVAugmentedCSub where
      InsertTVInCS :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
          -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:Type -> k_a:Kind
          -> th':CSub -> th:CSub -> ProofOf(DenotesEnv (concatE (ConsT a k_a g) g') th)
          -> ( p:Pred -> { pf:Proof | csubst th p  ==  csubst th'  (subFTV a t_a p) } )
          -> ( t:Type -> { pf:Proof | ctsubst th t == ctsubst th' (tsubFTV a t_a t) } )
          -> ProofOf(TVAugmentedCSub g g' a t_a k_a th') @-}

lem_add_var_csubst g Empty           x v_x_ t_x p_vx_tx p_env_wf zth' den_env'_th' = undefined 

{-@ lem_add_tvar_csubst :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:Type
        -> k_a:Kind -> ProofOf(WFType g t_a k_a)
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') )
        -> th':CSub -> ProofOf(DenotesEnv (concatE g (esubFTV a t_a g')) th')
        -> ProofOf(TVAugmentedCSub g g' a t_a k_a th') / [envsize g'] @-}
lem_add_tvar_csubst :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                          -> CSub -> DenotesEnv -> TVAugmentedCSub
lem_add_tvar_csubst g Empty            a t_a k_a p_g_ta p_env_wf   th'   den_env'_th'
  = case p_env_wf of -- env = ConsT a k_a g
      (WFEBindT _ p_g_wf _ _) -> {-case (lem_denote_sound_typ g v_x_ t_x p_vx_tx 
                                                               p_g_wf zth' den_env'_th') of
        (ValDen _ _ val ev_th'vx_val den_th'tx_val) -}
          -> InsertTVInCS g Empty a t_a k_a zth' 
                 (CConsT a th'ta {-is th'vx-} (zth' ? lem_binds_env_th g zth' den_env'_th'))
                 (DExtT g zth' den_env'_th' a k_a th'ta p_emp_th'ta) eq_func1 eq_func2
                 {- (DExt g zth' den_env'_th' x t_x th'vx  den_th'tx_th'vx) -}
               where {-
                 {-@ v_x :: { v_x:Value | Set_sub (fv v_x) (bindsC zth') && v_x == v_x_ } @-}
                 v_x   = v_x_ ? lem_binds_env_th g zth' den_env'_th'
                              ? lem_fv_subset_binds g v_x_ t_x p_vx_tx
                              ? lem_csubst_value zth' v_x_
                              ? lem_den_nofv (csubst zth' v_x_) (ctsubst zth' t_x) -- den_th'tx_th'vx
                                    (den_th'tx_val ? lem_value_refl (csubst zth' v_x_) val ev_th'vx_val) -}
                 {-@ th'ta :: { t:Type | Set_emp (free t) && Set_emp (freeTV t) &&
                       Set_emp (tfreeBV t) && Set_emp (tfreeBTV t) && t == ctsubst zth' t_a } @-}
                 th'ta :: Type
                 th'ta_ = ctsubst zth' t_a 
                 th'ta  = th'ta_ ? lem_den_nofv (csubst zth' v_x) (ctsubst zth' t_x) -- den_th'tx_th'vx 
                                                (den_th'tx_val ? lem_value_refl th'vx_ val ev_th'vx_val) 
                                 ? lem_den_nobv (csubst zth' v_x) (ctsubst zth' t_x) -- den_th'tx_th'vx 
                                                (den_th'tx_val ? lem_value_refl th'vx_ val ev_th'vx_val) 
        --(WFEBind _ p_g_wf _ _ _) = p_env_wf 
        --vd_th'vx_th'tx = lem_denote_sound_typ g v_x t_x p_vx_tx p_g_wf zth' den_env'_th' 
        --(ValDen _ _ val ev_th'vx_val den_th'tx_val) = vd_th'vx_th'tx
                 {-@ den_th'tx_th'vx :: ProofOf(Denotes (ctsubst zth' t_x) (csubst zth' v_x)) @-}
                 den_th'tx_th'vx :: Denotes
                 den_th'tx_th'vx = den_th'tx_val ? lem_value_refl th'vx val ev_th'vx_val
        {- @ eq_func1 :: p:Pred -> { pf:Proof | csubst th p == csubst zth' (subFV x v_x_ p) } @-}
                 eq_func1 :: Expr -> Proof   -- csubst th p
                 eq_func1 p = () ? lem_csubst_subFV   zth' x v_x  p 
        {- @ eq_func2 :: t:Type -> { pf:Proof | ctsubst th t == ctsubst zth' (tsubFV x v_x_ t) } @-}
                 eq_func2 :: Type -> Proof
                 eq_func2 t = () ? lem_ctsubst_tsubFV zth' x v_x  t
        --th    = (CCons x th'vx (zth' ? lem_binds_env_th g zth' den_env'_th')) -}
lem_add_tvar_csubst g (Cons  z t_z g') a t_a k_a p_g_ta p_zenv_wf  zth'  den_zenv'_zth'
  = undefined
lem_add_var_csubst g (Cons z t_z g') x v_x_ t_x p_vx_tx p_zenv_wf zth' den_zenv'_zth'
  = {- -}undefined {-} case den_zenv'_zth' of   
      (DExt env' th' den_env'_th' _z tzvx v_z_ den_th'tzvx_vz)
        -> InsertInCS g (Cons z t_z g') x v_x_ t_x zth' zth den_zenv_zth eq_funcz1 eq_funcz2
             where
               v_z          = v_z_ ? lem_den_nofv v_z_ (ctsubst th' tzvx) den_th'tzvx_vz
                                   ? lem_den_nobv v_z_ (ctsubst th' tzvx) den_th'tzvx_vz 
               zth          = CCons z v_z (th ? lem_binds_env_th env th den_env_th) 
               den_zenv_zth = DExt env th den_env_th z t_z v_z den_thtz_vz
               den_thtz_vz  = den_th'tzvx_vz ? eq_func2 t_z

               (WFEBind _ p_env_wf _ _ _ _) = p_zenv_wf
               env          = concatE (Cons x t_x g) g'
               {-@ eq_func1 :: p:Pred -> { pf:Proof | csubst th p == csubst th' (subFV x v_x_ p) } @-}
               {-@ eq_func2 :: t:Type -> { pf:Proof | ctsubst th t == ctsubst th' (tsubFV x v_x_ t) } @-}
               eq_func1 :: Pred -> Proof
               eq_func2 :: Type -> Proof 
               (InsertInCS _ _ _ _ _ _ th den_env_th eq_func1 eq_func2)
                            = lem_add_var_csubst g g' x v_x_ t_x p_vx_tx p_env_wf th' den_env'_th'
               -- csubst zth p  ==  csubst zth'  (subFV x v_x p)
               {-@ eq_funcz1 :: p:Pred
                        -> { pf:Proof | csubst (CCons z v_z th) p == csubst zth' (subFV x v_x_ p) } @-}
               eq_funcz1 :: Expr -> Proof
               eq_funcz1 p = ()     ? toProof ( csubst zth' (subFV x v_x_ p) 
                                              ? lem_binds_env_th env' th' den_env'_th'
                                              ? toProof ( zth' === CCons z v_z th' )
                                            === csubst th' (subFV z v_z (subFV x v_x_ p))
                                            === csubst th' (subFV z (subFV x v_x_ v_z) (subFV x v_x_ p)) 
                                              ? lem_commute_subFV  z v_z x -- v_x_ p
                                                       (v_x_ ? lem_fv_bound_in_env g v_x_ t_x p_vx_tx z) p
                                            === csubst th' (subFV x v_x_ (subFV z v_z p)) 
                                              ? eq_func1 (subFV z v_z p)
                                            === csubst th (subFV z v_z p) ) 
               {-@ eq_funcz2 :: t:Type 
                        -> { pf:Proof | ctsubst (CCons z v_z th) t == ctsubst zth' (tsubFV x v_x_ t) } @-}
               eq_funcz2 :: Type -> Proof
               eq_funcz2 t = ()     ? toProof ( ctsubst zth' (tsubFV x v_x_ t) 
                                              ? lem_binds_env_th env' th' den_env'_th'
                                              ? toProof ( zth' === CCons z v_z th' )
                                            === ctsubst th' (tsubFV z v_z (tsubFV x v_x_ t))
                                            === ctsubst th' (tsubFV z (subFV x v_x_ v_z) (tsubFV x v_x_ t)) 
                                              ? lem_commute_tsubFV  z v_z x -- v_x_ p
                                                       (v_x_ ? lem_fv_bound_in_env g v_x_ t_x p_vx_tx z) t
                                            === ctsubst th' (tsubFV x v_x_ (tsubFV z v_z t)) 
                                              ? eq_func2 (tsubFV z v_z t)
                                            === ctsubst th (tsubFV z v_z t) )     { - -}
lem_add_tvar_csubst g (ConsT a1 k1 g') a t_a k_a p_g_ta p_a1env_wf a1th' den_a1env'_a1th'
  = undefined
lem_add_var_csubst g (ConsT a k_a g') x v_x_ t_x p_vx_tx p_aenv_wf ath' den_aenv'_ath' 
  = {- - }undefined { -} case den_aenv'_ath' of   
      (DExtT env' th' den_env'_th' _a _ka {-tavx-} t_a p_emp_ta {-den_th'tzvx_vz-})
        -> InsertInCS g (ConsT a k_a g') x v_x_ t_x ath' ath den_aenv_ath eq_funca1 eq_funca2
             where
--               t_a          = t_a_ ? lem_free_subset_binds Empty 
{-               v_z          = v_z_ ? lem_den_nofv v_z_ (ctsubst th' tzvx) den_th'tzvx_vz
                                   ? lem_den_nobv v_z_ (ctsubst th' tzvx) den_th'tzvx_vz -}
               ath          = CConsT a t_a (th ? lem_binds_env_th env th den_env_th) 
               den_aenv_ath = DExtT env th den_env_th a k_a t_a p_emp_ta --den_thtz_vz

               (WFEBindT _ p_env_wf _ _) = p_aenv_wf
               env          = concatE (Cons x t_x g) g'
               {-@ eq_func1 :: p:Pred -> { pf:Proof | csubst th p == csubst th' (subFV x v_x_ p) } @-}
               {-@ eq_func2 :: t:Type -> { pf:Proof | ctsubst th t == ctsubst th' (tsubFV x v_x_ t) } @-}
               eq_func1 :: Pred -> Proof
               eq_func2 :: Type -> Proof 
               (InsertInCS _ _ _ _ _ _ th den_env_th eq_func1 eq_func2)
                            = lem_add_var_csubst g g' x v_x_ t_x p_vx_tx p_env_wf th' den_env'_th'
               -- csubst zth p  ==  csubst zth'  (subFV x v_x p)
               {-@ eq_funcz1 :: p:Pred
                        -> { pf:Proof | csubst (CConsT a t_a th) p == csubst ath' (subFV x v_x_ p) } @-}
               eq_funcz1 :: Expr -> Proof
               eq_funcz1 p = ()     ? toProof ( csubst ath' (subFV x v_x_ p) 
                                              ? lem_binds_env_th env' th' den_env'_th'
                                              ? toProof ( ath' === CConsT a t_a th' )
                                            === csubst th' (subFTV a t_a (subFV x v_x_ p))
                                            === csubst th' (subFTV a (tsubFV x v_x_ t_a) (subFV x v_x_ p)) 
                                              ? lem_commute_subFTV_subFV  a t_a x
                                                       (v_x_ ? lem_fv_bound_in_env g v_x_ t_x p_vx_tx a) p
                                            === csubst th' (subFV x v_x_ (subFTV a t_a p)) 
                                              ? eq_func1  (subFTV a t_a p)
                                            === csubst th (subFTV a t_a p) ) 
               {-@ eq_funcz2 :: t:Type 
                        -> { pf:Proof | ctsubst (CConsT a t_a th) t == ctsubst ath' (tsubFV x v_x_ t) } @-}
               eq_funcz2 :: Type -> Proof
               eq_funcz2 t = ()     ? toProof ( ctsubst ath' (tsubFV x v_x_ t) 
                                              ? lem_binds_env_th env' th' den_env'_th'
                                              ? toProof ( ath' === CConsT a t_a th' )
                                            === ctsubst th' (tsubFTV a t_a (tsubFV x v_x_ t))
                                            === ctsubst th' (tsubFTV a (tsubFV x v_x_ t_a) (tsubFV x v_x_ t)) 
                                              ? lem_commute_tsub_FTV tsubFV  a t_a x 
                                                       (v_x_ ? lem_fv_bound_in_env g v_x_ t_x p_vx_tx a) t
                                            === ctsubst th' (tsubFV x v_x_ (tsubFTV a t_a t)) 
                                              ? eq_func2 (tsubFTV a t_a t)
                                            === ctsubst th (tsubFTV a t_a t) ) 
-}
{- CHECKED
{-@ lem_subst_tv_ent :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:Type
            -> k_a:Kind -> ProofOf(WFType g t_a k_a)
            -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) 
            -> { p:Pred | Set_sub (Set_cup (fv p) (ftv p)) (binds (concatE (ConsT a k_a g) g')) }
            -> ProofOf(Entails (concatE (ConsT a k_a g) g') p) 
            -> ProofOf(Entails (concatE g (esubFTV a t_a g')) (subFTV a t_a p)) @-}
lem_subst_tv_ent :: Env -> Env -> Vname -> Type -> Kind -> WFType 
                        -> WFEnv -> Pred -> Entails -> Entails
lem_subst_tv_ent g g' a t_a k_a p_g_ta p_env_wf p (EntPred env _p evals_func)
  = EntPred (concatE g (esubFTV a t_a g')) (subFTV a t_a p) evals_func'
      where
        {-@ evals_func' :: th':CSub -> ProofOf(DenotesEnv (concatE g (esubFTV a t_a g')) th')
                                 -> ProofOf(EvalsTo (csubst th' (subFTV a t_a p)) (Bc True)) @-}
        evals_func' :: CSub -> DenotesEnv -> EvalsTo
        evals_func' th' den_env'_th' = evals_func th den_env_th ? eq_func p
          where
            (InsertTVInCS _ _ _ _ _ _ th den_env_th eq_func _) 
                = lem_add_tvar_csubst g g' a t_a k_a p_g_ta p_env_wf th' den_env'_th'
-}
