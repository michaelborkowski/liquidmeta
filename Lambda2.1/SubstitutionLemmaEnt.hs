{-# LANGUAGE GADTs #-}

{-@ LIQUID "--no-termination" @-} -- TODO assume
{-@ LIQUID "--no-totality" @-} -- TODO assume
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
import LemmasWellFormedness
import LemmasTyping
import LemmasSubtyping
import LemmasChangeVarTyp
import LemmasWeakenTyp
--import SubstitutionLemmaWF
import DenotationsSelfify
import DenotationsSoundnessSub
import PrimitivesSemantics
import PrimitivesDenotations
import DenotationsSoundnessTyp
import LemmasExactness

{-@ reflect foo53 @-}
foo53 x = Just x
foo53 :: a -> Maybe a

{-@ measure envSize @-}
{-@ envSize :: Env -> { n:Int | n >= 0 } @-}
envSize :: Env -> Int
envSize Empty          = 0
envSize (Cons x t_x g) = 1 + envSize g
envSize (ConsT a k g)  = 1 + envSize g

{-@ lem_subst_wfenv :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> ProofOf(HasType g v_x t_x)
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') )
        -> ProofOf(WFEnv (concatE g (esubFV x v_x g')) ) / [envSize g'] @-}
lem_subst_wfenv :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv -> WFEnv
lem_subst_wfenv g Empty           x v_x t_x p_vx_tx p_xg_wf  = case p_xg_wf of
  (WFEBind  _g p_g_wf _x _tx _ _) -> p_g_wf
  (WFEBindT _g p_g_wf _  _)       -> p_g_wf
lem_subst_wfenv g (Cons z t_z g') x v_x t_x p_vx_tx p_env_wf = case p_env_wf of
  (WFEBind env' p_env'_wf _z _tz p_env'_tz) -> WFEBind env'' p_env''_wf z (tsubFV x v_x t_z) p_env''_tzvx
    where
      env''        = concatE g (esubFV x v_x g')
      p_env''_wf   = lem_subst_wfenv g g' x v_x t_x p_vx_tx p_env'_wf
      p_env''_tzvx = lem_subst_wf g g' x v_x t_x p_vx_tx p_env'_wf t_z p_env'_tz
lem_subst_wfenv g (ConsT a k_a g') x v_x t_x p_vx_tx p_env_wf = case p_env_wf of
  (WFEBindT {}) -> undefined

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
        -> ProofOf(AugmentedCSub g g' x v_x t_x th') / [envSize g'] @-}
lem_add_var_csubst :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                          -> CSub -> DenotesEnv -> AugmentedCSub
lem_add_var_csubst g Empty           x v_x_ t_x p_vx_tx p_env_wf zth' den_env'_th' 
  = undefined {- case p_env_wf of 
  (WFEBind _ p_g_wf _ _ _) -> case (lem_denote_sound_typ g v_x_ t_x p_vx_tx p_g_wf zth' den_env'_th') of
      (ValDen _ _ val ev_th'vx_val den_th'tx_val) 
        -> InsertInCS g Empty x v_x t_x zth' {-th-} (CCons x th'vx (zth' ? lem_binds_env_th g zth' den_env'_th'))
                      (DExt g zth' den_env'_th' x t_x th'vx  den_th'tx_th'vx) eq_func1 eq_func2
                     {-(csubst zth' v_x ? lem_csubst_value zth' v_x
                                      ? lem_den_nofv (csubst zth' v_x) (ctsubst zth' t_x)
                                                     (den_th'tx_val ? lem_value_refl th'vx val ev_th'vx_val)))-}
                  {-   (den_th'tx_val ? lem_value_refl th'vx 
                          {-(csubst zth' v_x ? lem_csubst_value zth' v_x
                                           ? lem_den_nofv (csubst zth' v_x) (ctsubst zth' t_x)
                                                   (den_th'tx_val ? lem_value_refl th'vx val ev_th'vx_val)))-}
                          val ev_th'vx_val)) eq_func1 eq_func2 -}
             where
               {-@ v_x :: { v_x:Value | Set_sub (fv v_x) (bindsC zth') && v_x == v_x_ } @-}
               v_x   = v_x_ ? lem_binds_env_th g zth' den_env'_th'
                            ? lem_fv_subset_bindsB (erase_env g) v_x_ (erase t_x) p_vx_er_tx
                            ? lem_csubst_value zth' v_x_
                            ? lem_den_nofv (csubst zth' v_x_) (ctsubst zth' t_x) -- den_th'tx_th'vx
                                               (den_th'tx_val ? lem_value_refl (csubst zth' v_x_) val ev_th'vx_val) 
               p_vx_er_tx   = lem_typing_hasbtype g v_x_ t_x p_vx_tx p_g_wf
               {-@ th'vx :: { v:Value | Set_emp (fv v) && v == csubst zth' v_x } @-}
               th'vx :: Expr
               th'vx = csubst zth' v_x {-? lem_csubst_value zth' v_x
                                ? lem_den_nofv (csubst zth' v_x) (ctsubst zth' t_x) -- den_th'tx_th'vx 
                                               (den_th'tx_val ? lem_value_refl th'vx val ev_th'vx_val) -}
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
lem_add_var_csubst g (Cons z t_z g') x v_x_ t_x p_vx_tx p_zenv_wf zth' den_zenv'_zth'
  = undefined {- case den_zenv'_zth' of   
      (DExt env' th' den_env'_th' _z tzvx v_z den_th'tzvx_vz)
        -> InsertInCS g (Cons z t_z g') x v_x_ t_x zth' zth den_zenv_zth eq_funcz1 eq_funcz2
             where
               zth          = CCons z v_z (th ? lem_binds_env_th env th den_env_th) 
               den_zenv_zth = DExt env th den_env_th z t_z v_z den_thtz_vz
               den_thtz_vz  = den_th'tzvx_vz ? eq_func2 t_z

               (WFEBind _ p_env_wf _ _ _) = p_zenv_wf
               env          = concatE (Cons x t_x g) g'
               p_vx_er_tx   = lem_typing_hasbtype g v_x_ t_x p_vx_tx p_g_wf
               p_xg_wf      = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
               (WFEBind _ p_g_wf _ _ _) = p_xg_wf
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
                                                       (v_x_ ? lem_fv_bound_in_benv (erase_env g) v_x_ (erase t_x) 
                                                                   p_vx_er_tx z) p
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
                                                       (v_x_ ? lem_fv_bound_in_benv (erase_env g) v_x_ (erase t_x) 
                                                                   p_vx_er_tx z) t
                                            === ctsubst th' (tsubFV x v_x_ (tsubFV z v_z t))
                                              ? eq_func2 (tsubFV z v_z t)
                                            === ctsubst th (tsubFV z v_z t) ) -}
lem_add_var_csubst g (ConsT a k_a g') x v_x_ t_x p_vx_tx p_zenv_wf zth' den_zenv'_zth' = undefined


{-@ lem_subst_ent :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
            -> t_x:Type -> ProofOf(HasType g v_x t_x) 
            -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) 
            -> { p:Pred | Set_sub (fv p) (binds (concatE (Cons x t_x g) g')) }
            -> ProofOf(Entails (concatE (Cons x t_x g) g') p) 
            -> ProofOf(Entails (concatE g (esubFV x v_x g')) (subFV x v_x p)) @-}
lem_subst_ent :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv -> Pred -> Entails -> Entails
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

