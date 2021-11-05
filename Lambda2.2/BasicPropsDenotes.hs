{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module BasicPropsDenotes where

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
import SystemFLemmasFTyping2
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst

{-@ reflect foo28 @-}
foo28 x = Just x 
foo28 :: a -> Maybe a 

{-@ lem_step_in_drefn :: b:Basic -> x:RVname -> q:Pred -> v:Value
        -> ProofOf(Denotes (TRefn b x q) v)  
        -> p:Pred -> ProofOf(CommonEvals (subBV 0 v q) (subBV 0 v p))
        -> ProofOf(Denotes (TRefn b x p) v) @-}
lem_step_in_drefn :: Basic -> RVname -> Expr -> Expr -> Denotes -> Expr -> CommonEvals -> Denotes
lem_step_in_drefn b x q v den_bxq_v p evboth_p_q = case den_bxq_v of
    (DRefn _ _ _ _ p_v_b ev_qv_tt) -> DRefn b x p v p_v_b ev_pv_tt
      where
        ev_pv_tt = lem_common_evals_extend (subBV 0 v q) (subBV 0 v p) evboth_p_q (Bc True) ev_qv_tt

{-@ lem_exch_refn_in_dfunc :: { y:Vname | y /= 0 } -> t_y:Type -> b:Basic -> z:RVname -> q:Pred -> v:Value
        -> ProofOf(Denotes (TFunc y t_y (TRefn b z q)) v) -> p:Pred 
        -> ( v_y:Value -> ProofOf(Denotes t_y v_y)  -> v':Value -> ProofOf(Denotes (tsubBV y v_y (TRefn b z q)) v')
                       -> ProofOf(CommonEvals (subBV 0 v' (subBV y v_y q)) (subBV 0 v' (subBV y v_y p))) )
        -> ProofOf(Denotes (TFunc y t_y (TRefn b z p)) v) @-}
lem_exch_refn_in_dfunc :: Vname -> Type -> Basic -> RVname -> Expr -> Expr -> Denotes -> Expr
                                -> (Expr -> Denotes -> Expr -> Denotes -> CommonEvals) -> Denotes
lem_exch_refn_in_dfunc y t_y b z q v den_tybzq_v p step_func = case den_tybzq_v of
  (DFunc _ _ _ _ p_v_tyt val_den_func) -> DFunc y t_y (TRefn b z p) v p_v_tyt val_den_func'
    where  
      val_den_func' v_y den_ty_vy = ValDen (App v v_y) (tsubBV y v_y (TRefn b z p)) v'
                                           ev_vvy_v' den_bzpvy_v'
        where
          (ValDen _ _ v' ev_vvy_v' den_bzqvy_v') = val_den_func v_y den_ty_vy
          cmev_qvyv'_pvyv' = step_func v_y den_ty_vy v' den_bzqvy_v'
          den_bzpvy_v'     = lem_step_in_drefn b z (subBV y v_y q) v' den_bzqvy_v' 
                                             (subBV y v_y p) cmev_qvyv'_pvyv' 

{-@ lem_exch_refn_in_dfunc2 :: { x:Vname | x /= 0 } -> t_x:Type -> { y:Vname | y /= x && y /= 0 }
        -> { t_y:Type | not (Set_mem x (tfreeBV t_y)) } -> b:Basic -> z:RVname -> q:Pred -> v:Value 
        -> ProofOf(Denotes (TFunc x t_x (TFunc y t_y (TRefn b z q))) v) -> p:Pred
        -> ( v_x:Value -> ProofOf(Denotes t_x v_x) -> v_y:Value -> ProofOf(Denotes t_y v_y) 
                       -> v':Value -> ProofOf(Denotes (tsubBV y v_y (tsubBV x v_x (TRefn b z q))) v')
                       -> ProofOf(CommonEvals (subBV 0 v' (subBV y v_y (subBV x v_x q))) 
                                               (subBV 0 v' (subBV y v_y (subBV x v_x p)))) )
        -> ProofOf(Denotes (TFunc x t_x (TFunc y t_y (TRefn b z p))) v) @-}
lem_exch_refn_in_dfunc2 :: Vname -> Type -> Vname -> Type -> Basic -> RVname 
                                 -> Expr -> Expr -> Denotes -> Expr 
                 -> (Expr -> Denotes -> Expr -> Denotes -> Expr -> Denotes -> CommonEvals) -> Denotes    
lem_exch_refn_in_dfunc2 x t_x y t_y b z q v den_txtybzq_v p step_func = case den_txtybzq_v of
  (DFunc _ _ _ _ p_v_txtyt val_den_func) -> DFunc x t_x (TFunc y t_y (TRefn b z p)) v 
                                                  p_v_txtyt val_den_func'
    where
      val_den_func' v_x den_tx_vx = ValDen (App v v_x) (tsubBV x v_x (TFunc y t_y (TRefn b z p)))
                                           v' ev_vvx_v' den_tybzpvx_v'
        where
          inner_step_func = step_func v_x den_tx_vx
          (ValDen _ _ v' ev_vvx_v' den_tybzqvx_v') = val_den_func v_x den_tx_vx
          den_tybzpvx_v'  = lem_exch_refn_in_dfunc y t_y b z (subBV x v_x q) v' 
                                                   (den_tybzqvx_v' ? lem_tsubBV_notin x v_x t_y)
                                                   (subBV x v_x p) inner_step_func
                                                   ? lem_tsubBV_notin x v_x t_y

{-@ lem_drefn_to_trivial :: b:Basic -> x:RVname -> p:Pred -> v:Value
        -> ProofOf(Denotes (TRefn b x p) v) -> ProofOf(Denotes (TRefn b x (Bc True)) v) @-}
lem_drefn_to_trivial :: Basic -> RVname -> Expr -> Expr -> Denotes -> Denotes
lem_drefn_to_trivial b x p v den_bxp_v = case den_bxp_v of
    (DRefn _ _ _ _ p_v_b _) -> DRefn b x (Bc True) v p_v_b (Refl (Bc True))

{-@ lem_drefn_in_dfunc_from_trivial :: x:Vname -> b:Basic -> z:RVname -> t:Type -> v:Value
        -> ProofOf(Denotes (TFunc x (TRefn b z (Bc True)) t) v) -> p:Pred
        -> ProofOf(Denotes (TFunc x (TRefn b z p) t) v) @-}
lem_drefn_in_dfunc_from_trivial :: Vname -> Basic -> RVname -> Type -> Expr -> Denotes 
                                                                    -> Expr -> Denotes
lem_drefn_in_dfunc_from_trivial x b z t v den_xttt_v p = case den_xttt_v of
  (DFunc _ _ _ _ p_v_ertxt val_den_func) -> DFunc x (TRefn b z p) t v p_v_ertxt val_den_func'
    where
      val_den_func' v_x den_tp_vx = val_den_func v_x (lem_drefn_to_trivial b z p v_x den_tp_vx)

{-@ lem_drefn_in_dfunc_twice :: x:Vname -> { y:Vname | y /= x } -> b:Basic -> z:RVname -> t:Type -> v:Value
        -> ProofOf(Denotes (TFunc x (TRefn b z (Bc True)) (TFunc y (TRefn b z (Bc True)) t)) v) 
        -> { p:Pred | Set_emp (tfreeBV (TRefn b z p)) }
        -> ProofOf(Denotes (TFunc x (TRefn b z p) (TFunc y (TRefn b z p) t)) v) @-}
lem_drefn_in_dfunc_twice :: Vname -> Vname -> Basic -> RVname -> Type -> Expr -> Denotes 
                                                                      -> Expr -> Denotes
lem_drefn_in_dfunc_twice x y b z t v den_xyt_v p = case den_xyt_v of
  (DFunc _ _ _ _ p_v_erxyt val_den_func) -> DFunc x (TRefn b z p) ypt v p_v_erxyt val_den_func'
    where
      ytt                         = TFunc y (TRefn b z (Bc True)) t
      ypt                         = TFunc y (TRefn b z p) t
      val_den_func' v_x den_tp_vx = vden_vvx_ypt
        where
          {-@ vden_vvx_ytt :: ProofOf(ValueDenoted (App v v_x) 
                                        (tsubBV x v_x (TFunc y (TRefn b z (Bc True)) t))) @-}
          vden_vvx_ytt = val_den_func v_x (lem_drefn_to_trivial b z p v_x den_tp_vx)
          {- @ den_yttvx_v' :: ProofOf(Denotes (tsubBV x v_x (TFunc y (TRefn b z (Bc True)) t)) v') @-}
          {-@ den_yttvx_v' :: ProofOf(Denotes (TFunc y (TRefn b z (Bc True)) (tsubBV x v_x t)) v') @-}
          (ValDen _ _ v' ev_vvx_v' den_yttvx_v') = vden_vvx_ytt
                                   ? lem_tsubBV_notin x v_x (TRefn b z (Bc True))  
          den_yptvx_v' = lem_drefn_in_dfunc_from_trivial y b z (tsubBV x v_x t) v' den_yttvx_v' p
                                   ? lem_tsubBV_notin x v_x (TRefn b z p)  
          vden_vvx_ypt = ValDen (App v v_x) (tsubBV x v_x ypt) v' ev_vvx_v' den_yptvx_v'

  -- formal properties
 
{-@ lem_change_var_denote :: th:CSub -> t:Type -> { v:Value | Set_emp (fv v) }
      -> ProofOf(Denotes (ctsubst th t) v) -> { x:Vname | (v_in_csubst x th) } 
      -> { y:Vname | y == x || ( not (in_csubst y th) && not (Set_mem y (free t))) } 
      -> ProofOf(Denotes (ctsubst (change_varCS th x y) (tsubFV x (FV y) t)) v ) @-}
lem_change_var_denote :: CSub -> Type -> Expr -> Denotes -> Vname -> Vname -> Denotes
lem_change_var_denote th t v den_tht_v x y = den_tht_v ? lem_change_var_in_ctsubst th x y t

{-@ lem_change_tvar_denote :: th:CSub -> t:Type -> { v:Value | Set_emp (ftv v) }
      -> ProofOf(Denotes (ctsubst th t) v) -> { a:Vname | (tv_in_csubst a th) } 
      -> { a':Vname | a == a' || ( not (in_csubst a' th) && not (Set_mem a' (freeTV t))) } 
      -> ProofOf(Denotes (ctsubst (change_tvarCS th a a') (tchgFTV a a' t)) v ) @-}
lem_change_tvar_denote :: CSub -> Type -> Expr -> Denotes -> Vname -> Vname -> Denotes
lem_change_tvar_denote th t v den_tht_v a a' = den_tht_v ? lem_change_tvar_in_ctsubst th a a' t

{-@ lem_remove_var_denote :: th:CSub -> t:Type -> { v:Value | Set_emp (fv v) }
      -> ProofOf(Denotes (ctsubst th t) v) -> { x:Vname | v_in_csubst x th && not (Set_mem x (free t)) } 
      -> ProofOf(Denotes (ctsubst (remove_fromCS th x) t) v) @-}
lem_remove_var_denote :: CSub -> Type -> Expr -> Denotes -> Vname -> Denotes
lem_remove_var_denote th t v den_tht_v x = den_tht_v ? lem_remove_ctsubst th x t

{-@ lem_remove_tvar_denote :: th:CSub -> t:Type -> { v:Value | Set_emp (ftv v) }
      -> ProofOf(Denotes (ctsubst th t) v) -> { a:Vname | tv_in_csubst a th && not (Set_mem a (freeTV t)) } 
      -> ProofOf(Denotes (ctsubst (remove_fromCS th a) t) v) @-}
lem_remove_tvar_denote :: CSub -> Type -> Expr -> Denotes -> Vname -> Denotes
lem_remove_tvar_denote th t v den_tht_v a = den_tht_v ? lem_remove_tv_ctsubst th a t

{-@ lem_change_var_denote_env :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
      -> th:CSub -> ProofOf(DenotesEnv (concatE (Cons x t_x g) g') th)
      -> { y:Vname | (y == x || not (in_csubst y th)) && not (in_env y g) && not (in_env y g') } 
      -> ProofOf(DenotesEnv (concatE (Cons y t_x g) (esubFV x (FV y) g')) (change_varCS th x y)) @-}
lem_change_var_denote_env :: Env -> Vname -> Type -> Env -> WFEnv -> CSub 
                                 -> DenotesEnv -> Vname -> DenotesEnv
lem_change_var_denote_env g x t_x Empty            p_env_wf th den_env_th y  
  = case den_env_th of
      (DExt env' th' den_env'_th' _x _tx v_x den_th'tx_vx) 
        -> DExt env' th' den_env'_th' y t_x v_x den_th'tx_vx
lem_change_var_denote_env g x_ t_x (Cons z t_z g') p_env_wf th den_env_th y_ = case den_env_th of
  (DExt env' th' den_env'_th' _z _tz v_z den_th'tz_vz) -- env' == concatE (Cons x t_x g) g'
    -> DExt (concatE (Cons y t_x g) (esubFV x (FV y) g')) (change_varCS th' x y) den_env'y_th'y
            z (tsubFV x (FV y) t_z) v_z den_th'ytzy_vz
      where
        (WFEBind _ p_env'_wf _ _ k_z p_env'_tz) = p_env_wf 
        x              = x_ ? lem_binds_env_th (concatE (Cons x_ t_x g) g') th' den_env'_th'
                            ? lem_in_env_concat g g' x_
        y              = y_ ? lem_binds_env_th (concatE (Cons x t_x g) g') th' den_env'_th' 
                            ? lem_in_env_concat g g' y_
                            ? lem_in_env_concat (Cons x t_x g) g' y_
                            ? lem_free_subset_binds (concatE (Cons x t_x g) g') t_z k_z p_env'_tz 
        den_env'y_th'y = lem_change_var_denote_env g x t_x g' p_env'_wf th' den_env'_th' y 
        den_th'ytzy_vz = lem_change_var_denote th' t_z v_z den_th'tz_vz x y
lem_change_var_denote_env g x_ t_x (ConsT a k_a g') p_env_wf th den_env_th y_ = case den_env_th of
  (DExtT env' th' den_env'_th' _a _ka t_a p_emp_ta)
    -> DExtT (concatE (Cons y t_x g) (esubFV x (FV y) g')) (change_varCS th' x y) den_env'y_th'y
              a k_a t_a p_emp_ta ? lem_tsubFV_notin x (FV y) t_a
      where
        (WFEBindT _ p_env'_wf _ _) = p_env_wf 
        x              = x_ ? lem_binds_env_th (concatE (Cons x_ t_x g) g') th' den_env'_th'
                            ? lem_in_env_concat g g' x_
        y              = y_ ? lem_binds_env_th (concatE (Cons x t_x g) g') th' den_env'_th' 
                            ? lem_in_env_concat g g' y_
                            ? lem_in_env_concat (Cons x t_x g) g' y_
        den_env'y_th'y = lem_change_var_denote_env g x t_x g' p_env'_wf th' den_env'_th' y 

{-@ lem_change_tvar_denote_env :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
      -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (ConsT a k_a g) g'))
      -> th:CSub -> ProofOf(DenotesEnv (concatE (ConsT a k_a g) g') th)
      -> { a':Vname | (a' == a || not (in_csubst a' th)) && not (in_env a' g) && not (in_env a' g') } 
      -> ProofOf(DenotesEnv (concatE (ConsT a' k_a g) (echgFTV a a' g')) (change_tvarCS th a a')) @-}
lem_change_tvar_denote_env :: Env -> Vname -> Kind -> Env -> WFEnv -> CSub 
                                 -> DenotesEnv -> Vname -> DenotesEnv
lem_change_tvar_denote_env g a k_a Empty            p_env_wf th den_env_th a' = case den_env_th of 
  (DExtT env' th' den_env'_th' _a _ka t_a p_emp_ta)
    -> DExtT env' th' den_env'_th' a' k_a t_a p_emp_ta
lem_change_tvar_denote_env g a_ k_a (Cons z t_z g')  p_env_wf th den_env_th a'_ = case den_env_th of
  (DExt env' th' den_env'_th' _z _tz v_z den_th'tz_vz)
    -> DExt (concatE (ConsT a' k_a g) (echgFTV a a' g')) (change_tvarCS th' a a') den_env'a'_th'a'
            z (tchgFTV a a' t_z) v_z den_th'a'tz_vz
      where
        (WFEBind _ p_env'_wf _ _ k_z p_env'_tz) = p_env_wf
        a                = a_  ? lem_binds_env_th (concatE (ConsT a_ k_a g) g') th' den_env'_th' 
                               ? lem_in_env_concat g g' a_
        a'               = a'_ ? lem_binds_env_th (concatE (ConsT a k_a g) g') th' den_env'_th'
                               ? lem_in_env_concat g g' a'_
                               ? lem_in_env_concat (ConsT a k_a g) g' a'_
                               ? lem_free_subset_binds (concatE (ConsT a k_a g) g') t_z k_z p_env'_tz
        den_env'a'_th'a' = lem_change_tvar_denote_env g a k_a g' p_env'_wf th' den_env'_th' a'
        den_th'a'tz_vz   = lem_change_tvar_denote th' t_z v_z den_th'tz_vz a a'
lem_change_tvar_denote_env g a_ k_a (ConsT a1 k1 g') p_env_wf th den_env_th a'_ = case den_env_th of
  (DExtT env' th' den_env'_th' _a1 _k1 t_a1 p_emp_ta1)
    -> DExtT (concatE (ConsT a' k_a g) (echgFTV a a' g')) (change_tvarCS th' a a') den_env'a'_th'a'
             a1 k1 t_a1 p_emp_ta1 ? lem_tchgFTV_notin a a' t_a1
      where
        (WFEBindT _ p_env'_wf _ _) = p_env_wf  
        a                = a_  ? lem_binds_env_th (concatE (ConsT a_ k_a g) g') th' den_env'_th' 
                               ? lem_in_env_concat g g' a_
        a'               = a'_ ? lem_binds_env_th (concatE (ConsT a k_a g) g') th' den_env'_th'
                               ? lem_in_env_concat g g' a'_
                               ? lem_in_env_concat (ConsT a k_a g) g' a'_
        den_env'a'_th'a' = lem_change_tvar_denote_env g a k_a g' p_env'_wf th' den_env'_th' a'                       

{-@ lem_remove_var_denote_env :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
       -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
       -> ProofOf(WFEnv (concatE g g'))
       -> th:CSub -> ProofOf(DenotesEnv (concatE (Cons x t_x g) g') th)
       -> ProofOf(DenotesEnv (concatE g g') (remove_fromCS th x )) @-}
lem_remove_var_denote_env :: Env -> Vname -> Type -> Env -> WFEnv -> CSub 
                                 -> DenotesEnv -> DenotesEnv
lem_remove_var_denote_env g x  t_x Empty           p_g'g_wf  th den_env_th = case den_env_th of
  (DExt env' th' den_env'_th' _ _tx v_x den_th'tx_vx) -> den_env'_th'
lem_remove_var_denote_env g x_ t_x (Cons z t_z g') p_zg'g_wf th den_env_th = case den_env_th of
  (DExt env' th' den_env'_th' _z _tz v_z den_th'tz_vz) -- env' == concatE (Cons x t_x g) g' 
    -> DExt (concatE g g') (remove_fromCS th' x) den_env''_th'' z t_z v_z den_th''tz_vz
      where
        (WFEBind _ p_g'g_wf _ _ k_z p_g'g_tz) = p_zg'g_wf
        x              = x_ ? lem_binds_env_th (concatE (Cons x_ t_x g) g') th' den_env'_th'
                            ? lem_in_env_concat g g' x_ 
                            ? lem_free_bound_in_env (concatE g g') t_z k_z p_g'g_tz x_
        den_env''_th'' = lem_remove_var_denote_env g x t_x g' p_g'g_wf th' den_env'_th'
        den_th''tz_vz  = lem_remove_var_denote th' t_z v_z den_th'tz_vz x
lem_remove_var_denote_env g x_ t_x (ConsT a k_a g') p_zg'g_wf th den_env_th = case den_env_th of
  (DExtT env' th' den_env'_th' _a _ka t_a p_emp_ta)
    -> DExtT (concatE g g') (remove_fromCS th' x) den_env''_th'' a k_a t_a p_emp_ta
      where
        (WFEBindT _ p_g'g_wf _ _) = p_zg'g_wf
        x              = x_ ? lem_binds_env_th (concatE (Cons x_ t_x g) g') th' den_env'_th'
                            ? lem_in_env_concat g g' x_ 
        den_env''_th'' = lem_remove_var_denote_env g x t_x g' p_g'g_wf th' den_env'_th'

{-@ lem_remove_tvar_denote_env :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
       -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
       -> ProofOf(WFEnv (concatE g g'))
       -> th:CSub -> ProofOf(DenotesEnv (concatE (ConsT a k_a g) g') th)
       -> ProofOf(DenotesEnv (concatE g g') (remove_fromCS th a )) @-}
lem_remove_tvar_denote_env :: Env -> Vname -> Kind -> Env -> WFEnv -> CSub 
                                 -> DenotesEnv -> DenotesEnv
lem_remove_tvar_denote_env g a  k_a Empty           p_g'g_wf  th den_env_th = case den_env_th of 
  (DExtT env' th' den_env'_th' _ _ t_a p_emp_ta) -> den_env'_th'
lem_remove_tvar_denote_env g a_ k_a (Cons z t_z g') p_ag'g_wf th den_env_th = case den_env_th of
  (DExt env' th' den_env'_th' _z _tz v_z den_th'tz_vz) -- env' == concatE (Cons x t_x g) g' 
    -> DExt (concatE g g') (remove_fromCS th' a) den_env''_th'' z t_z v_z den_th''tz_vz
      where
        (WFEBind _ p_g'g_wf _ _ k_z p_g'g_tz) = p_ag'g_wf
        a              = a_ ? lem_binds_env_th (concatE (ConsT a_ k_a g) g') th' den_env'_th'
                            ? lem_in_env_concat g g' a_ 
                            ? lem_free_bound_in_env (concatE g g') t_z k_z p_g'g_tz a_
        den_env''_th'' = lem_remove_tvar_denote_env g a k_a g' p_g'g_wf th' den_env'_th'
        den_th''tz_vz  = lem_remove_tvar_denote th' t_z v_z den_th'tz_vz a
lem_remove_tvar_denote_env g a_ k_a (ConsT a1 k1 g') p_a1g'g_wf th den_env_th = case den_env_th of
  (DExtT env' th' den_env'_th' _a1 _k1 t_a1 p_emp_ta1)
    -> DExtT (concatE g g') (remove_fromCS th' a) den_env''_th'' a1 k1 t_a1 p_emp_ta1
      where
        (WFEBindT _ p_g'g_wf _ _) = p_a1g'g_wf
        a              = a_ ? lem_binds_env_th (concatE (ConsT a_ k_a g) g') th' den_env'_th'
                            ? lem_in_env_concat g g' a_ 
        den_env''_th'' = lem_remove_tvar_denote_env g a k_a g' p_g'g_wf th' den_env'_th'
