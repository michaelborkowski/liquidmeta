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
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst

{-@ reflect foo27 @-}
foo27 x = Just x 
foo27 :: a -> Maybe a 

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
      -> ProofOf(Denotes (ctsubst th t) v) -> { x:Vname | in_csubst x th && not (Set_mem x (free t)) } 
      -> ProofOf(Denotes (ctsubst (remove_fromCS th x) t) v) @-}
lem_remove_var_denote :: CSub -> Type -> Expr -> Denotes -> Vname -> Denotes
lem_remove_var_denote th t v den_tht_v x = den_tht_v ? lem_remove_ctsubst th x t

{-@ lem_change_var_denote_env :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
      -> th:CSub -> ProofOf(DenotesEnv (concatE (Cons x t_x g) g') th)
      -> { y:Vname | (y == x || not (in_csubst y th)) && not (in_env y g) && not (in_env y g') } 
      -> ProofOf(DenotesEnv (concatE (Cons y t_x g) (esubFV x (FV y) g')) (change_varCS th x y)) @-}
lem_change_var_denote_env :: Env -> Vname -> Type -> Env -> WFEnv -> CSub 
                                 -> DenotesEnv -> Vname -> DenotesEnv
lem_change_var_denote_env g x t_x Empty            p_env_wf th den_env_th y  
  = undefined {-= case den_env_th of
  (DExt env' th' den_env'_th' _x _tx v_x den_th'tx_vx) -> DExt env' th' den_env'_th' y t_x v_x den_th'tx_vx-}
lem_change_var_denote_env g x_ t_x (Cons z t_z g') p_env_wf th den_env_th y_ 
  = undefined {- 2 -} {-case den_env_th of
  (DExt env' th' den_env'_th' _z _tz v_z den_th'tz_vz) -- env' == concatE (Cons x t_x g) g'
    -> DExt (concatE (Cons y t_x g) (esubFV x (FV y) g')) (change_varCS th' x y) den_env'y_th'y
            z (tsubFV x (FV y) t_z) v_z den_th'ytzy_vz
      where
        (WFEBind _ p_env'_wf _ _ p_env'_tz) = p_env_wf -- tODO remove this
        x              = x_ ? lem_binds_env_th (concatE (Cons x_ t_x g) g') th' den_env'_th'
                            ? lem_in_env_concat g g' x_
        y              = y_ ? lem_binds_env_th (concatE (Cons x t_x g) g') th' den_env'_th' 
                            ? lem_in_env_concat g g' y_
                            ? lem_in_env_concat (Cons x t_x g) g' y_
                            ? lem_free_subset_binds (concatE (Cons x t_x g) g') t_z p_env'_tz 
        den_env'y_th'y = lem_change_var_denote_env g x t_x g' p_env'_wf th' den_env'_th' y 
        den_th'ytzy_vz = lem_change_var_denote th' t_z v_z den_th'tz_vz x y-}
lem_change_var_denote_env g x_ t_x (ConsT a k_a g') p_env_wf th den_env_th y_ 
  = undefined {- 2 -}

{-@ lem_change_tvar_denote_env :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
      -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (ConsT a k_a g) g'))
      -> th:CSub -> ProofOf(DenotesEnv (concatE (ConsT a k_a g) g') th)
      -> { a':Vname | (a' == a || not (in_csubst a' th)) && not (in_env a' g) && not (in_env a' g') } 
      -> ProofOf(DenotesEnv (concatE (ConsT a' k_a g) (echgFTV a a' g')) (change_tvarCS th a a')) @-}
lem_change_tvar_denote_env :: Env -> Vname -> Kind -> Env -> WFEnv -> CSub 
                                 -> DenotesEnv -> Vname -> DenotesEnv
lem_change_tvar_denote_env g a k_a Empty            p_env_wf th den_env_th a' = undefined
lem_change_tvar_denote_env g a k_a (Cons z t_z g')  p_env_wf th den_env_th a' = undefined {- 2 -}
lem_change_tvar_denote_env g a k_a (ConsT a1 k1 g') p_env_wf th den_env_th a' = undefined {- 2 -}

{-@ lem_remove_var_denote_env :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
       -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
       -> ProofOf(WFEnv (concatE g g'))
       -> th:CSub -> ProofOf(DenotesEnv (concatE (Cons x t_x g) g') th)
       -> ProofOf(DenotesEnv (concatE g g') (remove_fromCS th x )) @-}
lem_remove_var_denote_env :: Env -> Vname -> Type -> Env -> WFEnv -> CSub 
                                 -> DenotesEnv -> DenotesEnv
lem_remove_var_denote_env g x  t_x Empty           p_g'g_wf  th den_env_th = case den_env_th of
  (DExt env' th' den_env'_th'_ _ _tx v_x den_th'tx_vx) -> den_env'_th'
            ? toProof ( remove_fromCS (CCons x v_x th') x === th' ) 
            ? toProof ( CCons x v_x th' === th )
      where
        den_env'_th' = den_env'_th'_ ? lem_binds_env_th env' th' den_env'_th'_
lem_remove_var_denote_env g x_ t_x (Cons z t_z g') p_zg'g_wf th den_env_th 
  = undefined {- 2 -} {-
   case den_env_th of
  (DEmp)                                               -> impossible "th != CEmpty"
  (DExt env' th' den_env'_th' _z _tz v_z den_th'tz_vz) -- env' == concatE (Cons x t_x g) g' 
    -> DExt (concatE g g') (remove_fromCS th' x) den_env''_th'' z t_z v_z den_th''tz_vz
            ? toProof ( remove_fromCS (CCons z v_z th') x === CCons z v_z (remove_fromCS th' x) )
            ? toProof ( CCons z v_z th' === th )
      where
        (WFEBind _ p_g'g_wf _ _ p_g'g_tz) = p_zg'g_wf
        x              = x_ ? lem_binds_env_th (concatE (Cons x_ t_x g) g') th' den_env'_th'
                            ? lem_in_env_concat g g' x_ 
                            ? lem_in_env_concat g (Cons z t_z g') x_
                            ? lem_free_bound_in_env (concatE g g') t_z p_g'g_tz x_
        den_env''_th'' = lem_remove_var_denote_env g x t_x g' p_g'g_wf th' den_env'_th'
        den_th''tz_vz  = lem_remove_var_denote th' t_z v_z den_th'tz_vz x-}
lem_remove_var_denote_env g x_ t_x (ConsT a k_a g') p_zg'g_wf th den_env_th
  = undefined {- 2 -}

{-@ lem_remove_tvar_denote_env :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
       -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
       -> ProofOf(WFEnv (concatE g g'))
       -> th:CSub -> ProofOf(DenotesEnv (concatE (ConsT a k_a g) g') th)
       -> ProofOf(DenotesEnv (concatE g g') (remove_fromCS th a )) @-}
lem_remove_tvar_denote_env :: Env -> Vname -> Kind -> Env -> WFEnv -> CSub 
                                 -> DenotesEnv -> DenotesEnv
lem_remove_tvar_denote_env g a  k_a Empty           p_g'g_wf  th den_env_th = undefined {- 1 -}
lem_remove_tvar_denote_env g a  k_a (Cons {})       p_g'g_wf  th den_env_th = undefined {- 2 -}
lem_remove_tvar_denote_env g a  k_a (ConsT {})      p_g'g_wf  th den_env_th = undefined {- 2 -}


{-@ lem_csubst_hasbtype' :: g:Env -> e:Expr -> t:Type -> ProofOf(HasFType (erase_env g) e (erase t))
        -> th:CSub -> ProofOf(DenotesEnv g th) -> ProofOf(HasFType FEmpty (csubst th e) (erase t)) @-} 
lem_csubst_hasbtype' :: Env -> Expr -> Type -> HasFType -> CSub -> DenotesEnv -> HasFType
lem_csubst_hasbtype' Empty           e t p_e_t th den_g_th = case den_g_th of 
  (DEmp)                                           -> p_e_t ? lem_binds_env_th Empty th den_g_th
lem_csubst_hasbtype' (Cons x t_x g') e t p_e_t th den_g_th 
  = undefined {- 2 -} {-case den_g_th of
  (DExt g' th' den_g'_th' _x _tx v_x den_th'tx_vx) -> p_the_t
    where
      p_emp_vx_tx = get_ftyp_from_den (ctsubst th' t_x) v_x den_th'tx_vx
                                      ? lem_erase_ctsubst th' t_x
      p_g'_vx_tx  = lem_weaken_many_ftyp FEmpty (erase_env g') v_x (erase t_x) p_emp_vx_tx
                                         ? lem_empty_concatF (erase_env g')
      p_evx_t     = lem_subst_ftyp (erase_env g') FEmpty x v_x (erase t_x) p_g'_vx_tx -- ? lem_empty_concatE g')
                                   e (erase t) p_e_t ? lem_erase_tsubFV x v_x t
      p_the_t     = lem_csubst_hasbtype' g' (subFV x v_x e) (tsubFV x v_x t) p_evx_t th' den_g'_th' -}
lem_csubst_hasbtype' (ConsT a k_a g') e t p_e_t th den_g_th 
  = undefined {- 2 -}
