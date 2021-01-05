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
import SystemFAlphaEquivalence
import BasicPropsCSubst

{-@ reflect foo29 @-}
foo29 x = Just x 
foo29 :: a -> Maybe a 

  -- smart constructors 

{-@ simpleDFunc :: x:Vname -> t_x:Type -> t:Type -> v:Value  
                  -> ProofOf(HasFType FEmpty v (erase (TFunc x t_x t)))
                  -> ( v_x:Value -> ProofOf(Denotes t_x v_x)
                                 -> ProofOf(ValueDenoted (App v v_x) (tsubBV x v_x t)) ) 
                  -> ProofOf(Denotes (TFunc x t_x t) v) @-}
simpleDFunc :: Vname -> Type -> Type -> Expr -> HasFType 
                     -> ( Expr -> Denotes -> ValueDenoted ) -> Denotes
simpleDFunc x t_x t v p_v_er_txt val_den_func
  = DFunc x t_x t v (erase t_x) (erase t) eqv_txt_txt p_v_er_txt val_den_func
      where
        p_emp_er_txt = lem_ftyping_wfft FEmpty v (erase (TFunc x t_x t)) p_v_er_txt WFFEmpty
        eqv_txt_txt  = lem_alpha_refl FEmpty (erase (TFunc x t_x t) 
                           ? lem_ffreeTV_subset_bindsF FEmpty (erase (TFunc x t_x t)) Star p_emp_er_txt)

{-@ simpleDPoly :: a:Vname -> k:Kind -> t:Type -> v:Value 
                  -> ProofOf(HasFType FEmpty v (FTPoly a k (erase t)))
                  -> ( t_a:UserType -> ProofOf(WFType Empty t_a k) 
                                    -> ProofOf(ValueDenoted (AppT v t_a) (tsubBTV a t_a t)) )
                  -> ProofOf(Denotes (TPoly a k t) v) @-} 
simpleDPoly :: Vname -> Kind -> Type -> Expr -> HasFType
                     -> (Type -> WFType -> ValueDenoted) -> Denotes
simpleDPoly a k t v p_v_at val_den_func
  = DPoly a k t v a (erase t) eqv_at_at p_v_at val_den_func
      where
        p_emp_er_at = lem_ftyping_wfft FEmpty v (FTPoly a k (erase t)) p_v_at WFFEmpty
        eqv_at_at   = lem_alpha_refl FEmpty (erase (TPoly a k t)
                          ? lem_ffreeTV_subset_bindsF FEmpty (erase (TPoly a k t)) Star p_emp_er_at)

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
        (WFEBindT _ p_env'_wf _ _) = p_env_wf -- TODO can we remove this?
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

{-@ lem_csubst_hasftype' :: g:Env -> e:Expr -> t:Type -> s:FType
        -> ProofOf(AlphaEqv (erase_env g) s (erase t)) -> ProofOf(HasFType (erase_env g) e s)
        -> ProofOf(WFFE (erase_env g)) -> th:CSub -> ProofOf(DenotesEnv g th)
        -> ProofOf(EqvFTyping FEmpty (csubst th e) (erase (ctsubst th t))) @-}
lem_csubst_hasftype' :: Env -> Expr -> Type -> FType -> AlphaEqv -> HasFType -> WFFE 
                            -> CSub -> DenotesEnv -> EqvFTyping
lem_csubst_hasftype' Empty           e t s aeqv_s_t p_e_s p_g_wf th den_g_th = case den_g_th of
  (DEmp) -> AEWitness FEmpty e (erase t) s aeqv_s_t p_e_s ? lem_binds_env_th Empty th den_g_th
{-    where
      p_femp_t = lem_ftyping_wfft FEmpty e (erase t) p_e_s WFFEmpty
      aeqv_t_t = lem_alpha_refl FEmpty (erase t
                                ? lem_ffreeTV_subset_bindsF FEmpty (erase t) Star p_femp_t)-}
lem_csubst_hasftype' (Cons x t_x g') e t s aeqv_s_t p_e_s p_g_wf th den_g_th = undefined {-case den_g_th of
  (DExt g' th' den_g'_th' _x _tx v_x den_th'tx_vx)
      -> AEWitness FEmpty (csubst th e) (erase (ctsubst th t)) s'' aeqv_s''_tht p_the_s''
    where
      (WFFBind _ p_g'_wf_ _ _ _ _) = p_g_wf
      p_g'_wf     = p_g'_wf_ ? lem_empty_concatF (erase_env g')
      (AEWitness _ _ _ s_x eqv_sx_tx p_emp_vx_sx)  -- this citation here is not true
                  = get_aewitness_from_den (t_x ? lem_ctsubst_nofree th' t_x)  v_x den_th'tx_vx
      p_g'_vx_sx  = lem_weaken_many_ftyp FEmpty (erase_env g') p_g'_wf v_x s_x p_emp_vx_sx
                                         ? lem_empty_concatF (erase_env g')
      p_g'_sx     = lem_ftyping_wfft (erase_env g') v_x s_x p_g'_vx_sx p_g'_wf
      p_xg'_wf    = WFFBind (erase_env g') p_g'_wf x s_x Star p_g'_sx
      (AEWitness _xg' _e _s s' aeqv_s'_s p_e_s')
                  = lem_alpha_in_env_ftyp (erase_env g') FEmpty x s_x (erase t_x) eqv_sx_tx e s p_e_s
      aeqv'_s_t   = lem_strengthen_alpha (erase_env g') x (erase t_x) FEmpty s (erase t) aeqv_s_t
      aeqv''_s_t  = lem_weaken_alpha     (erase_env g')               FEmpty s (erase t) aeqv'_s_t x s_x
      aeqv_s'_t   = lem_alpha_trans (FCons x s_x (erase_env g')) s' s (erase t) aeqv_s'_s aeqv''_s_t
                                    ? lem_erase_tsubFV x v_x t
      p_evx_s'vx  = lem_subst_ftyp (erase_env g') FEmpty x v_x s_x p_g'_vx_sx p_xg'_wf
                                   e s' p_e_s' -- (erase t) p_e_t ? lem_erase_tsubFV x v_x t
      (AEWitness _ _the _tht s'' aeqv_s''_tht p_the_s'')
                  = lem_csubst_hasftype' g' (subFV x v_x e) (tsubFV x v_x t) s' aeqv_s'_t p_evx_s'vx
                                         p_g'_wf th' den_g'_th' -- th(s) ~ s' and t ~ s so is th(t) ~~?
-} -- need a lemma for ctsubst of FV x, then do induction on the structure of p_e_s
lem_csubst_hasftype' (ConsT a k_a g') e t s aeqv_s_t p_e_s p_g_wf th den_g_th
  = undefined {- 1 -}
