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
import PrimitivesSemantics
import Entailments
import LemmasChangeVarWF
import LemmasWeakenWF
import LemmasWellFormedness
import LemmasTyping
import LemmasSubtyping
import LemmasChangeVarTyp
import LemmasWeakenTyp
import SubstitutionLemmaWF
import SubstitutionLemmaWFTV
import SubstitutionWFAgain
import DenotationsSelfify
import DenotationsSoundness
--import LemmasExactness

{-@ reflect foo62 @-}
foo62 x = Just x
foo62 :: a -> Maybe a

data TVAugmentedCSubP where
    TVAugmentedCSub :: Env -> Env -> Vname -> Type -> Kind -> CSub -> TVAugmentedCSubP

data TVAugmentedCSub where
    InsertTVInCS :: Env -> Env -> Vname -> Type -> Kind -> CSub -> CSub -> DenotesEnv
                      -> (Expr -> Proof) -> (Type -> Proof) -> TVAugmentedCSub

{-@ data TVAugmentedCSub where
      InsertTVInCS :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
          -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType -> k_a:Kind
          -> th':CSub -> th:CSub -> ProofOf(DenotesEnv (concatE (ConsT a k_a g) g') th)
          -> ( p:Pred -> { pf:Proof | csubst th p  ==  csubst th'  (subFTV a t_a p) } )
          -> ( t:Type -> { pf:Proof | ctsubst th t == ctsubst th' (tsubFTV a t_a t) } )
          -> ProofOf(TVAugmentedCSub g g' a t_a k_a th') @-}


{-@ lem_add_tvar_csubst :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
        -> k_a:Kind -> ProofOf(WFType g t_a k_a)
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') )
        -> th':CSub -> ProofOf(DenotesEnv (concatE g (esubFTV a t_a g')) th')
        -> ProofOf(TVAugmentedCSub g g' a t_a k_a th') / [envsize g'] @-}
lem_add_tvar_csubst :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv
                          -> CSub -> DenotesEnv -> TVAugmentedCSub
lem_add_tvar_csubst g Empty            a t_a_ k_a p_g_ta p_env_wf   th'   den_env'_th'
  = case p_env_wf of -- env = ConsT a k_a g
      (WFEBindT _ p_g_wf _ _) -> InsertTVInCS g Empty a t_a k_a th' 
                 (CConsT a th'ta {-is th'vx-} (th' ? lem_binds_env_th g th' den_env'_th'))
                 (DExtT g th' den_env'_th' a k_a th'ta p_emp_th'ta) eq_func1 eq_func2
               where 
                 t_a = t_a_ ? lem_free_subset_binds g t_a_ k_a p_g_ta
                            ? lem_binds_env_th g th' den_env'_th'
                 {-@ th'ta :: { t:Type | Set_emp (free t) && Set_emp (freeTV t) &&
                       Set_emp (tfreeBV t) && Set_emp (tfreeBTV t) && t == ctsubst th' t_a } @-}
                 th'ta :: Type
                 th'ta_ = ctsubst th' t_a 
                 th'ta  = th'ta_ ? lem_ctsubst_no_more_fv th' t_a	
                                 ? lem_ctsubst_no_more_bv th' 
                                       (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta)
                                 ? lem_ctsubst_usertype th' t_a
                 (WFEBindT _ p_g_wf _ _) = p_env_wf 
                 p_emp_th'ta = lem_ctsubst_wf g t_a k_a p_g_ta p_g_wf th' den_env'_th'
        {- @ eq_func1 :: p:Pred -> { pf:Proof | csubst th p == csubst zth' (subFTV a t_a p) } @-}
                 eq_func1 :: Expr -> Proof   -- csubst th p
                 eq_func1 p = () ? lem_csubst_subFTV   th' a t_a  p 
        {- @ eq_func2 :: t:Type -> { pf:Proof | ctsubst th t == ctsubst zth' (tsubFTV a t_a t) } @-}
                 eq_func2 :: Type -> Proof
                 eq_func2 t = () ? lem_ctsubst_tsubFTV th' a t_a  t
lem_add_tvar_csubst g (Cons  z t_z g') a t_a_ k_a p_g_ta p_zenv_wf  zth'  den_zenv'_zth'
  = case den_zenv'_zth' of   
      (DExt env' th' den_env'_th' _z tzta v_z_ den_th'tzta_vz)
        -> InsertTVInCS g (Cons z t_z g') a t_a k_a zth' zth den_zenv_zth eq_funcz1 eq_funcz2
             where
               t_a          = t_a_
               v_z          = v_z_ ? lem_den_nofv v_z_ (ctsubst th' tzta) den_th'tzta_vz
                                   ? lem_den_nobv v_z_ (ctsubst th' tzta) den_th'tzta_vz 
               zth          = CCons z v_z (th ? lem_binds_env_th env th den_env_th) 
               den_zenv_zth = DExt env th den_env_th z t_z v_z den_thtz_vz
               den_thtz_vz  = den_th'tzta_vz ? eq_func2 t_z
               (WFEBind _ p_env_wf _ _ _ _) = p_zenv_wf
               env          = concatE (ConsT a k_a g) g'
               {- @ eq_func1 :: p:Pred -> { pf:Proof | csubst th p == csubst th' (subFTV a t_a p) } @-}
               {-@ eq_func2 :: t:Type -> { pf:Proof | ctsubst th t == ctsubst th' (tsubFTV a t_a t) } @-}
               eq_func1 :: Pred -> Proof
               eq_func2 :: Type -> Proof 
               (InsertTVInCS _ _ _ _ _ _ th den_env_th eq_func1 eq_func2)
                            = lem_add_tvar_csubst g g' a t_a k_a p_g_ta p_env_wf th' den_env'_th'
               -- csubst zth p  ==  csubst zth'  (subFV x v_x p)
               {- @ eq_funcz1 :: p:Pred
                        -> { pf:Proof | csubst (CCons z v_z th) p == csubst zth' (subFTV a t_a p) } @-}
               eq_funcz1 :: Expr -> Proof
               eq_funcz1 p = ()-- ? toProof ( csubst zth' (subFTV a t_a p) 
                                            ? lem_binds_env_th env' th' den_env'_th'
                                            ? toProof ( zth' === CCons z v_z th' )
--                                        === csubst th' (subFV z v_z (subFTV a t_a p))
                                            ? lem_subFTV_notin a t_a v_z
--                                        === csubst th' (subFV z (subFTV a t_a v_z) (subFTV a t_a p)) 
                                            ? lem_commute_subFTV_subFV  z v_z a -- v_x_ p
                                                    (t_a ? lem_free_bound_in_env g t_a k_a p_g_ta z) p
--                                        === csubst th' (subFTV a t_a (subFV z v_z p)) 
                                            ? eq_func1 (subFV z v_z p)
--                                        === csubst th (subFV z v_z p) ) 
               {- @ eq_funcz2 :: t:Type 
                        -> { pf:Proof | ctsubst (CCons z v_z th) t == ctsubst zth' (tsubFTV a t_a t) } @-}
               eq_funcz2 :: Type -> Proof
               eq_funcz2 t = ()-- ? toProof ( ctsubst zth' (tsubFTV a t_a t) 
                                            ? lem_binds_env_th env' th' den_env'_th'
                                            ? toProof ( zth' === CCons z v_z th' )
--                                        === ctsubst th' (tsubFV z v_z (tsubFTV a t_a t))
                                            ? lem_subFTV_notin a t_a v_z
--                                        === ctsubst th' (tsubFV z (subFTV a t_a v_z) (tsubFTV a t_a t)) 
                                            ? lem_commute_tsubFTV_tsubFV  z v_z a -- v_x_ p
                                                    (t_a ? lem_free_bound_in_env g t_a k_a p_g_ta z) t
--                                        === ctsubst th' (tsubFTV a t_a (tsubFV z v_z t)) 
                                            ? eq_func2 (tsubFV z v_z t)
--                                        === ctsubst th (tsubFV z v_z t) )     
lem_add_tvar_csubst g (ConsT a1 k1 g') a t_a k_a p_g_ta p_a1env_wf a1th' den_a1env'_a1th'
  = case den_a1env'_a1th' of   
      (DExtT env' th' den_env'_th' _a1 _k1 {-tavx-} ta1 p_emp_ta1 {-den_th'tzvx_vz-})
        -> InsertTVInCS g (ConsT a1 k1 g') a t_a k_a a1th' a1th den_a1env_a1th eq_funca1_1 eq_funca1_2
             where
               a1th           = CConsT a1 ta1 (th ? lem_binds_env_th env th den_env_th) 
               den_a1env_a1th = DExtT env th den_env_th a1 k1 ta1 p_emp_ta1 --den_thtz_vz
               (WFEBindT _ p_env_wf _ _) = p_a1env_wf
               env          = concatE (ConsT a k_a g) g'
               {- @ eq_func1 :: p:Pred -> { pf:Proof | csubst th p == csubst th' (subFTV a t_a p) } @-}
               {- @ eq_func2 :: t:Type -> { pf:Proof | ctsubst th t == ctsubst th' (tsubFTV a t_a t) } @-}
               eq_func1 :: Pred -> Proof
               eq_func2 :: Type -> Proof 
               (InsertTVInCS _ _ _ _ _ _ th den_env_th eq_func1 eq_func2)
                            = lem_add_tvar_csubst g g' a t_a k_a p_g_ta p_env_wf th' den_env'_th'
               {- @ eq_funca1_1 :: p:Pred
                        -> { pf:Proof | csubst (CConsT a1 ta1 th) p == csubst a1th' (subFTV a t_a p) } @-}
               eq_funca1_1 :: Expr -> Proof
               eq_funca1_1 p = () -- ? toProof ( csubst a1th' (subFTV a t_a p) 
                                            ? lem_binds_env_th env' th' den_env'_th'
                                            ? toProof ( a1th' === CConsT a1 ta1 th' )
--                                        === csubst th' (subFTV a1 ta1 (subFTV a t_a p))
                                            ? lem_tsubFTV_notin a t_a ta1
--                                        === csubst th' (subFTV a1 (tsubFTV a t_a ta1) (subFTV a t_a p)) 
                                            ? lem_commute_subFTV  a1 ta1 a
                                                    (t_a ? lem_free_bound_in_env g t_a k_a p_g_ta a1) p
--                                        === csubst th' (subFTV a t_a (subFTV a1 ta1 p)) 
                                            ? eq_func1  (subFTV a1 ta1 p)
--                                        === csubst th (subFTV a1 ta1 p) ) 
               {- @ eq_funca1_2 :: t:Type 
                        -> { pf:Proof | ctsubst (CConsT a1 ta1 th) t == ctsubst a1th' (tsubFTV a t_a t) } @-}
               eq_funca1_2 :: Type -> Proof
               eq_funca1_2 t = () -- ? toProof ( ctsubst a1th' (tsubFTV a t_a t) 
                                            ? lem_binds_env_th env' th' den_env'_th'
                                            ? toProof ( a1th' === CConsT a1 ta1 th' )
--                                        === ctsubst th' (tsubFTV a1 ta1 (tsubFTV a t_a t))
                                            ? lem_tsubFTV_notin a t_a ta1
--                                        === ctsubst th' (tsubFTV a1 (tsubFTV a t_a ta1) (tsubFTV a t_a t)) 
                                            ? lem_commute_tsubFTV a1 ta1 a
                                                    (t_a ? lem_free_bound_in_env g t_a k_a p_g_ta a1) t
--                                        === ctsubst th' (tsubFV x v_x_ (tsubFTV a1 ta1 t)) 
                                            ? eq_func2 (tsubFTV a1 ta1 t)
--                                        === ctsubst th (tsubFTV a1 ta1 t) ) 


{-@ lem_subst_tv_ent :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:UserType
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

