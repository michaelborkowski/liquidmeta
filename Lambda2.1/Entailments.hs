{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Entailments where

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
import SystemFLemmasSubstitution
import SystemFSoundness
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import BasicPropsEraseTyping
import PrimitivesSemantics
import LemmasWellFormedness
import Implications

{-@ reflect foo39 @-}   
foo39 x = Just x 
foo39 :: a -> Maybe a 

 --- PRELIMINARIES

{-@ get_wftype_from_denv :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th)
        -> a:Vname -> { k_a:Kind | tv_bound_in a k_a g }
        -> (UserType, WFType)<{\t_a pf -> t_a == csubst_tv th a &&
                                          propOf pf == WFType Empty t_a k_a }> @-}
get_wftype_from_denv :: Env -> CSub -> DenotesEnv -> Vname -> Kind -> (Type, WFType)
get_wftype_from_denv Empty          _   den_g_th   a k_a = case den_g_th of
  DEmp -> impossible ""
get_wftype_from_denv (Cons z t_z g) zth den_zg_zth a k_a = case den_zg_zth of
  (DExt _g th den_g_th _ _ _ _) -> get_wftype_from_denv g th den_g_th a k_a
get_wftype_from_denv (ConsT a' k' g) a'th den_a'g_a'th a k_a = case den_a'g_a'th of
  (DExtT _g th den_g_th _ _ t' p_emp_t') -> case (a == a') of
    True  -> (t', p_emp_t')
    False -> get_wftype_from_denv g th den_g_th a k_a

{-@ lem_canonical_ctsubst_tv :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th)
        -> a:Vname -> z:RVname -> p:Pred -> ProofOf(WFType g (TRefn (FTV a) z p) Base) 
        -> (UserType, WFType)<{\t_a pf -> isTRefn t_a && propOf pf == WFType Empty t_a Base &&
               t_a == csubst_tv th a && 
               ctsubst th (TRefn (FTV a) Z p) == push (csubst th p) t_a}> @-}
lem_canonical_ctsubst_tv :: Env -> CSub -> DenotesEnv -> Vname -> RVname -> Expr 
                                -> WFType -> (Type, WFType) --(Basic, Expr)
lem_canonical_ctsubst_tv g th den_g_th a z p p_g_t 
  = case (kind_for_tv a (g ? lem_free_subset_binds g (TRefn (FTV a) z p) Base p_g_t)) of
      Base -> (t_a ? lem_wf_usertype_base_trefn Empty t_a p_emp_ta, 
               p_emp_ta ? lem_ctsubst_refn_tv th (a ? lem_binds_env_th g th den_g_th) z p)
        where
          (t_a, p_emp_ta) = get_wftype_from_denv g th den_g_th a Base 
      Star -> impossible ("by lemma" ? lem_wf_refn_kind g a z p Base p_g_t)

{-@ lem_ctsubst_refn_istrefn :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th)
        -> b:Basic -> x:RVname -> p:Pred -> ProofOf(WFType g (TRefn b x p) Base)
        -> { pf:_ | isTRefn (ctsubst th (TRefn b x p)) } @-}
lem_ctsubst_refn_istrefn :: Env -> CSub -> DenotesEnv -> Basic -> RVname -> Expr -> WFType -> Proof
lem_ctsubst_refn_istrefn g th den_g_th b x p p_g_t = case b of
  (FTV a) -> case ( csubst_tv th (a ? lem_wf_refn_tv_in_env g a x p Base p_g_t
                                    ? lem_binds_env_th g th den_g_th) ) of
    (TRefn b' z q_) -> () ? lem_ctsubst_refn_tv th a x p
                          ? toProof ( noExists (TRefn b' z (strengthen (csubst th p) q)) === True )
      where
        q = q_ ? lem_refn_is_pred (TRefn b' z q_) b' z q_
    (TFunc {})     -> impossible ("by lemma" ? lem_wf_usertype_base_trefn Empty t_a p_emp_ta )
      where
        (t_a, p_emp_ta) = lem_canonical_ctsubst_tv g th den_g_th a x p p_g_t
    (TPoly {})     -> impossible ("by lemma" ? lem_wf_usertype_base_trefn Empty t_a p_emp_ta )
      where
        (t_a, p_emp_ta) = lem_canonical_ctsubst_tv g th den_g_th a x p p_g_t
  _       -> () ? lem_ctsubst_refn    th b x p

-------------------------
--- LEMMAS on Entailments
-------------------------

{-@ get_evals_from_drefn :: b:Basic -> x:RVname -> p:Pred -> v:Value 
        -> ProofOf(Denotes (TRefn b x p) v) -> ProofOf(EvalsTo (subBV 0 v p) (Bc True)) @-}
get_evals_from_drefn :: Basic -> RVname -> Expr -> Expr -> Denotes -> EvalsTo
get_evals_from_drefn b x p v (DRefn _ _ _ _ _ ev_pv_tt) = ev_pv_tt

{-@ get_evals_from_ctsubst_drefn :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th) 
        -> ProofOf(WFFE (erase_env g))
        -> b:Basic -> z:RVname -> p:Pred -> ProofOf(WFType g (TRefn b z p) Base)
        -> v:Value -> ProofOf(Denotes (ctsubst th (TRefn b z p)) v)
        -> ProofOf(EvalsTo (subBV 0 v (csubst th p)) (Bc True))  @-}
get_evals_from_ctsubst_drefn :: Env -> CSub -> DenotesEnv -> WFFE -> Basic -> RVname -> Expr
                                    -> WFType -> Expr -> Denotes -> EvalsTo
get_evals_from_ctsubst_drefn g th den_g_th p_g_wf b z p p_g_t v den_tht_v = case b of 
   TBool    -> case (den_tht_v ? lem_ctsubst_refn th b z p) of
     (DRefn _ _ _ _ _ ev_thpv_tt) -> ev_thpv_tt ? lem_ctsubst_refn th b z p
   TInt     -> case (den_tht_v ? lem_ctsubst_refn th b z p) of
     (DRefn _ _ _ _ _ ev_thpv_tt) -> ev_thpv_tt ? lem_ctsubst_refn th b z p
   (FTV a_)  -> ev_thpv_tt
     where
       a               = a_ ? lem_free_subset_binds g (TRefn (FTV a_) z p) Base p_g_t
                            ? lem_binds_env_th g th den_g_th
       (t_a, p_emp_ta) = lem_canonical_ctsubst_tv g th den_g_th a z p p_g_t 
       (TRefn b'_ Z q_) = t_a ? lem_wf_usertype_base_trefn Empty t_a p_emp_ta
       b'              = b'_ ? lem_base_types (erase t_a) (lem_erase_wftype Empty t_a Base p_emp_ta)
       q               = q_  ? lem_refn_is_pred (TRefn b' Z q_) b' Z q_
       ev_thpqv_tt = get_evals_from_drefn b' Z (strengthen (csubst th p) q) v 
                         (den_tht_v ? lem_ctsubst_refn_tv th a z p)
       p_v_b'      = get_ftyp_from_den (TRefn b' Z (strengthen (csubst th p) q)) v 
                         (den_tht_v ? lem_ctsubst_refn_tv th a z p)
       y_          = fresh_var g
       y           = y_ ? lem_free_bound_in_env g (TRefn b z p) Base p_g_t y_
                        ? lem_binds_env_th g th den_g_th   
       pf_yg_p_bl  = lem_ftyp_for_wf_trefn' g b z p Base p_g_t p_g_wf
       p_yg_wf         = WFFBind (erase_env g) p_g_wf y (FTBasic b) Base 
                                 (lem_erase_wftype g (TRefn b z p) Base p_g_t)
       p_yemp_wf       = WFFBind FEmpty WFFEmpty y (FTBasic b') Base (WFFTBasic FEmpty b')
       pf_y_thp_bl     = lem_partial_csubst_hasftype g (Cons y (TRefn b z p) Empty) p_yg_wf
                                 th den_g_th (unbind 0 y p) (TRefn TBool Z (Bc True)) pf_yg_p_bl 
                                 ? lem_csubst_cons_env th y (TRefn b z p) Empty
                                 ? lem_csubst_env_empty th
                                 ? lem_ctsubst_refn th TBool Z (Bc True)
       pf_thpv_bl      = lem_subst_ftyp FEmpty FEmpty y v (FTBasic b') p_v_b' p_yemp_wf 
                                 (csubst th (unbind 0 y p)) (FTBasic TBool) pf_y_thp_bl
                                 ? lem_unroll_csubst_left th y  
                                       (v ? lem_den_nofv v (ctsubst th (TRefn b z p)) den_tht_v)
                                       (unbind 0 y p)
                                 ? lem_subFV_unbind 0 y v 
                                           (p ? lem_free_subset_binds g (TRefn b z p) Base p_g_t
                                              ? lem_binds_env_th g th den_g_th) 
                                 ? lem_csubst_subBV 0 v (FTBasic b') p_v_b' th p 
                                 ? lem_empty_concatF FEmpty

       y'_             = fresh_var Empty
       y'              = y'_ ? lem_free_bound_in_env Empty (TRefn b' Z q) Base p_emp_ta y'_
       pf_y'_q_bl      = lem_ftyp_for_wf_trefn' Empty b' Z q Base p_emp_ta WFFEmpty
       p_y'emp_wf      = WFFBind FEmpty WFFEmpty y' (FTBasic b') Base (WFFTBasic FEmpty b')
       pf_qv_bl        = lem_subst_ftyp FEmpty FEmpty y' v (FTBasic b') p_v_b' p_y'emp_wf 
                                 (unbind 0 y' q) (FTBasic TBool) pf_y'_q_bl
                                 ? lem_subFV_unbind 0 y' v q
       (ev_thpv_tt, _) = lem_strengthen_elimination (subBV 0 v (csubst th p)) (subBV 0 v q) 
                                 pf_thpv_bl pf_qv_bl (ev_thpqv_tt
                                 ? lem_subBV_strengthen 0 v (csubst th p) q)
   (BTV a)  -> impossible ("by lemma" ? lem_btv_not_wf g a z p Base p_g_t)

{-@ lem_entails_elimination :: g:Env -> ProofOf(WFFE (erase_env g)) 
        -> b:Basic -> x:RVname -> p:Term -> { q:Pred | Set_sub (freeBV q) (Set_sng 0) }
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (fv q)) } 
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y p) (FTBasic TBool))
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y q) (FTBasic TBool))
        -> ProofOf(WFType g (TRefn b x (Conj p q)) Base)
        -> ProofOf(Entails (Cons y (TRefn b x (Conj p q)) g) (unbind 0 y q)) @-}
lem_entails_elimination :: Env -> WFFE -> Basic -> RVname -> Expr -> Expr -> Vname 
                               -> HasFType -> HasFType -> WFType -> Entails
lem_entails_elimination g p_g_wf b x p_ q y pf_p_bl pf_q_bl p_g_t1
  = EntPred (Cons y t1 g) (unbind 0 y q) ev_func
   where
    {-@ ev_func :: th:CSub -> ProofOf(DenotesEnv (Cons y t1 g) th) 
                           -> ProofOf(EvalsTo (csubst th (unbind 0 y q)) (Bc True)) @-}
    ev_func :: CSub -> DenotesEnv -> EvalsTo
    ev_func th den_g1_th = case den_g1_th of
      (DExt _g th' den_g_th' _y _t1 th'y den_th't1_th'y) ->
            snd (lem_implies_elimination (Cons y t1 g) th den_g1_th p_yg_wf 
                     (unbind 0 y p) (unbind 0 y q) 
                     pf_p_bl pf_q_bl ( ev_thpq_tt 
               {-? toProof ( subBV x th'y (csubst th' pandq)-}
                           ? lem_csubst_subBV 0 th'y (erase (ctsubst th' t1)) {-(FTBasic b)-} 
                                              p_th'y_th't1 th' pandq
                      {- === csubst th' (subBV x th'y pandq)-}
                           ? lem_subFV_unbind 0 y th'y pandq
                      {- === csubst th' (subFV y th'y (unbind x y pandq)) 
                         === csubst th (unbind x y pandq) ) -}
            {-   ? toProof ( unbind x y pandq === subBV x (FV y) pandq
                         === App (subBV x (FV y) (App (Prim And) p)) (subBV x (FV y) q) 
                         === App (App (subBV x (FV y) (Prim And)) (subBV x (FV y) p)) (subBV x (FV y) q) 
                         === App (App (Prim And) (subBV x (FV y) p)) (subBV x (FV y) q) ) -} )
                     ? lem_binds_env_th g th' den_g_th' )
        where
          {-@ ev_thpq_tt :: ProofOf(EvalsTo (subBV 0 th'y (csubst th' (Conj p q))) (Bc True)) @-}
          {-@ p_th'y_th't1 :: ProofOf(HasFType FEmpty th'y (erase (ctsubst th' t1))) @-}
          ev_thpq_tt   = get_evals_from_ctsubst_drefn g th' den_g_th' p_g_wf b x pandq p_g_t1
                                                      th'y den_th't1_th'y
          p_th'y_th't1 = get_ftyp_from_den (ctsubst th' t1) th'y den_th't1_th'y
    p     = p_ ? lem_term_pred p_
    p_yg_wf = WFFBind (erase_env g) p_g_wf y (erase t1) Base 
                      (lem_erase_wftype g t1 Base p_g_t1)
    t1    = TRefn b x (Conj p q)
    pandq = Conj p q {-? toProof ( fv (App (App (Prim And) p) q)
                               === S.union (fv (App (Prim And) p)) (fv q)
                               === S.union (fv p) (fv q) ) -}

{-@ lem_entails_itself :: g:Env -> ProofOf(WFFE (erase_env g)) -> b:Basic -> x:RVname -> p:Pred
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) } 
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y p) (FTBasic TBool))
        -> ProofOf(WFType g (TRefn b x p) Base)
        -> ProofOf(Entails (Cons y (TRefn b x p) g) (unbind 0 y p ) ) @-}
lem_entails_itself :: Env -> WFFE -> Basic -> RVname -> Expr -> Vname -> HasFType -> WFType -> Entails
lem_entails_itself g p_g_wf b x p y pf_p_bl p_g_t
  = EntPred (Cons y (TRefn b x p) g) (unbind 0 y p) ev_func
      where 
        {-@ ev_func :: th:CSub -> ProofOf(DenotesEnv (Cons y (TRefn b x p) g) th)
                               -> ProofOf(EvalsTo (csubst th (unbind 0 y p)) (Bc True)) @-}
        ev_func :: CSub -> DenotesEnv -> EvalsTo
        ev_func th den_yg_th = case den_yg_th of 
          (DExt _g th' den_g_th' _y _t th'y den_th't_th'y) 
            -> ev_thp_tt ? lem_csubst_subBV 0 th'y (erase (ctsubst th' (TRefn b x p)))             
                                             p_th'y_b th' p
                         ? lem_subFV_unbind 0 y th'y p
            where
              {-@ ev_thp_tt :: ProofOf(EvalsTo (subBV 0 th'y (csubst th' p)) (Bc True)) @-}
              {-@ p_th'y_b :: ProofOf(HasFType FEmpty th'y (erase (ctsubst th' (TRefn b x p)))) @-}
              ev_thp_tt     = get_evals_from_ctsubst_drefn g th' den_g_th' p_g_wf b x 
                                                           p p_g_t th'y den_th't_th'y
              p_th'y_b      = get_ftyp_from_den (ctsubst th' (TRefn b x p)) th'y den_th't_th'y

{-@ lem_entails_itself_trivial :: g:Env -> ProofOf(WFFE (erase_env g)) -> b:Basic -> x:RVname 
        -> { tt:Pred | isTrivial tt} -> { y:Vname | not (in_env y g) && not (Set_mem y (fv tt)) } 
        -> ProofOf(Entails (Cons y (TRefn b x tt) g) (unbind 0 y tt ) ) @-}
lem_entails_itself_trivial :: Env -> WFFE -> Basic -> RVname -> Expr -> Vname -> Entails
lem_entails_itself_trivial g p_g_wf b x tt y --pf_p_bl p_g_t
  = EntPred (Cons y (TRefn b x tt) g) (unbind 0 y tt) ev_func
      where 
        {-@ ev_func :: th:CSub -> ProofOf(DenotesEnv (Cons y (TRefn b x tt) g) th)
                               -> ProofOf(EvalsTo (csubst th (unbind 0 y tt)) (Bc True)) @-}
        ev_func :: CSub -> DenotesEnv -> EvalsTo
        ev_func th den_yg_th = lem_evals_trivial tt ? lem_subBV_notin 0 (FV y) (tt ? lem_trivial_nobv tt)
                                                    ? lem_csubst_trivial th tt

{-@ lem_entails_repetition :: g:Env -> ProofOf(WFFE (erase_env g)) -> b:Basic -> x:RVname -> p:Term
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) } 
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y p) (FTBasic TBool))
        -> ProofOf(WFType g (TRefn b x p) Base)
        -> ProofOf(Entails (Cons y (TRefn b x p) g) (unbind 0 y (Conj p p)) ) @-}
lem_entails_repetition :: Env -> WFFE -> Basic -> RVname -> Expr -> Vname -> HasFType -> WFType -> Entails
lem_entails_repetition g p_g_wf b x p_ y pf_p_bl p_g_t
  = EntPred (Cons y (TRefn b x p) g) (unbind 0 y pandp) ev_func
      where 
        {-@ ev_func :: th:CSub -> ProofOf(DenotesEnv (Cons y (TRefn b x p) g) th)
                               -> ProofOf(EvalsTo (csubst th (unbind 0 y pandp)) (Bc True)) @-}
        ev_func :: CSub -> DenotesEnv -> EvalsTo
        ev_func th den_yg_th = case den_yg_th of 
          (DExt _g th' den_g_th' _y _t th'y den_th't_th'y) ->
              lem_implies_conjunction (Cons y (TRefn b x p) g) th den_yg_th 
                                      (unbind 0 y p ? lem_term_pred p) (unbind 0 y p) 
                                      (ev_thp_tt ? lem_csubst_subBV 0 th'y --(FTBasic b) 
                                                       (erase (ctsubst th' (TRefn b x p)))             
                                                       p_th'y_b th' p
                                                 ? lem_subFV_unbind 0 y th'y p)
                                      ev_thp_tt  ? lem_binds_env_th g th' den_g_th'
            where
              {-@ ev_thp_tt :: ProofOf(EvalsTo (subBV 0 th'y (csubst th' p)) (Bc True)) @-}
              {-@ p_th'y_b :: ProofOf(HasFType FEmpty th'y (erase (ctsubst th' (TRefn b x p)))) @-}
              ev_thp_tt     = get_evals_from_ctsubst_drefn g th' den_g_th' p_g_wf b x 
                                                           p p_g_t th'y den_th't_th'y
              p_th'y_b      = get_ftyp_from_den (ctsubst th' (TRefn b x p)) th'y den_th't_th'y
        p     = p_ ? lem_term_pred p_
        pandp = Conj p p 

{-@ lem_entails_redundancy :: g:Env -> ProofOf(WFFE (erase_env g)) -> b:Basic -> x:RVname -> p:Term
        -> { q:Pred | Set_sub (freeBV q) (Set_sng 0) }
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (fv q)) } 
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y p) (FTBasic TBool))
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y q) (FTBasic TBool))
        -> ProofOf(WFType g (TRefn b x (Conj p q)) Base) -> { p':Term | not (Set_mem y (fv p')) }
        -> ( th':CSub -> ProofOf(DenotesEnv (Cons y (TRefn b x (Conj p q)) g) th') 
                      -> ProofOf(EvalsTo (csubst th' (unbind 0 y p)) (Bc True))
                      -> ProofOf(EvalsTo (csubst th' (unbind 0 y p')) (Bc True)) )
        -> ProofOf(Entails (Cons y (TRefn b x (Conj p q)) g) 
                           (unbind 0 y (Conj p' (Conj p q)))) @-}
lem_entails_redundancy :: Env -> WFFE -> Basic -> RVname -> Expr -> Expr -> Vname -> HasFType 
     -> HasFType -> WFType -> Expr -> (CSub -> DenotesEnv -> EvalsTo -> EvalsTo ) -> Entails
lem_entails_redundancy g p_g_wf b x p_ q y pf_p_bl pf_q_bl p_g_tpq p'_ transf_func
  = EntPred (Cons y tpandq g) (unbind 0 y pandpandq) ev_func
      where
        {-@ ev_func :: th:CSub -> ProofOf(DenotesEnv (Cons y tpandq g) th)
                               -> ProofOf(EvalsTo (csubst th (unbind 0 y pandpandq)) (Bc True)) @-} 
        ev_func :: CSub -> DenotesEnv -> EvalsTo
        ev_func th den_yg_th = case den_yg_th of
          (DExt _g th' den_g_th' _y _tpq th'y den_th'tpq_th'y) ->
              lem_implies_conjunction (Cons y tpandq g) th den_yg_th
                          (unbind 0 y p') (unbind 0 y pandq) --(unbind 0 y q)
                          (ev_thp'_tt ? lem_csubst_subBV 0 th'y (erase (ctsubst th' tpandq)) --(FTBasic b) 
                                            p_th'y_b th' p'
                                      ? lem_subFV_unbind 0 y th'y p') 
                          (ev_thpq_tt ? lem_csubst_subBV 0 th'y (erase (ctsubst th' tpandq)) --(FTBasic b) 
                                            p_th'y_b th' pandq
                                      ? lem_subFV_unbind 0 y th'y pandq)
                          ? lem_binds_env_th g th' den_g_th'
            where
              {-@ ev_thpq_tt :: ProofOf(EvalsTo (subBV 0 th'y (csubst th' (Conj p q))) (Bc True)) @-}
              {-@ p_th'y_b :: ProofOf(HasFType FEmpty th'y (erase (ctsubst th' tpandq))) @-}
              ev_thpq_tt = get_evals_from_ctsubst_drefn g th' den_g_th' p_g_wf b x pandq 
                                                        p_g_tpq th'y den_th'tpq_th'y
              p_th'y_b = get_ftyp_from_den (ctsubst th' tpandq) th'y den_th'tpq_th'y
                               ? lem_erase_ctsubst th' tpandq
              (ev_thp_tt, _) = lem_implies_elimination (Cons y tpandq g) th den_yg_th p_yg_wf
                                      (unbind 0 y p) (unbind 0 y q) pf_p_bl pf_q_bl 
                                      (ev_thpq_tt ? lem_csubst_subBV 0 th'y (erase (ctsubst th' tpandq))
                                                        p_th'y_b th' pandq
                                                  ? lem_subFV_unbind 0 y th'y pandq)
                                      ? lem_binds_env_th g th' den_g_th'
              ev_thp'_tt     = transf_func th den_yg_th ev_thp_tt
        p         = p_  ? lem_term_pred p_
        p'        = p'_ ? lem_term_pred p'_
        tpandq    = TRefn b x (Conj p q) 
        pandq     =            Conj p q
        pandpandq = Conj p' (Conj p q)
        p_yg_wf   = WFFBind (erase_env g) p_g_wf y (erase tpandq) Base 
                            (lem_erase_wftype g tpandq Base p_g_tpq)

{-  NOT NEEDED: This is no longer needed, nothing is logically dependent on this anymore
{-@ lem_entails_conj_commutes :: see Lambda 1.1 @-} -} 
{- NOT NEEDED: we effectively assume all RVname binders are the same
{-@ lem_entails_change_bv @-} -}
