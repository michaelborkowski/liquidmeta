{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple-local"   @-}
{-@ LIQUID "--short-names" @-}

module LemmasExactness where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Strengthenings
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import PrimitivesWFType
import SystemFLemmasFTyping
import SystemFLemmasFTyping2
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import BasicPropsEraseTyping
import Implications
import Entailments
import SubtypingFromEntailments
import LemmasChangeVarWF
import LemmasWeakenWF
import LemmasWellFormedness
import LemmasTyping
import LemmasSubtyping
import LemmasWeakenTyp
import DenotationsSelfify
import DenotationsSoundness
import PrimitivesSemantics
--import PrimitivesDenotations
import SubstitutionLemmaWFEnv

{-@ reflect foo62 @-}
foo62 x = Just x           
foo62 :: a -> Maybe a    

{-@ lem_csubst_eqlPred_ftyp :: g:Env -> ProofOf(WFEnv g) -> b:Basic -> x:RVname -> p:Pred
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (ftv p)) }
        -> ProofOf(WFType g (TRefn b x p) Base) -> e:Term -> ProofOf(HasFType (erase_env g) e (FTBasic b))
        -> { th:CSub | not (Set_mem y (bindsC th)) } -> ProofOf(DenotesEnv g th)  
        -> { v:Value | Set_emp (fv v) && Set_emp (ftv v) && Set_emp (freeBV v) && Set_emp (freeBTV v) } 
        -> ProofOf(HasFType FEmpty v (erase (ctsubst th (TRefn b x p ))))
        -> ProofOf(Denotes  (ctsubst th (TRefn b x (selfify p b x e))) v)
        -> ProofOf(HasFType FEmpty (subBV 0 v (csubst th (eqlPred (TRefn b x p) e))) (FTBasic TBool)) @-}
lem_csubst_eqlPred_ftyp :: Env -> WFEnv -> Basic -> RVname -> Expr -> Vname -> WFType -> Expr
                               -> HasFType -> CSub -> DenotesEnv -> Expr -> HasFType -> Denotes -> HasFType
lem_csubst_eqlPred_ftyp g p_g_wf b x1 p1 y p_g_s e p_e_s th den_g_th v p_v_thb den_thselfs_v = undefined {- CHECKED 2021 pf_eqlthe_bl
  where
    yg            = Cons y (TRefn b x1 (selfify p1 b x1 e)) g
    self_s        =         TRefn b x1 (selfify p1 b x1 e)
    p_er_g_wf     = lem_erase_env_wfenv g p_g_wf
    p_yg_wf       = WFFBind (erase_env g) p_er_g_wf (y ? binds_pf) (FTBasic b) Base 
                            (lem_erase_wftype g (TRefn b x1 p1) Base p_g_s ? erase_pf_b)
    yth           = CCons y v th
    den_yg_yth    = DExt g th den_g_th y self_s v den_thselfs_v
    unb_eqlpred    = unbind 0 y (eqlPred (TRefn b x1 p1 ? refn_pf) e) 

    {-@ pf_y_eqle_bl :: ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) unb_eqlpred (FTBasic TBool)) @-}
    pf_y_eqle_bl  = lem_eqlPred_ftyping'    g b x1 p1      p_g_s p_er_g_wf y e p_e_s  ? erase_env_pf
    pf_eqlthe_bl   = lem_csubst_hasftype' yg  unb_eqlpred  (TRefn TBool Z (Bc True))
                                          pf_y_eqle_bl (p_yg_wf ? erase_env_pf)  yth  den_yg_yth   
       ? toProof ( csubst yth unb_eqlpred
               === csubst (CCons y v th) (unbind 0 y (eqlPred (TRefn b x1 p1 ? refn_pf) e))
                 ? lem_csubst_and_unbind 0 y v (erase (ctsubst th (TRefn b x1 p1))) p_v_thb th 
                       (eqlPred (TRefn b x1 p1 ? refn_pf) e 
                           ? lem_free_bound_in_env g (TRefn b x1 p1) Base p_g_s y
                           ? lem_fv_bound_in_fenv (erase_env g) e (FTBasic b) p_e_s (y ? binds_pf))
               === subBV 0 v (csubst th (eqlPred (TRefn b x1 p1 ? refn_pf) e)) )
       ? lem_ctsubst_nofree yth (TRefn TBool Z (Bc True) ? free_pf ? fv_pf)
       ? erase_pf
    binds_pf      = toProof ( in_envF y (erase_env g) === in_env y g )
                  ? toProof ( bindsF (erase_env g) === binds g )
    erase_pf      = toProof ( erase (TRefn TBool Z (Bc True)) === FTBasic TBool )
    erase_pf_b    = toProof ( erase (TRefn b x1 p1) === FTBasic b )
    erase_env_pf  = toProof ( erase_env (Cons y (TRefn b x1 (selfify p1 b x1 e)) g)
                          === FCons y (erase (TRefn b x1 (selfify p1 b x1 e))) (erase_env g ? binds_pf)
                          === FCons y (FTBasic b) (erase_env g ? binds_pf) )
    free_pf       = toProof ( freeTV (TRefn TBool Z (Bc True)) === ftv (Bc True) === S.empty )
    fv_pf         = toProof ( free (TRefn TBool Z (Bc True))   === fv (Bc True)  === S.empty )
    refn_pf       = toProof ( isTRefn ( TRefn b x1 p1 ) === True )
-}

{-@ ple lem_evals_eqlPred @-}
{-@ lem_evals_eqlPred :: b:Basic -> x1:RVname 
        -> { p1:Pred | Set_emp (tfreeBV (TRefn b x1 p1)) && Set_emp (tfreeBTV (TRefn b x1 p1)) }
        -> { e:Expr | Set_emp (freeBV e) && Set_emp (freeBTV e) } -> v:Value -> th:CSub
        -> ProofOf(EvalsTo (subBV 0 v (csubst th (eqlPred (TRefn b x1 p1) e))) (Bc True))
        -> ProofOf(EvalsTo (App (App (AppT (Prim Eql) (ctsubst th (TRefn b x1 p1))) v) (csubst th e)) (Bc True)) @-}
lem_evals_eqlPred :: Basic -> RVname -> Expr -> Expr -> Expr -> CSub -> EvalsTo -> EvalsTo
lem_evals_eqlPred b x1 p1 e v th ev_theqlv_tt 
 = undefined {- CHECKED 2021
  = ev_theqlv_tt ? lem_csubst_app  th (App (AppT (Prim Eql) (TRefn b x1 p1)) (BV 0)) e
                 ? lem_csubst_app  th (AppT (Prim Eql) (TRefn b x1 p1)) (BV 0)
                 ? lem_csubst_appT th (Prim Eql) (TRefn b x1 p1)
                 ? lem_csubst_prim th Eql -- change precons if necc for th(s)
                 ? lem_csubst_bv   th 0
                 ? lem_subBV_notin  0 v (csubst  th e ? lem_csubst_no_more_bv th e)
                 ? lem_tsubBV_notin 0 v (ctsubst th (TRefn b x1 p1) ? lem_ctsubst_no_more_bv th (TRefn b x1 p1))
-}

{-@ ple lem_eqlPred_exchange_refn @-}
{-@ lem_eqlPred_exchange_refn :: { b:Basic | b == TBool || b == TInt } 
        -> { t1:UserType | erase t1 == FTBasic b } -> { t2:UserType | erase t2 == erase t1 }
        -> e:Term -> v:Value
        -> ProofOf(EvalsTo (App (App (AppT (Prim Eql) t1) v) e) (Bc True)) 
        -> ProofOf(EvalsTo (App (App (AppT (Prim Eql) t2) v) e) (Bc True)) @-}
lem_eqlPred_exchange_refn :: Basic -> Type -> Type -> Expr -> Expr -> EvalsTo -> EvalsTo
lem_eqlPred_exchange_refn b t1 t2 e v ev_eql1_tt = undefined {- CHECKED 2021    case ev_eql1_tt of
  (AddStep eql1 eql1' st_eql1_eql' _true ev_eql'_tt) 
    -> AddStep eql2 eql' st_eql2_eql' (Bc True) 
               (ev_eql'_tt ? lem_sem_det eql1 eql1' st_eql1_eql' eql' step_one1)
         where
           eql2         = App (App (AppT (Prim Eql) t2) v) e
           (Prim c)     = deltaT Eql t1
           eql'         = App (App (Prim c) v) e
           step1        = EApp1 (AppT (Prim Eql) t1) (Prim c) (EPrimT Eql t1) v
           step_one1    = EApp1 (App (AppT (Prim Eql) t1) v) (App (Prim c) v) step1 e
           step2        = EApp1 (AppT (Prim Eql) t2) (Prim c) (EPrimT Eql t2) v
           st_eql2_eql' = EApp1 (App (AppT (Prim Eql) t2) v) (App (Prim c) v) step2 e
-}

{-@ ple lem_ctsubst_refn_isrefnconc @-} 
{-@ lem_ctsubst_refn_isrefnconc :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th)
          -> b:Basic -> x:RVname -> p:Pred -> ProofOf(WFType g (TRefn b x p) Base)
          -> { b':Basic | isTRefn (ctsubst th (TRefn b x p)) && noExists (ctsubst th (TRefn b x p)) &&
                          erase (ctsubst th (TRefn b x p)) == FTBasic b' &&
                        ( b' == TBool || b' == TInt ) } @-}
lem_ctsubst_refn_isrefnconc :: Env -> CSub -> DenotesEnv -> Basic -> RVname -> Expr -> WFType -> Basic
lem_ctsubst_refn_isrefnconc g th den_g_th b x p p_g_t = undefined {- CHECKED case b of
  (FTV a) -> case ( csubst_tv th (a ? lem_wf_refn_tv_in_env g a x p Base p_g_t
                                    ? lem_binds_env_th g th den_g_th) ) of
    (TRefn b' z q_) -> case b' of 
         (BTV a') -> impossible () 
         (FTV a') -> impossible () 
         _        -> b' ? lem_ctsubst_refn_tv th a x p
                        ? toProof ( noExists (TRefn b' z (strengthen (csubst th p) q)) === True )
      where
        q        = q_ ? lem_refn_is_pred (TRefn b' z q_) b' z q_
    (TFunc {})     -> impossible ("by lemma" ? lem_wf_usertype_base_trefn Empty t_a p_emp_ta )
      where
        (t_a, p_emp_ta) = lem_canonical_ctsubst_tv g th den_g_th a x p p_g_t
    (TPoly {})     -> impossible ("by lemma" ? lem_wf_usertype_base_trefn Empty t_a p_emp_ta )
      where
        (t_a, p_emp_ta) = lem_canonical_ctsubst_tv g th den_g_th a x p p_g_t
  (BTV a) -> impossible ("by lemma" ? lem_btv_not_wf g a x p Base p_g_t)
  _       -> b ? lem_ctsubst_refn    th b x p
-}

{-@ lem_self_entails_self :: g:Env -> ProofOf(WFEnv g) -> b:Basic -> x1:RVname -> p1:Pred 
        -> x2:RVname -> p2:Pred 
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p1)) && not (Set_mem y (fv p2)) 
                                        && not (Set_mem y (ftv p1)) && not (Set_mem y (ftv p2)) }  
        -> ProofOf(WFType g (TRefn b x1 p1) Base) -> ProofOf(WFType g (TRefn b x2 p2) Base)   
        -> ProofOf(Subtype g (TRefn b x1 p1) (TRefn b x2 p2))
        -> ProofOf(Entails (Cons y (TRefn b x1 p1) g) (unbind 0 y p2)) 
        -> e:Term -> ProofOf(HasFType (erase_env g) e (FTBasic b))
        -> ProofOf(Entails (Cons y (TRefn b x1 (selfify p1 b x1 e)) g) 
                           (unbind 0 y (selfify p2 b x2 e))) @-}
lem_self_entails_self :: Env -> WFEnv -> Basic -> RVname -> Expr -> RVname -> Expr -> Vname 
                             -> WFType -> WFType -> Subtype -> Entails -> Expr -> HasFType -> Entails
lem_self_entails_self g p_g_wf b x1 p1 x2 p2 y p_g_s p_g_t p_s_t ent_yg_p2 e p_e_t 
 = undefined {- CHECKED 2021
  = EntPred yg (unbind 0 y (selfify p2 b x2 e)) reduce_thselfp2_tt             
      where
        s             = TRefn b x1 p1     ? toProof ( isTRefn ( TRefn b x1 p1 ) === True )
        t             = TRefn b x2 p2     ? toProof ( isTRefn ( TRefn b x2 p2 ) === True )
        yg            = Cons y (TRefn b x1 (selfify p1 b x1 e)) g
        self_s        =         TRefn b x1 (selfify p1 b x1 e)
        p_g_b         = lem_erase_wftype    g (TRefn b x1 p1) Base p_g_s 
        p_er_g_wf     = lem_erase_env_wfenv g p_g_wf
        p_g_selfs     = lem_selfify_wf      g s Base p_g_s p_er_g_wf e
                                            (p_e_t ? erase_s) -- ? lem_erase_subtype g s t p_s_t)
        p_selfs_s     = lem_self_is_subtype g s Base p_g_s e 
                                            (p_e_t ? erase_s) p_g_wf -- ? lem_erase_subtype g s t p_s_t) p_g_wf
        p_g_selft     = lem_selfify_wf      g t Base p_g_t      p_er_g_wf e (p_e_t ? erase_t )
        y'_           = fresh_var g
        y'            = y'_ ? lem_free_bound_in_env g s Base p_g_s y'_
        y'g           = Cons y' (TRefn b x1 (selfify p1 b x1 e)) g
        p_y'_p1_bl    = lem_ftyp_for_wf_trefn' g b x1 p1 Base p_g_s p_er_g_wf
        p_yg_wf       = WFFBind (erase_env g) p_er_g_wf  y              (FTBasic b) Base p_g_b
        p_y'g_wf      = WFFBind (erase_env g) p_er_g_wf (y' ? binds_pf) (FTBasic b) Base p_g_b
        {-@ reduce_thselfp2_tt :: yth:CSub -> ProofOf(DenotesEnv yg yth)
                        -> ProofOf(EvalsTo (csubst yth (unbind 0 y (selfify p2 b x2 e))) (Bc True)) @-}
        reduce_thselfp2_tt :: CSub -> DenotesEnv -> EvalsTo
        reduce_thselfp2_tt yth den_yg_yth = case den_yg_yth of
          (DExt _g th_ den_g_th _y _selfs v den_thselfs_v) -> ev_thselp2v_tt
            where
              th             = th_ ? lem_binds_env_th g th_ den_g_th
              p_v_b          = get_ftyp_from_den (ctsubst th self_s) v den_thselfs_v
              {-@ ev_thselp1_tt :: ProofOf(EvalsTo (subBV 0 v (csubst th (strengthen (eqlPred s e) p1))) (Bc True)) @-}
              ev_thselp1_tt  = get_evals_from_ctsubst_drefn g th den_g_th p_er_g_wf b x1
                                                    (selfify p1 b x1 e) p_g_selfs v den_thselfs_v
                                ? toProof ( selfify p1 b x1 e === (strengthen (eqlPred (TRefn b x1 p1) e) p1) )
              {-@ ev_thselp1_tt' :: ProofOf(EvalsTo (strengthen (subBV 0 v (csubst th (eqlPred s e))) (subBV 0 v (csubst th p1))) (Bc True)) @-}
              ev_thselp1_tt' = ev_thselp1_tt ? lem_csubst_strengthen th (eqlPred s e) p1
                                             ? lem_subBV_strengthen 0 v (csubst th (eqlPred s e)) (csubst th p1)
              den_ths_v      = lem_denote_sound_sub g self_s Base s Base p_selfs_s p_g_wf
                                                    p_g_selfs p_g_s th den_g_th v den_thselfs_v
              den_tht_v      = lem_denote_sound_sub g s Base t Base p_s_t p_g_wf 
                                                    p_g_s p_g_t th den_g_th v den_ths_v
              {-@ p_emp_tht :: ProofOf(WFType Empty (ctsubst th t) Base) @-}
              p_emp_tht      = lem_ctsubst_wf'      g t Base p_g_t p_g_wf th den_g_th
              p_the_tht      = lem_csubst_hasftype' g e t p_e_t p_er_g_wf th den_g_th

              p_v_thb        = p_v_b ? lem_erase_ctsubst th self_s (s ? lem_erase_subtype g self_s s p_selfs_s)
              {-@ pf_eqlthe_bl :: ProofOf(HasFType FEmpty (subBV 0 v (csubst th (eqlPred (TRefn b x1 p1) e))) (FTBasic TBool)) @-}
              pf_eqlthe_bl   = lem_csubst_eqlPred_ftyp g p_g_wf b x1 p1 y p_g_s e 
                                                       (p_e_t ? lem_erase_subtype g s t p_s_t) 
                                                       th den_g_th v p_v_thb den_thselfs_v

              y'th           = CCons y' v th
              den_y'g_y'th   = DExt g th den_g_th y' (TRefn b x1 (selfify p1 b x1 e)) v den_thselfs_v
              {-@ pf_thp1v_bl :: ProofOf(HasFType FEmpty (subBV 0 v (csubst th p1)) (FTBasic TBool)) @-}
              pf_thp1v_bl    = lem_csubst_hasftype' y'g (unbind 0 y' p1) (TRefn TBool Z (Bc True))
                                                    p_y'_p1_bl (p_y'g_wf ? erase_env_pf) y'th den_y'g_y'th 
                ? toProof ( csubst y'th (unbind 0 y' p1)
                        === csubst (CCons y' v th) (unbind 0 y' p1) 
                          ? lem_csubst_and_unbind 0 y' v (erase (ctsubst th self_s)) p_v_b th 
                                (p1 ? lem_free_bound_in_env g (TRefn b x1 p1) Base p_g_s y'
                                    ? toProof (S.isSubsetOf (fv p1) (free (TRefn b x1 p1))) )
                        === subBV 0 v (csubst th p1) )
                ? lem_ctsubst_nofree y'th (TRefn TBool Z (Bc True) ? free_pf ? fv_pf)
                ? erase_pf

              b'             = lem_ctsubst_refn_isrefnconc g th den_g_th b x1 p1 p_g_s
              (ev_eqle_tt,_) = lem_strengthen_elimination (subBV 0 v (csubst th (eqlPred s e))) --eqlpred_v_the 
                                                          (subBV 0 v (csubst th p1)) 
                                                          pf_eqlthe_bl pf_thp1v_bl ev_thselp1_tt'
              ev_eql1e_tt    = lem_evals_eqlPred b x1 (p1 ? lem_tfreeBV_empty g (TRefn b x1 p1) Base p_g_s)
                                                 (e ? lem_freeBV_emptyB (erase_env g) e (FTBasic b) p_e_t)
                                                 v th ev_eqle_tt
              {-@ ev_eql2e_tt :: ProofOf(EvalsTo (App (App (AppT (Prim Eql) (ctsubst th (TRefn b x2 p2))) v) 
                                                      (csubst th e)) (Bc True)) @-}
              ev_eql2e_tt    = lem_eqlPred_exchange_refn b' (ctsubst th s)
                                   (ctsubst th t ? lem_erase_ctsubst th s (t ? erase_s ? erase_t)
                                                 ? lem_ctsubst_usertype th (t ? noexists_pf)) 
                                   (csubst th e) v ev_eql1e_tt

              den_thselft_v  = lem_denotations_selfify' 
                                    (ctsubst th t ? lem_ctsubst_usertype th (t ? noexists_pf)) 
                                    Base p_emp_tht (csubst  th e ? lem_csubst_no_more_bv th 
                                                     (e ? lem_freeBV_emptyB (erase_env g) e (FTBasic b) p_e_t )) 
                                    p_the_tht v ev_eql2e_tt den_tht_v
                                    ? lem_ctsubst_self th (TRefn b x2 p2) e Base
              ev_thselp2v_tt = get_evals_from_ctsubst_drefn g th den_g_th p_er_g_wf b x2 
                                                    (selfify p2 b x2 e) p_g_selft
                                                    v den_thselft_v
                ? toProof ( csubst yth (unbind 0 y (selfify p2 b x2 e))
                        === csubst (CCons y v th) (unbind 0 y (selfify p2 b x2 e)) 
                          ? lem_csubst_and_unbind 0 y v (erase (ctsubst th self_s)) p_v_b 
                                    (th ? toProof ( S.member y (binds g) === S.member y (bindsC th) )) 
                                    (selfify p2 b x2 e ? self_fv_pf)
                        === subBV 0 v (csubst th (selfify p2 b x2 e)) )
              bindsC_pf     = toProof ( S.member y (binds g) ? lem_binds_env_th g th den_g_th 
                                    === S.member y (bindsC th) )
                       
        binds_y_pf    = toProof ( in_envF y (erase_env g) === in_env y g )
                      ? toProof ( bindsF (erase_env g) === binds g )
        binds_pf      = toProof ( in_envF y' (erase_env g) === in_env y' g )
                      ? toProof ( bindsF (erase_env g) === binds g )
        erase_s       = toProof ( erase (TRefn b x1 p1)            === FTBasic b )
        erase_t       = toProof ( erase (TRefn b x2 p2)            === FTBasic b )
        erase_pf      = toProof ( erase (TRefn TBool Z (Bc True))  === FTBasic TBool )
        erase_env_pf  = toProof ( erase_env (Cons y' (TRefn b x1 (selfify p1 b x1 e)) g)
                              === FCons y' (erase (TRefn b x1 (selfify p1 b x1 e))) (erase_env g ? binds_pf)
                              === FCons y' (FTBasic b) (erase_env g ? binds_pf) )
        free_pf       = toProof ( freeTV (TRefn TBool Z (Bc True)) === ftv (Bc True) === S.empty )
        fv_pf         = toProof ( free (TRefn TBool Z (Bc True))   === fv (Bc True)  === S.empty )
        self_fv_pf    = toProof ( fv (selfify p2 b x2 e) === S.union (fv p2) (fv e) ) 
                      ? lem_fv_bound_in_fenv (erase_env g) e (FTBasic b) p_e_t (y ? binds_y_pf)
        noexists_pf   = toProof ( noExists (TRefn b x2 p2) === True )
-}

{-@ ple lem_subtype_in_exists @-}
{-@ lem_subtype_in_exists :: g:Env -> x:Vname -> t_x:Type -> k_x:Kind 
        -> ProofOf(WFType g t_x k_x) -> ProofOf(WFEnv g) -> t:Type 
        -> { t':Type | not (Set_mem x (tfreeBV t')) }
        -> { y:Vname | not (in_env y g) && not (Set_mem y (free t))
                                        && not (Set_mem y (free t')) }
        -> ProofOf(Subtype (Cons y t_x g) (unbindT x y t) (unbindT x y t'))
        -> ProofOf(Subtype g (TExists x t_x t) (TExists x t_x t')) @-}
lem_subtype_in_exists :: Env -> Vname -> Type -> Kind -> WFType -> WFEnv -> Type -> Type 
                           -> Vname -> Subtype -> Subtype
lem_subtype_in_exists g x t_x k_x p_g_tx p_g_wf t t' y p_yg_t_t' 
 = undefined {- CHECKED 2021
  = SBind g x t_x t (TExists x t_x t' ? lem_free_bound_in_env g t_x k_x p_g_tx y
                                      ? lem_tfreeBV_empty g t_x k_x p_g_tx 
                                      ? toProof ( free (TExists x t_x t') === S.union (free t_x) (free t') ))
          y p_t_ext'
      where
        p_yg_wf     = WFEBind g p_g_wf y t_x k_x p_g_tx
        p_yg_tx     = lem_weaken_wf' g Empty p_g_wf t_x k_x p_g_tx y t_x
        -- y:t_x, g |- (self t_x y) <: tx
        p_selftx_tx = lem_self_is_subtype (Cons y t_x g) t_x k_x p_yg_tx (FV y) 
                                          (FTVar1 (erase_env g) y (erase t_x)) p_yg_wf
        p_y_tx      = TSub (Cons y t_x g) (FV y) (self t_x (FV y) k_x) 
                           (TVar1 g y t_x k_x p_g_tx) t_x k_x p_yg_tx p_selftx_tx
        p_t_ext'    = SWitn (Cons y t_x g) (FV y) t_x p_y_tx (unbindT x y t) x t' p_yg_t_t'        
-}

{-@ ple lem_self_idempotent_upper @-}
{-@ lem_self_idempotent_upper :: g:Env -> t:Type -> k:Kind -> ProofOf(WFType g t k)
        -> e:Expr -> ProofOf(HasFType (erase_env g) e (erase t))
        -> ProofOf(WFEnv g) -> ProofOf(Subtype g (self t e k) (self (self t e k) e k)) / [tsize t] @-}
lem_self_idempotent_upper :: Env -> Type -> Kind -> WFType -> Expr -> HasFType -> WFEnv -> Subtype
lem_self_idempotent_upper g (TRefn b z q_) Base p_g_t e_ p_e_t p_g_wf 
  = SBase g z b (selfify q b z e) z (selfify (selfify q b z e) b z e) y p_ent_ssq
      where 
        q         = q_ ? lem_refn_is_pred (TRefn b z q_) b z q_
        e         = e_ ? lem_freeBV_emptyB (erase_env g) e_ (FTBasic b) p_e_t
        y_        = fresh_var g
        y         = y_ ? lem_free_bound_in_env g (TRefn b z q) Base p_g_t y_
                       ? lem_fv_bound_in_fenv (erase_env g) e (FTBasic b) p_e_t y_
        p_er_g_wf = lem_erase_env_wfenv g p_g_wf
	pf_q_bl   = lem_ftyp_for_wf_trefn' g b z q Base p_g_t p_er_g_wf        



        -- use eqlPred ftyping
        p         = (App (App (AppT (Prim Eql) (TRefn b 1 (Bc True))) (BV z)) e)
        pf_p_bl   = undefined...
        p_ent_ssp = lem_entails_redundancy g p_er_g_wf b z p q y pf_p_bl pf_q_bl
{- Lambda 1.1 version
lem_self_idempotent_upper g t{- @(TRefn b z p)-} p_g_t@(WFRefn _ z b p w pf_wg_p) 
                          e_ p_e_t p_g_wf  
  = SBase g z b (selfify p b z e) z (selfify (selfify p b z e) b z e) y p_ent_ssp
      where 
        (Prim c)  = equals b
        e         = e_ ? lem_freeBV_emptyB (erase_env g) e_ (FTBasic b) p_e_t
--        (WFRefn _g _ _ _p w pf_wg_p) = p_g_t
        y_        = fresh_var g
        y         = y_ ? lem_free_bound_in_env g (TRefn b z p) p_g_t y_
                       ? lem_fv_bound_in_fenv (erase_env g) e (FTBasic b) p_e_t y_ 
        pf_yg_p   = lem_change_var_ftyp (erase_env g) w (FTBasic b) FEmpty (unbind z w p) 
                                        (FTBasic TBool) pf_wg_p y
                                        ? lem_subFV_unbind z w (FV y) p
        g'        = FCons y (FTBasic b) (erase_env g)
        p_g'_e_t  = lem_weaken_ftyp (erase_env g) FEmpty e (erase t) p_e_t y (FTBasic b)
        q         = App (App (equals b) (BV z)) e
        pf_eqy_bl = FTApp g' (equals b) (FTBasic b) (FTFunc (FTBasic b) (FTBasic TBool))
                          (FTPrm g' c) (FV y) (FTVar1 (erase_env g) y (FTBasic b))
        {-@ pf_q_bl :: ProofOf(HasFType g' (unbind z y q) (FTBasic TBool)) @-}
        pf_q_bl   = FTApp g' (App (equals b) (FV y)) (FTBasic b) (FTBasic TBool)
                          pf_eqy_bl e p_g'_e_t
                          ? lem_subBV_notin z (FV y) (e
                                ? lem_freeBV_emptyB g' e (erase t) p_g'_e_t)
        p_ent_ssp = lem_entails_redundancy g b z p q y pf_yg_p pf_q_bl-}
lem_self_idempotent_upper g t@(TFunc z t_z t') Base p_g_t e p_e_t p_g_wf 
  = lem_sub_refl g t Base p_g_t p_g_wf
lem_self_idempotent_upper g (TExists z t_z t') Base p_g_t e_ p_e_t p_g_wf = undefined {- NOT WORKING
  = lem_subtype_in_exists g z t_z k_z p_g_tz p_g_wf (self t' e Base) 
                          (self (self t' e Base) e Base) y p_st'_sst' 
      where
        e           = e_ ? lem_freeBV_emptyB (erase_env g) e_ (erase t') p_e_t
        (WFExis _ _ _tz k_z p_g_tz _t' _ y0 p_y0g_t') = p_g_t 
--                    = lem_wfexis_for_wf_texists g z t_z t' Base p_g_t
        y_          = fresh_var g
        y           = y_ ? lem_free_bound_in_env g (TExists z t_z t') Base p_g_t y_
                         -- ? lem_erase_concat g Empty
                         ? lem_fv_bound_in_fenv (erase_env g) e (erase t') p_e_t y_
        p_y0g_wf    = WFEBind g p_g_wf y0 t_z k_z p_g_tz
        p_yg_wf     = WFEBind g p_g_wf y  t_z k_z p_g_tz
        p_yg_t'     = lem_change_var_wf g y0 t_z Empty p_y0g_wf (unbindT z y0 t') Base p_y0g_t' y
                                        ? lem_tsubFV_unbindT z y0 (FV y) t'
        p_er_g      = lem_erase_env_wfenv g p_g_wf
        p_e_t'      = lem_weaken_ftyp (erase_env g) FEmpty p_er_g e (erase t') p_e_t y (erase t_z)
        p_st'_sst'  = lem_self_idempotent_upper (Cons y t_z g) (unbindT z y t') Base p_yg_t'
                          e (p_e_t' ? lem_tsubBV_self z (FV y) (self (unbindT z y t') e Base) e Base
                                    ? lem_tsubBV_self z (FV y) (unbindT z y t') e Base ) p_yg_wf
-}
{- Lambda 1.1 version
lem_self_idempotent_upper g t{-(TExists z t_z t')-} p_g_t@(WFExis _ z t_z p_g_tz t' y0 p_y0g_t')
                          e_ p_e_t p_g_wf  
  = lem_subtype_in_exists g z t_z p_g_tz p_g_wf (self {-(unbindT z y-} t'{-)-} e)
                          (self (self {-(unbindT z y-} t'{-)-} e) e) y p_st'_sst' 
      where
        e           = e_ ? lem_freeBV_emptyB (erase_env g) e_ (erase t') p_e_t
        y_          = fresh_var g
        y           = y_ ? lem_free_bound_in_env g (TExists z t_z t') p_g_t y_
                         ? lem_fv_bound_in_fenv (erase_env g) e (erase t') p_e_t y_
        p_yg_wf     = WFEBind g p_g_wf y  t_z p_g_tz
        p_yg_t'     = lem_change_var_wf g y0 t_z Empty (unbindT z y0 t') p_y0g_t' y
                                        ? lem_tsubFV_unbindT z y0 (FV y) t'
        p_e_t'      = lem_weaken_ftyp (erase_env g) FEmpty e (erase t') p_e_t y (erase t_z)
        p_st'_sst'  = lem_self_idempotent_upper (Cons y t_z g) (unbindT z y t') p_yg_t'
                          e (p_e_t' ? lem_erase_tsubBV z (FV y) t') p_yg_wf
                           ? lem_tsubBV_self z (FV y) (self t' e) e
                           ? lem_tsubBV_self z (FV y) t' e
 -}
lem_self_idempotent_upper g t@(TPoly a k_a t') Base p_g_t e p_e_t p_g_wf 
  = lem_sub_refl g t Base p_g_t p_g_wf
lem_self_idempotent_upper g t                  Star p_g_t e p_e_t p_g_wf 
  = lem_sub_refl g t Star p_g_t p_g_wf

{-@ ple lem_self_idempotent_lower @-}
{-@ lem_self_idempotent_lower :: g:Env -> t:Type -> k:Kind -> ProofOf(WFType g t k)
        -> e:Expr -> ProofOf(HasFType (erase_env g) e (erase t))
        -> ProofOf(WFEnv g) -> ProofOf(Subtype g (self (self t e k) e k) (self t e k)) @-}
lem_self_idempotent_lower :: Env -> Type -> Kind -> WFType -> Expr -> HasFType -> WFEnv -> Subtype
lem_self_idempotent_lower g t k p_g_t e_ p_e_t p_g_wf 
  = lem_self_is_subtype g (self t e k) k p_g_selft e p_g_wf
      where
        e         = e_ ? lem_fv_subset_bindsF (erase_env g) e_ (erase t) p_e_t
                       ? lem_freeBV_emptyB    (erase_env g) e_ (erase t) p_e_t
        p_g_selft = lem_selfify_wf g t k p_g_t e p_e_t

--        -> k:Kind -> { e:Expr | Set_emp (freeBV e) } -> t_e:Type -> ProofOf(HasType g e t_e) 
{-@ ple lem_exact_subtype @-}
{-@ lem_exact_subtype :: g:Env -> ProofOf(WFEnv g) -> s:Type -> k_s:Kind -> ProofOf(WFType g s k_s)
        -> t:Type -> ProofOf(Subtype g s t) -> k:Kind -> ProofOf(WFType g t k)
        -> { e:Term | Set_emp (freeBV e) && Set_sub (fv e) (binds g) } 
        -> ProofOf(HasFType (erase_env g) e (erase t))
        -> ProofOf(Subtype g (self s e k) (self t e k)) @-}
lem_exact_subtype :: Env -> WFEnv -> Type -> Kind -> WFType -> Type -> Subtype -> Kind -> WFType
                         -> Expr -> HasFType -> Subtype
-- lem_exact_subtype = undefined {-
lem_exact_subtype g p_g_wf s k_s p_g_s t p_s_t@(SBase _ x1 b p1 x2 p2 y_ ent_yg_p2) Base p_g_t e p_e_t = undefined {- OK!
  = SBase g x1 b (selfify p1 b x1 e) x2 (selfify p2 b x2 e) y ent_yg_selfp2
      where
        y             = y_ ? lem_free_bound_in_env g (TRefn b x1 p1) k_s  p_g_s y_
                           ? lem_free_bound_in_env g (TRefn b x2 p2) Base p_g_t y_  
        (EntPred _ _ reduce_thp2_tt) = ent_yg_p2
        g'            = Cons y (TRefn b x1 (selfify p1 b x1 e)) g
        p_g_s_base    = lem_sub_sbase_pullback_wftype g p_g_wf s t p_s_t k_s p_g_s Base p_g_t
        ent_yg_selfp2 = lem_self_entails_self g p_g_wf b x1 p1 x2 p2 y p_g_s_base p_g_t p_s_t 
                                              ent_yg_p2 e p_e_t
-}
lem_exact_subtype g p_g_wf s k_s p_g_s t p_s_t@(SFunc {}) k _ e p_e_t = p_s_t
lem_exact_subtype g p_g_wf s k_s p_g_s t p_s_t@(SWitn _ v_x t_x p_vx_tx _s x t' p_s_t'vx) Base p_g_t e p_e_t = undefined {-
  = SWitn g v_x t_x p_vx_tx (self s e Base) x (self t' e Base) p_self_s_t'vx
      where 
        p_self_s_t'vx = lem_exact_subtype g p_g_wf s k_s p_g_s (tsubBV x v_x t') p_s_t'vx Base e 
                                          (p_e_t ? lem_erase_tsubBV x v_x t')
                                          ? lem_tsubBV_self x v_x t' e Base
-}
lem_exact_subtype g p_g_wf s k_s p_g_s t p_s_t@(SBind _ x s_x s' _t y p_s'_t) Base p_g_t e p_e_t  = undefined {-
  = SBind g x s_x (self s' e Base) (self t e Base) y p_self_s'_t
      where
        (WFExis _ _ _sx p_g_sx _ w p_wg_s') = p_g_s
        p_yg_wf     = WFEBind g p_g_wf y s_x p_g_sx
        p_yg_e_t    = lem_weaken_ftyp (erase_env g) FEmpty e (erase t) p_e_t y (erase s_x)
        p_yg_s'     = lem_change_var_wf g w s_x Empty (unbindT x w s') p_wg_s' y
                                        ? lem_tsubFV_unbindT x w (FV y) s'
        p_self_s'_t = lem_exact_subtype (Cons y s_x g) p_yg_wf (unbindT x y s') p_yg_s' t 
                                        p_s'_t e p_yg_e_t
                                        ? lem_tsubBV_self x (FV y) s' e 
        --p_self_s'_t = lem_exact_subtype (Cons y s_x g) (unbindT x y s') t p_s'_t Base e p_e_t
        --                                ? lem_tsubBV_self x (FV y) s' e Base
        -}                                
lem_exact_subtype g p_g_wf s k_s p_g_s t p_s_t@(SPoly {}) k _ e p_e_t = p_s_t
lem_exact_subtype g p_g_wf s k_s p_g_s t p_s_t Star _ e p_e_t 
  = p_s_t ? toProof (self s e Star === s)
          ? toProof (self t e Star === t)

{-
{-@ lem_exact_type :: g:Env -> v:Value -> t:Type -> ProofOf(HasType g v t) -> k:Kind
        -> ProofOf(WFEnv g) -> ProofOf(HasType g v (self t v k)) @-}
lem_exact_type :: Env -> Expr -> Type -> HasType -> Kind -> WFEnv -> HasType
lem_exact_type g e t _ _ _ = undefined {-
lem_exact_type g e t (TBC _ b)   Base p_g_wf  = undefined {- recheck
  = TSub g (Bc b) (tybc b) (TBC g b) (self (tybc b) (Bc b) Base) Base p_g_self_tybc tybc_self_tybc
      where
        refn_tybc      = App (App () (BV 0)) (Bc b)
        p_g_tybc       = lem_wf_tybc g b
        p_g_self_tybc  = lem_selfify_wf' g (tybc b) Base p_g_tybc p_g_wf (Bc b) (TBC g b)
        tybc_self_tybc = lem_subtype_repetition g TBool Z refn_tybc p_g_tybc
-}
lem_exact_type g e t (TIC _ n)   Base p_g_wf  = undefined {- recheck
  = TSub g (Ic n) (tyic n) (TIC g n) (self (tyic n) (Ic n) Base) Base p_g_self_tyic tyic_self_tyic
      where
        refn_tyic      = App (App (Prim Eq) (BV 0)) (Ic n)
        p_g_tyic       = lem_wf_tyic g n
        p_g_self_tyic  = lem_selfify_wf' g (tyic n) Base p_g_tyic p_g_wf (Ic n) (TIC g n)
        tyic_self_tyic = lem_subtype_repetition g TInt Z refn_tyic p_g_tyic
-}
lem_exact_type g e t p_e_t@(TVar1 env z t' k' p_env_t)   Base p_g_wf  = undefined {- redo
  = TSub g (FV z) (self t' (FV z) Base) p_e_t (self (self t' (FV z) Base) (FV z) Base) 
         Base p_g_selft t_self_t 
      where
        (WFEBind _env p_env_wf _ _ _ p_env_t') = p_g_wf 
        p_g_t'    = lem_weaken_wf   env Empty t' p_env_t' z t'
        p_g_t     = lem_typing_wf   g e t p_e_t p_g_wf
        p_g_selft = lem_selfify_wf' g   t p_g_t p_g_wf (FV z) p_e_t
        p_g_t_t'  = lem_self_is_subtype g t' p_g_t' (FV z) p_z_t' p_g_wf
        p_z_t'    = FTVar1 (erase_env env)  z (erase t')
        t_self_t  = lem_self_idempotent_upper g t' p_g_t' (FV z) p_z_t' p_g_wf
-}
lem_exact_type g e t (TVar2 env z _t p_z_t w t_w) Base p_g_wf 
  = TVar2 env z (self t e Base) p_z_selftz w t_w
      where
        (WFEBind _env p_env_wf _ _ _ p_env_tw) = p_g_wf 
        p_z_selftz = lem_exact_type env e t p_z_t Base p_env_wf
lem_exact_type g e t (TVar3 env z _t p_z_t a k_a) Base p_g_wf 
  = TVar3 env z (self t e Base) p_z_selftz a k_a
      where
        (WFEBindT _env p_env_wf _ _) = p_g_wf 
        p_z_selftz = lem_exact_type env e t p_z_t Base p_env_wf
lem_exact_type g e t p_e_t@(TPrm {})  Base p_g_wf  
  = case t of
      (TFunc {}) -> p_e_t 
      (TPoly {}) -> p_e_t
lem_exact_type g e t p_e_t@(TAbs env_ z t_z k_z p_env_tz e' t' y_ p_yenv_e'_t') Base p_g_wf
  = case t of
      (TFunc {}) -> p_e_t 
lem_exact_type g e t (TApp {})  Base p_g_wf = impossible "not a value"
lem_exact_type g e t p_e_t@(TAbsT _env a k e' t' k_t' a' p_a'env_e'_t' p_a'env_t') Base p_g_wf
  = case t of
      (TPoly {}) -> p_e_t
lem_exact_type g e t (TAppT {}) Base p_g_wf = impossible "not a value"
lem_exact_type g e t (TLet {})  Base p_g_wf = impossible "not a value"
lem_exact_type g e t (TAnn {})  Base p_g_wf = impossible "not a value"
lem_exact_type g e t p_e_t@(TSub _g e_ s p_g_e_s t_ k p_g_t p_g_s_t) Base p_g_wf = undefined {- recheck
  = TSub g e (self s e Base) p_e_selfs (self t e Base) k p_g_selft p_selfs_selft
     where
       p_g_s         = lem_typing_wf     g e s p_g_e_s p_g_wf
       p_e_selfs     = lem_exact_type    g e s p_g_e_s Base p_g_wf
       p_g_selft     = lem_selfify_wf'   g t k p_g_t p_g_wf e p_e_t
       p_e_er_t      = lem_typing_hasftype g e t p_e_t p_g_wf
       p_selfs_selft = lem_exact_subtype g p_g_wf s Star p_g_s t p_g_s_t Base (e
                           ? lem_freeBV_empty    g e t p_e_t p_g_wf
                           ? lem_fv_subset_binds g e t p_e_t p_g_wf) p_e_er_t
-}
{-     p_e_selfs     = lem_exact_type    g e s p_g_e_s Base
       p_g_selft_b   = lem_selfify_wf'   g t Base p_g_t e p_e_t
       p_g_selft     = if k == Base then p_g_selft_b
                       else WFKind g (self t e Base) p_g_selft_b
       p_selfs_selft = lem_exact_subtype g s t p_g_s_t Base (e ? lem_freeBV_empty -}
lem_exact_type g e t p_e_t Star p_g_wf = p_e_t ? toProof ( self t e Star === t )
-}-}
