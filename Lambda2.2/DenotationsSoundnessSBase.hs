{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module DenotationsSoundnessSBase where

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
import SystemFLemmasFTyping2
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import BasicPropsEraseTyping
import PrimitivesSemantics -- this module has moved "up" in the order
import Implications
import Entailments
import LemmasWeakenWF
import LemmasWeakenWFTV
import LemmasWellFormedness
import SubstitutionLemmaWF
import SubstitutionLemmaWFTV
import SubstitutionWFAgain
import DenotationsSelfify

{-@ reflect foo60 @-}
foo60 :: a -> Maybe a
foo60 x = Just x

{-@ lem_wfftvar_tv_in_csubst :: g:Env -> a:Vname -> k:Kind 
        -> ProofOf(WFFT (erase_env g) (FTBasic (FTV a)) k) -> th:CSub -> ProofOf(DenotesEnv g th)
        -> { pf:_ | tv_in_env a g && tv_in_csubst a th } @-}
lem_wfftvar_tv_in_csubst :: Env -> Vname -> Kind -> WFFT -> CSub -> DenotesEnv -> Proof
lem_wfftvar_tv_in_csubst g a k p_g_a th den_g_th
  = () ? lem_wfftvar_tv_in_env (erase_env g) a k p_g_a
       ? lem_binds_env_th g th den_g_th

{-@ lem_make_denote_strengthen :: g:Env -> th:CSub  -> a:Vname
        -> x1:RVname -> { p1:Pred | Set_sub (fv p1) (vbinds g) && Set_sub (ftv p1) (tvbinds g) } 
        -> x2:RVname -> p2:Pred 
        -> { y:Vname | not (in_env y g) && not (in_csubst y th) && 
                       not (Set_mem y (fv p1)) && not (Set_mem y (fv p2)) }
        -> ProofOf(Entails (Cons y (TRefn (FTV a) x1 p1) g) (unbind 0 y p2))
        -> { b:Basic | b == TBool || b == TInt } -> z:RVname 
        -> { q:Pred | Set_emp (fv q) && Set_emp (ftv q) && (TRefn b z q) == csubst_tv th a } 
        -> v:Value -> ProofOf(HasFType FEmpty v (FTBasic b))
        -> ProofOf(DenotesEnv (Cons y (TRefn (FTV a) x1 p1) g) (CCons y v th))
        -> ProofOf(HasFType FEmpty (subBV 0 v (csubst th p2)) (FTBasic TBool))
        -> ProofOf(EvalsTo (subBV 0 v q) (Bc True))
        -> ProofOf(Denotes (TRefn b z (strengthen (csubst th p2) q)) v)  @-}
lem_make_denote_strengthen :: Env -> CSub -> Vname -> RVname -> Expr -> RVname -> Expr -> Vname -> Entails 
    -> Basic -> RVname -> Expr -> Expr -> HasFType -> DenotesEnv -> HasFType -> EvalsTo -> Denotes 
lem_make_denote_strengthen g th a x1 p1 x2 p2 y pf_ent_p2 b z q v_ p_v_b
                           den_g'_th' pf_thp2v_bl ev_qv_tt = den_t2_v 
    where
      v = v_ ? lem_fv_subset_bindsF FEmpty v_ (FTBasic b) p_v_b
             ? lem_freeBV_emptyB    FEmpty v_ (FTBasic b) p_v_b
      {-@ red_thp2_tt :: th':CSub -> ProofOf(DenotesEnv (Cons y (TRefn (FTV a) x1 p1) g) th')
                                  -> ProofOf(EvalsTo (csubst th' (unbind 0 y p2)) (Bc True)) @-}
      red_thp2_tt :: CSub -> DenotesEnv -> EvalsTo
      (EntPred y_g _p2 red_thp2_tt) = pf_ent_p2 -- this is unbind x2 y p2    
      {-@ ev_thp2v_tt :: ProofOf(EvalsTo (subBV 0 v (csubst th p2)) (Bc True)) @-} 
      ev_thp2v_tt  = red_thp2_tt (CCons y v th) den_g'_th' -- ? lem_subFV_unbind 0 y v p2
                                 ? lem_csubst_and_unbind 0 y v (FTBasic b) p_v_b th p2
      {-@ ev_thp2qv_tt :: ProofOf(EvalsTo (subBV 0 v (strengthen (csubst th p2) q)) (Bc True)) @-}
      ev_thp2qv_tt = lem_strengthen_evals_subBV (csubst th p2) q v pf_thp2v_bl ev_thp2v_tt ev_qv_tt 
      den_t2_v = DRefn b z (strengthen (csubst th p2) q) v p_v_b ev_thp2qv_tt          

{-@ lem_make_csubst_hasftype :: g:Env -> ProofOf(WFFE (erase_env g)) -> th:CSub
        -> a:Vname -> k:Kind -> ProofOf(WFFT (erase_env g) (FTBasic (FTV a)) k)
        -> x:RVname -> { p:Pred | Set_sub (fv p) (vbinds g) && Set_sub (ftv p) (tvbinds g) } 
        -> { y:Vname | not (in_env y g) && not (in_csubst y th) && not (Set_mem y (fv p)) }
        -> ProofOf(HasFType (FCons y (FTBasic (FTV a)) (erase_env g)) (unbind 0 y p) (FTBasic TBool))
        -> { b:Basic | b == TBool || b == TInt } -> z:RVname 
        -> { q:Pred | Set_emp (fv q) && Set_emp (ftv q) && (TRefn b z q) == csubst_tv th a } 
        -> k_a:Kind -> ProofOf(WFType Empty (TRefn b z q) k_a) -> ProofOf(DenotesEnv g th) -> v:Value
        -> ProofOf(HasFType FEmpty v (FTBasic b))
        -> ProofOf(HasFType FEmpty (subBV 0 v (csubst th p)) (FTBasic TBool)) @-}
lem_make_csubst_hasftype :: Env -> WFFE -> CSub -> Vname -> Kind -> WFFT -> RVname -> Expr  
        -> Vname -> HasFType -> Basic -> RVname -> Expr -> Kind -> WFType 
        -> DenotesEnv -> Expr -> HasFType -> HasFType
lem_make_csubst_hasftype g p_g_wf th a_ k p_g_a x p y pf_p_bl 
                         b z q k_a p_emp_ta den_g_th v_ p_v_b = pf_thpv_bl
    where
      a            = a_ ? lem_wfftvar_tv_in_env (erase_env g) a_ k p_g_a
                        ? lem_binds_env_th g th den_g_th
      v            = v_ ? lem_fv_subset_bindsF FEmpty v_ (FTBasic b) p_v_b
                        ? lem_freeBV_emptyB    FEmpty v_ (FTBasic b) p_v_b
      th'          = CCons y v th -- (th ? lem_binds_env_th g th den_g_th)
      p_yg_wf      = WFFBind (erase_env g) p_g_wf y (FTBasic (FTV a)) k p_g_a
                             ? lem_erase_concat g (Cons y (TRefn (FTV a) Z (Bc True)) Empty)
      p_emp_er_ta  = lem_erase_wftype Empty (TRefn b z q) k_a p_emp_ta
      p_y_wf       = WFFBind FEmpty WFFEmpty y (FTBasic b) k_a p_emp_er_ta

      {-@ pf_thp_bl :: ProofOf(HasFType (FCons y (FTBasic b) FEmpty) 
                                        (unbind 0 y (csubst th p)) (FTBasic TBool)) @-}
      pf_thp_bl    = lem_partial_csubst_hasftype g (Cons y (TRefn (FTV a) Z (Bc True)) Empty)
                             p_yg_wf th den_g_th (unbind 0 y p) (TRefn TBool Z (Bc True)) pf_p_bl 
                             ? lem_commute_csubst_subBV th 0 (FV y) p
                             ? lem_csubst_cons_env th y (TRefn (FTV a) Z (Bc True)) Empty
                             ? lem_csubst_env_empty th
                             ? lem_csubst_fv th y
                             ? lem_ctsubst_refn_tv' th a Z (Bc True) b z q
                             ? lem_ctsubst_nofree th (TRefn TBool Z (Bc True))
      {-@ pf_thpv_bl :: ProofOf(HasFType FEmpty (subBV 0 v (csubst th p)) (FTBasic TBool)) @-}
      pf_thpv_bl   = lem_subst_ftyp FEmpty FEmpty y v (FTBasic b) p_v_b p_y_wf
                             (unbind 0 y (csubst th p)) (FTBasic TBool) pf_thp_bl
                             ? lem_subFV_unbind 0 (y ? lem_csubst_no_more_fv th p) v (csubst th p)
                             ? lem_empty_concatF FEmpty

{-@ lem_denote_push_ent_pred_trefn :: g:Env -> ProofOf(WFFE (erase_env g)) 
        -> a:Vname -> k:Kind -> ProofOf(WFFT (erase_env g) (FTBasic (FTV a)) k)
        -> x1:RVname -> { p1:Pred | Set_sub (fv p1) (vbinds g) && Set_sub (ftv p1) (tvbinds g) } 
        -> x2:RVname -> { p2:Pred | Set_sub (fv p2) (vbinds g) && Set_sub (ftv p2) (tvbinds g) }
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p1)) && not (Set_mem y (fv p2)) }
        -> ProofOf(HasFType (FCons y (FTBasic (FTV a)) (erase_env g)) (unbind 0 y p1) (FTBasic TBool))
        -> ProofOf(HasFType (FCons y (FTBasic (FTV a)) (erase_env g)) (unbind 0 y p2) (FTBasic TBool))
        -> ProofOf(Entails (Cons y (TRefn (FTV a) x1 p1) g) (unbind 0 y p2))
        -> { th:CSub | not (in_csubst y th) } 
        -> { b:Basic | b == TBool || b == TInt } -> z:RVname 
        -> { q:Pred | Set_emp (fv q) && Set_emp (ftv q) && (TRefn b z q) == csubst_tv th a } 
        -> k_a:Kind -> ProofOf(WFType Empty (TRefn b z q) k_a) -> ProofOf(DenotesEnv g th) -> v:Value
        -> ProofOf(Denotes (TRefn b z (strengthen (csubst th p1) q)) v) 
        -> ProofOf(Denotes (TRefn b z (strengthen (csubst th p2) q)) v)  @-}
lem_denote_push_ent_pred_trefn :: Env -> WFFE -> Vname -> Kind -> WFFT -> RVname -> Expr -> RVname 
    -> Expr -> Vname -> HasFType -> HasFType -> Entails -> CSub -> Basic -> RVname -> Expr -> Kind -> WFType 
    -> DenotesEnv -> Expr -> Denotes ->     Denotes 
lem_denote_push_ent_pred_trefn g p_g_wf a_ k p_g_a x1 p1 x2 p2 y pf_p1_bl pf_p2_bl pf_ent_p2 th b z q 
                               k_a p_emp_ta den_g_th v den_thp1ta_v = den_t2_v 
    where
      a            = a_ ? lem_wfftvar_tv_in_csubst g a_ k p_g_a th den_g_th
      {-@ ev_thp1qv_tt :: ProofOf(EvalsTo (subBV 0 v (strengthen (csubst th p1) q)) (Bc True)) @-}
      (DRefn _b _z str_thp1_q _v p_v_b ev_thp1qv_tt) = den_thp1ta_v
      {-@ t1 :: { t1_:Type | t1_ == ctsubst th (TRefn (FTV a) x1 p1)  } @-}
      t1           = TRefn b z (strengthen (csubst th p1) q) ? lem_ctsubst_refn_tv' th a x1 p1 b z q
                                           
      th'          = CCons y v th -- (th ? lem_binds_env_th g th den_g_th)
      {-@ den_g'_th' :: ProofOf(DenotesEnv (Cons y (TRefn (FTV a) x1 p1) g) (CCons y v th)) @-}
      den_g'_th'   = DExt g th den_g_th y (TRefn (FTV a) x1 p1) 
                          (v ? lem_den_nobv v  t1 den_thp1ta_v 
                             ? lem_den_nofv v  t1 den_thp1ta_v) den_thp1ta_v

      {-@ pf_thp1v_bl :: ProofOf(HasFType FEmpty (subBV 0 v (csubst th p1)) (FTBasic TBool)) @-}
      pf_thp1v_bl  = lem_make_csubst_hasftype g p_g_wf th a k p_g_a x1 p1 y pf_p1_bl
                         b z q k_a p_emp_ta den_g_th v p_v_b
      {-@ pf_thp2v_bl :: ProofOf(HasFType FEmpty (subBV 0 v (csubst th p2)) (FTBasic TBool)) @-}
      pf_thp2v_bl  = lem_make_csubst_hasftype g p_g_wf th a k p_g_a x2 p2 y pf_p2_bl
                         b z q k_a p_emp_ta den_g_th v p_v_b

      y'_          = fresh_var Empty
      y'           = y'_ ? lem_free_bound_in_env Empty (TRefn b z q) k_a p_emp_ta y'_
      p_emp_er_ta  = lem_erase_wftype Empty (TRefn b z q) k_a p_emp_ta
      p_y'_wf      = WFFBind FEmpty WFFEmpty y' (FTBasic b) k_a p_emp_er_ta
      pf_y'_q_bl   = lem_ftyp_for_wf_trefn' Empty b z q k_a p_emp_ta WFFEmpty
      {-@ pf_qv_bl :: ProofOf(HasFType FEmpty (subBV 0 v q) (FTBasic TBool)) @-}
      pf_qv_bl     = lem_subst_ftyp FEmpty FEmpty y' v (FTBasic b) p_v_b p_y'_wf
                                  (unbind 0 y' q) (FTBasic TBool) pf_y'_q_bl
                                  ? lem_subFV_unbind 0 y' v q
                                  ? lem_empty_concatF FEmpty
      {-@ ev_qv_tt :: ProofOf(EvalsTo (subBV 0 v q) (Bc True)) @-} 
      (_,ev_qv_tt) = lem_strengthen_elimination (subBV 0 v (csubst th p1)) (subBV 0 v q)
                                                pf_thp1v_bl pf_qv_bl (ev_thp1qv_tt
                                  ? lem_subBV_strengthen 0 v (csubst th p1) q)
      den_t2_v = lem_make_denote_strengthen g th a x1 p1 x2 p2 y pf_ent_p2 b z q v p_v_b 
                                            den_g'_th' pf_thp2v_bl ev_qv_tt 

{-@ lem_denote_push_ent_pred :: g:Env -> ProofOf(WFFE (erase_env g)) 
        -> a:Vname -> k:Kind -> ProofOf(WFFT (erase_env g) (FTBasic (FTV a)) k)
        -> x1:RVname -> { p1:Pred | Set_sub (fv p1) (vbinds g) && Set_sub (ftv p1) (tvbinds g) } 
        -> x2:RVname -> { p2:Pred | Set_sub (fv p2) (vbinds g) && Set_sub (ftv p2) (tvbinds g) }
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p1)) && not (Set_mem y (fv p2)) }
        -> ProofOf(HasFType (FCons y (FTBasic (FTV a)) (erase_env g)) (unbind 0 y p1) (FTBasic TBool))
        -> ProofOf(HasFType (FCons y (FTBasic (FTV a)) (erase_env g)) (unbind 0 y p2) (FTBasic TBool))
        -> ProofOf(Entails (Cons y (TRefn (FTV a) x1 p1) g) (unbind 0 y p2))
        -> { th:CSub | not (in_csubst y th) } 
        -> { t_a:UserType | Set_emp (free t_a) && Set_emp (freeTV t_a) && t_a == csubst_tv th a } 
        -> k_a:Kind -> ProofOf(WFType Empty t_a k_a) -> ProofOf(DenotesEnv g th) -> v:Value
        -> ProofOf(Denotes (push (csubst th p1) t_a) v)
        -> ProofOf(Denotes (push (csubst th p2) t_a) v) / [tsize t_a] @-}
lem_denote_push_ent_pred :: Env -> WFFE -> Vname -> Kind -> WFFT -> RVname -> Expr -> RVname 
        -> Expr -> Vname -> HasFType -> HasFType -> Entails -> CSub -> Type -> Kind -> WFType 
        -> DenotesEnv -> Expr -> Denotes ->  Denotes 
lem_denote_push_ent_pred g p_g_wf a_ k p_g_a x1 p1 x2 p2 y pf_p1_bl pf_p2_bl pf_ent_p2 th (TRefn b z q) 
                         k_a p_emp_ta den_g_th v den_thp1ta_v 
  = lem_denote_push_ent_pred_trefn g p_g_wf a_ k p_g_a x1 p1 x2 p2 y pf_p1_bl pf_p2_bl pf_ent_p2 th 
                                   (b ? lem_free_subset_binds Empty (TRefn b z q) k_a p_emp_ta
                                      ? lem_tfreeBV_empty     Empty (TRefn b z q) k_a p_emp_ta) z 
                                   (q ? lem_refn_is_pred (TRefn b z q) b z q)
                                   k_a p_emp_ta den_g_th v den_thp1ta_v
lem_denote_push_ent_pred g _ a k _ x1 p1 x2 p2 y _ _ _ th (TFunc z t_z t') _ _ den_g_th v den_thp1ta_v
  = den_thp1ta_v
lem_denote_push_ent_pred g _ a k _ x1 p1 x2 p2 y _ _ _ th (TPoly a' k' t') _ _ den_g_th v den_thp1ta_v
  = den_thp1ta_v

{-@ lem_denote_sound_sub_sbase_ftv :: g:Env -> a:Vname -> x1:RVname -> p1:Pred -> k1:Kind
        -> x2:RVname -> p2:Pred -> k2:Kind 
        -> ProofOf(Subtype g (TRefn (FTV a) x1 p1) (TRefn (FTV a) x2 p2)) -> ProofOf(WFEnv g)
        -> ProofOf(WFType g (TRefn (FTV a) x1 p1) k1) -> ProofOf(WFType g (TRefn (FTV a) x2 p2) k2)
        ->  th:CSub -> ProofOf(DenotesEnv g th) -> v:Value 
        -> ProofOf(Denotes (ctsubst th (TRefn (FTV a) x1 p1)) v)
        -> ProofOf(Denotes (ctsubst th (TRefn (FTV a) x2 p2)) v) @-}
lem_denote_sound_sub_sbase_ftv :: Env -> Vname -> RVname -> Expr -> Kind -> RVname -> Expr -> Kind
        -> Subtype -> WFEnv -> WFType -> WFType -> CSub -> DenotesEnv -> Expr -> Denotes -> Denotes 
lem_denote_sound_sub_sbase_ftv g a x1 p1_ k1 x2 p2_ k2 (SBase _ _ _ _ _ _ y pf_ent_p2) p_g_wf
                               p_g_t1 p_g_t2 th den_g_th v den_tht1_v_
  = lem_denote_push_ent_pred g p_er_g_wf a k1 p_g_er_a x1 p1 x2 p2 y pf_y_p1_bl pf_y_p2_bl 
                             pf_ent_p2 (th ? lem_binds_env_th g th den_g_th) 
                             (t_a ? lem_free_subset_binds Empty t_a k_a p_emp_ta) k_a p_emp_ta
                             den_g_th v den_tht1_v
                             ? lem_ctsubst_refn_tv th 
                                     (a ? lem_wfftvar_tv_in_csubst g a k1 p_g_er_a th den_g_th) 
                                     x2 p2_
      where
        p1            = p1_ ? lem_free_subset_binds g (TRefn (FTV a) x1 p1_) k1 p_g_t1
        p2            = p2_ ? lem_free_subset_binds g (TRefn (FTV a) x2 p2_) k2 p_g_t2
        p_er_g_wf     = lem_erase_env_wfenv g p_g_wf 
        p_g_er_a      = lem_erase_wftype g (TRefn (FTV a) x1 p1) k1 p_g_t1

        y'            = fresh_var g
        p_y'g_wf      = WFFBind (erase_env g) p_er_g_wf y' (FTBasic (FTV a)) k1 p_g_er_a
        pf_y'_p1_bl   = lem_ftyp_for_wf_trefn' g (FTV a) x1 p1 k1 p_g_t1 p_er_g_wf
        pf_y'_p2_bl   = lem_ftyp_for_wf_trefn' g (FTV a) x2 p2 k2 p_g_t2 p_er_g_wf
        pf_y_p1_bl    = lem_change_var_ftyp (erase_env g) y' (FTBasic (FTV a)) FEmpty p_y'g_wf
                                            (unbind 0 y' p1) (FTBasic TBool) pf_y'_p1_bl y
                                            ? lem_subFV_unbind 0 y' (FV y) p1
        pf_y_p2_bl    = lem_change_var_ftyp (erase_env g) y' (FTBasic (FTV a)) FEmpty p_y'g_wf
                                            (unbind 0 y' p2) (FTBasic TBool) pf_y'_p2_bl y
                                            ? lem_subFV_unbind 0 y' (FV y) p2

        k_a        = kind_for_tv a (g ? lem_free_subset_binds g (TRefn (FTV a) x1 p1) k1 p_g_t1)
        {-@ t_a :: { t':UserType | t' == csubst_tv th a } @-}
        (t_a, p_emp_ta) = get_wftype_from_denv g th den_g_th a k_a
        {-@ den_tht1_v :: ProofOf(Denotes (push (csubst th p1_) (csubst_tv th a)) v) @-}
        den_tht1_v = den_tht1_v_ ? lem_ctsubst_refn_tv th 
                                     (a ? lem_wfftvar_tv_in_csubst g a k1 p_g_er_a th den_g_th) 
                                     x1 p1_

{-@ lem_denote_sound_sub_sbase :: g:Env -> t1:Type -> k1:Kind -> t2:Type -> k2:Kind 
                -> { p_t1_t2:_ | propOf p_t1_t2 == Subtype g t1 t2 && isSBase p_t1_t2}
                -> ProofOf(WFEnv g) -> ProofOf(WFType g t1 k1) -> ProofOf(WFType g t2 k2) 
                ->  th:CSub 
                -> ProofOf(DenotesEnv g th) -> v:Value -> ProofOf(Denotes (ctsubst th t1) v) 
                -> ProofOf(Denotes (ctsubst th t2) v) / [subtypSize p_t1_t2,0] @-}
lem_denote_sound_sub_sbase :: Env -> Type -> Kind -> Type -> Kind -> Subtype -> WFEnv -> WFType -> WFType
                            -> CSub -> DenotesEnv -> Expr -> Denotes -> Denotes 
lem_denote_sound_sub_sbase g t1 k1 t2 k2 p_t1_t2@(SBase _g x1 b p1 x2 p2 y pf_ent_p2) p_g_wf p_g_t1 p_g_t2
                    -- t1 = b{x1:p1}, t2 = b{x2:p2}  -- Pf(Entails g' p2[y/x2])
                       th den_g_th val_ den_t1_v 
  = case b of 
      (FTV a) -> lem_denote_sound_sub_sbase_ftv g a x1 p1 k1 x2 p2 k2 p_t1_t2 p_g_wf
                                                p_g_t1 p_g_t2 th den_g_th val_ den_t1_v
      (BTV a) -> impossible ("by lemma" ? lem_btv_not_wf g a x1 p1 k1 p_g_t1)
      _       -> case den_t1_v of
        (DRefn b_ _ _ also_val pf_v_b pf_th_p1v_tt) -> case (pf_ent_p2) of   -- EvalsTo th(p1[v/x1]) tt
          (EntPred y_g _p2 ev_thp2_tt)     -- forall th' in [[x1,g]]. EvalsTo th'(p2[x1/x2]) tt 
            -> DRefn b x2 (csubst th p2) also_val pf_v_b' pf_th'_p2v_tt
                     `withProof` lem_ctsubst_refn th b x2 p2
                 where
                   val           = val_ ? lem_den_nofv val_ (ctsubst th t1) den_t1_v
                                        ? lem_den_nobv val_ (ctsubst th t1) den_t1_v
                   pf_v_b'       = pf_v_b `withProof`  lem_ctsubst_refn th b x1 p1 
                   den_g'_th'    = DExt g th den_g_th y t1 val den_t1_v
                   th'           = CCons y val (th ? lem_binds_env_th g th den_g_th) -- y is fresh repl. x1
                                         -- th' = (y |-> v, th) \in [[ Cons y t1 g ]]
                   pf_th'_p2v_tt = ev_thp2_tt th' den_g'_th' 
                                     `withProof` lem_csubst_and_unbind 0 y val (FTBasic b) pf_v_b' th p2
        (_) -> impossible ("by lemma" ? lem_ctsubst_refn th b x1 p1) 
