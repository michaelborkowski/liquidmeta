Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.Strengthenings.
Require Import SystemRF.LocalClosure.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.PrimitivesFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.BasicPropsWellFormedness.
Require Import SystemRF.SystemFLemmasWellFormedness.
Require Import SystemRF.Typing.
Require Import SystemRF.LemmasWellFormedness.
Require Import SystemRF.LemmasTyping.
Require Import SystemRF.LemmasWeakenWF.
Require Import SystemRF.SubstitutionLemmaWF.
Require Import SystemRF.LemmasWeakenTyp.
Require Import Denotations.ClosingSubstitutions.
Require Import Denotations.Denotations.
Require Import Denotations.PrimitivesSemantics.
Require Import Denotations.BasicPropsCSubst.
Require Import Denotations.BasicPropsDenotes.
Require Import Denotations.BasicPropsSemantics.
Require Import Denotations.LemmasWidening.
Require Import Denotations.EnvironmentSubstitutions.
Require Import Denotations.MultiSubstitutionLemmas.
Require Import Denotations.LemmasDenotesEnv.
Require Import Denotations.PrimitivesDenotations.
Require Import Denotations.SelfifyDenotations.

Require Import Arith.
Require Import ZArith.
Require Import Lists.ListSet.

(* Helper lemma requires its own induction *)

Lemma lem_den_subtype_lift_list : forall (g:env) (t1 t2:type) (th:csub) (v:expr),
    Subtype g t1 t2 -> DenotesEnv g th -> isValue v -> isList v
      -> (forall (v':expr), isValue v' 
            -> Denotes (ctsubst th t1) v' -> Denotes (ctsubst th t2) v')
      -> Denotes (TList (ctsubst th t1) PEmpty) v
      -> Denotes (TList (ctsubst th t2) PEmpty) v.
Proof. intros g t1 t2 th; induction v; intros;  
  simpl in H2; try contradiction.
  - (* v = Nil *) rewrite Denotes_equation_17; split;
    rewrite Denotes_equation_17 in H4; simpl in H4;
    destruct H4; simpl;
    try rewrite <- lem_erase_ctsubst with th t1 t2;
    try apply lem_erase_subtype with g;
    try apply lem_denotesenv_substitutable with g; trivial.
  - (* v = Cons v1 v2 *)
    rewrite Denotes_equation_18; repeat split; simpl;
    rewrite Denotes_equation_18 in H4; simpl in H4; 
    destruct H4 as [p_v1v2 [val1 [val2 [den_v1 [den_v2 ev_emp]]]]];
    try apply H3; try apply IHv2;
    try rewrite <- lem_erase_ctsubst with th t1 t2;
    try apply lem_erase_subtype with g;
    try apply lem_denotesenv_substitutable with g; trivial.
  Qed.     

Lemma lem_denote_sound : ( forall (g:env) (e:expr) (t:type),
    Hastype g e t -> forall (th:csub),
        WFEnv g -> DenotesEnv g th 
            -> EvalsDenotes (ctsubst th t) (csubst th e) ) /\ ((
  forall (g:env) (t1 t2:type),
    Subtype g t1 t2 -> forall (k1:kind) (k2:kind) (th:csub),
        WFEnv g -> WFtype g t1 k1 -> WFtype g t2 k2 -> DenotesEnv g th
            -> (forall (v:expr), isValue v
                -> Denotes (ctsubst th t1) v -> Denotes (ctsubst th t2) v) ) /\ (
  forall (g:env) (ps qs:preds),
    Implies g ps qs -> DImplies g ps qs)).  
Proof. apply ( judgments_mutind3
  (fun (g:env) (e:expr) (t:type) (p_e_t : Hastype g e t) =>
    forall (th:csub), WFEnv g -> DenotesEnv g th 
        -> EvalsDenotes (ctsubst th t) (csubst th e) )
  (fun (g:env) (t1 t2:type) (p_t1_t2 : Subtype g t1 t2) =>
    forall (k1 k2:kind) (th:csub),
      WFEnv g -> WFtype g t1 k1 -> WFtype g t2 k2 -> DenotesEnv g th
        -> (forall (v:expr), isValue v
              -> Denotes (ctsubst th t1) v -> Denotes (ctsubst th t2) v) )
  (fun (g:env) (ps qs:preds) (p_ps_qs : Implies g ps qs) => DImplies g ps qs));
  intros.
  - (* TBC *) rewrite lem_csubst_bc; rewrite lem_ctsubst_nofree;
    try apply lem_den_evalsdenotes; try apply lem_den_tybc;
    unfold tybc; simpl; reflexivity.
  - (* TIC *) rewrite lem_csubst_ic; rewrite lem_ctsubst_nofree;
    try apply lem_den_evalsdenotes; try apply lem_den_tyic;
    unfold tyic; simpl; reflexivity.
  - (* TVar *) unfold EvalsDenotes; exists (csubst th (FV x));
    repeat split; try apply Refl;
    try apply lem_denotes_ctsubst_self;
    try apply lem_denotations_selfify;
    try apply lem_den_hasftype;
    try apply lem_bound_in_denotesenv with g;
    try apply lem_csubst_value;
    try apply lem_ctsubst_wf with g;
    try apply lem_denotesenv_closed with g;
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g;
    try apply lem_denotesenv_uniqueC with g;
    try apply wfenv_unique; try apply val_FV;
    unfold isLC; simpl; trivial.
  - (* TPrm *) rewrite lem_csubst_prim; unfold EvalsDenotes;
    exists (Prim c); repeat split; try apply Refl; try apply val_Prm.
    apply lem_den_ty with g; apply H0.
  - (* TAbs *) rewrite lem_csubst_lambda; rewrite lem_ctsubst_func;
    unfold EvalsDenotes; exists (Lambda (csubst th e));
    split; try split; try apply Refl; 
    try rewrite Denotes_equation_2; repeat split; try apply val_Lam.
    * rewrite <- lem_csubst_lambda; rewrite <- lem_ctsubst_func;
      apply lem_csubst_hasftype with g;
      try apply lem_typing_hasftype; try apply TAbs with k_x nms;
      try apply lem_erase_env_wfenv; try apply wfenv_unique; trivial.
    * intros; pose proof (fresh_var_not_elem nms g) as Hy; 
      set (y := fresh_var nms g) in Hy; destruct Hy as [Hy Hyg]; 
      apply H with y (CCons y v_x th) in Hy;
      try apply WFEBind with k_x; try apply DExt; trivial.
      unfold EvalsDenotes in Hy; destruct Hy as [v' Hy];
      destruct Hy; simpl in H5; destruct H5;
      rewrite <- lem_subFV_unbind in H5;
      rewrite <- lem_tsubFV_unbindT in H6;
      assert (Hastype g (Lambda e) (TFunc t_x t)) as Het
        by (apply TAbs with k_x nms; trivial);
      apply lem_typing_wf in Het as Ht; try apply H0;
      apply lem_fv_subset_binds in Het; try apply H0;
      apply lem_free_subset_binds in Ht; 
      destruct Het; destruct Ht; simpl in H7; simpl in H9;
      assert (Subset (free t) (union (free t_x) (free t)))
        by apply subset_union_intro_r;
      pose proof (vbinds_subset g);
      try apply not_elem_subset with (vbinds g);
      try apply not_elem_subset with (binds g); trivial; 
      try apply subset_trans with (union (free t_x) (free t)); trivial.
      exists v'; repeat split; try apply H4;
      try apply AddStep with (csubst th (subBV v_x e)); 
      try apply H5; try rewrite lem_csubst_subBV;
      try rewrite lem_csubst_nofv with th v_x; try apply EAppAbs;
      try apply lem_den_nofv in H3 as Hvx; destruct Hvx;
      try rewrite lem_ctsubst_tsubBV in H6;
      try rewrite lem_csubst_nofv with th v_x in H6;
      try apply lem_denotesenv_loc_closed with g;
      try apply lem_denotesenv_substitutable with g; 
      trivial.
  - (* TApp *) rewrite lem_csubst_app; rewrite lem_ctsubst_exis;
    unfold EvalsDenotes; apply H in H2 as den_thtxt_the;
    apply H0 in H2 as den_thtx_the'; try apply H1;
    unfold EvalsDenotes in den_thtx_the'; 
    unfold EvalsDenotes in den_thtxt_the; 
    destruct den_thtx_the' as [v_x Hvx]; destruct Hvx; 
    destruct H4 as [ev_the'_vx den_thtx_vx];
    destruct den_thtxt_the as [v Hv]; destruct Hv;
    destruct H5 as [ev_the_v den_thtxt_v];
    rewrite lem_ctsubst_func in den_thtxt_v;
    rewrite Denotes_equation_2 in den_thtxt_v;
    destruct den_thtxt_v as [_ Hv];
    destruct Hv as [p_v_thtxt den_func];
    apply den_func in den_thtx_vx as Hv'; try apply H3;
    destruct Hv' as [v' [Hv' [ev_vvx_v' den_v']]];
    exists v'; split; try split; try apply Hv';
    try apply lemma_evals_trans with (App v v_x);
    try apply lemma_app_both_many; trivial.
    rewrite Denotes_equation_3; repeat split;
    apply lem_den_hasftype in den_v' as p_v'_tvx;
    rewrite lem_erase_tsubBV in p_v'_tvx; simpl; trivial.
    exists v_x; split; try split; trivial.
  - (* TAbsT *) rewrite lem_csubst_lambdaT; rewrite lem_ctsubst_poly;
    unfold EvalsDenotes; exists (LambdaT k (csubst th e));
    split; try split; try apply Refl;
    try rewrite Denotes_equation_4; repeat split; try apply val_LamT.
    * rewrite <- lem_csubst_lambdaT; rewrite <- lem_ctsubst_poly;
      apply lem_csubst_hasftype with g;
      try apply lem_typing_hasftype; try apply TAbsT with nms;
      try apply lem_erase_env_wfenv; try apply wfenv_unique; trivial.
    * intros; pose proof (fresh_var_not_elem nms g) as Ha; 
      set (a := fresh_var nms g) in Ha; destruct Ha as [Ha Ha'];
      apply H with a (CConsT a t_a th) in Ha;
      try apply WFEBindT; try apply DExtT; trivial.
      unfold EvalsDenotes in Ha; destruct Ha as [v' [Hv' [ev_the_v' den_v']]];
      simpl in ev_the_v'; rewrite <- lem_subFTV_unbind_tv in ev_the_v';
      simpl in den_v'; rewrite <- lem_tsubFTV_unbind_tvT in den_v';
      assert (Hastype g (LambdaT k e) (TPoly k t)) as Het
        by (apply TAbsT with nms; trivial);
      apply lem_typing_wf in Het as Ht; try apply H0;
      apply lem_fv_subset_binds in Het; try apply H0;
      apply lem_free_subset_binds in Ht; 
      destruct Het; destruct Ht; simpl in H5; simpl in H7;
      pose proof (tvbinds_subset g);
      try apply not_elem_subset with (tvbinds g);
      try apply not_elem_subset with (binds g); trivial.
      exists v'; repeat split; try apply Hv';
      try apply AddStep with (csubst th (subBTV t_a e)); 
      try apply ev_the_v'; try rewrite lem_csubst_subBTV;
      try rewrite lem_ctsubst_nofree with th t_a; try apply EAppTAbs;
      try apply lem_free_subset_binds in H3; simpl in H3; destruct H3;
      try rewrite lem_ctsubst_tsubBTV in den_v';
      try rewrite lem_ctsubst_nofree with th t_a in den_v';
      try apply lem_denotesenv_loc_closed with g;
      try apply lem_denotesenv_substitutable with g; 
      try apply no_elem_empty; trivial. 
  - (* TAppT *) rewrite lem_csubst_appT; rewrite lem_ctsubst_tsubBTV;
    unfold EvalsDenotes; apply H in H1 as den_thks_the;
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g; trivial;
    unfold EvalsDenotes in den_thks_the.
    destruct den_thks_the as [v' [Hv' [ev_the_v' den_v']]].
    rewrite lem_ctsubst_poly in den_v';
    rewrite Denotes_equation_4 in den_v';
    destruct den_v' as [_ [p_v'_ks den_func]].
    assert (WFtype Empty (ctsubst th t) k) as p_tht
      by (apply lem_ctsubst_wf with g; 
          try apply wfenv_unique; trivial);
    apply den_func in p_tht as Htht;
    try apply lem_ctsubst_isMono;
    try apply lem_ctsubst_noExists; 
    try apply lem_denotesenv_substitutable with g; trivial.
    destruct Htht as [v'' [Hv'' [ev_thet_v'' den_v'']]];
    exists v''; split; try split; try apply Hv'';
    try apply lemma_evals_trans with (AppT v' (ctsubst th t));
    try apply lemma_appT_many; 
    try apply lem_ctsubst_noExists;
    try apply lem_denotesenv_substitutable with g; trivial.
  - (* TLet *) rewrite lem_csubst_let; 
    unfold EvalsDenotes in H; apply H in H2 as Hvx; try apply H1;
    destruct Hvx as [v_x [Hvx [ev_thex_vx den_thtx_vx]]].
    pose proof (fresh_var_not_elem nms g) as Hy; 
    set (y := fresh_var nms g) in Hy; destruct Hy as [Hy Hyg].
    apply H0 with y (CCons y v_x th) in Hy;
    apply lem_typing_wf in h as p_tx;
    try apply WFEBind with Star; try apply DExt; trivial.
    unfold EvalsDenotes in Hy; 
    destruct Hy as [v' [Hy [ev_thvxe_v' den_thvxt_v']]];
    simpl in ev_thvxe_v'; simpl in den_thvxt_v';
    rewrite <- lem_subFV_unbind in ev_thvxe_v';
    rewrite <- lem_tsubFV_unbindT in den_thvxt_v';
    try rewrite lem_ctsubst_tsubBV in den_thvxt_v';
    try rewrite lem_csubst_nofv in den_thvxt_v';
    try rewrite lem_tsubBV_lct in den_thvxt_v';
    try apply lem_ctsubst_isLCT;
    try apply lem_wftype_islct with g k;
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g;
    try apply lem_den_nofv in den_thtx_vx; destruct den_thtx_vx;
    assert (Hastype g (Let e_x e) t) as Het
      by (apply TLet with t_x k nms; trivial);
    apply lem_fv_subset_binds in Het;
    apply lem_free_subset_binds in w as Ht; try apply H1;
    destruct Het; destruct Ht; simpl in H5;     
    assert (Subset (fv e) (union (fv e_x) (fv e)))
      by apply subset_union_intro_r;
    pose proof (vbinds_subset g);
    try apply not_elem_subset with (vbinds g);
    try apply not_elem_subset with (binds g); trivial;
    try apply subset_trans with (union (fv e_x) (fv e)); trivial.
    unfold EvalsDenotes;
    try exists v'; try repeat split; try assumption.         
    apply lemma_evals_trans with (Let v_x (csubst th e));
    try apply lemma_let_many; try apply ev_thex_vx.
    try apply AddStep with (csubst th (subBV v_x e));
    try apply ev_thvxe_v'; rewrite lem_csubst_subBV;
    try rewrite lem_csubst_nofv with th v_x; try apply ELetV;
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g; trivial.
  - (* TAnn *) rewrite lem_csubst_annot; unfold EvalsDenotes;
    apply H in H1 as Hthe; try apply H0;
    unfold EvalsDenotes in Hthe; 
    destruct Hthe as [v [Hv [ev_the_v den_tht_v]]].
    exists v; repeat split; try assumption.
    apply lemma_evals_trans with (Annot v (ctsubst th t));
    try apply lemma_annot_many; try apply ev_the_v.
    apply lem_step_evals; apply EAnnV; apply Hv.
  - (* TIf *) rewrite lem_csubst_if;
    try apply lem_typing_wf in h as p_ps; 
    try inversion p_ps; try subst g0 t0;
    apply H in H3 as Hv0; try apply H2;
    unfold EvalsDenotes in Hv0;
    destruct Hv0 as [v0 [Hv0 [ev_the0_v0 den_v0]]];
    rewrite lem_ctsubst_refn in den_v0; simpl; auto;
    rewrite Denotes_equation_1 in den_v0; simpl in den_v0;
    destruct den_v0 as [_ [p_v0_bl pev_psv0]].
    apply (lem_bool_values v0 Hv0) in p_v0_bl as Hb;
    destruct v0; simpl in Hb; try contradiction;
    destruct b.
    * (* True *) 
      pose proof (fresh_varE_not_elem nms g e1) as Hy; 
      set (y := fresh_varE nms g e1) in Hy; 
      destruct Hy as [Hye1 [_ [Hy Hyg]]];
      apply H0 with y (CCons y (Bc true) th) in Hy as He1;
      try apply WFEBind with Base; 
      try apply lem_selfify_wf;
      try apply DExt;
      try apply lem_denotes_ctsubst_self;
      try rewrite lem_csubst_bc;
      try apply lem_denotations_selfify;
      try apply lem_ctsubst_wf with g;
      try rewrite lem_ctsubst_refn; simpl;
      try rewrite Denotes_equation_1;
      try apply FTBC;
      try apply lem_denotesenv_closed with g;
      try apply lem_denotesenv_loc_closed with g;
      try apply lem_denotesenv_substitutable with g;
      try apply lem_denotesenv_uniqueC with g;
      try apply wfenv_unique; auto. 
      unfold EvalsDenotes; unfold EvalsDenotes in He1;
      destruct He1 as [v [Hv [ev_th'e1_v den_th't_v]]];
      exists v; repeat split; try apply Hv;
      try apply lemma_evals_trans 
          with (If (Bc true) (csubst th e1) (csubst th e2));
      try apply lemma_if_many; try apply ev_the0_v0;
      try apply AddStep with (csubst th e1); try apply EIfT;
      simpl in ev_th'e1_v; rewrite lem_subFV_notin' in ev_th'e1_v;
      simpl in den_th't_v; rewrite lem_tsubFV_notin in den_th't_v;
      apply lem_free_subset_binds in w; destruct w; 
      pose proof vbinds_subset; trivial;
      apply not_elem_subset with (vbinds g);
      try apply not_elem_subset with (binds g); trivial.      
    * (* False *) 
      pose proof (fresh_varE_not_elem nms g e2) as Hy; 
      set (y := fresh_varE nms g e2) in Hy; 
      destruct Hy as [Hye2 [_ [Hy Hyg]]];
      apply H1 with y (CCons y (Bc false) th) in Hy as He2;
      try apply WFEBind with Base; 
      try apply lem_selfify_wf; 
      try apply DExt; 
      try apply lem_denotes_ctsubst_self;
      try rewrite lem_csubst_bc;
      try apply lem_denotations_selfify;
      try apply lem_ctsubst_wf with g;
      try rewrite lem_ctsubst_refn; simpl;
      try rewrite Denotes_equation_1;
      try apply FTBC;
      try apply lem_denotesenv_closed with g;
      try apply lem_denotesenv_loc_closed with g;
      try apply lem_denotesenv_substitutable with g;
      try apply lem_denotesenv_uniqueC with g;
      try apply wfenv_unique; auto. 
      unfold EvalsDenotes; unfold EvalsDenotes in He2;
      destruct He2 as [v [Hv [ev_th'e2_v den_th't_v]]];
      exists v; repeat split; try apply Hv;
      try apply lemma_evals_trans 
          with (If (Bc false) (csubst th e1) (csubst th e2));
      try apply lemma_if_many; try apply ev_the0_v0;
      try apply AddStep with (csubst th e2); try apply EIfF;
      simpl in ev_th'e2_v; rewrite lem_subFV_notin' in ev_th'e2_v;
      simpl in den_th't_v; rewrite lem_tsubFV_notin in den_th't_v;
      apply lem_free_subset_binds in w; destruct w; 
      pose proof vbinds_subset; trivial;
      apply not_elem_subset with (vbinds g);
      try apply not_elem_subset with (binds g); trivial.
  - (* TNil *) rewrite lem_csubst_nil; rewrite lem_ctsubst_list;
    apply lem_den_evalsdenotes;
    try rewrite Denotes_equation_17; repeat split; simpl;
    try apply FTNil with k; apply lem_wftype_islct in w as Hlct;
    apply lem_ctsubst_wf with g t k th in w;
    try apply lem_erase_wftype in w as p_emp_tht; 
    try rewrite lem_cpsubst_pcons;
    try rewrite lem_cpsubst_pempty;
    try rewrite <- lem_csubst_nil with th;
    unfold psubBV; (*unfold eq; unfold length;*)
    try apply PECons; try apply PEEmp; fold subBV_at; 
    try rewrite <- lem_csubst_subBV; unfold subBV; simpl;
    try rewrite <- lem_csubst_bc with th true;
    try apply lem_csubst_evals;
    pose proof lem_subBV_at_lc_at as [_ [Hsubt _]];
    try rewrite Hsubt with t 0 Nil 0 0;
    try apply lemma_semantics_refn_length_nil;
    try apply wfenv_unique;
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g;
    trivial.
  - (* TCons *) rewrite lem_csubst_cons; rewrite lem_ctsubst_exis;
    apply H in H2 as HvH; try apply H0 in H2 as HvT; try apply H1;
    apply lem_typing_wf in h as p_g_t;
    try apply lem_wftype_islct in p_g_t as Hlct; try apply H1.
    unfold EvalsDenotes in HvH; unfold EvalsDenotes in HvT;
    destruct HvH as [vH [val1 [ev_theH_vH HvH]]];
    destruct HvT as [vT [val2 [ev_theT_vT HvT]]];
    unfold EvalsDenotes; exists (Cons vH vT); split; try split;
    try rewrite Denotes_equation_3; try split; try split;
    try apply val_Cons; try apply lemma_cons_both_many; trivial;
    simpl; try (rewrite lem_ctsubst_list; apply FTCons);
    try apply lem_den_hasftype in HvH as p_vH;
    try apply lem_den_hasftype in HvT as p_vT; 
    rewrite lem_ctsubst_list in p_vT; simpl in p_vT; 
    apply lem_ftyp_islc in p_vT as HlcvT; trivial.
    exists vT; split; try split; trivial;
    try rewrite <- (lem_csubst_nofv th vT) at 1;
    try rewrite <- lem_ctsubst_tsubBV; unfold tsubBV; simpl;
    pose proof lem_subBV_at_lc_at as [Hsube [Hsubt _]];
    try rewrite Hsubt with t 0 vT 0 0;
    try rewrite Hsubt with t 1 vT 0 0;
    try rewrite lem_ctsubst_list;

    try rewrite Denotes_equation_18; try repeat split; simpl;
    try apply FTCons;
    try rewrite <- (lem_csubst_nofv th (Cons vH vT));
    try rewrite <- lem_cpsubst_psubBV; unfold psubBV; simpl;
    try rewrite Hsube with vT 0 (Cons vH vT) 0 0;
    try rewrite Hsubt with t  0 (Cons vH vT) 0 0;
    try rewrite lem_cpsubst_pcons; try apply PECons;
    try rewrite lem_cpsubst_pempty; try apply PEEmp;
    try rewrite <- lem_csubst_bc with th true;
    try apply lem_csubst_evals;
    try apply lemma_semantics_refn_length_cons;
    try apply lem_denotes_list_pempty with (cpsubst th ps);
    rewrite lem_ctsubst_list in HvT; 
    try apply lem_den_list with (erase (ctsubst th t)) in HvT as lst;
    try apply lem_den_lists 
      with (TList (ctsubst th t) (cpsubst th ps)) (ctsubst th t) vT 
      in HvT as lst;
    
    try apply lem_fv_subset_bindsF in p_vH as Hfv;  simpl in Hfv;
    try apply lem_fv_subset_bindsF in p_vT as Hfv'; simpl in Hfv';
    destruct Hfv; destruct Hfv'; try apply no_elem_empty;
    intros; try apply not_elem_union_intro; try revert x;
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g;
    try apply val_Cons; simpl; auto.
  - (* TSwitch *) assert (Hastype g (Switch e eN eC) t' ) 
      as p_swt_t' by (apply TSwit with t ps k nms; trivial);  
    apply lem_free_subset_binds in w as Hfr_t';
    destruct Hfr_t' as [Hfr_t' _];
    apply lem_fv_subset_binds in p_swt_t' as Hfv_sw; try apply H2;
    simpl in Hfv_sw; destruct Hfv_sw as [Hfv_sw _];
    apply subset_union_elim_l in Hfv_sw; destruct Hfv_sw as [Hfv_e Hfv_sw];
    apply subset_union_elim_l in Hfv_sw; destruct Hfv_sw as [Hfv_eN Hfv_eC];
    pose proof (vbinds_subset g) as Hg.
    rewrite lem_csubst_switch. 
    pose proof (fresh_var_not_elem nms g) as Hy; 
    set (y:=fresh_var nms g) in Hy;
    pose proof (fresh_var_excluding_not_elem nms g y) as Hz;
    set (z := fresh_var_excluding nms g y) in Hz;
    destruct Hy as [Hy Hy'];
    destruct Hz as [Hzy [Hz Hz']].
    (* th(e) ~>* v \in [[th([t]{ps})]] *)
    apply H in H3 as evden_e; try apply H2.
    unfold EvalsDenotes in evden_e;
    destruct evden_e as [v [val [ev_the_v den_thtps_v]]];
    rewrite lem_ctsubst_list in den_thtps_v.
    apply lem_den_lists with (TList (ctsubst th t) (cpsubst th ps)) (ctsubst th t) v 
      in den_thtps_v as lst_v; trivial.
    destruct v eqn:V; simpl in lst_v; try contradiction.
    * (* th(e) ~>* v = Nil *)
      apply H0 with y (CCons y Nil th) in Hy as evden_eN;
      try apply DExt; try rewrite lem_ctsubst_list;
      try apply lem_den_len_zero_nil;
      try apply WFEBind with Star;
      try apply lem_wflist_len_zero; try apply lem_typing_wf with e;
      try apply lem_denotesenv_loc_closed with g;
      try apply lem_denotesenv_substitutable with g; trivial.
      (* By the IH, (y:Nil,th)(eN) ~>* vN *)
      unfold EvalsDenotes in evden_eN;
      destruct evden_eN as [vN [valN [ev_ytheN_vN den_ytht'_vN]]];
      simpl in ev_ytheN_vN; rewrite lem_subFV_notin' in ev_ytheN_vN;
      try apply not_elem_subset with (vbinds g); 
      try apply not_elem_subset with (binds g); trivial;
      unfold EvalsDenotes; exists vN; split; try split; trivial.
      (* th(Switch e eN eC) ~>* vN *)
      apply lemma_evals_trans with (Switch Nil (csubst th eN) (csubst th eC));
      try apply lemma_switch_many; try apply ev_the_v;
      try apply AddStep with (csubst th eN); 
      try apply ESwitchN; apply ev_ytheN_vN.
      (* vN \in [[ th(t') ]] *)
      simpl in den_ytht'_vN; rewrite lem_tsubFV_notin in den_ytht'_vN;
      try apply not_elem_subset with (vbinds g); 
      try apply not_elem_subset with (binds g); trivial.
    * (* th(e) ~>* v = Cons v1 v2 *)
      set (v1 := e0_1) in *; set (v2 := e0_2) in *.
      apply H1 with y z (CCons z (Cons v1 v2) (CCons y v2 th))
               in Hy as evden_eC;
      try repeat apply WFEBind with Star;
      try repeat apply DExt; 
      unfold in_env; try apply not_elem_names_add_intro; try split;
      try apply lem_wflist_len_succ;
      try apply lem_typing_wf in h as p_g_tps;
      try apply lem_wflist_wftype in p_g_tps as p_g_t;
      try apply WFList with Star;
      try rewrite lem_ctsubst_list; trivial;
      apply lem_free_subset_binds in p_g_t as Hfr_t;
      destruct Hfr_t as [Hfr_t _];
      try apply lem_den_len_succ_cons; try apply den_thtps_v;
      try rewrite Denotes_equation_18 in den_thtps_v;
      destruct den_thtps_v as [p_v1v2 [val1 [val2 [den_tht_v1 [den_thts_v2 ev_psv1v2]]]]];
      try rewrite lem_cpsubst_pempty;
      try apply lem_ftyp_islc in p_v1v2 as v1v2_lc; 
      simpl in v1v2_lc; destruct v1v2_lc;
      try apply lem_fv_subset_bindsF in p_v1v2;
      simpl in p_v1v2; destruct p_v1v2 as [Hfv1 Hfv2];
      apply subset_union_elim_l in Hfv1; destruct Hfv1;
      apply subset_union_elim_l in Hfv2; destruct Hfv2;
      try apply no_elem_empty;
      try apply (lem_ctsubst_wf g (TList t ps) Star th) in p_g_tps as p_thtps;
      try rewrite lem_ctsubst_list in p_thtps;
      try apply lem_free_subset_binds in p_thtps; 
      try simpl in p_thtps; try destruct p_thtps as [Hfree _];
      try apply subset_union_elim_l in Hfree; try destruct Hfree;
      unfold in_csubst; try rewrite <- lem_binds_env_th with g th;
      try apply lem_denotesenv_loc_closed with g;
      try apply lem_denotesenv_closed with g;
      try apply lem_denotesenv_substitutable with g;
      try apply wfenv_unique; trivial.
      (* By the IH, (z:(v1:v2),y:v2,th)(eC) ~>* vC *)
      unfold EvalsDenotes in evden_eC;
      destruct evden_eC as [vC [valC [ev_theC_vC den_tht'_vC]]];
      simpl in ev_theC_vC;
      rewrite lem_subFV_notin' in ev_theC_vC;
      try rewrite lem_subFV_notin' in ev_theC_vC;
      try rewrite lem_subFV_notin';
      try apply not_elem_subset with (vbinds g); 
      try apply not_elem_subset with (binds g); trivial.
      (* ((vC v1) v2) ~>* some v'' value *)
      repeat rewrite lem_ctsubst_func in den_tht'_vC;
      rewrite lem_ctsubst_list in den_tht'_vC.
      unfold ctsubst in den_tht'_vC; fold ctsubst in den_tht'_vC;      
      unfold cpsubst in den_tht'_vC; fold cpsubst in den_tht'_vC;      
      unfold psubFV in den_tht'_vC;        
      unfold eq in den_tht'_vC;      unfold length in den_tht'_vC;
      fold subFV in den_tht'_vC;     fold tsubFV in den_tht'_vC.
      assert (y =? y = true) as Hyy by (apply Nat.eqb_eq; trivial);
      assert (z =? y = false) as Hyz by (apply Nat.eqb_neq; trivial);
      rewrite Hyz in den_tht'_vC; unfold subFV in den_tht'_vC;
      rewrite Hyy in den_tht'_vC;
      rewrite lem_tsubFV_notin in den_tht'_vC;
      try rewrite lem_tsubFV_notin in den_tht'_vC;
      try rewrite lem_tsubFV_notin in den_tht'_vC;
      try rewrite lem_tsubFV_notin in den_tht'_vC;
      try rewrite lem_tsubFV_notin;
      try apply not_elem_subset with (vbinds g); 
      try apply not_elem_subset with (binds g); trivial.
      rewrite Denotes_equation_2 in den_tht'_vC.
      destruct den_tht'_vC as [_ [p_vC mk_evden_vCvx]].
      apply mk_evden_vCvx in den_tht_v1 as evden_vCv1; try apply val1; 
      destruct evden_vCv1 as [v' [val' [ev_vCv1_v den_v']]].
      unfold tsubBV in den_v';  unfold tsubBV_at in den_v';
      fold tsubBV_at in den_v'; fold psubBV_at in den_v'.
      rewrite lem_tsubBV_lct in den_v';
      pose proof lem_subBV_at_lc_at as [_ [HtsubBV HpsubBV]];
      rewrite HtsubBV with (ctsubst th t') (0+1) v1 0 0 in den_v';
      rewrite HpsubBV 
        with (cpsubst th (PCons (App (App (Prim Eq) (App (AppT (Prim Length) t) v2)) 
                                     (App (AppT (Prim Length) t) (BV 0))) PEmpty))
             (0+1) v1 1 0 in den_v';
      try apply lem_ctsubst_isLCT;     
      try apply lem_cpsubst_isLCP_at;
      simpl; try repeat split; 
      try apply lem_islc_at_weaken with 0 0;
      try apply lem_wftype_islct in p_g_t as Hlct;
      try apply lem_wftype_islct in w as Hlct';
      try apply lem_denotesenv_loc_closed with g;
      try apply lem_denotesenv_substitutable with g; auto;

      rewrite Denotes_equation_2 in den_v';
      destruct den_v' as [_ [p_v' mk_evden_v'vx]];
      apply mk_evden_v'vx in val2 as mk_evden_v'v2;
      try apply lem_den_eqlLenPred; 
      try destruct mk_evden_v'v2 as [v'' [val'' [ev_v'v2_v'' den_v'']]];
      try rewrite lem_tsubBV_lct in den_v'';   
      try apply lem_ctsubst_isLCT; 
      try apply lem_denotesenv_loc_closed with g;
      try apply lem_denotesenv_substitutable with g; trivial.
      
      (* th(Switch e eN eC) ~>* v'' *)
      unfold EvalsDenotes; exists v''; split; try split; trivial.
      apply lemma_evals_trans 
        with (Switch (Cons v1 v2) (csubst th eN) (csubst th eC));
      try apply lemma_switch_many; try apply ev_the_v;
      try apply AddStep with (App (App (csubst th eC) v1) v2); 
      try apply ESwitchC; 
      try apply lemma_evals_trans with (App (App vC v1) v2);
      try apply lemma_app_many; try apply lemma_app_many;
      try apply ev_theC_vC;
      try apply lemma_evals_trans with (App v' v2);
      try apply lemma_app_many; try apply ev_vCv1_v;
      try apply ev_v'v2_v''; trivial.
      (* v'' \in [[ th(t') ]]  handled above? *)  
  - (* TSub *) unfold EvalsDenotes; apply H in H2 as H'; 
    try apply H1; try unfold EvalsDenotes in H';
    destruct H' as [v [Hv [ev_the_v den_ths_v]]];
    exists v; repeat split; try apply H0 with Star k;
    try apply lem_typing_wf with e; trivial.

  - (* SBase *) destruct b eqn:B.
    * (* TBool *) rewrite lem_ctsubst_refn; 
      try rewrite Denotes_equation_1;
      rewrite lem_ctsubst_refn in H5;
      try rewrite Denotes_equation_1 in H5; 
      simpl in H5; simpl; intuition.
      pose proof (fresh_var_not_elem nms g) as Hy; 
      set (y := fresh_var nms g) in Hy; destruct Hy as [Hy Hyg].
      apply H in Hy as IH; inversion IH.
      assert (Denotes (TRefn TBool PEmpty) v).
        rewrite Denotes_equation_1; unfold psubBV;
        simpl; repeat split; try apply PEEmp; trivial.
      assert (DenotesEnv (ECons y (TRefn TBool PEmpty) g) (CCons y v th)).
        apply DExt; try rewrite lem_ctsubst_refn; 
        try rewrite lem_cpsubst_pempty; simpl; auto. 
      apply lem_den_nofv in H12 as Hv; destruct Hv.
      assert (v = csubst th v)
        by (symmetry; apply lem_csubst_nofv; trivial).
      rewrite H16; rewrite <- lem_cpsubst_psubBV;
      try rewrite lem_psubFV_unbindP with y v p2;
      pose proof (H7 (CCons y v th) H13) as H'; 
      simpl in H'; try apply H';
      try rewrite <- lem_psubFV_unbindP;
      try rewrite lem_cpsubst_psubBV; try rewrite <- H16;
      apply lem_free_subset_binds in H1; simpl in H1;
      apply lem_free_subset_binds in H2; simpl in H2;
      destruct H1; destruct H2;
      try apply not_elem_subset with (vbinds g);
      try apply not_elem_subset with (binds g);
      pose proof vbinds_subset;
      try apply lem_denotesenv_loc_closed with g;
      try apply lem_denotesenv_substitutable with g;
      trivial.
    * (* TInt *) rewrite lem_ctsubst_refn; 
      try rewrite Denotes_equation_1;
      rewrite lem_ctsubst_refn in H5;
      try rewrite Denotes_equation_1 in H5; 
      simpl in H5; simpl; intuition.
      pose proof (fresh_var_not_elem nms g) as Hy; 
      set (y := fresh_var nms g) in Hy; destruct Hy as [Hy Hyg].
      apply H in Hy as IH; inversion IH.
      assert (Denotes (TRefn TInt PEmpty) v).
        rewrite Denotes_equation_1; unfold psubBV;
        simpl; repeat split; try apply PEEmp; trivial.
      assert (DenotesEnv (ECons y (TRefn TInt PEmpty) g) (CCons y v th)).
        apply DExt; try rewrite lem_ctsubst_refn; 
        try rewrite lem_cpsubst_pempty; simpl; auto. 
      apply lem_den_nofv in H12 as Hv; destruct Hv.
      assert (v = csubst th v)
        by (symmetry; apply lem_csubst_nofv; trivial).
      rewrite H16; rewrite <- lem_cpsubst_psubBV;
      try rewrite lem_psubFV_unbindP with y v p2;
      pose proof (H7 (CCons y v th) H13) as H'; 
      simpl in H'; try apply H';
      try rewrite <- lem_psubFV_unbindP;
      try rewrite lem_cpsubst_psubBV; try rewrite <- H16;
      apply lem_free_subset_binds in H1; simpl in H1;
      apply lem_free_subset_binds in H2; simpl in H2;
      destruct H1; destruct H2;
      try apply not_elem_subset with (vbinds g);
      try apply not_elem_subset with (binds g);
      pose proof vbinds_subset;
      try apply lem_denotesenv_loc_closed with g;
      try apply lem_denotesenv_substitutable with g;
      trivial.
    * (* BTV *) inversion H1; try simpl in H10; 
      try inversion H8; try simpl in H15;
      try inversion H6; try inversion H13; try contradiction.
    * (* FTV *)
      apply lem_free_subset_binds in H1 as Ha; simpl in Ha;
      destruct Ha as [Hfv1 Ha].
      assert (Elem a (tvbinds g))
        by (apply Ha; apply set_add_intro2; reflexivity).
      apply lem_tvbinds_denotesenv with a g th in H6 as H';
      try destruct H' as [t_a [Hta' [p_ta Hta]]];
      try rewrite lem_ctsubst_refn_tv with th a t_a p1 in H5;
      try rewrite lem_ctsubst_refn_tv with th a t_a p2;
      try apply lem_denotesenv_closed with g;
      try apply lem_denotesenv_substitutable with g;
      try apply lem_denotesenv_uniqueC with g; trivial.
      (* WTS: Denotes (push (cpsubst th p1) t_a) v
           -> Denotes (push (cpsubst th p2) t_a) v*)
      destruct t_a eqn:TA; simpl in Hta'; try contradiction;
      simpl; simpl in H5; try apply H5. 
      (* the case that remains: t_a is b0{ps}.
        WTS: Denotes (TRefn b0 (strengthen (cpsubst th p1) ps)) v
          -> Denotes (TRefn b0 (strengthen (cpsubst th p2) ps)) v*)
      rewrite Denotes_equation_1; rewrite Denotes_equation_1 in H5.
      simpl in H5; destruct H5 as [_ [p_v_b0 ev_p1]];
      simpl; repeat split; try assumption;
      rewrite lem_psubBV_strengthen;
      rewrite lem_psubBV_strengthen in ev_p1.
      apply lemma_strengthen_semantics;
      apply lemma_semantics_strengthen in ev_p1; 
      destruct ev_p1 as [ev_p1 ev_ps]; try apply ev_ps.

      pose proof (fresh_var_not_elem nms g) as Hy; 
      set (y := fresh_var nms g) in Hy; destruct Hy as [Hy Hyg].
      apply H in Hy as IH; inversion IH.

      assert (Denotes (TRefn b0 ps) v).
        rewrite Denotes_equation_1; unfold psubBV;
        simpl; repeat split; try apply PEEmp; trivial.
      assert (DenotesEnv (ECons y (TRefn (FTV a) PEmpty) g) (CCons y v th)).
        apply DExt; try rewrite lem_ctsubst_refn_tv with th a t_a PEmpty;
        try rewrite lem_cpsubst_pempty; subst t_a;
        try rewrite lem_push_empty;
        try apply lem_denotesenv_closed with g;
        try apply lem_denotesenv_substitutable with g;
        try apply lem_denotesenv_uniqueC with g;
        trivial.
      apply lem_fv_subset_bindsF in p_v_b0; destruct p_v_b0;
      simpl in H12; simpl in H13.
      assert (v = csubst th v)
        by (symmetry; apply lem_csubst_nofv; 
            apply no_elem_empty; trivial).
      rewrite H14; rewrite <- lem_cpsubst_psubBV;
      try rewrite lem_psubFV_unbindP with y v p2;
      pose proof (H5 (CCons y v th) H11) as H';
      simpl in H'; try apply H';
      try rewrite <- lem_psubFV_unbindP;
      try rewrite lem_cpsubst_psubBV; try rewrite <- H14;
      apply lem_free_subset_binds in H1; simpl in H1;
      apply lem_free_subset_binds in H2; simpl in H2;
      destruct H1; destruct H2;
      try apply not_elem_subset with (vbinds g);
      try apply not_elem_subset with (binds g);
      pose proof vbinds_subset;
      try apply lem_denotesenv_loc_closed with g;
      try apply lem_denotesenv_substitutable with g;
      trivial.
  - (* SFunc *) inversion H2; try inversion H7;
    inversion H3; try inversion H14;
    rewrite lem_ctsubst_func;
    rewrite Denotes_equation_2; simpl;
    rewrite lem_ctsubst_func in H6;
    rewrite Denotes_equation_2 in H6; simpl in H6;
    destruct H6 as [_ [p_v_s1t1 den_func]]; repeat split;
    apply lem_erase_subtype in s as Hs;
    apply lem_erase_ctsubst with th s2 s1 in Hs;
    pose proof (fresh_varT_not_elem (union nms (union nms0 nms1)) 
                                    g (TFunc t1 t2)) as Hy; 
    set (y := fresh_varT (union nms (union nms0 nms1)) g (TFunc t1 t2)) 
        in Hy; simpl in Hy;
    destruct Hy as [Hfv [Hftv [Hy Hyg]]];
    apply not_elem_union_elim in Hy as [Hy Hy0];
    apply not_elem_union_elim in Hy0 as [Hy0 Hy1];
    apply not_elem_union_elim in Hfv; destruct Hfv;
    apply s0 in Hy as p_t1_t2;
    apply lem_erase_subtype in p_t1_t2;
    repeat rewrite lem_erase_unbind in p_t1_t2;
    apply lem_erase_ctsubst with th t1 t2 in p_t1_t2 as Ht;
    try rewrite Hs; try rewrite <- Ht;
    try apply lem_denotesenv_substitutable with g; trivial.
    intros; apply lem_den_nofv in H23 as Hvx; destruct Hvx;
    apply H with k_x0 k_x th v_x in H23 as H''; trivial.
    apply den_func in H''; try apply H22. 
    destruct H'' as [v' [Hv' [ev_vvx_v' den_v']]];
    exists v'; repeat split; trivial.
    assert (Denotes (ctsubst (CCons y v_x th) (unbindT y t1)) v' 
              -> Denotes (ctsubst (CCons y v_x th) (unbindT y t2)) v') as Hden.
        apply H0 with k k0; try apply WFEBind with k_x0;
        try apply H19; try apply lem_narrow_wf_top with s1; 
        try apply H12; try apply DExt; 
        try apply wfenv_unique; trivial.
    simpl in Hden; rewrite <- lem_tsubFV_unbindT in Hden;
    rewrite <- lem_tsubFV_unbindT in Hden;
    try rewrite lem_ctsubst_tsubBV in Hden;
    try rewrite lem_ctsubst_tsubBV in Hden;
    try rewrite lem_csubst_nofv in Hden; 
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g; trivial;
    apply Hden; apply den_v'.
  - (* SWtin *) rewrite lem_ctsubst_exis;
    rewrite Denotes_equation_3; simpl; repeat split;
    apply lem_erase_subtype in s as Htt';
    rewrite lem_erase_tsubBV in Htt';
    apply lem_erase_ctsubst with th t t' in Htt';
    try rewrite <- Htt'; try apply lem_den_hasftype;
    try apply lem_denotesenv_substitutable with g; trivial.

    unfold EvalsDenotes in H; 
    destruct H with th as [vx' [Hvx' [ev_thvx den_vx']]];
    trivial; apply lem_evals_val_det
      with (csubst th v_x) (csubst th v_x) vx' in ev_thvx;
    try apply Refl; try apply lem_csubst_value; 
    try apply lem_denotesenv_substitutable with g; trivial.
    subst vx'; exists (csubst th v_x); repeat split;
    try apply lem_csubst_value;
    try rewrite <- lem_ctsubst_tsubBV; 
    try apply H0 with k1 k2;
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g; trivial.

    inversion H3; try inversion H7;
    pose proof (fresh_varT_not_elem nms g t') as Hy;
    set (y := fresh_varT nms g t') in Hy; destruct Hy as [Ht [Ht' [Hy Hyg]]];
    apply H12 in Hy || apply H16 in Hy;
    rewrite lem_tsubFV_unbindT with y v_x t';
    try apply lem_subst_wf_top with t_x;
    try apply lem_typing_hasftype;
    try apply WFKind;
    try apply wfenv_unique; trivial. 
  - (* SBind *) rewrite lem_ctsubst_exis in H5;
    rewrite Denotes_equation_3 in H5; simpl in H5;
    destruct H5 as [_ [p_v_tht ex_vx]];
    destruct ex_vx as [v_x [Hvx [den_thtx_vx dentht_v]]].
    inversion H1; try inversion H5;
    pose proof (fresh_varT_not_elem (union nms nms0) g 
                                    (TExists t t')) as Hy;
    set (y := fresh_varT (union nms nms0) g (TExists t t')) in Hy;
    simpl in Hy; destruct Hy as [Ht [_ [Hy Hyg]]];
    apply not_elem_union_elim in Ht; destruct Ht as [Ht Ht'];
    apply not_elem_union_elim in Hy; destruct Hy as [Hy Hy0];
    assert (ctsubst th t' = ctsubst (CCons y v_x th) t')
      by (simpl; try rewrite lem_tsubFV_notin; trivial);
    rewrite H12 || rewrite H15; apply H with y k1 k2;
    try apply WFEBind with k_x;
    try apply H10; try rewrite <- H8; 
    try apply WFKind; try apply H14;
    try apply DExt; simpl;
    try rewrite <- lem_tsubFV_unbindT;
    try apply lem_weaken_wf_top; 
    try rewrite lem_ctsubst_tsubBV; 
    try rewrite lem_csubst_nofv;
    apply lem_den_nofv in den_thtx_vx as Hfr; destruct Hfr;
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g; trivial. 
  - (* SPoly *) inversion H1; try inversion H6;
    inversion H2; try inversion H12;
    rewrite lem_ctsubst_poly;
    rewrite Denotes_equation_4; simpl;
    rewrite lem_ctsubst_poly in H5;
    rewrite Denotes_equation_4 in H5; simpl in H5;
    destruct H5 as [_ [p_v_kt1 den_func]]; repeat split;
    pose proof (fresh_varT_not_elem (union nms (union nms0 nms1)) 
                                    g (TFunc t1 t2)) as Ha;
    set (a := fresh_varT (union nms (union nms0 nms1)) 
                           g (TFunc t1 t2)) 
        in Ha; simpl in Ha;
    destruct Ha as [_ [Hftv [Ha Hg]]];
    apply not_elem_union_elim in Ha as [Ha Ha0];
    apply not_elem_union_elim in Ha0 as [Ha0 Ha1];
    apply not_elem_union_elim in Hftv; destruct Hftv;
    apply s in Ha as p_t1_t2;
    apply lem_erase_subtype in p_t1_t2;
    repeat rewrite lem_erase_unbind_tvT in p_t1_t2;
    apply lem_openFT_at_equals in p_t1_t2;
    pose proof (lem_erase_freeTV t1);
    pose proof (lem_erase_freeTV t2);
    try (apply not_elem_subset with (freeTV t1); apply H5 || apply H19);
    try (apply not_elem_subset with (freeTV t2); apply H18 || apply H20);
    try apply lem_erase_ctsubst with th t1 t2 in p_t1_t2 as Ht;
    try rewrite <- Ht;
    try apply lem_denotesenv_substitutable with g; trivial.

    intros; subst k1 k2 g0 k0 t g1 k3 t0;
    apply den_func in H22 as H''; try assumption;
    destruct H'' as [v' [Hv' [ev_vta_v' den_v']]];
    exists v'; repeat split; trivial.

    assert (Denotes (ctsubst (CConsT a t_a th) (unbind_tvT a t1)) v' 
              -> Denotes (ctsubst (CConsT a t_a th) (unbind_tvT a t2)) v') as Hden.
        apply H with k_t k_t0; try apply WFEBindT;
        try apply H10; try apply H16; 
        try apply DExtT; trivial.
    simpl in Hden; rewrite <- lem_tsubFTV_unbind_tvT in Hden;
    rewrite <- lem_tsubFTV_unbind_tvT in Hden;
    try rewrite lem_ctsubst_tsubBTV in Hden;
    try rewrite lem_ctsubst_tsubBTV in Hden;
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g; trivial;
    try rewrite lem_ctsubst_nofree in Hden;
    try apply lem_free_subset_binds in H22; 
    simpl in H22; destruct H22;
    try apply no_elem_empty; trivial.
    apply Hden; apply den_v'.
  - (* SList *) rewrite lem_ctsubst_list in H6;
    apply lem_den_lists 
      with (TList (ctsubst th t1) (cpsubst th p1)) (ctsubst th t1) v
      in H6 as Hlis; trivial;
    destruct v eqn:V; try simpl in Hlis; try contradiction;
    rewrite lem_ctsubst_list.
    * (* v = Nil *) rewrite Denotes_equation_17; split;
      rewrite Denotes_equation_17 in H6; destruct H6;
      simpl in H6; simpl;
      try rewrite lem_erase_ctsubst with th t2 t1;
      try symmetry; try apply lem_erase_subtype with g;
      try apply lem_denotesenv_substitutable with g; trivial.
      pose proof (fresh_var_not_elem nms g) as Hy;
      set (y:=fresh_var nms g ) in Hy; destruct Hy.
      apply H0 in H8 as Himp; inversion Himp.
      rewrite <- (lem_csubst_nil th) at 1;
      try rewrite <- lem_cpsubst_psubBV;
      try rewrite lem_psubFV_unbindP with y Nil p2;
      try apply (H10 (CCons y Nil th)); simpl;
      try rewrite <- lem_psubFV_unbindP;
      try rewrite lem_cpsubst_psubBV;
      try rewrite lem_csubst_nil;

      try apply DExt; try rewrite lem_ctsubst_list;
      try rewrite Denotes_equation_17; try split;
      try rewrite lem_cpsubst_pempty; unfold psubBV; 
      try apply PEEmp;
      apply lem_free_subset_binds in H2; simpl in H2;
      apply lem_free_subset_binds in H3; simpl in H3;
      destruct H2; destruct H3;
      apply subset_union_elim_l in H2; destruct H2;
      apply subset_union_elim_l in H3; destruct H3; try apply H9;
      try apply not_elem_subset with (vbinds g);
      try apply not_elem_subset with (binds g);
      try apply (vbinds_subset g);
      try apply lem_denotesenv_loc_closed with g;
      try apply lem_denotesenv_substitutable with g; trivial.
    * (* v = Cons v1 v2 *) 
      apply lem_wflist_wftype in H2 as p_g_t1;
      apply lem_wflist_wftype in H3 as p_g_t2;
      rewrite Denotes_equation_18; repeat split;
      pose proof H6 as H6';
      rewrite Denotes_equation_18 in H6'; 
      destruct H6' as [p_v1v2 [val1 [val2 [den_v1 [den_v2 ev_p1v_tt]]]]];
      simpl in p_v1v2; simpl; 
      try rewrite lem_erase_ctsubst with th t2 t1;
      try symmetry; try apply lem_erase_subtype with g;
      try apply lem_denotesenv_substitutable with g;
      apply (H Star Star th) with e1 in H4 as sub_den12_e1; trivial;
      (* th(p2)[0:=Cons v1 v2] ~>* true *)
      pose proof (fresh_var_not_elem nms g) as Hy;
      set (y:=fresh_var nms g ) in Hy; destruct Hy;
      apply H0 in H7 as Himp; inversion Himp;
      try rewrite <- (lem_csubst_nofv th (Cons e1 e2));
      try rewrite <- lem_cpsubst_psubBV;
      try rewrite lem_psubFV_unbindP with y (Cons e1 e2) p2;
      try apply (H9 (CCons y (Cons e1 e2) th)); simpl;
      try rewrite <- lem_psubFV_unbindP;
      try rewrite lem_cpsubst_psubBV;
      try rewrite (lem_csubst_nofv th (Cons e1 e2));
      try apply DExt;  
      try rewrite lem_ctsubst_list;
      try rewrite lem_cpsubst_pempty;
      try (apply lem_denotes_list_pempty with (cpsubst th p1);
           apply H6 || assumption);
      apply lem_fv_subset_bindsF in p_v1v2 as Hv1v2; 
      simpl in Hv1v2; destruct Hv1v2; simpl;
      try apply no_elem_empty;
      apply lem_free_subset_binds in H2; simpl in H2;
      apply lem_free_subset_binds in H3; simpl in H3;
      destruct H2; destruct H3;
      apply subset_union_elim_l in H2; destruct H2;
      apply subset_union_elim_l in H3; destruct H3; try apply H8;
      try apply not_elem_subset with (vbinds g);
      try apply not_elem_subset with (binds g);
      try apply (vbinds_subset g);
      try apply lem_denotesenv_loc_closed with g;
      try apply lem_denotesenv_substitutable with g; trivial.     
      (* v2 \in [[ th([t2]{tt}) ]] *)
      apply lem_den_subtype_lift_list with g t1;
      try apply H with Star Star; trivial.

  - (* IRefl *) apply DImp; trivial.
  - (* ITrans *) apply DImp; inversion H; inversion H0.
    intros; apply H5; try apply H1; apply H9 || apply H10.
  - (* IFaith *) apply DImp; intros;
    rewrite lem_cpsubst_pempty; apply PEEmp.
  - (* IConj *) apply DImp; intros;
    rewrite lem_cpsubst_strengthen;
    apply lemma_strengthen_semantics;
    inversion H; inversion H0;
    apply H3 || apply H7; trivial.

  - (* ICons1 *) apply DImp; intros;
    rewrite lem_cpsubst_pcons;
    rewrite lem_cpsubst_pcons in H0;
    rewrite lem_cpsubst_pempty;
    inversion H0; apply PECons; try apply PEEmp; trivial.
  - (* ICons2 *) apply DImp; intros;
    rewrite lem_cpsubst_pcons in H0;
    inversion H0; apply H4.
  - (* IRepeat *) apply DImp; intro th;
    repeat rewrite lem_cpsubst_pcons; intros;
    inversion H0; repeat apply PECons; trivial.
  - (* INarrow *) apply DImp; intros th Hden.
    inversion H0; apply H1.
    apply lem_widen_denotes with s_x; trivial; 
    intros; apply H with k_sx k_tx; trivial.

  - (* IWeak *) apply DImp; intros th Hden Hps;
    inversion H; 
    rewrite lem_remove_cpsubst with th x ps in Hps;
    try rewrite lem_remove_cpsubst with th x qs;
    try apply H0;
    try apply lem_remove_var_denote_env with t_x;
    try rewrite <- lem_binds_env_th 
      with (concatE (ECons x t_x g) g') th;
    try apply lem_binds_concat;
    try apply set_union_intro1; 
    try apply set_add_intro2;
    try apply lem_denotesenv_closed 
      with (concatE (ECons x t_x g) g');
    try apply lem_denotesenv_substitutable 
      with (concatE (ECons x t_x g) g');
    try apply lem_denotesenv_uniqueC
      with (concatE (ECons x t_x g) g');  auto.
  - (* IWeakTV *) apply DImp; intros th Hden Hps;
    inversion H;
    rewrite lem_remove_cpsubst with th a ps in Hps;
    try rewrite lem_remove_cpsubst with th a qs;
    try apply H0;
    try apply lem_remove_tvar_denote_env with k_a;
    try rewrite <- lem_binds_env_th 
      with (concatE (EConsT a k_a g) g') th;
    try apply lem_binds_concat;
    try apply set_union_intro1; 
    try apply set_add_intro2;
    try apply lem_denotesenv_closed 
      with (concatE (EConsT a k_a g) g');
    try apply lem_denotesenv_substitutable 
      with (concatE (EConsT a k_a g) g');
    try apply lem_denotesenv_uniqueC
      with (concatE (EConsT a k_a g) g');  auto.
  - (* ISub *) apply DImp; intros th Hden Hps;
    inversion H0;
    apply lem_add_var_denote_env with g g' x v_x t_x th 
      in Hden as Hth';
    try destruct Hth' as [th' [den_env_th' [Hcs [Hcs' Hcs'']]]];
    try pose proof (H1 _ den_env_th') as ev_func;
    repeat rewrite Hcs'' in ev_func; try apply ev_func; auto.
    apply lem_extend_denotes with g (esubFV x v_x g');
    try apply lem_typing_wf with v_x; intros;
    try apply lem_evalsdenotes_value; try apply H;
    try apply lem_csubst_value; 
    try apply lem_denotesenv_substitutable with g; auto.
  - (* ISubTV *) apply DImp; intros th Hden Hps.
    inversion H;  subst g0 ps0 qs0.
    apply lem_add_tvar_denote_env with g g' a t_a k_a th 
      in Hden as Hth';
    try destruct Hth' as [th' [den_env_th' [Hcs [Hcs' Hcs'']]]];
    try pose proof (H0 _ den_env_th') as ev_func;
    repeat rewrite Hcs'' in ev_func; try apply ev_func; auto.
  
  - (* IEqlSub *) apply DImp; intros th den_g_th.
    repeat rewrite lem_cpsubst_pcons;
    rewrite lem_cpsubst_pempty;
    repeat rewrite lem_csubst_app;
    repeat rewrite lem_csubst_appT;
    rewrite lem_csubst_prim; intros;
    inversion H; inversion H2; subst ps0 e3.
    apply PECons; try apply PEEmp.
    apply AddStep with e2; try apply H5.
    (* investigate e2 *)
    inversion H4;  try inversion H8.
    inversion H9;  try inversion H13; try inversion pf.
    inversion H14; try apply lem_value_stuck in H20;
                   try apply val_Prm; try contradiction. 
    apply EApp1; apply EApp1; 
    assert (isCompatT Eql (ctsubst th (TRefn b ps))) as pf'
      by (inversion pf; 
          (apply isCptT_EqlB; rewrite <- H20) || 
              (apply isCptT_EqlZ; rewrite <- H20);
          apply lem_erase_ctsubst;
          try apply lem_denotesenv_substitutable with g; auto). 
    pose proof (deltaT_exchange_type Eql (ctsubst th (TRefn b PEmpty)) 
                                         (ctsubst th (TRefn b ps)) pf pf');
    rewrite H20; try apply lem_erase_ctsubst;
    try apply EPrimT; try apply lem_ctsubst_noExists;
    try apply lem_denotesenv_substitutable with g; simpl; trivial.

  - (* ILenSub *) apply DImp; intros th den_g_th.
    apply lem_csubst_value with th e in i;
    try apply lem_denotesenv_substitutable with g; trivial.
    repeat rewrite lem_cpsubst_pcons;
    unfold eq; unfold length;
    repeat rewrite lem_csubst_app;
    repeat rewrite lem_csubst_appT;
    repeat rewrite lem_csubst_prim; intros.
    try apply PECons; inversion H0; try apply H4; subst p ps0.
    inversion H3; subst e1 e3.    
    (* investigate e2 *)
    inversion H1; try inversion H7; subst e0 e1 e2; clear H9.
    inversion H8; try apply lem_value_stuck in H9; try apply val_Prm;
                  try apply lem_value_stuck in H10; try apply i;
                  try contradiction.
    assert (isValue e') by (subst e'; apply lem_delta_value).
    apply AddStep
      with (App e' (App (AppT (Prim Length) (ctsubst th t)) (csubst th (FV y))));
    try apply EApp1; try apply H8.
    (* investigate e' *)
    inversion H2; subst e1 e3;
    inversion H11; try (inversion H16; contradiction);
                   try apply lem_value_stuck in H16; try apply H10;
                   try contradiction; subst v e0.
    inversion H17; try apply lem_value_stuck in H19; try apply val_Len;
                   try apply lem_value_stuck in H20;
                   try apply lem_csubst_value; try apply val_FV;
                   try apply lem_denotesenv_substitutable with g;
                   trivial; try contradiction.
    apply AddStep with (App e' e'0); try (subst e2; apply H12);
    apply EApp2; try apply H15; subst e'0; apply EPrimM; apply H20.
  - (* ILenSub2 *) apply DImp; intros th den_g_th.
    apply lem_csubst_value with th e in i;
    try apply lem_denotesenv_substitutable with g; trivial.
    repeat rewrite lem_cpsubst_pcons;
    unfold eq; unfold length;
    repeat rewrite lem_csubst_app;
    repeat rewrite lem_csubst_appT;
    repeat rewrite lem_csubst_prim; intros.
    try apply PECons; inversion H0; try apply H4; subst p ps0.
    inversion H3; subst e1 e3.    
    (* investigate e2 *)
    inversion H1;  try inversion H7; subst e0 e1 e2; clear H9.
    inversion H8;  try (inversion H9; contradiction).
    inversion H10; try (inversion H14; contradiction).
    inversion H15; try apply lem_value_stuck in H19; try apply val_Len;
                   try apply lem_value_stuck in H20; try apply i;
                   try contradiction.
    assert (isList (csubst th e)) as the_lis
      by (apply lem_compatM_list with Length; apply pf).
    subst v0 e'0 e' e1 c t0 w.
    (* evaluate LHS of goal down to a value *)           
    pose proof (lemma_length_list_semantics (ctsubst th s) 
                  (csubst th e) i the_lis) as ev_lens_the_n.
    destruct ev_lens_the_n as [n ev_lens_the_n].
    assert (EvalsTo e'1 (Ic n)) as ev_e'1_n
      by (apply lem_decompose_evals with 
          (App (AppT (Prim Length) (ctsubst th s)) (csubst th e));
          try apply ev_lens_the_n; try apply val_Ic; 
          try apply lem_step_evals; apply H15).
    apply AddStep
      with (App (App (Prim Eq) (App (Prim Succ) e'1)) 
                (App (AppT (Prim Length) (ctsubst th t)) (csubst th (FV y))));
    try apply EApp1; try apply EApp2; try apply EApp2;
    try apply val_Prm; try (subst e'1; apply EPrimM); try apply i.
    apply lemma_evals_trans with 
      (App (App (Prim Eq) (Ic (1 + n)))
           (App (AppT (Prim Length) (ctsubst th t)) (csubst th (FV y))));
    try apply lemma_app_many; try apply lemma_app_many2;
    try apply val_Prm; try apply lemma_succ_semantics; try apply ev_e'1_n.
    apply AddStep
      with (App (Prim (Eqn (1 + n))) 
                (App (AppT (Prim Length) (ctsubst th t)) (csubst th (FV y))));
    try apply EApp1; try apply lem_step_eq.
    (* evaluate LHS of H2 down to a value *)  
    assert (EvalsTo (App (App (Prim Eq) (App (Prim Succ) e'1)) 
                         (App (AppT (Prim Length) (ctsubst th s)) (csubst th (FV y))))
                    (App (Prim (Eqn (1 + n))) 
                         (App (AppT (Prim Length) (ctsubst th s)) (csubst th (FV y))))
      ) as H2'
      by (apply lemma_app_many; 
          apply lemma_evals_trans with (App (Prim Eq) (Ic (1+n)));
          try apply lemma_app_many2; try apply val_Prm;
          try apply lemma_succ_semantics; try apply ev_e'1_n;
          apply lem_step_evals; apply lem_step_eq).
    apply (lem_decompose_evals 
                    (App (App (Prim Eq) (App (Prim Succ) e'1)) 
                         (App (AppT (Prim Length) (ctsubst th s)) (csubst th (FV y))))
                    (App (Prim (Eqn (1 + n))) 
                         (App (AppT (Prim Length) (ctsubst th s)) (csubst th (FV y))))
                    (Bc true) (val_Bc true) H2') in H2.
    (* now work on the RHS *)
    inversion H2; (* as e1 ~> e2 ~>...~> true *) set (m:=(1+n)%Z) in *.
    (* investigate e2; prove th(y) is a value and a list *)
    assert (isValue (csubst th (FV y))) as valy
      by (apply lem_csubst_value; try apply val_FV;
          apply lem_denotesenv_substitutable with g; apply den_g_th).
    inversion H9;  try (inversion H21; contradiction).
    inversion H22; try apply lem_value_stuck in H26; try apply val_Len;
                   try apply lem_value_stuck in H27; try apply valy;
                   try contradiction.
    assert (isList (csubst th (FV y))) as the_lis'
      by (apply lem_compatM_list with Length; apply pf0).
    subst v0 e3 c t0 w.
    (* evaluate RHS of goal down to a value *)   
    pose proof (lemma_length_list_semantics (ctsubst th s) 
                  (csubst th (FV y)) valy the_lis') as ev_lens_thy_n'.
    destruct ev_lens_thy_n' as [n' ev_lens_thy_n'].
    assert (EvalsTo e' (Ic n')) as ev_e'_n'
      by (apply lem_decompose_evals with 
          (App (AppT (Prim Length) (ctsubst th s)) (csubst th (FV y)));
          try apply ev_lens_thy_n'; try apply val_Ic; 
          try apply lem_step_evals; trivial).
    apply AddStep with (App (Prim (Eqn m)) e');
    try apply EApp2; try apply val_Prm;
    try (subst e'; apply EPrimM); try apply valy.
    (* H11 now matches goal *)  
    subst e2; apply H11.
  - (* IStren *) apply DImp; intros; inversion H.
    rewrite lem_cpsubst_strengthen;
    rewrite lem_cpsubst_strengthen in H1.
    apply lemma_strengthen_semantics;
    apply lemma_semantics_strengthen in H1;
    destruct H1; try apply H6; apply H2; try apply H1.
    inversion H0; apply DExt; try assumption.
    subst th; simpl in H6; rewrite <- lem_psubFV_unbindP in H6;
    try rewrite lem_cpsubst_psubBV in H6;
    try rewrite lem_csubst_nofv in H6;
    apply lem_den_nofv in H13 as Hfv; destruct Hfv;
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g; 
    auto; destruct b' eqn:B;
    try ( assert (isClosedBasic b' \/ isBTV b') 
            by (subst b'; simpl; auto);
          rewrite lem_ctsubst_refn in H13;
          try rewrite lem_ctsubst_refn;
          try rewrite Denotes_equation_1 in H13;
          try rewrite Denotes_equation_1;
          simpl; simpl in H13; intuition ).
    * (* FTV a *) 
      pose proof (set_In_dec Nat.eq_dec a (tvbinds g));
      destruct H15. (* a \in tvbinds g *)
      apply lem_tvbinds_denotesenv with a g th0 in s;
      try destruct s as [t_a [Hta [p_ta_s Ha]]];
      try rewrite lem_ctsubst_refn_tv with th0 a t_a qs;
      try rewrite lem_ctsubst_refn_tv with th0 a t_a PEmpty in H13;
      try rewrite lem_cpsubst_pempty in H13; 
      try rewrite lem_push_empty in H13; 
      try apply lem_denotesenv_closed with g;
      try apply lem_denotesenv_loc_closed with g;
      try apply lem_denotesenv_substitutable with g; 
      try apply lem_denotesenv_uniqueC with g; auto.
      destruct t_a; simpl in Hta; try contradiction; simpl;
      try apply H13; rewrite Denotes_equation_1 in H13;
      rewrite Denotes_equation_1; intuition;
      rewrite lem_psubBV_strengthen;
      apply lemma_strengthen_semantics; trivial.
      (* a \not\in tvbinds g *)
      rewrite lem_ctsubst_refn_tv_notin';
      try rewrite lem_ctsubst_refn_tv_notin' in H13;
      try rewrite <- lem_tvbinds_env_th with g th0; trivial.
      rewrite Denotes_equation_1 in H13;
      rewrite Denotes_equation_1; intuition.
  - (* IEvals  *) apply DImp; intros;
    rewrite lem_cpsubst_pcons in H0;
    rewrite lem_cpsubst_pcons; inversion H0;
    apply PECons;
    apply lem_csubst_evals with th p p' in e;
    try apply lem_decompose_evals with (csubst th p);
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g; 
    try apply val_Bc; simpl; auto.
  - (* IEvals2 *) apply DImp; intros;
    rewrite lem_cpsubst_pcons in H0;
    rewrite lem_cpsubst_pcons; inversion H0;
    apply PECons;
    apply lem_csubst_evals with th p' p in e;
    try apply lemma_evals_trans with (csubst th p);
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g; auto.
  - (* IExactQ *) apply DImp; intros.
    apply lem_bound_in_denotesenv_denotes 
      with x (self t_x v_x Base) g th in H0 as H'; trivial;
    destruct H' as [v [den_v b']].
    apply lem_denotes_self_ctsubst in den_v;
    try apply lem_denotes_self_equal in den_v.
    (* Lemma lem_bound_in_denotesenv_denotes :
        forall (x:vname) (t:type) (g:env) (th:csub),
          DenotesEnv g th -> bound_in x t g -> WFEnv g
              -> exists v, Denotes (ctsubst th t) v /\ bound_inC x v th. *)
    (* Lemma lem_denotes_ctsubst_self : 
        forall (th:csub) (t:type) (v v':expr) (k:kind),
          closed th -> loc_closed th -> substitutable th -> uniqueC th 
              -> isLC v -> ftv v = empty
              -> Denotes (self (ctsubst th t) (csubst th v) k) v'
              -> Denotes (ctsubst th (self t v k)) v'. *)
    (* Lemma lem_denotes_self_equal : forall (t:type) (v v':expr),
        WFtype Empty t Base -> noExists t
            -> isValue v -> HasFtype FEmpty v (erase t)
            -> Denotes (self t v Base) v' -> v = v'. *)
    try rewrite lem_remove_cpsubst with th x (psubFV x v_x ps).
    try rewrite <- lem_cpsubst_psubFV;
    try rewrite <- lem_remove_csubst with th x v_x;
    try rewrite den_v;
    try rewrite <- lem_reorder_unroll_cpsubst;
    
    (*try apply lem_denotesenv_closed with g;
    try apply lem_denotesenv_substitutable with g;
    try apply lem_denotesenv_uniqueC with g;*)
    try apply lem_boundinC_incsubst with v;
    trivial.

    pose bound_


    (* Lemma lem_denotes_self_eqlLen : forall (t:type) (ps:preds) (v v':expr),
          WFtype Empty (TList t ps) Star 
              -> isValue v -> HasFtype FEmpty v (FTList (erase t))
              -> Denotes (TList t (PCons (eqlLenPred t v) ps)) v' 
              -> exists n:Z, EvalsTo (length t v) (Ic n)
                              /\ EvalsTo (length t v') (Ic n). *)
  Qed.
