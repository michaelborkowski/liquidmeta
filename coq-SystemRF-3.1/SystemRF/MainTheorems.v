Require Import SystemRF.BasicDefinitions. 
Require Import SystemRF.Names.
Require Import SystemRF.LocalClosure.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.PrimitivesFTyping.
Require Import SystemRF.BasicPropsWellFormedness.
Require Import SystemRF.SystemFLemmasWeaken.
Require Import SystemRF.Typing.
Require Import SystemRF.LemmasWeakenWF.
Require Import SystemRF.LemmasWeakenTyp.
Require Import SystemRF.LemmasWellFormedness.
Require Import SystemRF.LemmasTyping.
Require Import SystemRF.LemmasSubtyping.
Require Import SystemRF.LemmasExactness.
Require Import SystemRF.SubstitutionLemmaTyp.
Require Import SystemRF.SubstitutionLemmaTypTV.
Require Import SystemRF.LemmasNarrowing.
Require Import SystemRF.LemmasTransitive.
Require Import SystemRF.LemmasInversion.
Require Import SystemRF.LemmasLists.
Require Import SystemRF.PrimitivesDeltaTyping.

Require Import Arith.
Require Import ZArith.

(*--------------------------------------------------------------------------------
--- | PROGRESS and PRESERVATION  
--------------------------------------------------------------------------------*)

Theorem thm_progress' : forall (g:env) (e:expr) (t:type),
    Hastype g e t -> g = Empty -> isValue e \/ exists e'', Step e e''.
Proof. intros g e t p_e_t; induction p_e_t; intro emp; simpl; subst g;
    (* TSub * ) try (apply IHp_e_t; reflexivity); *)
    (* values *) try (left; constructor; assumption).
  - (* App e e' *) right. inversion p_e_t1;
    try simpl in H0; try contradiction;
    destruct IHp_e_t1 as [H'|H']; try reflexivity;
    (* consider e not a value *)
    try ( destruct H' as [e1' H']; exists (App e1' e'); apply EApp1; 
          subst e; try subst t0; assumption);
    (* else e must be a value *)
    try (subst e; inversion H'; contradiction);
    (* consider e' not a value *)
    destruct IHp_e_t2 as [H''|H'']; try reflexivity;
    try ( destruct H'' as [e'' H'']; exists (App e e''); 
          subst e; apply EApp2; assumption );
    (* then e and e' are both values *)
    apply lem_typing_hasftype in p_e_t1 as p_e_ert1; 
    try apply WFEEmpty; simpl in p_e_ert1;
    apply lemma_function_values with e (erase t_x) (erase t) in H'; trivial;
    try match goal with
        | [ |- exists e'': expr, Step (App e e') _] 
              => destruct e eqn:E; simpl in H'; try contradiction
        end;
    assert (Hastype Empty (App e e') (TExists t_x t)) 
      as p_pe'_txt by (apply TApp; try rewrite <- E in p_e_t1; trivial);
    (* either e = Prim c ...*)
    try set (p := c); subst e;
    try ( pose proof (lem_prim_compat_in_tapp p e' (TExists t_x t) 
                        H'' p_pe'_txt) as pf;
          apply compat_prop_set in pf; exists (delta p e' pf); 
          apply EPrim; trivial );
    (* or e = Lambda e1... *)
    try (exists (subBV e' e0); apply EAppAbs; assumption);
    try (exists (subBV e' e1); apply EAppAbs; assumption);
    (* ... or e = (AppT (Prim Length) t0) *)
    try subst e0; try destruct e0; try destruct e1; 
    simpl in H'; try contradiction;
    apply lem_prim_compatM_in_tappappT in p_pe'_txt as pf;
    trivial; apply compatM_prop_set in pf;
    exists (deltaM p e' pf); try apply EPrimM; apply H''.
  - (* AppT e rt *) inversion p_e_t;
    try simpl in H3; try contradiction;
    destruct IHp_e_t as [H'|H']; try reflexivity;
    (* consider e not a value *)
    try ( destruct H' as [e' H']; right; 
          exists (AppT e' t); apply EAppT; 
          subst e; try subst k0; try subst t0; assumption);
    (* else e must be a value *)
    try (subst e; inversion H'; contradiction);
    apply lem_typing_hasftype in p_e_t as p_e_ert; 
    try apply WFEEmpty; simpl in p_e_ert;
    apply lemma_tfunction_values with e k (erase s) in H'; trivial;
    try match goal with
        | [ |- isValue (AppT e t) \/ _] 
              => destruct e eqn:E; simpl in H'; try contradiction
        end;
    subst e; simpl in H'; try contradiction;
    (* either e = Prim c ...*)
    try destruct p; try destruct c; 
    simpl in H5; try discriminate; try inversion p_e_ert;
    try (left; constructor); right;
    try assert (~ isMeasure c) as nomeas by (subst c; auto);
    try assert (Hastype Empty (AppT (Prim c) t) (tsubBTV t s)) 
      as p_pt_st
      by (apply TAppT with k; subst c; trivial);
    try ( pose proof (lem_prim_compatT_in_tappT c t (tsubBTV t s)
                        nomeas H0 p_pt_st) as pf;
          apply compatT_prop_set in pf; exists (deltaT c t pf);
          subst c; apply EPrimT; trivial);
    (* ... or e = LambdaT k e1 *)
    try exists (subBTV t e1); try exists (subBTV t e0);
    apply EAppTAbs; assumption.
  - (* Let e_x e *) right; destruct IHp_e_t; try reflexivity.
      * (* e_x val *) exists (subBV e_x e); apply ELetV; apply H2.
      * (* otherw. *) destruct H2 as [e_x' H2]; exists (Let e_x' e);
        apply ELet; apply H2.
  - (* Annot e t1 *) right; destruct IHp_e_t; try reflexivity.
      * (* e val *) exists e; apply EAnnV; apply H0.
      * (* other *) destruct H0 as [e'' H0]; exists (Annot e'' t); apply EAnn; apply H0.
  - (* If e1 e2 e3 *) right; destruct IHp_e_t; try reflexivity.
      * (* e0 val *) apply lem_typing_hasftype in p_e_t as p_e_ert;
        try apply lem_bool_values in p_e_ert as H_bool; 
        try assumption; try apply WFEEmpty.
        destruct e0; simpl in H_bool; try contradiction;
        destruct b; (exists e1; apply EIfT) || (exists e2; apply EIfF).
      * (* otherw *) destruct H4 as [e0' st_e0_e0']; exists (If e0' e1 e2); 
        apply EIf; apply st_e0_e0'.
  - (* Cons eH eT *) destruct IHp_e_t1; destruct IHp_e_t2; 
    try reflexivity;
    (* eH not a value *)
    try destruct H1 as [eH' st_eH_eH'];
    try (right; exists (Cons t eH' eT)); 
    try apply ECons1; try apply st_eH_eH';
    (* eT not a value *)
    try destruct H2 as [eT' st_eT_eT'];
    try (right; exists (Cons t eH eT')); 
    try apply ECons2; try apply st_eT_eT'; try apply H1;
    (* both values *) left;
    apply val_Cons; trivial.
  - (* Switch e eN eC *) destruct IHp_e_t as [IH|IH]; 
    try reflexivity;
    (* e not a value *)
    try destruct IH as [e' st_e_e'];
    try (right; exists (Switch e' eN eC)); 
    try apply ESwitch; try apply st_e_e'.
    (* otherwise *) apply lem_typing_hasftype in p_e_t as p_e_ert;
    try apply lemma_list_values in p_e_ert as H_list;
    try assumption; try apply WFEEmpty; right.
    destruct e; simpl in H_list; try contradiction; 
    try (exists eN; apply ESwitchN); 
    inversion IH; exists (App (App eC e1) e2); 
    apply ESwitchC; trivial.
  - (* TSub *) apply IHp_e_t; reflexivity.
  Qed.

Theorem thm_progress : forall (e:expr) (t:type),
    Hastype Empty e t -> isValue e \/ exists e'', Step e e''.
Proof. intros; apply thm_progress' with Empty t; apply H || reflexivity. Qed.
  
Theorem thm_preservation' : forall (g:env) (e:expr) (t:type) (e':expr),
    Hastype g e t -> g = Empty -> Step e e' -> Hastype Empty e' t.
Proof. intros g e t e' p_e_t; revert e'; induction p_e_t; 
  intros e'' emp st_e_e''; simpl; subst g;
  try (apply lem_value_stuck in st_e_e'' as H'; 
       constructor || contradiction; reflexivity).
  - (* TApp e e' *) apply thm_progress in p_e_t1 as Hprog;
    apply thm_progress in p_e_t2 as Hprog';
    destruct Hprog; destruct Hprog';
    (* e not value: *)
    try destruct H as [e1 st_e_e1];
    try apply lem_sem_det with (App e e') e'' (App e1 e') 
      in st_e_e'' as He'';
    try apply EApp1; try assumption; try subst e'';
    try apply TApp; try apply IHp_e_t1; try apply p_e_t2; trivial; 
    (* e' not a value *)
    try destruct H0 as [e'1 st_e_e'1];
    try apply lem_sem_det with (App e e') e'' (App e e'1) 
      in st_e_e'' as He'';
    try apply EApp2; try assumption; try subst e'';
    try apply TApp; try apply p_e_t1; try apply IHp_e_t2; trivial.
    (* both values *)
    apply lem_typing_hasftype in p_e_t1 as p_e_ert1;
    try simpl in p_e_ert1; try apply WFEEmpty;
    try apply lemma_function_values with e (erase t_x) (erase t) 
      in H as Hfval; trivial.
    destruct e eqn:E; simpl in Hfval; try contradiction.
    * (* App (Prim p) val *) 
      assert (Hastype Empty (App (Prim p) e') (TExists t_x t))
        by (apply TApp; assumption);
      rewrite <- E in H;
      pose proof (lem_prim_compat_in_tapp p e' (TExists t_x t) H0 H1) as pf;
      apply compat_prop_set in pf; subst e;
      apply lem_sem_det with (App (Prim p) e') e'' (delta p e' pf) in st_e_e'' 
        as He''; try apply EPrim; try assumption; subst e'';
      pose proof (lem_delta_typ p e' t_x t H0 p_e_t1 p_e_t2) as He''.
      rewrite <- delta_delta' with p e' pf in He''; destruct He'';
      destruct H2; injection H2 as H2; subst x; assumption.
    * (* App (Lambda e0) val *) subst e;
      assert (Hastype Empty (App (Lambda e0) e') (TExists t_x t)) as p_ee'_txt
        by (apply TApp; assumption);
      apply lem_sem_det with (App (Lambda e0) e') e'' (subBV e' e0) in st_e_e'' 
        as He''; try apply EAppAbs; try assumption; subst e'';
      apply lem_typing_wf in p_e_t1 as p_emp_txt; try apply WFEEmpty;
      pose proof lem_invert_tabs Empty e0 t_x t p_e_t1 WFEEmpty p_emp_txt;
      destruct H1 as [nms p_e0_t];
      pose proof (fresh_not_elem nms) as Hy; set (y := fresh nms) in Hy;
      rewrite lem_subFV_unbind with y e' e0;
      try apply TSub with (tsubFV  y e' (unbindT y t)) Star;
      try apply lem_subst_typ_top with t_x; try apply p_e0_t;
      try rewrite <- lem_tsubFV_unbindT; 
      try apply lem_witness_sub with Star;
      try apply lem_typing_wf with (App (Lambda e0) e');
      pose proof lem_fv_bound_in_fenv FEmpty (Lambda e0) 
                    (FTFunc (erase t_x) (erase t)) y p_e_ert1 as Hfv;
      pose proof lem_free_bound_in_env Empty (TFunc t_x t) Star y p_emp_txt as Hfr;
      destruct Hfv; destruct Hfr; try simpl in H3;
      try apply not_elem_union_elim in H3; try destruct H3;
      try apply WFEEmpty; intuition. 
    * (* App (AppT Length t) val *)
      destruct e0 eqn:E0; try contradiction;
      destruct p eqn:P; try contradiction.
      assert (isCompatM' Length e') as pf
        by (apply lem_prim_compatM_in_tappappT with t0 (TExists t_x t);
            try apply TApp; trivial);
      apply compatM_prop_set in pf.
      assert (Hastype Empty (App (AppT (Prim Length) t0) e') 
                      (TExists t_x t)) as p_ee'_txt
        by (apply TApp; assumption).
      apply lem_sem_det 
        with (App (AppT (Prim Length) t0) e') e'' (deltaM Length e' pf) 
        in st_e_e'' as He''; try apply EPrimM; try assumption.
      pose proof (lem_deltaM_typ Length t0 e' t_x t) as He'''.
      destruct He''' as [e''' [He''' p_e''_txt]]; trivial.
      rewrite <- deltaM_deltaM' with Length e' pf in He''';
      injection He''' as He'''; subst e'' e'''; apply p_e''_txt.

  - (* TAppT e t *) apply thm_progress in p_e_t as Hprog; 
    destruct Hprog;
    (* e not value: *)
    try destruct H2 as [e' st_e_e'];
    try apply lem_sem_det with (AppT e t) e'' (AppT e' t)
      in st_e_e'' as He'';
    try apply EAppT; try assumption; try subst e'';
    try apply TAppT with k; try apply IHp_e_t; trivial.
    (* e is a value *) 
    apply lem_typing_hasftype in p_e_t as p_e_ert;
    try simpl in p_e_ert; try apply WFEEmpty.    
    apply lemma_tfunction_values in p_e_ert as Hfval; 
    try apply H2; destruct e eqn:E; simpl in Hfval; try contradiction.
    * (* AppT (Prim p) t *) 
      assert (isMeasure p \/ ~ isMeasure p) as nomeas
        by (destruct p; intuition).
      destruct nomeas as [meas|nomeas];
      try ( destruct p; simpl in meas; try contradiction;
            apply lem_value_stuck in st_e_e''; 
            try apply val_Len; contradiction ). 
      assert (Hastype Empty (AppT (Prim p) t) (tsubBTV t s))
        by (apply TAppT with k; assumption).
      pose proof (lem_prim_compatT_in_tappT p t (tsubBTV t s) 
                                            nomeas H0 H3) as pf;
      apply compatT_prop_set in pf; subst e;
      apply lem_sem_det with (AppT (Prim p) t) e'' (deltaT p t pf) in st_e_e'' 
        as He''; try apply EPrimT; try assumption; subst e'';
      pose proof (lem_deltaT_typ p t k s nomeas H H0 p_e_t H1) as He'';
      rewrite deltaT_deltaT' with p t pf in He''; destruct He'';
      destruct H4; injection H4 as H4; subst x; assumption.
    * (* App (Lambda e0) val *) subst e;
      assert (Hastype Empty (AppT (LambdaT k0 e0) t) (tsubBTV t s)) as p_et_st
        by (apply TAppT with k; assumption);
      assert (k0 = k) as Hk0  
        by (apply lem_lambdaT_tpoly_same_kind with Empty e0 s;
            try apply lem_typing_wf with (LambdaT k0 e0); 
            try apply WFEEmpty; trivial); subst k;
      apply lem_sem_det with (AppT (LambdaT k0 e0) t) e'' (subBTV t e0) in st_e_e'' 
        as He''; try apply EAppTAbs; try assumption; subst e'';
      apply lem_typing_wf in p_e_t as p_emp_ks; try apply WFEEmpty;
      pose proof lem_invert_tabst Empty k0 e0 s p_e_t WFEEmpty p_emp_ks as p_e0_s;
      destruct p_e0_s as [nms p_e0_s];
      pose proof (fresh_not_elem nms) as Ha; set (a := fresh nms) in Ha;
      rewrite lem_subFTV_unbind_tv with a t e0;
      try rewrite lem_tsubFTV_unbind_tvT with a t s;
      try apply lem_subst_tv_typ_top with k0; try apply p_e0_s;
      pose proof lem_fv_bound_in_fenv FEmpty (LambdaT k0 e0) 
                    (FTPoly k0 (erase s)) a p_e_ert as Hfv;
      pose proof lem_free_bound_in_env Empty (TPoly k0 s) Star a p_emp_ks as Hfr;
      destruct Hfv; destruct Hfr;
      try apply WFEEmpty; auto.
  - (* TLet e_x e *) apply thm_progress in p_e_t as Hprog; destruct Hprog.
    * (* e_x is a value *)
      apply lem_sem_det with (Let e_x e) e'' (subBV e_x e) in st_e_e'';
      try apply ELetV; try apply H2; subst e'';
      pose proof (fresh_not_elem nms) as Hy; set (y := fresh nms) in Hy;
      rewrite lem_subFV_unbind with y e_x e;
      pose proof lem_subFV_notin as Hnot; destruct Hnot as [_ [Hnot _]];
      try rewrite <- Hnot with t y e_x;
      try apply lem_subst_typ_top with t_x;
      try rewrite <- lem_unbindT_lct with y t;
      try apply H0; try rewrite lem_unbindT_lct;
      try apply lem_wftype_islct with Empty k;
      assert (Hastype Empty (Let e_x e) t) as p_exe_t 
        by (apply TLet with t_x k nms; trivial);
      assert (HasFtype (erase_env Empty) (Let e_x e) (erase t)) as p_exe_ert
        by (apply lem_typing_hasftype; try apply WFEEmpty; trivial);
      pose proof lem_fv_bound_in_fenv FEmpty (Let e_x e) 
                    (erase t) y p_exe_ert as Hfv;  
      pose proof lem_free_bound_in_env Empty t k y H as Hfr;
      destruct Hfv; destruct Hfr; auto;
      try apply not_elem_union_elim in H3; try destruct H3;
      try apply WFEEmpty; simpl; intuition.
    * (* e_x not value: *)
      destruct H2 as [e_x' Hstep];
      apply lem_sem_det with (Let e_x e) e'' (Let e_x' e) in st_e_e'' as He'';
      try apply ELet; try apply Hstep; subst e'';
      apply TLet with t_x k nms; try apply IHp_e_t; trivial.
  - (* TAnn e t *) apply thm_progress in p_e_t as Hprog; destruct Hprog.
    * (* e is a value *)
      apply lem_sem_det with (Annot e t) e'' e in st_e_e'';
      try apply EAnnV; try apply H0; subst e''; assumption.
    * (* e not a value*) destruct H0 as [e' Hstep];
      apply lem_sem_det with (Annot e t) e'' (Annot e' t) in st_e_e'';
      try apply EAnn; try apply Hstep; subst e'';
      apply TAnn; try apply IHp_e_t; trivial.
  - (* TIf *) apply thm_progress in p_e_t as Hprog; destruct Hprog.
    * (* e0 value *) apply lem_typing_hasftype in p_e_t as p_e_ert;
      try apply lem_typing_wf in p_e_t as p_emp_t;
      try apply lem_bool_values in p_e_ert as H_bool; 
      try assumption; try apply WFEEmpty.
      destruct e0; simpl in H_bool; try contradiction.
      pose proof (fresh_varE_not_elem nms Empty (Annot e'' t)) as Hy; 
      set (y := fresh_varE nms Empty (Annot e'' t)) in Hy; 
      simpl in Hy; destruct Hy; destruct H6; destruct H7;
      apply not_elem_union_elim in H5; apply not_elem_union_elim in H6; 
      pose proof lem_subFV_notin as Hnot; destruct Hnot as [Hnot_e Hnot_t];
      destruct Hnot_t as [Hnot_t _];
      rewrite <- Hnot_e with e'' y (Bc b); 
      try rewrite <- Hnot_t with t y (Bc b);
      try apply lem_subst_typ_top with (self (TRefn TBool ps) (Bc b) Base);
      try apply WFEEmpty; intuition; destruct b;
      try assert (e'' = e1) 
          by (apply lem_sem_det with (If (Bc true) e1 e2); try apply EIfT; assumption);
      try assert (e'' = e2) 
          by (apply lem_sem_det with (If (Bc false) e1 e2); try apply EIfF; assumption);
      subst e'';
      try apply H0; try apply H2; try apply lem_exact_type;
      trivial; try apply WFEEmpty;
      inversion p_emp_t; apply H6.
    * (* otherw *) destruct H4 as [e0' st_e1_e1']; assert (e'' = If e0' e1 e2)
        by (apply lem_sem_det with (If e0 e1 e2); try apply EIf; assumption);
      subst e''; apply TIf with ps k nms; try assumption; apply IHp_e_t; trivial.
  - (* TCons *) apply thm_progress in p_e_t1 as Hprog;
    apply thm_progress in p_e_t2 as Hprog';
    destruct Hprog; destruct Hprog';
    (* eH not value: *)
    try destruct H1 as [eH1 st_eH_eH1];
    try apply lem_sem_det with (Cons t eH eT) e'' (Cons t eH1 eT) 
      in st_e_e'' as He'';
    try apply ECons1; try assumption; try subst e'';
    try apply TCons; try apply IHp_e_t1; try apply p_e_t2; trivial; 
    (* e' not a value *)
    try destruct H2 as [eT1 st_eT_eT1];
    try apply lem_sem_det with (Cons t eH eT) e'' (Cons t eH eT1) 
      in st_e_e'' as He'';
    try apply ECons2; try assumption; try subst e'';
    try apply TCons; try apply p_e_t1; try apply IHp_e_t2; trivial.
    (* both values *)
    apply lem_value_stuck in st_e_e''; try apply val_Cons;
    try assumption. contradiction.  
  - (* TSwitch *) apply thm_progress in p_e_t as Hprog; 
    destruct Hprog;
    (* e not value: *)
    try destruct H6 as [e' st_e_e'];
    try apply lem_sem_det with (Switch e eN eC) e'' (Switch e' eN eC)
      in st_e_e'' as He'';
    try apply ESwitch; try assumption; try subst e'';
    try apply TSwit with t ps k nms; try apply IHp_e_t; trivial.
    (* e is a value *) 
    assert (Hastype Empty (Switch e eN eC) t') as p_sw_t'
      by (apply TSwit with t ps k nms; assumption).
    apply lem_typing_hasftype in p_e_t as p_e_ert;
    try apply lem_typing_wf in p_e_t as p_emp_t;
    try simpl in p_e_ert; try apply WFEEmpty;
    try apply lem_wftype_islct in p_emp_t as Hlct; 
    unfold isLCT in Hlct; simpl in Hlct;
    destruct Hlct as [Hlct Hlcp1];
    pose proof lem_open_at_lc_at as [Hope [Hopt Hopp]];
    apply lemma_list_values in p_e_ert as Hfval; try apply H6. 
    destruct e eqn:E; simpl in Hfval; try contradiction.
    * (* e = Nil *) clear H3 H5 IHp_e_t.
      apply lem_sem_det with (Switch (Nil t0) eN eC) e'' eN 
        in st_e_e'' as He''; try apply ESwitchN; subst e''.
      
      try apply lem_invert_nil in p_e_t as Hinv ; 
      try destruct Hinv 
        as [p_s'_t [p_emp_s' [Hs'1 [Hs'2 p_ls'_ltps]]]];
      try inversion p_ls'_ltps;
      try apply lem_wftype_islct in p_emp_s' as Hlcs';
      try unfold isLCT in Hlcs';
      try apply WFEEmpty; try apply p_emp_t;
      
      pose proof (fresh_varE_not_elem (union nms nms0) Empty (Annot eN t')) 
        as Hy; 
      set (y := fresh_varE (union nms nms0) Empty (Annot eN t')) in Hy. 
      simpl in Hy; destruct Hy as [Hfv [Hftv [Hnms Hemp]]]. 
      apply not_elem_union_elim in Hnms; destruct Hnms;
      apply not_elem_union_elim in Hfv; destruct Hfv as [Hfv Hfv'];
      apply not_elem_union_elim in Hftv; destruct Hftv as [Hftv Hftv'];
      pose proof lem_subFV_notin as Hnot. 
      destruct Hnot as [Hnot_e [Hnot_t _]].

      rewrite <- Hnot_e with eN y (Nil t0); 
      try rewrite <- Hnot_t with t' y (Nil t0);
      try apply lem_subst_typ_top 
        with (TList t (PCons (eq (Ic 0) (length t (BV 0))) ps));
      try apply H2; 
      try apply TSub 
        with (TList t0 (PCons (eq (Ic 0) (length t0 (BV 0))) PEmpty)) Star;
      try apply TNil with Star;
      try apply lem_wflist_len_zero;

      try apply SList with (union nms nms0);
      try apply p_s'_t; intros;
      try apply not_elem_union_elim in H14; try destruct H14;
      try apply WFEEmpty; auto.

      assert (
        unbindP y0 (PCons (eq (Ic 0) (length t (BV 0))) ps)
            = strengthen 
                (unbindP y0 (PCons (eq (Ic 0) (length t (BV 0))) PEmpty)) 
                (unbindP y0 ps) )
        as Hpred by reflexivity; try rewrite Hpred.
      apply IConj; try apply H11;
      unfold unbindP; simpl;
      try rewrite Hopt with t  0 0 y0;
      try rewrite Hopt with t0 0 0 y0;
      try apply ILenSub; try apply val_Ic;
      try apply lem_weaken_subtype_top with Star Star;
      try apply (lem_wflist_wftype Empty t ps Star);
      try apply WFEEmpty; trivial.  
    * (* e = Cons t0 v1 v2 *)  clear H3 H5 IHp_e_t.
      (* We must have Switch e eN eC ~> App (App eC v1) v2 *)
      inversion H6; subst t1 e0_1 e0_2.
      apply lem_sem_det 
        with (Switch (Cons t0 v1 v2) eN eC) e'' (App (App eC v1) v2) 
        in st_e_e'' as He''; try apply ESwitchC;
        try assumption; subst e''. 

      (* Invert the typing judgment for e *)
      apply lem_invert_tlist in p_e_t as Hinv_t;
      try destruct Hinv_t as [ps' [p_v1_t p_v2_tps']];
      try apply lem_invert_cons in p_e_t as Hinv;
      try destruct Hinv 
        as [rs [p_s'_t [p_emp_s' [Hs'1 [Hs'2 
              [p_v1_s' [p_v2_s'rs p_ls'_ltps]]]]]]];
      try inversion p_ls'_ltps;
      try unfold unbindT in H12; try simpl in H12;
      try apply lem_wftype_islct in p_emp_s' as Hlcs';
      try unfold isLCT in Hlcs';
      try apply WFEEmpty; try apply p_emp_t; trivial.
      pose proof lem_islc_at_weaken as [Hwke [Hwkt _]].

      
      (* boilerplate: set up our fresh variables *)
      pose proof (fresh_varE_not_elem (union nms nms0) Empty (Annot eC t')) 
        as Hy; 
      set (y := fresh_varE (union nms nms0) Empty (Annot eC t')) in Hy; 
      simpl in Hy; destruct Hy as [Hyfv [Hyftv [Hynms Hemp]]]; 
      apply not_elem_union_elim in Hynms; destruct Hynms;
      apply not_elem_union_elim in Hyfv; 
      destruct Hyfv as [Hyfv Hyfv'];
      apply not_elem_union_elim in Hyftv; 
      destruct Hyftv as [Hyftv Hyftv'];

      try apply H12 in H14 as p_y_ls'_lt;
      try rewrite Hopt with t0 0 0 y in p_y_ls'_lt;
      try rewrite Hopt with t0 1 0 y in p_y_ls'_lt;
      try apply Hwkt with 0 0; auto;
      inversion p_y_ls'_lt; try subst g0 t1 p1 t2 p2.

      pose proof (fresh_varE_not_elem (names_add y nms) Empty eC) as Hz; 
      set (z := fresh_varE (names_add y nms) Empty eC) in Hz. 
      simpl in Hz; destruct Hz as [Hfv' [Hftv' [Hynms' Hemp']]].
      apply not_elem_names_add_elim in Hynms';
      destruct Hynms' as [Hzy Hnms'].

      apply lem_free_bound_in_env with Empty t' k y in H1 as Hfr'; 
      try apply Hemp; destruct Hfr' as [Hfr' _];
      apply lem_free_bound_in_env with Empty (TList t ps) Star y 
        in p_emp_t as Hfr;  
      try apply Hemp; destruct Hfr as [Hfr _]; simpl in Hfr;
      apply not_elem_union_elim in Hfr; destruct Hfr as [Hfr HfvP];

      apply lem_free_bound_in_env with Empty t' k z in H1 as Hzfr'; 
      try apply Hemp; destruct Hzfr' as [Hzfr' _];      
      apply lem_free_bound_in_env with Empty (TList t ps) Star z 
        in p_emp_t as Hzfr;  
      try apply Hemp; destruct Hzfr as [Hzfr _]; simpl in Hzfr;
      apply not_elem_union_elim in Hzfr; destruct Hzfr as [Hzfr HzfvP].

      (* setup more judgments *)
      pose proof lem_subFV_notin as Hnot; 
      destruct Hnot as [Hnot_e [Hnot_t _]].
      assert (WFtype Empty t' Star) as p_emp_t'
        by (destruct k; try apply H1; apply WFKind; apply H1);
      apply lem_wftype_islct in p_emp_t' as Hlct' .
      apply lem_typ_islc in p_e_t as Hlcv;
      try apply WFEEmpty; unfold isLC in Hlcv;
      destruct Hlcv as [Hlct0 [Hlcv1 Hlcv2]];
      assert (WFtype Empty t Star) as p_emp_t_star
        by (apply lem_wflist_wftype with ps Star; trivial);
      assert (WFtype Empty (TList t PEmpty) Star) as p_emp_lt_star
        by (apply WFList with Star; trivial);
      assert (Hastype Empty v2 (TList t0 PEmpty)) as p_v2_ls'
        by (apply TSub with (TList t0 rs) Star;
            try apply SList with empty;
            try apply lem_sub_refl with Star;
            try apply WFList with Star;
            intros; unfold unbindP; simpl; 
            try apply IFaith; trivial);
      apply lem_erase_subtype in p_s'_t as Hersub.

      (* Goal: Hastype Empty (App (App eC v1) v2) t' *)
      apply TSub with 
        (TExists (TList t (PCons (eq (length t v2) 
                                     (length t (BV 0))) PEmpty)) 
                 t') k;
      try apply TApp;
      try apply SBind with empty; intros; unfold unbindT;
      try rewrite Hopt with t' 0 0 y0;
      try apply lem_sub_refl with Star;
      try apply lem_weaken_wf_top; 
      try apply lem_list_eq_length; 
      try apply WFEEmpty; trivial;

      match goal with
      | [ |- Hastype _ (App eC v1) ?ltt' ]
              => apply TSub with (TExists t ltt') Star
      | [ |- Hastype _ v2 _ ]
              => apply TSub with (TList t0 rs) Star;
                try apply SList with empty; intros;
                unfold unbindP; simpl; try apply IFaith; trivial
      end;
        (*  (TFunc (TList t (PCons (eq (length t (FV y)) 
                                       (length t (BV 0))) PEmpty)) 
                 t')) Star.*)
      try apply TApp;
      try apply WFFunc with Star Star (binds g);
      try apply lem_typing_hasftype in p_v2_tps' as p_v2_erlt;
      try apply lem_wflist_eq_length; intros; unfold unbindT;
      try rewrite Hopt with t' 0 0 y0;
      try apply lem_weaken_wf_top; 
      try apply WFEEmpty; trivial;

      try apply SBind with empty; intros;
      unfold unbindT; unfold isLCT; simpl; try repeat split; 
      try rewrite Hopt with t  0 0 y0;
      try rewrite Hopt with t  1 0 y0;
      try rewrite Hopt with t' 1 0 y0;
      try rewrite Hope with v2 1 0 y0;
      try apply Hwke with 0 0;
      try apply Hwkt with 0 0; auto;
      try apply SFunc with (singleton y0);
      try apply SList with (singleton y0);
      intros; try apply lem_sub_refl with Star; 
      try apply IRefl; unfold unbindT;
      try rewrite Hopt with t' 0 0 y1;
      try repeat apply lem_weaken_wf_top;   trivial.
      
      (* (1) eC typing: substitution *)
      try rewrite <- Hnot_e with eC y v2;
      try assert (y =? y = true) as Hyeq 
        by (apply Nat.eqb_eq; reflexivity);
      try assert (
        TFunc t (TFunc (TList t (PCons (eq (length t v2) 
                                           (length t (BV 0)))
                                PEmpty)) t')
          = tsubFV y v2
              (TFunc t (TFunc (TList t (PCons (eq (length t (FV y))
                                                  (length t (BV 0)))
                                      PEmpty)) t'))
      ) as Htsub by (unfold eq; unfold length; unfold tsubFV; 
                     fold tsubFV; fold subFV; rewrite Hnot_t; 
                     try rewrite Hyeq; try rewrite Hnot_t; trivial);
      try rewrite Htsub;
      (*try apply lem_subst_typ_top with (TList t PEmpty);*)
      try apply lem_subst_typ_top with (TList t0 (PCons (eqlLenPred t0 v2) PEmpty)) (*rs*);

      try rewrite <- Hnot_e with eC z (Cons t0 v1 v2);
      try rewrite <- Hnot_t with 
        (TFunc t (TFunc (TList t (PCons (eq (length t (FV y)) 
                                            (length t (BV 0))) PEmpty)) 
                        t')) z (Cons t0 v1 v2);
      try apply lem_subst_typ_top 
        with (TList t (PCons (eq (App (Prim Succ) (length t (FV y))) 
                                 (length t (BV 0))) ps)); auto;
      assert ( 
        ECons z (TList t (PCons (eq (App (Prim Succ) (length t (FV y))) 
                                    (length t (BV 0))) ps)) 
          (ECons y (TList t0 (PCons (eqlLenPred t0 v2) PEmpty)) (*rs*) Empty)
        = concatE (ECons y (TList t0 (PCons (eqlLenPred t0 v2) PEmpty)) (*rs*) Empty)
            (ECons z (TList t (PCons (eq (App (Prim Succ) (length t (FV y))) 
                                    (length t (BV 0))) ps)) Empty)
      ) as Henv_eC by reflexivity; try rewrite Henv_eC; 
      try apply lem_narrow_typ with (TList t PEmpty) Star Star;
      try apply H4; try split;

      try apply SList with empty;
      intros; unfold unbindP; simpl; try apply IFaith;

      try apply lem_list_eq_length;
      
      try apply WFEBind with Star;
      try apply WFEBind with Star;
      try apply lem_wflist_eq_length;
      try apply lem_wflist_eq_succ_length;
      try apply lem_typing_hasftype in p_v2_s'rs as p_v2_erls';
      try apply lem_weaken_wf_top; try apply p_emp_t;
      try apply WFList with Star;

      try (apply FTVar; simpl; rewrite Hersub);
      try rewrite Hnot_e;
      try repeat apply not_elem_union_intro;
      try apply not_elem_names_add_intro; try split;
      try apply not_elem_union_intro;
      try apply WFEEmpty; auto.

      (* Final Goal:
            Hastype (ECons y (TList t0 (PCons (eqlLenPred t0 v2) PEmpty)) Empty) 
                    (Cons t0 v1 v2) (TList t (PCons (eq (App (Prim Succ) (length t (FV y))) 
                                                                         (length t (BV 0))) ps)) 
          can be settled by TCons if we can prove: *)
      assert (
        Subtype (ECons y (TList t0 (PCons (eqlLenPred t0 v2) PEmpty)) Empty) 
          (TExists (TList t0 (PCons (eqlLenPred t0 v2) PEmpty)) 
                (TList t0 (PCons (eq (App (Prim Succ) (length t0 (BV 1))) (length t0 (BV 0))) PEmpty))) 
          (* intermediate:
          (TExists (TList t0 rs) 
                (TList t0 (PCons (eq (App (Prim Succ) (length t0 (BV 1))) (length t0 (BV 0))) PEmpty)))    
          *)
          (TList t (PCons (eq (App (Prim Succ) (length t (FV y))) (length t (BV 0))) ps)) 
      ) as H_ls'_tps
        by ( pose proof lem_subBV_at_lc_at as [Hsbe [Hsbt _]];
            apply lem_typing_wf in p_v2_s'rs as p_s'rs; try apply WFEEmpty;
            apply lem_wftype_islct in p_s'rs; 
            unfold isLCT in p_s'rs; simpl in p_s'rs;
            apply lem_exists_list_subtype_conj;
            try match goal with 
                | [ |- Subtype _ _ (TList _ (PCons _ _)) ] 
                      => apply lem_sub_trans with 
                            (TList t0 (PCons (eq (App (Prim Succ) (length t0 v2)) 
                                                 (length t0 (BV 0))) PEmpty)) Star Star Star      
                | [ |- Subtype _ _ (TList _ ps) ] 
                      => apply lem_sub_trans with 
                            (TExists (TList t0 rs) 
                                (TList t0 (PCons (eq (App (Prim Succ) (length t0 (BV 1))) 
                                                     (length t0 (BV 0))) PEmpty))) Star Star Star
                end;
            try match goal with
                | [ |- Subtype _ _ (TList t ps)]
                      => apply lem_weaken_subtype_top with Star Star
            end;
            try apply p_ls'_ltps;
            try apply WFEBind with Star;
            try apply WFExis with Star (singleton y);              

            try apply SBind with (singleton y); 
            intros; unfold unbindT; simpl;    
            try apply not_elem_names_add_elim in H15; try destruct H15;
            try rewrite Hopt with t0 0 0 y0;
            try rewrite Hopt with t0 1 0 y0;
            unfold isLCT; simpl; try repeat split;
            try apply SWitn with v2;
            unfold tsubBV; simpl;
            try rewrite Hsbt with t0 0 v2 0 0;
            try rewrite Hsbt with t0 1 v2 0 0;

            try apply lem_sub_refl with Star;
            try apply SList with (names_add y0 (singleton y));
            try intros y1 Hy1; unfold unbindP; simpl;
            try apply not_elem_names_add_elim in Hy1; try destruct Hy1 as [Hy1 Hy1'];
            try apply not_elem_names_add_elim in Hy1'; try destruct Hy1';
            try apply SList with (singleton y);
            try intros y1 Hy1; unfold unbindP; simpl;
            try apply not_elem_names_add_elim in Hy1; try destruct Hy1 as [Hy1 Hy1'];
            try apply lem_sub_refl with Star;
            try rewrite Hope with v2 0 0 y1;
            try rewrite Hopt with t0 0 0 y1;
            try rewrite Hopt with t 0 0 y1;

            try assert (y0 =? y0 = true) as Hy0eq 
              by (apply Nat.eqb_eq; reflexivity);
            try assert (y0 =? y1 = false) 
              as Hny0eq by (apply Nat.eqb_neq; symmetry; trivial);
            try assert (
              PCons (App (App (Prim Eq) (App (Prim Succ) (App (AppT (Prim Length) t0) v2))) 
                         (App (AppT (Prim Length) t0) (FV y1))) PEmpty
              = psubFV y0 v2 (PCons (App (App (Prim Eq) (App (Prim Succ) (App (AppT (Prim Length) t0) (FV y0)))) 
                                         (App (AppT (Prim Length) t0) (FV y1))) PEmpty)
            ) as Hexact0 by ( unfold psubFV; fold tsubFV;
                              rewrite Hy0eq; rewrite Hny0eq; rewrite Hnot_t;
                              try apply lem_free_bound_in_env with Empty Star; trivial);
            try rewrite Hexact0;
            try apply IExactLen with t0 PEmpty;

            try assert (y =? y1 = false) 
              as Hnyeq by (apply Nat.eqb_neq; symmetry; trivial);
            try assert (
              PCons (App (App (Prim Eq) (App (Prim Succ) (App (AppT (Prim Length) t0) v2))) 
                         (App (AppT (Prim Length) t0) (FV y1))) PEmpty
              = psubFV y v2 (PCons (App (App (Prim Eq) (App (Prim Succ) (App (AppT (Prim Length) t0) (FV y)))) 
                                        (App (AppT (Prim Length) t0) (FV y1))) PEmpty)
            ) as Hexact by ( unfold psubFV; fold tsubFV;
                             rewrite Hyeq; rewrite Hnyeq; rewrite Hnot_t;
                             try apply lem_free_bound_in_env with Empty Star; trivial);
            try rewrite Hexact;
            try apply ITrans with 
              (PCons (App (App (Prim Eq) (App (Prim Succ) (App (AppT (Prim Length) t0) (FV y)))) 
                          (App (AppT (Prim Length) t0) (FV y1))) PEmpty);
            try apply ILenSub2; try apply val_FV;
            try apply IExactLenRev with t0 PEmpty;
            
            try repeat apply lem_weaken_subtype_top with Star Star;
            try repeat apply lem_weaken_typ_top;

            try repeat apply WFEBind with Star;
            try apply lem_wflist_eq_succ_length;
            try apply lem_wflist_eq_length;
            try apply WFList with Star;
            try repeat apply lem_weaken_wf_top;
            try ( apply lem_typing_wf with v2; 
                  try apply p_v2_s'rs; apply WFEEmpty);
            simpl in p_v2_erlt; simpl in p_v2_erls';
            try apply FTVar; simpl;
            try apply lem_weaken_ftyp_top;

            try rewrite Hersub; unfold in_env;
            try apply not_elem_names_add_intro; (*try split;*)
            try repeat apply not_elem_union_intro;
            fold freeTV; try apply lem_free_bound_in_env with Empty Star;
            try apply lem_fv_bound_in_env with Empty (TList t0 PEmpty);
            try apply WFEEmpty; simpl; try split;
            try apply Hwke with 0 0;
            try apply Hwkt with 0 0; 
            try apply not_elem_sing in H5; intuition).
      
      apply TSub with  (* second subtyping obligation *)
        (TExists (TList t0 (PCons (eq (length t0 v2) (length t0 (BV 0))) PEmpty))
          (TList t0 (PCons (eq (App (Prim Succ) (length t0 (BV 1))) 
                              (length t0 (BV 0))) PEmpty))) Star;
      try apply TCons;
      try apply lem_weaken_typ_top;
      try apply lem_list_eq_length; 
      try apply lem_narrow_wf_top with (TList t PEmpty);
      try apply SList with empty;
      intros; unfold unbindP; try apply IFaith;
      try apply lem_wflist_len_succ;
      try apply wfenv_unique; try apply WFEEmpty; trivial. 
  - (* TSub e, s <: t *) apply TSub with s k; try apply IHp_e_t; trivial.
Qed.
  
Theorem thm_preservation : forall (e:expr) (t:type) (e':expr),
    Hastype Empty e t -> Step e e' -> Hastype Empty e' t.
Proof. intros; apply thm_preservation' with Empty e; trivial. Qed.

Theorem thm_many_preservation : forall (e e':expr) (t:type),
    EvalsTo e e' -> Hastype Empty e t -> Hastype Empty e' t.
Proof. intros e e' t ev_e_e'; induction ev_e_e'.
  - (* Refl  *) trivial.
  - (* AddSt *) intro p_e1_t; apply IHev_e_e'; 
    apply thm_preservation with e1; assumption. Qed.

Theorem thm_soundness : forall (e e':expr) (t:type),
    EvalsTo e e' -> Hastype Empty e t -> isValue e' \/  exists e'', Step e' e''.
Proof. intros e e' t ev_e_e'; induction ev_e_e'.
  - (* Refl *) intro p_e_t; apply thm_progress with t; apply p_e_t.
  - (* AddStep *) intro p_e1_t; apply IHev_e_e'; 
    apply thm_preservation with e1; trivial. Qed.