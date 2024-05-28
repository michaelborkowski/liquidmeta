Require Import SystemRF.BasicDefinitions. 
Require Import SystemRF.Names.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.PrimitivesFTyping.
Require Import SystemRF.BasicPropsWellFormedness.
Require Import SystemRF.Typing.
Require Import SystemRF.LemmasWeakenTyp.
Require Import SystemRF.LemmasWellFormedness.
Require Import SystemRF.LemmasTyping.
Require Import SystemRF.LemmasSubtyping.
Require Import SystemRF.LemmasExactness.
Require Import SystemRF.SubstitutionLemmaTyp.
Require Import SystemRF.SubstitutionLemmaTypTV.
Require Import SystemRF.LemmasNarrowing.
Require Import SystemRF.LemmasInversion.
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
    try (right; exists (Cons eH' eT)); 
    try apply ECons1; try apply st_eH_eH';
    (* eT not a value *)
    try destruct H2 as [eT' st_eT_eT'];
    try (right; exists (Cons eH eT')); 
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
    try apply lem_sem_det with (Cons eH eT) e'' (Cons eH1 eT) 
      in st_e_e'' as He'';
    try apply ECons1; try assumption; try subst e'';
    try apply TCons; try apply IHp_e_t1; try apply p_e_t2; trivial; 
    (* e' not a value *)
    try destruct H2 as [eT1 st_eT_eT1];
    try apply lem_sem_det with (Cons eH eT) e'' (Cons eH eT1) 
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
    apply lem_typing_hasftype in p_e_t as p_e_ert;
    try apply lem_typing_wf in p_e_t as p_emp_t;
    try simpl in p_e_ert; try apply WFEEmpty;
    try apply lem_wftype_islct in p_emp_t as Hlct; 
    unfold isLCT in Hlct; simpl in Hlct;
    destruct Hlct as [Hlct Hlcp1];
    pose proof lem_open_at_lc_at as [Hope [Hopt _]];
    apply lemma_list_values in p_e_ert as Hfval; 
    try apply H6; destruct e eqn:E; simpl in Hfval; try contradiction.
    * (* e = Nil *) clear H3 H5 IHp_e_t.
      apply lem_sem_det with (Switch Nil eN eC) e'' eN 
        in st_e_e'' as He''; try apply ESwitchN; subst e''.
      
      try apply lem_invert_nil in p_e_t as Hinv ; 
      try destruct Hinv 
        as [s' [p_s'_t [p_emp_s' [Hs'1 [Hs'2 p_ls'_ltps]]]]];
      try inversion p_ls'_ltps;
      try apply lem_wftype_islct in p_emp_s' as Hlcs';
      try unfold isLCT in Hlcs';
      try apply WFEEmpty; try apply p_emp_t.
      
      pose proof (fresh_varE_not_elem (union nms nms0) Empty (Annot eN t')) 
        as Hy; 
      set (y := fresh_varE (union nms nms0) Empty (Annot eN t')) in Hy. 
      simpl in Hy; destruct Hy as [Hfv [Hftv [Hnms Hemp]]]. 
      apply not_elem_union_elim in Hnms; destruct Hnms;
      apply not_elem_union_elim in Hfv; destruct Hfv as [Hfv Hfv'];
      apply not_elem_union_elim in Hftv; destruct Hftv as [Hftv Hftv'];
      pose proof lem_subFV_notin as Hnot. 
      destruct Hnot as [Hnot_e [Hnot_t _]].

      rewrite <- Hnot_e with eN y Nil; 
      try rewrite <- Hnot_t with t' y Nil;
      try apply lem_subst_typ_top 
        with (TList t (PCons (eq (Ic 0) (length t (BV 0))) ps));
      try apply H2; 
      try apply TSub 
        with (TList s' (PCons (eq (Ic 0) (length s' (BV 0))) PEmpty)) Star;
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
      try rewrite Hopt with s' 0 0 y0;
      try apply ILenSub; 
      try apply lem_weaken_subtype_top with Star Star;
      try apply (lem_wflist_wftype Empty t ps Star);
      try apply WFEEmpty; trivial. 
    * (* e = Cons v1 v2 *)  clear H3 H5 IHp_e_t.
      inversion H6; subst e0_1 e0_2.
      apply lem_sem_det 
        with (Switch (Cons v1 v2) eN eC) e'' (App (App eC v1) v2) 
        in st_e_e'' as He''; try apply ESwitchC;
        try assumption; subst e''. 

      pose proof (fresh_varE_not_elem nms Empty eC) as Hy; 
      set (y := fresh_varE nms Empty eC) in Hy. 
      simpl in Hy; destruct Hy as [Hfv [Hftv [Hnms Hemp]]].   
      apply lem_free_bound_in_env with Empty t' k y in H1 as Hfr'; 
      try apply Hemp; destruct Hfr' as [Hfr' _].
      apply lem_free_bound_in_env with Empty (TList t ps) Star y 
        in p_emp_t as Hfr;  
      try apply Hemp; destruct Hfr as [Hfr _]; simpl in Hfr;
      apply not_elem_union_elim in Hfr; destruct Hfr as [Hfr HfvP].
      pose proof lem_subFV_notin as Hnot; 
      destruct Hnot as [Hnot_e [Hnot_t _]].

      apply TSub with 
        (TExists (TList t (PCons (eq (length t (Cons v1 v2)) 
                                     (App (Prim Succ) (length t (BV 0))))
                                 PEmpty))
                 t') Star;
      try apply TApp;
      try match goal with
          | [ |- Hastype _ (App eC v1) ?ltt' ]
                => apply TSub with (TExists t ltt') Star
          end;
        (*  (TFunc (TList t (PCons (eq (length t (Cons v1 v2)) 
                                     (App (Prim Succ) (length t (BV 0))))
                                 PEmpty))
                 t')) Star.*)
      try apply TApp;      
      (* eC typing: substitution *)
      try rewrite <- Hnot_e with eC y (Cons v1 v2);
      try assert (y =? y = true) by (apply Nat.eqb_eq; reflexivity);
      try assert (
        TFunc t (TFunc (TList t (PCons (eq (length t (Cons v1 v2)) 
                                           (App (Prim Succ) (length t (BV 0)))) 
                                PEmpty)) t')
          = tsubFV y (Cons v1 v2)
              (TFunc t (TFunc (TList t (PCons (eq (length t (FV y))
                                                  (App (Prim Succ) (length t (BV 0)))) 
                                      PEmpty)) t'))
      ) as Htsub by (unfold eq; unfold length; unfold tsubFV; 
                     fold tsubFV; fold subFV; rewrite Hnot_t; 
                     try rewrite H3; try rewrite Hnot_t; trivial);
      try rewrite Htsub;
      try apply lem_subst_typ_top with (TList t ps);
      try apply H4; 
      try apply wfenv_unique; try apply WFEEmpty; trivial;
      (* v1 typing: inversion lemma *)
      apply lem_invert_tlist in p_e_t as Hv1v2;
      try apply WFEEmpty; trivial;
      destruct Hv1v2 as [qs [p_v1_t p_v2_tqs]];
      try apply p_v1_t.
      (* v2 typing: inversion lemma *)
      Focus 3. pose proof TCons.

      (* 2x subtyping: SBind *)
      (* 2x wellformedness *)
      
      try apply H4. apply H4.
      
      
      apply not_elem_union_elim in Hfv; apply not_elem_union_elim in Hftv; 

      rewrite <- Hnot_e with eN y Nil; 
      try rewrite <- Hnot_t with t' y Nil;
      try apply lem_subst_typ_top 
        with (TList t (PCons (eq (Ic 0) (length t (BV 0))) ps));

      try apply TSub 
        with (TList t (PCons (eq (Ic 0) (length t (BV 0))) PEmpty)) Star;
        
        try apply TNil with Star; intuition.
      
      Focus 3.
      apply SList with nms; intros.
      Focus 2.
      pose IStren.
      assert ( unbindP y0 (PCons (eq (Ic 0) (length t (BV 0))) PEmpty)
        = strengthen (PCons (eq (Ic 0) (length t (FV y0))) PEmpty) 
                     (unbindP y0 PEmpty) )

        as Hprd1 by (
        unfold unbindP; unfold eq; unfold length; simpl; 
                      rewrite Hopt with t 0 0 y0; trivial);
      rewrite Hprd1.
      assert ( unbindP y0 (PCons (eq (Ic 0) (length t (BV 0))) ps)
        = strengthen (PCons (eq (Ic 0) (length t (FV y0))) PEmpty) 
                     (unbindP y0 ps) )

        as Hprd2 by (
        unfold unbindP; unfold eq; unfold length; simpl; 
                      rewrite Hopt with t 0 0 y0; trivial);
      rewrite Hprd2.
      apply IStren.

      Lemma lem_narrow_typ_top : 
  forall (g:env) (x:vname) (s_x t_x:type) (k_sx k_tx:kind) (e:expr) (t:type),
    Hastype (ECons x t_x g) e t
            -> unique g -> ~ (in_env x g) 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x -> WFEnv g
            -> Hastype (ECons x s_x g) e t .

      try apply TSub 
        with (TList t (PCons (eq (Ic 0) (length t (BV 0))) ps)) Star;
      try apply WFEEmpty; intuition.
      apply TNil with Star.

      pose proof TNil.
      
      apply H2 with y.

      try apply H0; try apply H2; try apply lem_exact_type;
      trivial; try apply WFEEmpty;
      inversion p_emp_t; apply H6.

    * (* e = Cons v1 v2 *)
      apply lem_sem_det 
        with (Switch (Cons v1 v2) eN eC) e'' (App (App eC v1) v2)
        in st_e_e'' as He''; try apply ESwitchC; subst e''.

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