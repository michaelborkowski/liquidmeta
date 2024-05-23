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
Require Import SystemRF.LemmasTyping.
Require Import SystemRF.LemmasSubtyping.
Require Import SystemRF.LemmasExactness.
Require Import SystemRF.SubstitutionLemmaTyp.
Require Import SystemRF.SubstitutionLemmaTypTV.
Require Import SystemRF.LemmasNarrowing.
Require Import SystemRF.LemmasInversion.
Require Import SystemRF.PrimitivesDeltaTyping.

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
    * (* App (AppT Length t) *)
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
      subst e''; inversion pf; subst e';

      inversion p_e_t2; subst t_x.
      simpl.

        pose proof lem_deltaM_typ.

        pose proof lem_deltaM_ftyp.
    | EPrimM : forall (c : prim) (t : type) (w : expr) (pf : isCompatM c w),
          isValue w -> Step (App (AppT (Prim c) t) w) (deltaM c w pf) 

        inversion H7; rewrite <- H19 in H6; unfold ftsubBV in H6; 
        injection H6 as H6 H6'; subst b. 
        
        apply lem_deltaM_ftyp with Length k t' e2 (erase t) in H4 as He'; 
        simpl; trivial.  destruct He' as [del He']; destruct He'.
        assert (del = deltaM Length e2 pf)
          by (rewrite <- (deltaM_deltaM' Length e2 pf) in H16; 
              injection H16 as H16; assumption).
        subst del; assert (e' = deltaM Length e2 pf)
          by (apply lem_sem_det with (App (AppT (Prim Length) t) e2); 
              try apply EPrimM; assumption);
        subst e' t0 b'; assumption.
  - (* TAppT e t *) apply thm_progress in p_e_t as Hprog;
    destruct e eqn:E; simpl in Hprog;
    (* impossible cases: *)
    apply lem_typing_hasftype in p_e_t as p_e_ert; try simpl in p_e_ert;
    try assert (isValue e) as Hval by (subst e; simpl; tauto); try apply WFEEmpty;
    try apply lemma_tfunction_values with e k (erase s) in Hval as Hfval;
    try (rewrite E; apply p_e_ert);
    try (subst e; simpl in Hfval; contradiction);
    (* e not value: *)
    rewrite <- E in st_e_e'';
    try assert (exists e1 : expr, Step e e1) as HStep1 
        by (rewrite E; intuition; apply Hprog);
    try ( destruct HStep1 as [e1 HStep1]; 
          apply lem_sem_det with (AppT e t) e'' (AppT e1 t) in st_e_e'' as He'';
          try apply EAppT; try assumption; subst e'';
          apply TAppT with k; try apply IHp_e_t; subst e; trivial ).
    * (* AppT (Prim p) t *) 
      assert (Hastype Empty (AppT (Prim p) t) (tsubBTV t s))
        by (apply TAppT with k; assumption).
      pose proof (lem_prim_compatT_in_tappT p t (tsubBTV t s) H0 H2) as pf;
      apply compatT_prop_set in pf; subst e;
      apply lem_sem_det with (AppT (Prim p) t) e'' (deltaT p t pf) in st_e_e'' 
        as He''; try apply EPrimT; try assumption; subst e'';
      pose proof (lem_deltaT_typ p t k s H H0 p_e_t H1) as He'';
      rewrite deltaT_deltaT' with p t pf in He''; destruct He'';
      destruct H3; injection H3 as H3; subst x; assumption.
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
      try apply WFEEmpty; trivial.
  - (* TLet e_x e *) apply thm_progress in p_e_t as Hprog; destruct Hprog.
    * (* e_x is a value *)
      apply lem_sem_det with (Let e_x e) e'' (subBV e_x e) in st_e_e'';
      try apply ELetV; try apply H2; subst e'';
      pose proof (fresh_not_elem nms) as Hy; set (y := fresh nms) in Hy;
      rewrite lem_subFV_unbind with y e_x e;
      pose proof lem_subFV_notin as Hnot; destruct Hnot as [_ Hnot];
      destruct Hnot as [Hnot _]; try rewrite <- Hnot with t y e_x;
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
      destruct Hfv; destruct Hfr; trivial;
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