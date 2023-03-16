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
    (* values *) auto; right.
  - (* App e e' *) inversion p_e_t1; 
    try simpl in H0; try contradiction;
    destruct IHp_e_t1 as [H'|H']; try reflexivity; 
    (* consider e not a value *)
    try (subst e; simpl in H'; contradiction);
    try ( destruct H' as [e1' H']; exists (App e1' e'); apply EApp1; 
          subst e; try subst t0; assumption);
    (* else e must be a value *)
    (* consider e' not a value *)
    destruct IHp_e_t2 as [H''|H'']; try reflexivity;
    try ( destruct H'' as [e'' H'']; exists (App e e''); 
          subst e; apply EApp2; assumption );
    (* then e and e' are both values *)
    apply lem_typing_hasftype in p_e_t1 as p_e_ert1; 
    try apply WFEEmpty; simpl in p_e_ert1;
    apply lemma_function_values with e (erase t_x) (erase t) in H'; trivial;
    try destruct e eqn:E; try discriminate H0; try discriminate H2;
    simpl in H'; try contradiction;
    (* either e = Prim c ...*)
    try (injection H0 as H0; subst c);
    try ( assert (Hastype Empty (App (Prim p) e') (TExists t_x t)) as p_pe'_txt
            by (apply TApp; trivial);
          pose proof (lem_prim_compat_in_tapp p e' (TExists t_x t) 
                        H'' p_pe'_txt) as pf;
          apply compat_prop_set in pf; exists (delta p e' pf); 
          apply EPrim; trivial );
    (* ... or e = Lambda e1 *)
    try (injection H2 as H2; subst e0);
    exists (subBV e' e1); apply EAppAbs; assumption.
  - (* AppT e rt *) inversion p_e_t;
    try simpl in H2; try contradiction;
    destruct IHp_e_t as [H'|H']; try reflexivity;
    (* consider e not a value *)
    try (subst e; simpl in H'; contradiction);
    try (destruct H' as [e' H']; exists (AppT e' t); apply EAppT;
          subst e; try subst k0; try subst t0; assumption);
    (* else e must be a value *)
    apply lem_typing_hasftype in p_e_t as p_e_ert; 
    try apply WFEEmpty; simpl in p_e_ert;
    apply lemma_tfunction_values with e k (erase s) in H'; trivial;
    try destruct e eqn:E; try discriminate H2; try discriminate H3; 
    simpl in H'; try contradiction;
    (* either e = Prim c ...*)
    try (injection H2 as H2; subst c);
    try ( assert (Hastype Empty (AppT (Prim p) t) (tsubBTV t s)) as p_pt_st
            by (apply TAppT with k; trivial);
          pose proof (lem_prim_compatT_in_tappT p t (tsubBTV t s)
                        H p_pt_st) as pf;
          apply compatT_prop_set in pf; exists (deltaT p t pf); 
          apply EPrimT; trivial );
    (* ... or e = LambdaT k e1 *)
    try (injection H3 as Hk0 He0; subst e0; subst k0 k);
    exists (subBTV t e1); apply EAppTAbs; assumption.
  - (* Let e_x e *) destruct IHp_e_t; try reflexivity.
      * (* e_x val *) exists (subBV e_x e); apply ELetV; apply H2.
      * (* otherw. *) destruct H2 as [e_x' H2]; exists (Let e_x' e);
        apply ELet; apply H2.
  - (* Annot e t1 *) destruct IHp_e_t; try reflexivity.
      * (* e val *) exists e; apply EAnnV; apply H0.
      * (* other *) destruct H0 as [e'' H0]; exists (Annot e'' t); apply EAnn; apply H0.
  - (* If e1 e2 e3 *) destruct IHp_e_t; try reflexivity.
      * (* e0 val *) apply lem_typing_hasftype in p_e_t as p_e_ert;
        try apply lem_bool_values in p_e_ert as H_bool; 
        try assumption; try apply WFEEmpty.
        destruct e0; simpl in H_bool; try contradiction;
        destruct b; (exists e1; apply EIfT) || (exists e2; apply EIfF).
      * (* otherw *) destruct H4 as [e0' st_e0_e0']; exists (If e0' e1 e2); 
        apply EIf; apply st_e0_e0'.
  Qed.

Theorem thm_progress : forall (e:expr) (t:type),
    Hastype Empty e t -> isValue e \/ exists e'', Step e e''.
Proof. intros; apply thm_progress' with Empty t; apply H || reflexivity. Qed.
  
Theorem thm_preservation' : forall (g:env) (e:expr) (t:type) (e':expr),
    Hastype g e t -> g = Empty -> Step e e' -> Hastype Empty e' t.
Proof. intros g e t e' p_e_t; revert e'; induction p_e_t; 
  intros e'' emp st_e_e''; simpl; subst g;
  apply lem_value_stuck in st_e_e'' as H'; simpl in H'; try contradiction.
  - (* TApp e e' *) apply thm_progress in p_e_t1 as Hprog;
    destruct e eqn:E; simpl in Hprog;
    (* impossible cases: *)
    apply lem_typing_hasftype in p_e_t1 as p_e_ert1; try simpl in p_e_ert1;
    try assert (isValue e) as Hval by (subst e; simpl; tauto); try apply WFEEmpty;
    try apply lemma_function_values with e (erase t_x) (erase t) in Hval as Hfval;
    try (rewrite E; apply p_e_ert1);
    try (subst e; simpl in Hfval; contradiction);
    (* e not value: *)
    rewrite <- E in st_e_e'';
    try assert (exists e1 : expr, Step e e1) as HStep1 
        by (rewrite E; intuition; apply Hprog);
    try ( destruct HStep1 as [e1 HStep1]; 
          apply lem_sem_det with (App e e') e'' (App e1 e') in st_e_e'' as He'';
          try apply EApp1; try assumption; subst e'';
          apply TApp; apply IHp_e_t1 || apply p_e_t2; subst e; trivial );
    apply thm_progress in p_e_t2 as Hprog'; destruct Hprog';   
    (* e' not a value *)
    try ( destruct H as [e'1 H];
          apply lem_sem_det with (App e e') e'' (App e e'1) in st_e_e'' as He'';
          try apply EApp2; try assumption; subst e'';
          apply TApp; (subst e; apply p_e_t1) || apply IHp_e_t2; trivial ).
    * (* App (Prim p) val *) 
      assert (Hastype Empty (App (Prim p) e') (TExists t_x t))
        by (apply TApp; assumption);
      pose proof (lem_prim_compat_in_tapp p e' (TExists t_x t) H H0) as pf;
      apply compat_prop_set in pf; subst e;
      apply lem_sem_det with (App (Prim p) e') e'' (delta p e' pf) in st_e_e'' 
        as He''; try apply EPrim; try assumption; subst e'';
      pose proof (lem_delta_typ p e' t_x t H p_e_t1 p_e_t2) as He''.
      rewrite <- delta_delta' with p e' pf in He''; destruct He''; 
      destruct H1; injection H1 as H1; subst x; assumption.
    * (* App (Lambda e0) val *) subst e;
      assert (Hastype Empty (App (Lambda e0) e') (TExists t_x t)) as p_ee'_txt
        by (apply TApp; assumption);
      apply lem_sem_det with (App (Lambda e0) e') e'' (subBV e' e0) in st_e_e'' 
        as He''; try apply EAppAbs; try assumption; subst e'';
      apply lem_typing_wf in p_e_t1 as p_emp_txt; try apply WFEEmpty;
      pose proof lem_invert_tabs Empty e0 t_x t p_e_t1 WFEEmpty p_emp_txt;
      destruct H0 as [nms p_e0_t];
      pose proof (fresh_not_elem nms) as Hy; set (y := fresh nms) in Hy;
      rewrite lem_subFV_unbind with y e' e0;
      try apply TSub with (tsubFV  y e' (unbindT y t)) Star;
      try apply lem_subst_typ_top with t_x; try apply p_e0_t;
      try rewrite <- lem_tsubFV_unbindT; try apply lem_witness_sub with Star;
      try apply lem_typing_wf with (App (Lambda e0) e');
      pose proof lem_fv_bound_in_fenv FEmpty (Lambda e0) 
                    (FTFunc (erase t_x) (erase t)) y p_e_ert1 as Hfv;
      pose proof lem_free_bound_in_env Empty (TFunc t_x t) Star y p_emp_txt as Hfr;
      destruct Hfv; destruct Hfr; try simpl in H2;
      try apply not_elem_union_elim in H2; try destruct H2;
      try apply WFEEmpty; trivial.
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
      pose proof (lem_prim_compatT_in_tappT p t (tsubBTV t s) H H1) as pf;
      apply compatT_prop_set in pf; subst e;
      apply lem_sem_det with (AppT (Prim p) t) e'' (deltaT p t pf) in st_e_e'' 
        as He''; try apply EPrimT; try assumption; subst e'';
      pose proof (lem_deltaT_typ p t k s H p_e_t H0) as He'';
      rewrite deltaT_deltaT' with p t pf in He''; destruct He'';
      destruct H2; injection H2 as H2; subst x; assumption.
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
  - (* FTIf *) apply thm_progress in p_e_t as Hprog; destruct Hprog.
    * (* e0 value *) apply lem_typing_hasftype in p_e_t as p_e_ert;
      (*try apply lem_typing_wf in p_e_t as p_emp_t;*)
      try apply lem_bool_values in p_e_ert as H_bool; 
      try assumption; try apply WFEEmpty.
      destruct e0; simpl in H_bool; try contradiction;
      pose proof (fresh_not_elem nms) as Hy; set (y := fresh nms) in Hy;
      pose proof lem_subFV_notin as Hnot; destruct Hnot as [Hnot_e Hnot_t];
      destruct Hnot_t as [Hnot_t _];
      rewrite <- Hnot_e with e'' y (Bc true); 
      try rewrite <- Hnot_t with t y (Bc true).
      destruct b.
      + (* True  *) assert (e'' = e1) 
          by (apply lem_sem_det with (If (Bc true) e1 e2); try apply EIfT; assumption);
        subst e''. 
        
        Eval simpl in (self (TRefn TBool ps) (Bc true) Base).
        Eval simpl in (eqlPred TBool ps (Bc true)).
        
        apply lem_self
        
        
        apply lem_subst_typ_top with (TRefn TBool ps);

        try apply lem_narrow_typ_top with (TRefn TBool (PCons (BV 0) ps)) Base Base;
        try apply H0; try apply WFEEmpty;

        
        trivial. 
        apply TSub with (TRefn TBool ps) Base; try apply p_e_t.
        Focus 2.
        apply SBase with nms; intros; simpl.
        assert ( strengthen (PCons (FV y0) PEmpty) (unbindP y0 ps)
                 = unbindP y0 (PCons (BV 0) ps)) by reflexivity;
        rewrite <- H6.
        apply IConj.
        
        apply H0.
      + (* False *) assert (e'' = e2) 
          by (apply lem_sem_det with (If (Bc false) e1 e2); try apply EIfF; assumption);
        subst e''; apply H6.
    * (* otherw *) destruct H7 as [e1' st_e1_e1']; assert (e' = If e1' e2 e3)
        by (apply lem_sem_det with (If e1 e2 e3); try apply EIf; assumption);
      subst e'; apply FTIf; try assumption; apply IHe1; trivial.
  - (* Error *) inversion p_e_t.      
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