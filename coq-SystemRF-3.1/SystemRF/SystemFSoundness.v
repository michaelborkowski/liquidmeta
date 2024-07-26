Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFWellFormedness.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.PrimitivesFTyping.
Require Import SystemRF.SystemFLemmasWellFormedness.
Require Import SystemRF.SystemFLemmasSubstitution.

(*-----------------------------------------------------------------------------
----- | SOUNDNESS of the SYSTEM F LAMBDA CALCULUS
-----------------------------------------------------------------------------*)

  (* -- The System F Progress Lemma   *)
Theorem lemma_progress' : forall (g:fenv) (e:expr) (t:ftype),
    HasFtype g e t -> g = FEmpty -> isValue e \/ exists e'', Step e e''.
Proof. intros g e t p_e_t emp; induction p_e_t; simpl; subst g;
    (* values *) try (left; constructor; assumption).
  - (* App e e' *) right; destruct e eqn:E; inversion p_e_t1;
    try (simpl in H1; contradiction);
    try (destruct IHp_e_t1 as [H'|H']; try reflexivity; inversion H'; 
         exists (App x e'); apply EApp1; trivial).
      * (* e = Prim *) destruct IHp_e_t2; try reflexivity.
        { apply lem_prim_compat_in_ftapp with p e' b' in H0 as pf;
          try apply compat_prop_set in pf; try exists (delta p e' pf); 
          try apply EPrim; try apply FTApp with b; assumption. }
        { destruct H0 as [e'' H0]; exists (App (Prim p) e''); 
          apply EApp2; constructor || trivial. }
      * (* e = Lambda e0 *) destruct IHp_e_t2; try reflexivity.
        { exists (subBV e' e0); apply EAppAbs; assumption. }      (* Left *)
        { destruct H5 as [e'' H5]; exists (App (Lambda e0) e'').  (* Right *)
          apply EApp2; constructor || trivial. }
      * (* e = AptT e0 t *) destruct IHp_e_t1; try reflexivity.
        + (* e0 = Length *) inversion H10; subst e0 e1;
          destruct IHp_e_t2 as [IH2|IH2]; try reflexivity.
          { apply lem_prim_compatM_in_ftappappt with Length t e' b' 
              in IH2 as pf; simpl; try apply I;
            try apply compatM_prop_set in pf;
            try exists (deltaM Length e' pf); try apply EPrimM;
            try apply IH2;
            apply FTApp with b; apply p_e_t1 || apply p_e_t2. }
          { destruct IH2 as [e'' st_e'_e''].
            exists (App (AppT (Prim Length) t) e''). apply EApp2; auto. }
        + (* otherwise *) destruct H10 as [e0t' st_e0t_e0t'].
          exists (App e0t' e'); apply EApp1. apply st_e0t_e0t'.
  - (* AppT e rt *) (*right;*) destruct e eqn:E; inversion p_e_t; 
    try contradiction;
    try ( destruct IHp_e_t as [H'|H']; try reflexivity; inversion H';
          try ( subst e0 e1; inversion H8; subst t'0; 
                unfold ftsubBV in H7; simpl in H7; discriminate );
          right; exists (AppT x rt); apply EAppT; trivial ).
      * (* e = Prim p *) destruct p; simpl in H8; try discriminate;
        try (left; constructor); right;
        try apply FTAppT with FEmpty (Prim Eql)  k t' rt in p_e_t as pf;
        try apply FTAppT with FEmpty (Prim Leql) k t' rt in p_e_t as pf;
        try apply lem_prim_compatT_in_ftappt in pf; try apply compatT_prop_set in pf;
        try (exists (deltaT Eql rt pf); apply EPrimT);
        try (exists (deltaT Leql rt pf); apply EPrimT);
        unfold not; trivial.
      * (* e = LambdaT k e0 *) right; exists (subBTV rt e0); apply EAppTAbs; assumption.
  - (* Let e_x e *) right; destruct IHp_e_t; try reflexivity.
      * (* e_x val *) exists (subBV e_x e); apply ELetV; apply H1.
      * (* otherw. *) destruct H1 as [e_x' H1]; exists (Let e_x' e);
        apply ELet; apply H1.
  - (* Annot e t1 *) right; destruct IHp_e_t; try reflexivity.
      * (* e val *) exists e; apply EAnnV; apply H3.
      * (* other *) destruct H3 as [e'' H3]; exists (Annot e'' t1); apply EAnn; apply H3.
  - (* If e0 e1 e2 *) right; destruct IHp_e_t1; try reflexivity.
      * (* e0 val *) apply lem_bool_values in p_e_t1 as H_bool; try assumption.
        destruct e0; simpl in H_bool; try contradiction;
        destruct b; (exists e1; apply EIfT) || (exists e2; apply EIfF).
      * (* otherw *) destruct H as [e0' st_e0_e0']; exists (If e0' e1 e2); 
        apply EIf; apply st_e0_e0'.
  - (* Cons eH eT *) destruct IHp_e_t1 as [H4|H4]; destruct IHp_e_t2 as [H5|H5];
      try reflexivity. 
      * (* Both vals *) left; constructor; assumption.
      * (* eH value *) right; destruct H5 as [eT' step]; exists (Cons rt eH eT');
        apply ECons2; assumption .
      * (* eT value *) right; destruct H4 as [eH' step]; exists (Cons rt eH' eT);
        apply ECons1; assumption .
      * (* no vals *) right; destruct H4 as [eH' step]; exists (Cons rt eH' eT);
        apply ECons1; assumption .
  - (* Switch e eN eC *) right; destruct IHp_e_t1 as [H1|H1]; try reflexivity.
      * (* e value *) inversion H1; inversion p_e_t1; subst e;
        try discriminate; try contradiction.
        + (* can't be Prim *) destruct c0; simpl in H4; discriminate.
        + (* can't be Length [t] *) injection H9 as He0 Hrt; subst e0;
          inversion H2; subst t'0; discriminate.
        + (* Nil *) exists eN; apply ESwitchN.
        + (* Cons *) exists (App (App eC v1) v2); apply ESwitchC; assumption.
      * (* e not val *) destruct H1 as [e' step]; exists (Switch e' eN eC);
        constructor; apply step.
  Qed. 

Theorem lemma_progress : forall (e:expr) (t:ftype),
    HasFtype FEmpty e t -> isValue e \/ exists e'', Step e e''.
Proof. intros; apply lemma_progress' with FEmpty t; apply H || reflexivity. Qed.
  
Theorem lemma_preservation' : forall (g:fenv) (e:expr) (t:ftype) (e':expr),
    HasFtype g e t -> g = FEmpty -> Step e e' -> HasFtype FEmpty e' t.
Proof. intros g e; induction e; intros t0 e' p_e_t emp st_e_e'; simpl; subst g;
  try (apply lem_value_stuck in st_e_e' as H'; 
       constructor || contradiction; reflexivity).
  - (* FTApp e1 e2 *) inversion p_e_t; apply lemma_progress in H2 as Hprog;
    destruct Hprog as [Hval|Hstep].
    apply lemma_progress in H4 as He2; destruct He2 as [He2|He2].
    * (* e1 and e2  value: *) inversion Hval; subst e e1; inversion H2; 
      try contradiction.
      + (* App (Prim p) val *) 
        apply (lem_prim_compat_in_ftapp c e2 t0 He2) in p_e_t as pf;
        apply compat_prop_set in pf;
        apply lem_delta_ftyp with c e2 b t0 in He2 as He'; try assumption;
        destruct He' as [del He']; destruct He';
        assert (del = delta c e2 pf)
          by (rewrite <- (delta_delta' c e2 pf) in H5; injection H5 as H5; assumption);
        subst del; assert (e' = delta c e2 pf)
          by (apply lem_sem_det with (App (Prim c) e2); 
              try apply EPrim; assumption) ;
        subst e'; assumption.
      + (* App (Length [t]) val *) 
        apply lem_prim_compatM_in_ftappappt in p_e_t as pf; simpl; trivial; 
        apply compatM_prop_set in pf.
        inversion H7; rewrite <- H19 in H6; unfold ftsubBV in H6; 
        injection H6 as H6 H6'; subst b. pose proof lem_deltaM_ftyp.
        apply lem_deltaM_ftyp with Length k t' e2 (erase t) in H4 as He'; 
        simpl; trivial.  destruct He' as [del He']; destruct He'.
        assert (del = deltaM Length e2 pf)
          by (rewrite <- (deltaM_deltaM' Length e2 pf) in H16; 
              injection H16 as H16; assumption).
        subst del; assert (e' = deltaM Length e2 pf)
          by (apply lem_sem_det with (App (AppT (Prim Length) t) e2); 
              try apply EPrimM; assumption);
        subst e' t0 b'; assumption.
      + (* App (Lambda e0) val *) assert (e' = subBV e2 e0)
          by (apply lem_sem_det with (App (Lambda e0) e2); 
              try apply EAppAbs; assumption);
        assert (FEmpty = concatF FEmpty FEmpty) as Hemp by reflexivity;
        subst e'; inversion H2; pose proof (fresh_not_elem nms);
        rewrite lem_subFV_unbind with (fresh nms) e2 e0; try rewrite Hemp;
        try apply lem_subst_ftyp with b; simpl;
        try apply H9;
        apply lem_fv_bound_in_fenv 
          with FEmpty (Lambda e0) (FTFunc b t0) (fresh nms) in H2 as Hfv; 
        try simpl in Hfv; try destruct Hfv ; auto.
    * (* e1 value, not e2 *) 
         destruct He2 as [e2' He2];
         apply IHe2 with b e2' in H4 as H4'; trivial;
         apply EApp2 with e2 e2' e1 in Hval as HStep; try assumption;
         assert (e' = App e1 e2')
           by (apply lem_sem_det with (App e1 e2); assumption);
         subst e'; try subst t0;
         try apply FTApp with b; trivial.
    * (* e1 not value: *)
        destruct Hstep as [e1' Hstep];
        apply IHe1 with (FTFunc b t0) e1' in H2;
        apply EApp1 with e1 e1' e2 in Hstep as Hstep'; 
        apply lem_sem_det with (App e1 e2) e' (App e1' e2) in st_e_e' as He';
        try subst e'; try apply FTApp with b; auto. 
  - (* FTAppT e t *) inversion p_e_t; apply lemma_progress in H1 as Hprog;
    destruct Hprog as [Hval|Hstep].
    * (* e a value *) inversion Hval; subst e e0; inversion H1; try contradiction;
      try (inversion H12; subst t'0; discriminate H11).
      + (* AppT (Prim p) t *) 
        assert (isMeasure c \/ ~ isMeasure c) as Hmeas 
          by (destruct c; simpl; intuition); destruct Hmeas as [Hmeas | Hmeas].
        { destruct c; simpl in Hmeas; try contradiction;
          apply lem_value_stuck in st_e_e'; constructor || contradiction. }
        apply lem_prim_compatT_in_ftappt in p_e_t as pf; try apply Hmeas.
        apply compatT_prop_set in pf;
        apply lem_deltaT_ftyp with c k t' t in H1 as He'; try assumption;
        destruct He' as [delT He']; destruct He'.
        assert (delT = deltaT c t pf)
          by (rewrite -> (deltaT_deltaT' c t pf) in H10; injection H10 as H10; assumption).
        subst delT; assert (e' = deltaT c t pf)
          by (apply lem_sem_det with (AppT (Prim c) t); 
              try apply EPrimT; assumption);
        subst e'; assumption.
      + (* AppT (LambdaT k0 e1) t *) assert (e' = subBTV t e1)
          by (apply lem_sem_det with (AppT (LambdaT k0 e1) t); 
              try apply EAppTAbs; assumption);
        subst e'; inversion H1; pose proof (fresh_not_elem nms);
        assert (FEmpty = concatF FEmpty (fesubFV (fresh nms) (erase t) FEmpty)) 
          as Hemp by reflexivity;
        rewrite lem_subFTV_unbind_tv with (fresh nms) t e1;
        try rewrite lem_ftsubFV_unbindFT with (fresh nms) (erase t) t';
        try rewrite Hemp; try apply lem_subst_tv_ftyp with k; simpl;
        apply lem_fv_bound_in_fenv 
          with FEmpty (LambdaT k0 e1) (FTPoly k t') (fresh nms) in H1 as Hfr1;
        apply lem_ftyping_wfft in H1;
        try apply lem_ffreeTV_bound_in_fenv
          with FEmpty (FTPoly k t') Star (fresh nms) in H1 as Hfr2;
        try simpl in Hfr1; try simpl in Hfr2; try destruct Hfr1; constructor || auto.
    * (* e not value: *)
      destruct Hstep as [e'' HStep]; 
      apply IHe with (FTPoly k t') e'' in H1;
      apply EAppT with e e'' t in HStep as HStep0; trivial;
      apply lem_sem_det with (AppT e t) e' (AppT e'' t) in st_e_e' as He';
          try subst e'; try apply FTAppT with k; auto.
  - (* FTLet e1 e2 *) inversion p_e_t; apply lemma_progress in H2 as Hprog;
    destruct Hprog.
    * (* e1 value *) assert (e' = subBV e1 e2)
        by (apply lem_sem_det with (Let e1 e2); try apply ELetV; assumption);
      subst e';
      pose proof (fresh_not_elem nms);
      assert (FEmpty = concatF FEmpty FEmpty) as Hemp by reflexivity;
      rewrite Hemp; rewrite lem_subFV_unbind with (fresh nms) e1 e2;
      try apply lem_subst_ftyp with b; simpl; try apply H4;
      apply lem_fv_bound_in_fenv 
        with FEmpty (Let e1 e2) t0 (fresh nms) in p_e_t as Hfr; 
      try simpl in Hfr; try destruct Hfr; 
      try apply not_elem_union_elim in H7; try destruct H7; auto.
    * (* otherw *) destruct H5 as [e1' H5]; assert (e' = Let e1' e2)
        by (apply lem_sem_det with (Let e1 e2); try apply ELet; assumption);
      subst e'; apply FTLet with b nms;
      try apply IHe1; assumption || reflexivity.
  - (* FTAnn e t *) inversion p_e_t; apply lemma_progress in H7 as Hprog;
    destruct Hprog.
    * (* e value *) assert (e' = e)
        by (apply lem_sem_det with (Annot e t); try apply EAnnV; assumption);
      subst e'; apply H7.
    * (* otherw *) destruct H8 as [e'' H8]; assert (e' = Annot e'' t)
        by (apply lem_sem_det with (Annot e t); try apply EAnn; assumption);
      subst e'; apply FTAnn; try apply IHe; assumption || reflexivity.
  - (* FTIf *) inversion p_e_t; apply lemma_progress in H3 as Hprog; 
    destruct Hprog.
    * (* e0 value *) apply lem_bool_values in H3 as H_bool; try assumption;
      destruct e1; simpl in H_bool; try contradiction;
      destruct b.
      + (* True  *) assert (e' = e2) 
          by (apply lem_sem_det with (If (Bc true) e2 e3); try apply EIfT; assumption);
        subst e'; apply H5.
      + (* False *) assert (e' = e3) 
          by (apply lem_sem_det with (If (Bc false) e2 e3); try apply EIfF; assumption);
        subst e'; apply H6.
    * (* otherw *) destruct H7 as [e1' st_e1_e1']; assert (e' = If e1' e2 e3)
        by (apply lem_sem_det with (If e1 e2 e3); try apply EIf; assumption);
      subst e'; apply FTIf; try assumption; apply IHe1; trivial.
  - (* FTCons *) inversion p_e_t. apply lemma_progress in H9 as Hprog;
    destruct Hprog as [Hval|Hstep].
    * (* e1 value *) apply lemma_progress in H10 as Hprog2.
      destruct Hprog2 as [Hval2|Hstep2];
      try (assert (isValue (Cons t e1 e2)) by (constructor; assumption);
           apply lem_value_stuck in st_e_e'; assumption || contradiction);
      destruct Hstep2 as [e2' Hstep2].
      assert (e' = Cons t e1 e2')
        by (apply lem_sem_det with (Cons t e1 e2); try apply ECons2; assumption);
      subst e'; apply FTCons; assumption || apply IHe2; trivial.
    * (* e1 not val *) destruct Hstep as [e1' st_e1_e1']; assert (e' = Cons t e1' e2)
        by (apply lem_sem_det with (Cons t e1 e2); try apply ECons1; assumption);
      subst e'; apply FTCons; assumption || apply IHe1; assumption || reflexivity.
  - (* FTSwitch *) inversion p_e_t; subst e1 e2 e3 t0;
    apply lemma_progress in H3 as Hprog; destruct Hprog as [Hval|Hstep].
    * (* e value *)  (* need lemma for list values! *)
      apply lemma_list_values in H3 as H3'; try apply Hval;
      destruct e; simpl in H3'; try contradiction.
      + (* e = Nil *) assert (e' = eN) 
          by (apply (lem_sem_det (Switch (Nil t0) eN eC)); try apply ESwitchN; assumption);
        subst e'; apply H5.
      + (* e = Cons *) assert (e' = (App (App eC e1) e2))
          by (apply (lem_sem_det (Switch (Cons t0 e1 e2) eN eC)); inversion Hval;
              try apply ESwitchC; assumption);
        subst e'; inversion H3; apply FTApp with (FTList t); subst t;
        try apply H14; apply FTApp with (erase t0); assumption.
    * (* e not val *) destruct Hstep as [e1 st_e_e1]; assert (e' = Switch e1 eN eC)
          by (apply lem_sem_det with (Switch e eN eC); try apply ESwitch; assumption);
        subst e'; apply FTSwit with t; assumption || apply IHe1; trivial.
  - (* Error *) inversion p_e_t.
  Qed.

Theorem lemma_preservation : forall (e:expr) (t:ftype) (e':expr),
    HasFtype FEmpty e t -> Step e e' -> HasFtype FEmpty e' t.
Proof. intros; apply lemma_preservation' with FEmpty e; assumption || reflexivity. Qed.

Theorem lemma_many_preservation : forall (e e':expr) (b:ftype),
    EvalsTo e e' -> HasFtype FEmpty e b -> HasFtype FEmpty e' b.
Proof. intros; induction H; try assumption.
  apply IHEvalsTo; apply lemma_preservation with e1; assumption. Qed.

(* Lemma. The underlying bare type system is sound. This is the textbook
          soundness proof for the STLC. *)
Theorem lemma_soundness : forall (e e':expr) (t:ftype),
    EvalsTo e e' -> HasFtype FEmpty e t -> isValue e' \/ exists e'', Step e' e''.
Proof. intros e e' t ev_ee' p_e_t; induction ev_ee'.
  - apply lemma_progress with t; apply p_e_t.
  - apply IHev_ee'; apply lemma_preservation with e1; assumption. Qed. 