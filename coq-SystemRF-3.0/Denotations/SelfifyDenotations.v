Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.PrimitivesFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.Typing.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.BasicPropsWellFormedness.
Require Import SystemRF.LemmasWellFormedness.
Require Import SystemRF.SubstitutionLemmaWF.
Require Import SystemRF.LemmasTransitive.
Require Import Denotations.ClosingSubstitutions.
Require Import Denotations.Denotations.
Require Import Denotations.BasicPropsCSubst.
Require Import Denotations.BasicPropsSemantics.
Require Import Denotations.PrimitivesSemantics.
Require Import Denotations.PrimitivesDenotations.

Require Import Arith.
Require Import ZArith.

Lemma lem_denotations_selfify' : forall (n:nat) (g:env) (t:type) (k:kind) (v:expr),
    depth t <= n -> WFtype g t k -> g = Empty 
        -> HasFtype FEmpty v (erase t) -> isValue v
        -> Denotes t v -> Denotes (self t v k) v.
Proof. induction n.
  - (* n = 0 => TRefn *) intros; 
    assert (depth t = 0) by auto with *.
    destruct t; simpl in H5; try discriminate;
    clear H H5; subst g;
    destruct k; simpl; simpl in H2.
    * (* k = Base *) rewrite Denotes_equation_1.
      unfold psubBV; simpl; inversion H4; destruct H1;    
      simpl in H1; repeat split; try apply PECons;
      try assumption.
      apply lem_ftyp_islc in H1 as Hv; rewrite lem_subBV_lc; 
      try apply Hv.
      assert (isClosedBasic b) as Hb
        by (destruct b; inversion H0; simpl in H8; inversion H8; 
            try simpl in H14; try contradiction; trivial).
      destruct b eqn:B; simpl in Hb; try contradiction.
      + (* Bool *) assert (isBool v)
          by (apply lem_den_bools with (TRefn TBool ps); simpl; trivial);
        destruct v eqn:V; try contradiction.
        assert (true = Bool.eqb b0 b0) by (destruct b0; reflexivity);
        rewrite H7; apply lemma_eql_bool_semantics; apply Refl.
      + (* Int *) assert (isInt v)
          by (apply lem_den_ints with (TRefn TInt ps); simpl; trivial);
        destruct v eqn:V; try contradiction.
        assert ((Z.eqb n n) = true) by (apply Z.eqb_eq; reflexivity);
        rewrite <- H7; apply lemma_eql_int_semantics; apply Refl.
    * (* k = Star *) apply H4.
  - (* n > 0 *) intros; subst g; destruct t.
    * (* TRefn *) apply IHn with Empty; simpl in H2;
      simpl; auto with *. 
    * (* TFunc *) destruct k; simpl; apply H4.
    * (* TExis *) destruct k.
      + (* Base *) simpl; rewrite Denotes_equation_3; simpl; 
        rewrite lem_erase_self; repeat split; try assumption.
        rewrite Denotes_equation_3 in H4; simpl in H4;
        clear H2 H3; destruct H4; destruct H2.
        destruct H3 as [v_x H3]; exists v_x;
        repeat split; destruct H3; destruct H4;
        try rewrite lem_tsubBV_self; try apply IHn with Empty;
        simpl in H; apply Nat.succ_le_mono in H;
        try rewrite depth_tsubBV;
        try apply Nat.le_trans with (max (depth t1) (depth t2));
        try apply Nat.le_max_r;
        try rewrite lem_erase_tsubBV;
        try apply lem_ftyp_islc with FEmpty (erase t2);
        inversion H0; try apply H5;
        pose proof (fresh_not_elem (union nms (free t2))); 
        set (y := fresh (union (nms) (free t2))) in H12;        
        try rewrite lem_tsubFV_unbindT with y v_x t2;
        apply lem_den_hasftype in H4 as H13;
        try apply lem_subst_wf_top with t1;
        apply not_elem_union_elim in H12; destruct H12;
        try apply H11; simpl; auto. 
      + (* Star *) simpl; apply H4.
    * (* TPoly *) destruct k; simpl; apply H4.
    * (* TList *) destruct k; simpl; apply H4.
Qed.

Lemma lem_denotations_selfify : forall (t:type) (k:kind) (v:expr),
    WFtype Empty t k -> HasFtype FEmpty v (erase t) -> isValue v
        -> Denotes t v -> Denotes (self t v k) v.
Proof. intros t k v p_emp_t. 
  apply lem_denotations_selfify' with (depth t) Empty; trivial. Qed.

Lemma lem_denotes_self_equal' : forall (g:env) (t:type) (k:kind) (v v':expr),
    WFtype g t k -> g = Empty -> k = Base -> noExists t
        -> isValue v -> HasFtype FEmpty v (erase t)
        -> Denotes (self t v Base) v' -> v = v'.
Proof. intros g t k v v' H; induction H; intros Hg Hk; 
    intros; try discriminate.
  - simpl in H3; rewrite Denotes_equation_1 in H3;
    destruct H3; destruct H4; unfold eqlPred in H5;
    unfold psubBV in H5; simpl in H5; simpl in H2;
    rewrite lem_subBV_lc in H5; 
    try apply lem_ftyp_islc with FEmpty (FTBasic b);    
    try apply H2; destruct b; simpl in H; 
    try contradiction; simpl in H4; 
    apply lem_bool_values in H2 || apply lem_int_values in H2;
    try apply lem_bool_values in H4; try apply lem_int_values in H4;
    trivial; destruct v; simpl in H2; try contradiction;
    destruct v'; simpl in H4; try contradiction; f_equal;
    inversion H5;
    try pose proof 
      (lemma_eql_bool_semantics (Bc b) (Bc b0) b b0 (Refl (Bc b)) (Refl (Bc b0)));
    try pose proof 
      (lemma_eql_int_semantics (Ic n) (Ic n0) n n0 (Refl (Ic n)) (Refl (Ic n0)));
    rewrite <- H6 in H8; rewrite <- H6 in H10;
    try apply (lem_evals_val_det p (Bc (Bool.eqb b b0)) (Bc true)) in H8;
    try apply (lem_evals_val_det p (Bc (n =? n0)%Z) (Bc true)) in H8;
    try injection H8 as H8; 
    try apply Bool.eqb_prop in H8; try apply Z.eqb_eq in H8;
    try apply val_Bc; trivial.
  - apply IHWFtype; trivial; simpl; simpl in H5;
    rewrite Denotes_equation_1; rewrite Denotes_equation_1 in H5;
    destruct H5; destruct H6; split; try split;
    inversion H7; try apply PECons; try apply PEEmp;
    fold subBV_at; unfold eqlPred; simpl; trivial.
  - subst g; simpl in H; contradiction.
  - simpl in H2; contradiction.
  Qed.

Lemma lem_denotes_self_equal : forall (t:type) (v v':expr),
    WFtype Empty t Base -> noExists t
        -> isValue v -> HasFtype FEmpty v (erase t)
        -> Denotes (self t v Base) v' -> v = v'.
Proof. intros; apply lem_denotes_self_equal' with Empty t Base;
  trivial. Qed.   
    
(* List length versions *)

Lemma lem_denotes_self_eqlLen : forall (t:type) (ps:preds) (v v':expr),
    WFtype Empty (TList t ps) Star 
        -> isValue v -> HasFtype FEmpty v (FTList (erase t))
        -> Denotes (TList t (PCons (eqlLenPred t v) ps)) v' 
        -> exists n:Z, EvalsTo (length t v) (Ic n)
                        /\ EvalsTo (length t v') (Ic n).
Proof. intros. apply lemma_list_values with v (erase t) in H1 as vlis;
  try apply H0; apply lem_den_lists 
      with (TList t (PCons (eqlLenPred t v) ps)) t v' in H2 as v'lis;
  try apply lem_den_isvalue in H2 as val'; trivial;
  apply lemma_length_list_semantics with t v in vlis as Hsem;
  try apply lemma_length_list_semantics with t v' in v'lis as Hsem';
  try destruct Hsem as [n ev_lenv_n]; 
  try destruct Hsem' as [n' ev_lenv'_n']; trivial;
  apply lem_wflist_wftype in H as p_emp_t;
  apply lem_wftype_islct in p_emp_t as Hlct;
  apply lem_ftyp_islc in H1 as Hlc.
  destruct v'; simpl in v'lis; try contradiction.
  - rewrite Denotes_equation_17 in H2; destruct H2.
    inversion H3; rewrite <- H4 in H6;
    rewrite lem_subBV_lc in H4;
    rewrite lem_tsubBV_lct in H4; trivial.
    pose proof 
      (lemma_eq_semantics (App (AppT (Prim Length) t) v) 
                          (App (AppT (Prim Length) t) Nil)
                          n n' ev_lenv_n ev_lenv'_n').
    apply (lem_evals_val_det p (Bc (n =? n')%Z) (Bc true)) in H6;
    try injection H6 as H6; try apply Z.eqb_eq in H6;
    try exists n; try split; try subst n';
    try apply val_Bc; try subst p; trivial.
  - rewrite Denotes_equation_18 in H2;
    destruct H2 as [p_v'[_ [_ [den_v1 [den_v2 evals]]]]];
    inversion evals; rewrite <- H2 in H4; clear H3 H5;
    rewrite lem_subBV_lc in H2;
    rewrite lem_tsubBV_lct in H2; trivial.
    pose proof 
      (lemma_eq_semantics (App (AppT (Prim Length) t) v) 
                          (App (AppT (Prim Length) t) (Cons v'1 v'2))
                          n n' ev_lenv_n ev_lenv'_n').
    apply (lem_evals_val_det p (Bc (n =? n')%Z) (Bc true)) in H4;
    try injection H4 as H4; try apply Z.eqb_eq in H4;
    try exists n; try split; try subst n';
    try apply val_Bc; try subst p; trivial.
  Qed.

Lemma lem_free_safeListVarUseT : forall (x:vname) (t:type),
    free t = empty -> safeListVarUseT x t.
Proof. induction t; simpl; intros; try split;
  try apply IHt1; try apply IHt2; try apply IHt;
  try apply no_elem_empty; intros;
  try apply empty_no_elem with (fvP ps) x in H;
  try apply empty_no_elem with (union (free t1) (free t2)) x0 in H;
  try apply empty_no_elem with (union (free t) (fvP ps)) x0 in H;
  try apply empty_no_elem with (union (free t) (fvP ps)) x in H;
  try apply empty_no_elem with (free t) x0 in H;
  try apply not_elem_union_elim in H; try apply H;
  try destruct H; trivial. 
Qed.

Lemma lem_free_safeListVarUseE : forall (x:vname) (e:expr),
    fv e = empty -> safeListVarUseE x e.
Proof. induction e; simpl; intros; try discriminate;
  try right; try right;
  try split; try split; try (apply empty_no_elem; apply H);
  try apply IHe; try apply IHe1; try apply IHe2; try apply IHe3;
  try apply lem_free_safeListVarUseT; try apply no_elem_empty; intros;
  try apply empty_no_elem with (union (fv e1) (fv e2)) x0 in H;
  try apply empty_no_elem with (union (fv e1) (fv e2)) x  in H;
  try apply empty_no_elem with (union (fv e) (free t)) x0 in H;
  try apply empty_no_elem 
    with (union (fv e1) (union (fv e2) (fv e3))) x0 in H;
  try apply not_elem_union_elim in H;  try destruct H; 
  try apply not_elem_union_elim in H0; trivial;
  try destruct H0; trivial.
Qed.

Lemma lem_fvP_safeListVarUseP : forall (x:vname) (ps:preds),
    fvP ps = empty -> safeListVarUseP x ps.
Proof. induction ps; simpl; intros; trivial; split;
  try apply IHps; try apply lem_free_safeListVarUseE; 
  try apply no_elem_empty; intros;
  try apply empty_no_elem with (union (fv p) (fvP ps)) x0 in H;
  try apply not_elem_union_elim in H;  try destruct H; trivial.
Qed.

Lemma lem_safeListVarUseP_strength : forall (x:vname) (ps qs:preds),
    safeListVarUseP x ps -> safeListVarUseP x qs 
        -> safeListVarUseP x (strengthen ps qs).
Proof. intro x; induction ps; simpl; intros; try split;
  try destruct H; try apply IHps; trivial. Qed.

Lemma lem_safeListVarUseT_push : forall (t:type) (ps:preds) (x:vname),
    free t = empty -> noExists t -> ~ Elem x (fvP ps)
        -> safeListVarUseT x (push ps t).
Proof. induction t; simpl; intros.
  - apply not_elem_subset with (union (fvP ps0) (fvP ps));
    try apply fv_strengthen_elim; apply not_elem_union_intro;
    try apply H1; try apply empty_no_elem; apply H.
  - split; apply lem_free_safeListVarUseT; try apply no_elem_empty;
    intros; apply empty_no_elem with (union (free t1) (free t2)) x0 in H;
    try apply not_elem_union_elim in H; try destruct H; trivial.
  - contradiction.
  - apply lem_free_safeListVarUseT; apply H.
  - split; try apply lem_free_safeListVarUseT; try apply no_elem_empty;
    intros; apply empty_no_elem with (union (free t) (fvP ps)) x in H as H';
    try apply empty_no_elem with (union (free t) (fvP ps)) x0 in H;
    try apply not_elem_union_elim in H'; try destruct H'; 
    try apply not_elem_union_elim in H;  try destruct H; trivial.
Qed.


Lemma lem_safeListVarUseT_tsubFV : forall (t:type) (x:vname) (v:expr),
    safeListVarUseT x t -> tsubFV x v t = t.
Proof. induction t; simpl; intros.
  - rewrite lem_psubFV_notin; trivial.
  - destruct H; rewrite IHt1; try rewrite IHt2; trivial.
  - destruct H; rewrite IHt1; try rewrite IHt2; trivial.
  - rewrite IHt; trivial.
  - rewrite IHt; try rewrite lem_psubFV_notin; destruct H; trivial.
Qed.

Lemma lem_safeListVarUseT_ctsubst : forall (t:type) (x:vname) (th:csub),
    closed th -> substitutable th -> uniqueC th
      -> safeListVarUseT x t -> safeListVarUseT x (ctsubst th t).
Proof. induction t; simpl; intros.
  - destruct b eqn:B.
    * rewrite lem_ctsubst_refn; try left; simpl;
      try apply not_elem_subset with (fvP ps);
      try apply lem_fvP_cpsubst; trivial.
    * rewrite lem_ctsubst_refn; try left; simpl;
      try apply not_elem_subset with (fvP ps);
      try apply lem_fvP_cpsubst; trivial.
    * rewrite lem_ctsubst_refn; try right; simpl;
      try apply not_elem_subset with (fvP ps);
      try apply lem_fvP_cpsubst; trivial.
    * simpl; destruct (elem_dec a (tvbindsC th)).
      + apply lem_tvbindsC_tvboundinC in H3;
        destruct H3 as [t_a H3].
        rewrite lem_ctsubst_refn_tv with th a t_a ps;
        try apply lem_safeListVarUseT_push;
        try apply lem_tvboundinC_closed with a th;
        try apply lem_tvboundinC_substitutable with a th;
        try apply not_elem_subset with (fvP ps);
        try apply lem_fvP_cpsubst; trivial.
      + rewrite lem_ctsubst_refn_tv_notin'; simpl; try apply H3;
        try apply not_elem_subset with (fvP ps);
        try apply lem_fvP_cpsubst; trivial.
  - rewrite lem_ctsubst_func; simpl; split; apply IHt1 || apply IHt2;
    destruct H2; trivial.
  - rewrite lem_ctsubst_exis; simpl; split; apply IHt1 || apply IHt2;
    destruct H2; trivial.
  - rewrite lem_ctsubst_poly; simpl; apply IHt; trivial.
  - rewrite lem_ctsubst_list; simpl; split; try apply IHt;
    destruct H2; try apply not_elem_subset with (fvP ps);
    try apply lem_fvP_cpsubst; trivial.
Qed.
  
Lemma lem_safeListVarUseE_csubst : forall (e:expr) (x:vname) (th:csub),
    closed th -> substitutable th -> uniqueC th -> ~ in_csubst x th
      -> safeListVarUseE x e -> safeListVarUseE x (csubst th e).
Proof. induction e; simpl; intros; try contradiction.
  - rewrite lem_csubst_bc; simpl; exact I.
  - rewrite lem_csubst_ic; simpl; exact I.
  - rewrite lem_csubst_prim; simpl; exact I.
  - rewrite lem_csubst_bv; simpl; exact I.
  - destruct (elem_dec x (vbindsC th)).
    * apply lem_vbindsC_boundinC in H4; destruct H4 as [v_x H4]. 
      apply lem_csubst_fv_boundinC in H4 as H5; try rewrite H5;
      try apply lem_free_safeListVarUseE;
      try apply lem_boundinC_closed in H4; try destruct H4;
      simpl; trivial.
    * rewrite lem_csubst_fv'; simpl; trivial.
  - rewrite lem_csubst_lambda; simpl;
    apply not_elem_subset with (fv e); try apply lem_fv_csubst; trivial.
  - rewrite lem_csubst_app; simpl; destruct H3; try destruct H3.
    * left; split; destruct e1; simpl in H3; try contradiction;
      subst e1 e2; try rewrite lem_csubst_appT;
      try rewrite lem_csubst_prim; try rewrite lem_csubst_fv; 
      simpl; trivial.
    * right; left; split; destruct H3;
      destruct e1; simpl in H3; try contradiction;
      subst e1; try rewrite lem_csubst_appT;
      try rewrite lem_csubst_prim; try apply IHe2; simpl; trivial.
    * right; right; split; destruct H3; try apply IHe1;
      try apply IHe2; trivial.
  - rewrite lem_csubst_lambdaT; simpl;
    apply not_elem_subset with (fv e); try apply lem_fv_csubst; trivial.
  - rewrite lem_csubst_appT; simpl; split; destruct H3;
    try apply IHe; try apply lem_safeListVarUseT_ctsubst; trivial.
  - rewrite lem_csubst_let; simpl; split; destruct H3;
    try apply IHe1; try apply H2;
    try apply not_elem_subset with (fv e2); try apply lem_fv_csubst; trivial.
  - rewrite lem_csubst_annot; simpl; split; destruct H3;
    try apply IHe; try apply lem_safeListVarUseT_ctsubst; trivial.
  - rewrite lem_csubst_if; simpl; repeat split; destruct H3;
    destruct H4; try apply IHe1; try apply IHe2; try apply IHe3; trivial.
  - rewrite lem_csubst_nil; trivial.
  - rewrite lem_csubst_cons; simpl; split; destruct H3;
    try apply IHe1; try apply IHe2; trivial.
  - rewrite lem_csubst_switch; simpl; repeat split; destruct H3;
    destruct H4; try apply IHe1; try apply IHe2; try apply IHe3; trivial.
  - rewrite lem_csubst_error; trivial.
Qed.
  
Lemma lem_safeListVarUseP_csubst : forall (ps:preds) (x:vname) (th:csub),
    closed th -> substitutable th -> uniqueC th -> ~ in_csubst x th
      -> safeListVarUseP x ps -> safeListVarUseP x (cpsubst th ps).
Proof. induction ps; simpl; intros.
  - rewrite lem_cpsubst_pempty; trivial.
  - rewrite lem_cpsubst_pcons; simpl; split; destruct H3;
    try apply lem_safeListVarUseE_csubst; try apply IHps; trivial.
Qed.


Lemma lem_safeListVarUseE_eqlLen' : 
  forall (x:vname) (e:expr) (t:type) (v v' vf:expr) (m:Z),
    safeListVarUseE x e -> isValue v -> isValue v' -> isValue vf
      -> EvalsTo (length t v) (Ic m) -> EvalsTo (length t v') (Ic m)
      -> EvalsTo (subFV x v  e) vf
      -> EvalsTo (subFV x v' e) vf.
Proof. intro x; induction e; intros; simpl in H;
  try contradiction; simpl in *; trivial.
  - (* FV *) apply Nat.eqb_neq in H; rewrite H in *; trivial.
  - (* Lambda *) rewrite lem_subFV_notin' in H5;
    try rewrite lem_subFV_notin'; trivial.
  - (* App *) repeat destruct H.
    (* length call *) destruct e1; simpl in H; try contradiction;
    subst e1 e2; simpl in H5; simpl;
    assert (x =? x = true) as X by (apply Nat.eqb_eq; reflexivity);
    rewrite X in *;   
    inversion H3; inversion H;
    try ( apply lem_value_stuck in H13; trivial; contradiction );
    try ( inversion H12; try inversion pf; 
          apply lem_value_stuck in H17; try apply val_Prm; contradiction ).
    inversion H4; inversion H14;
    try ( apply lem_value_stuck in H21; try apply val_Len; contradiction );
    try ( apply lem_value_stuck in H22; trivial; contradiction ).
    inversion H5; try (rewrite <- H24 in H2; inversion H2);
    inversion H23;
    try ( apply lem_value_stuck in H30; try apply val_Len; contradiction );
    try ( apply lem_value_stuck in H31; trivial; contradiction ).
    rewrite deltaM_pf_indep with Length v pf1 pf in H28; subst e2 e7.
    assert (vf = (Ic m))
      by (apply lem_evals_val_det with (deltaM Length v pf);
          try apply val_Ic; trivial); subst vf e8;
    apply AddStep with e4; subst e4; try apply EPrimM; trivial.
    
    (* length call not x*) destruct e1; simpl in H; try contradiction.
    subst e1; simpl in H5; simpl. 
    apply lem_app_evals_val in H5 as Happ;
    try destruct Happ as [_ [v2 [_ [val2 [_ ev_e2v_v2]]]]]; try apply H2.
    apply IHe2 with t v v' v2 m in ev_e2v_v2 as ev_e2v'_v2; trivial.
    assert (EvalsTo (App (AppT (Prim Length) (tsubFV x v t0)) 
                         (subFV x v e2)) 
                    (App (AppT (Prim Length) (tsubFV x v t0)) v2))
      by (apply lemma_app_many2; try apply val_Len; trivial).
    apply lemma_evals_trans 
      with (App (AppT (Prim Length) (tsubFV x v' t0)) v2); 
    try apply lemma_app_many2; try apply val_Len; trivial.
    apply lem_decompose_evals 
      with (App (AppT (Prim Length) (tsubFV x v t0)) (subFV x v e2))
           (App (AppT (Prim Length) (tsubFV x v t0)) v2) vf in H5; 
    trivial. inversion H5; try (rewrite <- H8 in H2; inversion H2).
    inversion H7;
    try ( apply lem_value_stuck in H14; try apply val_Len; contradiction );
    try ( apply lem_value_stuck in H15; trivial; contradiction ).
    apply AddStep with e0; subst e0; try apply EPrimM; trivial.    
    
    (* otherwise *) apply lem_app_evals_val in H5 as Happ;
    try destruct Happ as [v1 [v2 [val1 [val2 [ev_e1v_v1 ev_e2v_v2]]]]];
    try apply H2;
    apply IHe1 with t v v' v1 m in ev_e1v_v1 as ev_e1v'_v1; 
    try apply IHe2 with t v v' v2 m in ev_e2v_v2 as ev_e2v'_v2;
    trivial; assert (EvalsTo (App (subFV x v e1) (subFV x v e2)) (App v1 v2))
      by (apply lemma_app_both_many; trivial);
    apply lemma_evals_trans with (App v1 v2);
    try apply lemma_app_both_many; trivial;
    apply lem_decompose_evals with (App (subFV x v e1) (subFV x v e2)); trivial.
  - (* LambdaT *) rewrite lem_subFV_notin' in H5;
    try rewrite lem_subFV_notin'; trivial.
  - (* AppT *) destruct H;
    rewrite lem_safeListVarUseT_tsubFV in H5;
    try rewrite lem_safeListVarUseT_tsubFV;
    try apply lem_appT_evals_val in H5 as HappT;
    try destruct HappT as [v1 [val1 ev_ev_v1]];
    try apply IHe with t0 v v' v1 m in ev_ev_v1 as ev_ev'_v1; trivial.
    inversion H5.
    * subst vf; inversion H2; destruct e; simpl in H; try contradiction;
      simpl in H9; try discriminate; simpl; rewrite H9; try apply Refl.
      apply Nat.eqb_neq in H; rewrite H; apply Refl.
    * inversion H7;
      assert (EvalsTo (AppT (subFV x v e) t) (AppT v1 t))
        by (apply lemma_appT_many; trivial);
      apply lemma_evals_trans with (AppT v1 t);
      try apply lemma_appT_many; trivial;
      apply lem_decompose_evals with (AppT (subFV x v e) t); trivial.
  - (* Let *) destruct H; rewrite (lem_subFV_notin' e2) in H5;
    try rewrite (lem_subFV_notin' e2); trivial;
    apply lem_let_evals_val in H5 as Hlet; try apply H2;
    try destruct Hlet as [v1 [val1 [ev_e1v_v1 ev_e2v1_vf]]].
    apply IHe1 with t v v' v1 m in ev_e1v_v1 as ev_e1v'_v1; trivial.
    try apply lemma_evals_trans with (Let v1 e2);
    try apply lemma_let_many; try apply ev_e1v'_v1;
    apply AddStep with (subBV v1 e2); try apply ELetV; trivial.
  - (* Annot *) destruct H;
    rewrite lem_safeListVarUseT_tsubFV in H5;
    try rewrite lem_safeListVarUseT_tsubFV;
    try apply lem_ann_evals_val in H5 as Hann;
    try destruct Hann as [v1 [val1 ev_ev_v1]];
    try apply IHe with t0 v v' v1 m in ev_ev_v1 as ev_ev'_v1; trivial.
    assert (EvalsTo (Annot (subFV x v e) t) (Annot v1 t))
      by (apply lemma_annot_many; trivial).
    apply lemma_evals_trans with (Annot v1 t);
    try apply lemma_annot_many; trivial;
    apply lem_decompose_evals with (Annot (subFV x v e) t); trivial.
  - (* If *) destruct H; destruct H6;
    try apply lem_if_evals_val in H5 as Hif; try apply H2;
    destruct Hif as [v'' [val' Hif]]; destruct Hif; destruct H8.
    * apply IHe1 with t v v' (Bc true) m in H8 as ev_e1v'_tt; 
      try apply val_Bc; trivial.
      assert (EvalsTo (If (subFV x v e1) (subFV x v e2) (subFV x v e3)) 
                      (If (Bc true) (subFV x v e2) (subFV x v e3)))
        by (apply lemma_if_many; trivial).
      apply lemma_evals_trans 
        with (If (Bc true) (subFV x v' e2) (subFV x v' e3));
      try apply lemma_if_many; trivial.
      assert (EvalsTo (If (Bc true) (subFV x v e2) (subFV x v e3)) vf)
        by (apply lem_decompose_evals 
              with (If (subFV x v e1) (subFV x v e2) (subFV x v e3)); trivial).
      inversion H11; try (subst vf; inversion H2; contradiction);
      inversion H12; 
      try (apply lem_value_stuck in H20; try apply val_Bc; contradiction).
      subst e4; apply AddStep with (subFV x v' e2);
      try apply EIfT; apply IHe2 with t v m; trivial.
    * apply IHe1 with t v v' (Bc false) m in H8 as ev_e1v'_tt; 
      try apply val_Bc; trivial.
      assert (EvalsTo (If (subFV x v e1) (subFV x v e2) (subFV x v e3)) 
                      (If (Bc false) (subFV x v e2) (subFV x v e3)))
        by (apply lemma_if_many; trivial).
      apply lemma_evals_trans 
        with (If (Bc false) (subFV x v' e2) (subFV x v' e3));
      try apply lemma_if_many; trivial.
      assert (EvalsTo (If (Bc false) (subFV x v e2) (subFV x v e3)) vf)
        by (apply lem_decompose_evals 
              with (If (subFV x v e1) (subFV x v e2) (subFV x v e3)); trivial).
      inversion H11; try (subst vf; inversion H2; contradiction);
      inversion H12; 
      try (apply lem_value_stuck in H20; try apply val_Bc; contradiction).
      subst e4; apply AddStep with (subFV x v' e3);
      try apply EIfF; apply IHe3 with t v m; trivial.
  - (* Cons *) destruct H; apply lem_cons_evals_val in H5 as Happ;
    try destruct Happ as [v1 [v2 [val1 [val2 [ev_e1v_v1 ev_e2v_v2]]]]];
    try apply H2;
    apply IHe1 with t v v' v1 m in ev_e1v_v1 as ev_e1v'_v1; 
    try apply IHe2 with t v v' v2 m in ev_e2v_v2 as ev_e2v'_v2;
    trivial; assert (EvalsTo (Cons (subFV x v e1) (subFV x v e2)) (Cons v1 v2))
      by (apply lemma_cons_both_many; trivial);
    apply lemma_evals_trans with (Cons v1 v2);
    try apply lemma_cons_both_many; trivial;
    apply lem_decompose_evals with (Cons (subFV x v e1) (subFV x v e2)); trivial.
  - (* Switch *) destruct H; destruct H6;
    try apply lem_switch_evals_val in H5 as Hsw; try apply H2;
    destruct Hsw as [v'' [val' Hsw]]; destruct Hsw. 
    * destruct H8; apply IHe1 with t v v' Nil m in H8 as ev_e1v'_nl; 
      try apply val_Nil; trivial.
      assert (EvalsTo (Switch (subFV x v e1) (subFV x v e2) (subFV x v e3)) 
                      (Switch Nil (subFV x v e2) (subFV x v e3)))
        by (apply lemma_switch_many; trivial).
      apply lemma_evals_trans 
        with (Switch Nil (subFV x v' e2) (subFV x v' e3));
      try apply lemma_switch_many; trivial.
      assert (EvalsTo (Switch Nil  (subFV x v e2) (subFV x v e3)) vf)
        by (apply lem_decompose_evals 
              with (Switch (subFV x v e1) (subFV x v e2) (subFV x v e3)); trivial).
      inversion H11; try (subst vf; inversion H2; contradiction);
      inversion H12;
      try (apply lem_value_stuck in H20; try apply val_Nil; contradiction).
      subst e4; apply AddStep with (subFV x v' e2);
      try apply ESwitchN; apply IHe2 with t v m; trivial.
    * destruct H8 as [v1 [v2 [val1 [val2 [ev_e1v_cn ev_e3v_v'']]]]];
      apply IHe1 with t v v' (Cons v1 v2) m in ev_e1v_cn as ev_e1v'_cn; 
      try apply val_Cons; trivial.
      assert (EvalsTo (Switch (subFV x v e1) (subFV x v e2) (subFV x v e3)) 
                      (Switch (Cons v1 v2) (subFV x v e2) (subFV x v e3)))
        by (apply lemma_switch_many; trivial).
      apply lemma_evals_trans 
        with (Switch (Cons v1 v2) (subFV x v' e2) (subFV x v' e3));
      try apply lemma_switch_many; trivial.
      assert (EvalsTo (Switch (Cons v1 v2)  (subFV x v e2) (subFV x v e3)) vf)
        by (apply lem_decompose_evals 
              with (Switch (subFV x v e1) (subFV x v e2) (subFV x v e3)); trivial).
      inversion H9; try (subst vf; inversion H2; contradiction);
      inversion H10;
      try ( apply lem_value_stuck in H18; try apply val_Cons; 
            trivial; contradiction ).
      subst e4; apply AddStep with (App (App (subFV x v' e3) v1) v2);
      try apply ESwitchC; try apply IHe3 with t v m; trivial.
      apply lem_app_evals_val in H11; try apply H2;
      destruct H11 as [v3' [_ [val3' [_ [ev_e3v'_v3' _]]]]];
      apply lem_app_evals_val in ev_e3v'_v3'; try apply val3';
      destruct ev_e3v'_v3' as [v3'' [_ [val3'' [_ [ev_e3v_v3'' _]]]]];
      apply IHe3 with t v v' v3'' m in ev_e3v_v3'' as ev_e3v'_v3'';
      trivial; apply lemma_evals_trans with (App (App v3'' v1) v2);
      try apply lemma_app_many; try apply lemma_app_many; trivial.
      inversion H9; try (subst vf e5; inversion H2; contradiction).
      inversion H11;
      try ( apply lem_value_stuck in H27; try apply val_Cons; 
            trivial; contradiction ).
      subst e6; apply lem_decompose_evals 
        with (App (App (subFV x v e3) v1) v2); 
      try apply lemma_app_many; try apply lemma_app_many; trivial.
Qed.

Lemma lem_safeListVarUseP_eqlLen : 
  forall (x:vname) (ps:preds) (t:type) (v v':expr) (m:Z),
    safeListVarUseP x ps -> isValue v -> isValue v'
      -> EvalsTo (length t v) (Ic m) -> EvalsTo (length t v') (Ic m)
      -> PEvalsTrue (psubFV x v ps) -> PEvalsTrue (psubFV x v' ps).
Proof. intro x; induction ps; simpl; intros; trivial.
  try apply PECons; inversion H4; destruct H.
  - apply lem_safeListVarUseE_eqlLen' with t v m; 
    try apply val_Bc; trivial.
  - apply IHps with t v m; trivial.
Qed.
      