Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.Strengthenings.
Require Import SystemRF.LocalClosure.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.BasicPropsWellFormedness.
Require Import SystemRF.Typing.
Require Import SystemRF.LemmasWellFormedness.
Require Import SystemRF.LemmasTransitive.
Require Import Denotations.ClosingSubstitutions.
Require Import Denotations.Denotations.
Require Import Denotations.PrimitivesSemantics.
Require Import Denotations.BasicPropsCSubst.

Require Import Arith.
Require Import Lists.ListSet.

Lemma lem_denotesenv_loc_closed : forall (g:env) (th:csub), 
    DenotesEnv g th -> loc_closed th.
Proof. intros; induction H; simpl; try split; trivial.
  - (* CCons *) apply lem_den_hasftype in H1; 
    apply lem_ftyp_islc in H1; assumption.
  - (* CConsT *) apply lem_wftype_islct in H3; assumption. 
  Qed.

Lemma lem_denotesenv_closed : forall (g:env) (th:csub), 
    DenotesEnv g th -> closed th.
Proof. intros; induction H; simpl; trivial.
  - (* CCons *) apply lem_den_hasftype in H1;
    apply lem_fv_subset_bindsF in H1; repeat split;
    try apply IHDenotesEnv; apply no_elem_empty; intuition.
  - (* CConsT *) apply lem_free_subset_binds in H3; repeat split;
    try apply IHDenotesEnv; apply no_elem_empty; intuition.
  Qed.

Lemma lem_denotesenv_substitutable : forall (g:env) (th:csub), 
    DenotesEnv g th -> substitutable th.
Proof. intros; induction H; simpl; repeat split; trivial.
  apply lem_den_isvalue with (ctsubst th t); apply H1. Qed.

Lemma lem_denotesenv_uniqueC : forall (g:env) (th:csub),
    DenotesEnv g th -> uniqueC th.
Proof. intros g th den_g_th; induction den_g_th; simpl; 
  try split; trivial; unfold in_csubst;
  rewrite <- lem_binds_env_th with g th; trivial. Qed.

Lemma lem_bound_in_denotesenv : 
  forall (x:vname) (t:type) (g:env) (th:csub),
    DenotesEnv g th -> bound_in x t g -> WFEnv g
        -> Denotes (ctsubst th t) (csubst th (FV x)).
Proof. intros x t; induction g.
  - simpl; intuition.
  - intros; inversion H;   subst x1 t1 g0;
    try apply H1;  simpl in H0; destruct H0.
    * (* x = x0 *) destruct H0; subst x0 t0;
      inversion H1; subst x0 t0 g0.
      simpl; destruct (x =? x) eqn:X;
      try apply Nat.eqb_neq in X; try unfold not in X; 
      try contradiction.
      apply lem_free_subset_binds in H10; destruct H10.
      assert (~ Elem x (free t))
        by (pose proof (vbinds_subset g);
            apply not_elem_subset with (vbinds g);
            try apply not_elem_subset with (binds g); trivial).
      rewrite lem_tsubFV_notin;
      apply lem_den_hasftype in H8 as H11;
      apply lem_fv_subset_bindsF in H11;
      simpl in H11; destruct H11;
      try apply no_elem_empty;
      try rewrite lem_csubst_nofv; 
      try apply no_elem_empty; trivial;
      intros; try apply not_elem_subset with empty.
    * (* x <> x0 *)
      apply boundin_wfenv_wftype in H0 as p_g_t; 
      pose proof (vbinds_subset g);
      assert (x0 <> x)
        by (apply lem_boundin_inenv in H0; 
            unfold in_env in H7; apply H2 in H0;
            unfold not; intros; subst x0; contradiction);
      apply Nat.eqb_neq in H3; simpl; try rewrite H3;
      try rewrite lem_tsubFV_notin;
      try apply lem_free_subset_binds in p_g_t; 
      try destruct p_g_t;
      try apply not_elem_subset with (vbinds g);
      try apply not_elem_subset with (binds g); 
      try apply IHg;
      inversion H1; trivial.
  - intros; simpl in H0;
    apply boundin_wfenv_wftype in H0 as p_g_t; 
    pose proof (tvbinds_subset g);
    try apply lem_free_subset_binds in p_g_t;
    try destruct p_g_t; 
    inversion H; subst a0 k0 g0; simpl;
    try rewrite lem_tsubFTV_notin;
    try apply IHg; 
    try apply not_elem_subset with (tvbinds g);
    try apply not_elem_subset with (binds g);
    inversion H1; trivial.
  Qed.

Lemma lem_tvbinds_denotesenv : 
  forall (a:vname) (g:env) (th:csub),
    DenotesEnv g th -> substitutable th -> Elem a (tvbinds g)
        -> exists t_a, noExists t_a /\ WFtype Empty t_a Star 
                                    /\ tv_bound_inC a t_a th.
Proof. intro a; induction g; intros; simpl in H1.
  - contradiction.
  - inversion H; simpl; apply IHg; 
    try apply lem_denotesenv_substitutable with g; trivial.
  - inversion H; subst a1 k0 g0; 
    destruct (a =? a0) eqn:A.
    * apply Nat.eqb_eq in A; subst a0.
      exists t; simpl; repeat split; auto;
      destruct k; apply H10 || apply WFKind; apply H10.
    * apply set_add_elim2 in H1; 
      try apply Nat.eqb_neq; try apply A;
      apply IHg in H5; try apply H1;
      subst th; simpl in H0; destruct H0;
      destruct H2; try apply H3.
      destruct H5 as [t_a [Hta [Hta' Hta'']]];
      exists t_a; simpl; repeat split; auto.
  Qed.

Lemma lem_fv_subset_bindsC : forall (th:csub) (t_x:type) (v_x:expr),
    closed th -> substitutable th -> Denotes (ctsubst th t_x) (csubst th v_x)
        -> Subset (fv v_x) (vbindsC th) /\ Subset (ftv v_x) (tvbindsC th).
Proof. induction th; simpl; intros.
  - (* CEmpty *) pose proof (lem_den_nofv v_x t_x H1); split; destruct H2; 
    try rewrite H2; try rewrite H3; apply subset_empty_l.
  - (* CCons  *) apply IHth in H1 as IH; try split;
    destruct H; destruct H0; destruct H2; try destruct IH;
    
    auto.
    pose 
    pose ftv_subFV_elim.

(*
Lemma get_wftype_from_denv : forall (g:env) (th:csub) (a:vname),
    DenotesEnv g th
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
*)  

(* Unfortunately, the self operator and tsubFTV do not quite 
   commute with each other, but are entirely semantically 
   equivalent. The next lemma shows that the denotation is
   unaffected (used to prove Denotational Soundness)
*)

Lemma lem_erase_tsubFTV_self :
  forall (a:vname) (t_a t:type) (v:expr) (k :kind),
    noExists t_a -> erase (self (tsubFTV a t_a t) v k) 
                      = erase (tsubFTV a t_a (self t v k)).
Proof. intros a t_a; induction t; intros v k' H;
  destruct k'; repeat rewrite lem_self_star; trivial;
  try destruct b eqn:B; simpl;
  try destruct (a =? a0) eqn:A; simpl; try reflexivity.
  - (* TRefn Base *) destruct t_a; simpl in H; simpl;
    try contradiction; reflexivity.
  - (* TExists Base *) apply IHt2; apply H.
  Qed.

Lemma lem_denotes_tsubFTV_self' : 
  forall (n:nat) (a:vname) (t_a t:type) (v v':expr) (k:kind),
    depth t <= n -> noExists t_a -> isLCT t_a -> freeTV t_a = empty
        -> subFTV a t_a v = v -> isLC v
        -> Denotes (self (tsubFTV a t_a t)  v  k) v'
        -> Denotes (tsubFTV a t_a (self t v k)) v'.
Proof. induction n.
  - (* n = 0 => TRefn *) intros; revert H5;
    assert (depth t = 0) by auto with *;
    destruct t; simpl in H5; try discriminate;
    destruct k; try rewrite lem_self_star; trivial. 
    destruct b; simpl; rewrite H3;
    unfold eqlPred; trivial. (* FTV a0 remains*)
    destruct (a =? a0) eqn:A; simpl; 
    unfold eqlPred; trivial.
    (* a = a0*) destruct t_a; simpl in A; try contradiction;
    simpl; trivial; unfold eqlPred.
    repeat rewrite Denotes_equation_1; intuition.
    apply PECons; fold subBV_at; fold psubBV_at;
    inversion H9; try apply H12. 
    destruct (0 =? 0) eqn:Z; simpl in Z; try discriminate;
    destruct b eqn:B; unfold isLCT in H1; simpl in H2;
    try destruct i; try destruct H1; try inversion H1;
    try apply (empty_no_elem (names_add a1 (ftvP ps0))) with a1 in H2;
    try apply not_elem_names_add_elim in H2; try destruct H2; intuition.
    * (* TBool *) 
      apply AddStep with (App (App (Prim Eqv) (subBV_at 0 v' v)) v').
      apply EApp1; apply EApp1; apply lem_step_eql_tbool.
      apply lem_decompose_evals with 
        (App (App (AppT (Prim Eql) (TRefn TBool PEmpty)) (subBV_at 0 v' v)) v');
      trivial; apply lem_step_evals;
      apply EApp1; apply EApp1; apply lem_step_eql_tbool.
    * (* TInt *) 
      apply AddStep with (App (App (Prim Eq) (subBV_at 0 v' v)) v').
      apply EApp1; apply EApp1; apply lem_step_eql_tint.
      apply lem_decompose_evals with 
        (App (App (AppT (Prim Eql) (TRefn TInt PEmpty)) (subBV_at 0 v' v)) v');
      trivial; apply lem_step_evals;
      apply EApp1; apply EApp1; apply lem_step_eql_tint.
  - (* n > 0 *) intros; destruct t.
    * (* TRefn *) apply IHn; revert H5; simpl; auto with *.
    * (* TFunc *) destruct k; simpl; simpl in H5; apply H5.
    * (* TExists *) revert H5; destruct k; simpl; trivial.
      (* Base *) repeat rewrite Denotes_equation_3;
      simpl; rewrite lem_erase_tsubFTV_self; intuition;
      destruct H8 as [v_x H8]; exists v_x; intuition.
      rewrite lem_tsubBV_self in H10; trivial.
      apply lem_den_hasftype in H8 as H9.
      apply lem_fv_subset_bindsF in H9 as H9;
      destruct H9; unfold Subset in H11; simpl in H11;
      assert (subFTV a t_a v_x = v_x)
        by (apply lem_subFTV_notin; unfold not; apply H11). 
      trivial || rewrite <- H12; rewrite <- H12 in H10.
      rewrite <- lem_commute_tsubFTV_tsubBV in H10;
      try rewrite <- lem_commute_tsubFTV_tsubBV;
      try assumption; rewrite lem_tsubBV_self;
      try apply IHn; simpl in H; apply Nat.succ_le_mono in H;
      try rewrite depth_tsubBV;
      try apply Nat.le_trans with (max (depth t1) (depth t2));
      try apply Nat.le_max_r;
      unfold isLC; simpl; trivial.
    * (* TPoly *) destruct k; simpl; simpl in H5; apply H5.
  Qed.
  
Lemma lem_denotes_tsubFTV_self : 
  forall (a:vname) (t_a t:type) (v v':expr) (k:kind),
    noExists t_a -> isLCT t_a -> freeTV t_a = empty
        -> subFTV a t_a v = v -> isLC v
        -> Denotes (self (tsubFTV a t_a t) v k) v'
        -> Denotes (tsubFTV a t_a (self t v k)) v'.
Proof. intros a t_a t v v' k.
  apply lem_denotes_tsubFTV_self' with (depth t); trivial. Qed.

Lemma lem_denotes_ctsubst_self : 
  forall (th:csub) (t:type) (v v':expr) (k:kind),
    closed th -> loc_closed th -> substitutable th -> uniqueC th 
        -> isLC v -> ftv v = empty
        -> Denotes (self (ctsubst th t) (csubst th v) k) v'
        -> Denotes (ctsubst th (self t v k)) v'.
Proof. induction th; intros t v v' k H1 H2 H3 H4 H5 H6; trivial;
  simpl in H1; simpl in H2; simpl in H3; simpl in H4;
  destruct H1; destruct H0; destruct H2; destruct H3; destruct H4.
  - (* CCons *) simpl; rewrite lem_tsubFV_self; apply IHth; 
    try apply lem_islc_at_subFV; auto with *.
    assert (Subset (ftv (subFV x v_x v)) (union (ftv v) (ftv v_x)))
      by apply ftv_subFV_elim;
    rewrite H0 in H10; rewrite H6 in H10;
    apply no_elem_empty; unfold not; intros;
    apply H10 in H11; intuition. 
  - (* CConsT *) intros;  
    pose proof (matchesExFTV_dec a t) as Hm; destruct Hm.
    * (* Yes *) destruct t eqn:T; try destruct b; remember H11 as H12;
      simpl in H11; try contradiction; try subst a0.
      + rewrite lem_unroll_ctsubst_tv_left;
        try split; destruct H8; trivial;
        rewrite lem_ctsubst_self_FTV with th a (TRefn (FTV a) ps) v k;
        try apply lem_denotes_tsubFTV_self;
        try apply lem_subFTV_notin;
        try apply lem_csubst_isLC;
        assert (ftv (csubst th v) = empty)
          by (apply lem_csubst_pres_noftv; trivial);
        try rewrite H13; simpl; auto.
        rewrite <- lem_unroll_ctsubst_tv_left;
        unfold csubst in H10; fold csubst in H10;
        assert (subFTV a t_a v = v)
          by (apply lem_subFTV_notin; rewrite H6; auto);
          rewrite H14 in H10; try apply H10; intuition.
      + rewrite lem_unroll_ctsubst_tv_left;
        try split; destruct H8; trivial;
        rewrite lem_ctsubst_self_FTV with th a (TExists t0_1 t0_2) v k;
        try apply lem_denotes_tsubFTV_self;
        try apply lem_subFTV_notin;
        try apply lem_csubst_isLC;
        assert (ftv (csubst th v) = empty)
          by (apply lem_csubst_pres_noftv; trivial);
        try rewrite H14;  
        try rewrite <- lem_unroll_ctsubst_tv_left;
        unfold csubst in H10; fold csubst in H10;
        assert (subFTV a t_a v = v)
          by (apply lem_subFTV_notin; rewrite H6; auto);
        try rewrite H15 in H10; 
        try apply H10;
        simpl; auto.
    * (* No *) simpl; rewrite lem_tsubFTV_self_noFTV;
      try apply IHth; simpl in H10; destruct H8;
      assert (subFTV a t_a v = v)
          by (apply lem_subFTV_notin; rewrite H6; auto);
      try apply H10; try rewrite H13; trivial.
  Qed.

Lemma lem_remove_var_denote : forall (th:csub) (t:type) (v:expr) (x:vname),
    Denotes (ctsubst th t) v -> Elem x (bindsC th) 
        -> ~ Elem x (free t) -> ~ Elem x (freeTV t)
        -> closed th -> uniqueC th -> substitutable th
        -> Denotes (ctsubst (remove_fromCS th x) t) v.
Proof. intros; rewrite <- lem_remove_ctsubst; trivial. Qed.

(*
Lemma lem_remove_tvar_denote : forall (th:csub) (t:type) (v:expr) (a:vname),
    Denotes (ctsubst th t) v -> Elem a (tvbindsC th) -> ~ Elem a (freeTV t)
        -> closed th -> uniqueC th -> substitutable th
        -> Denotes (ctsubst (remove_fromCS th a) t) v.
Proof. intros; rewrite <- lem_remove_tv_ctsubst; trivial. Qed.
*)
Lemma lem_remove_var_denote_env : forall (g g':env) (x:vname) (t_x:type) (th:csub),
    unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> ~ (in_env x g) -> ~ (in_env x g') 
        -> WFEnv (concatE g g')
        -> closed th -> uniqueC th -> substitutable th
        -> DenotesEnv (concatE (Cons x t_x g) g') th
        -> DenotesEnv (concatE g g') (remove_fromCS th x).
Proof. intro g; induction g'; simpl; intros.
  - (* CEmpty *) inversion H8; simpl;
    assert (x = x) by reflexivity;
    apply Nat.eqb_eq in H16; rewrite H16; apply H12.
  - (* CCons  *) inversion H4; inversion H8; 
    unfold in_env in H3; simpl in *;
    apply not_elem_names_add_elim in H3; destruct H3;
    apply Nat.eqb_neq in H3; rewrite H3.
    apply DExt; try apply IHg' with t_x;
    try apply lem_remove_var_denote;
    subst th; simpl in *; destruct H0;
    destruct H5; destruct H6; destruct H7; destruct H23;
    try rewrite <- lem_binds_env_th with (concatE (Cons x0 t_x g) g') th0;
    pose proof (lem_binds_concat (Cons x0 t_x g) g'); destruct H27;
    try apply H28; try apply set_union_intro1; 
    try apply set_add_intro2;
    try apply intersect_names_add_elim_r in H1; destruct H1;
    apply lem_free_subset_binds in H14; destruct H14;
    auto; apply not_elem_subset with (binds (concatE g g'));
    try apply not_elem_concat_intro;
    pose proof (vbinds_subset (concatE g g'));
    pose proof (tvbinds_subset (concatE g g'));
    try (apply subset_trans with (vbinds (concatE g g')); assumption);
    try (apply subset_trans with (tvbinds (concatE g g')); assumption); auto.
  - (* CConsT *) inversion H4; inversion H8; 
    unfold in_env in H3; simpl in *;
    apply not_elem_names_add_elim in H3; destruct H3;
    apply Nat.eqb_neq in H3; rewrite H3;
    apply DExtT; try apply IHg' with t_x;
    subst th; simpl in *; destruct H0;
    destruct H5 as [_ [_ H5]]; destruct H6; destruct H7; destruct H25;
    apply intersect_names_add_elim_r in H1; destruct H1; auto.
  Qed.
    
Lemma lem_remove_tvar_denote_env : forall (g g':env) (a:vname) (k_a:kind) (th:csub),
    unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> ~ (in_env a g) -> ~ (in_env a g') 
        -> WFEnv (concatE g g')
        -> closed th -> uniqueC th -> substitutable th
        -> DenotesEnv (concatE (ConsT a k_a g) g') th
        -> DenotesEnv (concatE g g') (remove_fromCS th a).
Proof. intro g; induction g'; simpl; intros.
  - (* CEmpty *) inversion H8; simpl;
    assert (a = a) by reflexivity;
    apply Nat.eqb_eq in H18; rewrite H18; apply H12.
  - (* CCons  *) inversion H4; inversion H8; 
    unfold in_env in H3; simpl in *;
    apply not_elem_names_add_elim in H3; destruct H3;
    apply Nat.eqb_neq in H3; rewrite H3.
    apply DExt; try apply IHg' with k_a;
    try apply lem_remove_var_denote;
    subst th; simpl in *; destruct H0;
    destruct H5; destruct H6; destruct H7; destruct H23;
    try rewrite <- lem_binds_env_th with (concatE (ConsT a k_a g) g') th0;
    pose proof (lem_binds_concat (ConsT a k_a g) g'); destruct H27;
    try apply H28; try apply set_union_intro1; 
    try apply set_add_intro2;
    try apply intersect_names_add_elim_r in H1; destruct H1;
    apply lem_free_subset_binds in H14; destruct H14;
    auto; apply not_elem_subset with (binds (concatE g g'));
    try apply not_elem_concat_intro;
    pose proof (vbinds_subset (concatE g g'));
    pose proof (tvbinds_subset (concatE g g'));
    try (apply subset_trans with (vbinds (concatE g g')); assumption);
    try (apply subset_trans with (tvbinds (concatE g g')); assumption); auto.
  - (* CConsT *) inversion H4; inversion H8; 
    unfold in_env in H3; simpl in *;
    apply not_elem_names_add_elim in H3; destruct H3;
    apply Nat.eqb_neq in H3; rewrite H3;
    apply DExtT; try apply IHg' with k_a;
    subst th; simpl in *; destruct H0;
    destruct H5 as [_ [_ H5]]; destruct H6; destruct H7; destruct H25;
    apply intersect_names_add_elim_r in H1; destruct H1; auto.
  Qed.

Lemma lem_add_var_denote_env : 
  forall (g g':env) (x:vname) (v_x:expr) (t_x:type) (th:csub),
    unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> ~ (in_env x g) -> ~ (in_env x g') 
        (*-> WFEnv (concatE g g')*) (*(WFEnv (concatE (Cons x t_x g) g') )*)
        (*-> Hastype g v_x t_x*)
        -> Denotes (ctsubst th t_x) (csubst th v_x)
        -> DenotesEnv (concatE g (esubFV x v_x g')) th
        -> exists th', DenotesEnv (concatE (Cons x t_x g) g') th' /\
                  (forall t, ctsubst th' t = ctsubst th (tsubFV x v_x t)) /\ 
                  (forall e, csubst th' e = csubst th (subFV x v_x e)).
Proof. intro g; induction g'; simpl; intros.
  - (* CEmpty *) exists (CCons x (csubst th v_x) th); repeat split; 
    try apply DExt; intros; simpl;
    try apply lem_csubst_subFV;
    try apply lem_ctsubst_tsubFV;
    
    unfold in_csubst; try rewrite <- lem_binds_env_th with g th;
    
    try apply lem_denotesenv_closed with g;
    try apply lem_denotesenv_substitutable with g;
    try apply lem_denotesenv_uniqueC with g;
    trivial.

    
    pose  lem_den_nofv.
    pose  lem_csubst_no_more_fv.

    pose fv_sub
    

    -> t_x:Type -> ProofOf(HasType g v_x t_x)
    -> ProofOf(WFEnv (concatE (Cons x t_x g) g') )
    -> th':CSub -> ProofOf(DenotesEnv (concatE g (esubFV x v_x g')) th')    
lem_add_var_csubst g Empty           x v_x_ t_x p_vx_tx p_env_wf zth' den_env'_th' 
  = case p_env_wf of -- env = Cons x t_x g
      (WFEBind _ p_g_wf _ _ _ _) -> case (lem_denote_sound_typ g v_x_ t_x p_vx_tx 
                                                               p_g_wf zth' den_env'_th') of
        (ValDen _ _ val ev_th'vx_val den_th'tx_val) 
          -> InsertInCS g Empty x v_x t_x zth' {-th-} 
                        (CCons x th'vx (zth' ? lem_binds_env_th g zth' den_env'_th'))
                        (DExt g zth' den_env'_th' x t_x th'vx  den_th'tx_th'vx) eq_func1 eq_func2
               where
                 {-@ v_x :: { v_x:Value | Set_sub (fv v_x)  (vbindsC zth') &&
                                          Set_sub (ftv v_x) (tvbindsC zth') && v_x == v_x_ } @-}
                 v_x   = v_x_ ? lem_binds_env_th g zth' den_env'_th'
                              ? lem_fv_subset_binds g v_x_ t_x p_vx_tx p_g_wf
                              ? lem_csubst_value zth' v_x_
                              ? lem_den_nofv (csubst zth' v_x_) (ctsubst zth' t_x) -- den_th'tx_th'vx
                                    (den_th'tx_val ? lem_value_refl (csubst zth' v_x_) val ev_th'vx_val) 
                 {-@ th'vx :: { v:Value | Set_emp (fv v) && v == csubst zth' v_x } @-}
                 th'vx :: Expr
                 th'vx_ = csubst zth' v_x {-? lem_csubst_value zth' v_x -}
                 th'vx  = th'vx_ ? lem_den_nofv (csubst zth' v_x) (ctsubst zth' t_x) -- den_th'tx_th'vx 
                                                (den_th'tx_val ? lem_value_refl th'vx_ val ev_th'vx_val) 
                                 ? lem_den_nobv (csubst zth' v_x) (ctsubst zth' t_x) -- den_th'tx_th'vx 
                                                (den_th'tx_val ? lem_value_refl th'vx_ val ev_th'vx_val) 
                 {-@ den_th'tx_th'vx :: ProofOf(Denotes (ctsubst zth' t_x) (csubst zth' v_x)) @-}
                 den_th'tx_th'vx :: Denotes
                 den_th'tx_th'vx = den_th'tx_val ? lem_value_refl th'vx val ev_th'vx_val
        {- @ eq_func1 :: p:Pred -> { pf:Proof | csubst th p == csubst zth' (subFV x v_x_ p) } @-}
                 eq_func1 :: Expr -> Proof   -- csubst th p
                 eq_func1 p = () ? lem_csubst_subFV   zth' x v_x  p 
                                 ? lem_binds_env_th g zth' den_env'_th'
        {- @ eq_func2 :: t:Type -> { pf:Proof | ctsubst th t == ctsubst zth' (tsubFV x v_x_ t) } @-}
                 eq_func2 :: Type -> Proof
                 eq_func2 t = () ? lem_ctsubst_tsubFV zth' x v_x  t
                                 ? lem_binds_env_th g zth' den_env'_th'

  - (* CCons  *) destruct H0;
    apply intersect_names_add_elim_r in H1; destruct H1;
    apply not_elem_names_add_elim in H3; destruct H3;
    inversion H5; apply IHg' with x0 v_x t_x th0 in H11 as IH;
    fold binds in H7; auto.
    (* exists th', DenotesEnv (Cons x t (concatE (Cons x0 t_x g) g')) th' *)
    destruct IH as [th' d_env_th'].
    exists (CCons x v0 th'); apply DExt; 
    try apply not_elem_concat_intro;
    try apply not_elem_names_add_intro; 
    try split; auto.
    
    (* EvalsDenotes (ctsubst th0 t_x) (csubst th0 v_x) *)

 
lem_add_var_csubst g (Cons z t_z g') x v_x_ t_x p_vx_tx p_zenv_wf zth' den_zenv'_zth'
= case den_zenv'_zth' of   
    (DExt env' th' den_env'_th' _z tzvx v_z_ den_th'tzvx_vz)
      -> InsertInCS g (Cons z t_z g') x v_x_ t_x zth' zth den_zenv_zth eq_funcz1 eq_funcz2
           where
             v_z          = v_z_ ? lem_den_nofv v_z_ (ctsubst th' tzvx) den_th'tzvx_vz
                                 ? lem_den_nobv v_z_ (ctsubst th' tzvx) den_th'tzvx_vz 
             zth          = CCons z v_z (th ? lem_binds_env_th env th den_env_th) 
             den_zenv_zth = DExt env th den_env_th z t_z v_z den_thtz_vz
             den_thtz_vz  = den_th'tzvx_vz ? eq_func2 t_z
             (WFEBind _ p_env_wf _ _ _ _) = p_zenv_wf
             p_xg_wf = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
             (WFEBind _ p_g_wf _ _ _ _) = p_xg_wf 
             env          = concatE (Cons x t_x g) g'
             {-@ eq_func1 :: p:Pred -> { pf:Proof | csubst th p == csubst th' (subFV x v_x_ p) } @-}
             {-@ eq_func2 :: t:Type -> { pf:Proof | ctsubst th t == ctsubst th' (tsubFV x v_x_ t) } @-}
             eq_func1 :: Expr -> Proof
             eq_func2 :: Type -> Proof 
             (InsertInCS _ _ _ _ _ _ th den_env_th eq_func1 eq_func2)
                          = lem_add_var_csubst g g' x v_x_ t_x p_vx_tx p_env_wf th' den_env'_th'
             -- csubst zth p  ==  csubst zth'  (subFV x v_x p)
             {-@ eq_funcz1 :: p:Pred
                      -> { pf:Proof | csubst (CCons z v_z th) p == csubst zth' (subFV x v_x_ p) } @-}
             eq_funcz1 :: Expr -> Proof
             eq_funcz1 p = () --    ? toProof ( csubst zth' (subFV x v_x_ p) 
                                            ? lem_binds_env_th env' th' den_env'_th'
                                            ? toProof ( zth' === CCons z v_z th' )
--                                            === csubst th' (subFV z v_z (subFV x v_x_ p))
                                            ? lem_subFV_notin x v_x_ v_z
--                                            === csubst th' (subFV z (subFV x v_x_ v_z) (subFV x v_x_ p)) 
                                            ? lem_commute_subFV  z v_z x -- v_x_ p
                                                     (v_x_ ? lem_fv_bound_in_env g v_x_ t_x p_vx_tx p_g_wf z) p
--                                            === csubst th' (subFV x v_x_ (subFV z v_z p)) 
                                            ? eq_func1 (subFV z v_z p)
--                                            === csubst th (subFV z v_z p) ) 
             {-@ eq_funcz2 :: t:Type 
                      -> { pf:Proof | ctsubst (CCons z v_z th) t == ctsubst zth' (tsubFV x v_x_ t) } @-}
             eq_funcz2 :: Type -> Proof
             eq_funcz2 t = () --    ? toProof ( ctsubst zth' (tsubFV x v_x_ t) 
                                            ? lem_binds_env_th env' th' den_env'_th'
                                            ? toProof ( zth' === CCons z v_z th' )
--                                            === ctsubst th' (tsubFV z v_z (tsubFV x v_x_ t))
                                            ? lem_subFV_notin x v_x_ v_z
--                                            === ctsubst th' (tsubFV z (subFV x v_x_ v_z) (tsubFV x v_x_ t)) 
                                            ? lem_commute_tsubFV  z v_z x -- v_x_ p
                                                     (v_x_ ? lem_fv_bound_in_env g v_x_ t_x p_vx_tx p_g_wf z) t
--                                            === ctsubst th' (tsubFV x v_x_ (tsubFV z v_z t)) 
                                            ? eq_func2 (tsubFV z v_z t)
--                                            === ctsubst th (tsubFV z v_z t) )  


{-@ data AugmentedCSub where
    InsertInCS :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value -> t_x:Type 
        -> th':CSub -> th:CSub -> ProofOf(DenotesEnv (concatE (Cons x t_x g) g') th)
        -> ( p:Pred -> { pf:Proof | csubst th p  ==  csubst th'  (subFV x v_x p) } )
        -> ( t:Type -> { pf:Proof | ctsubst th t == ctsubst th' (tsubFV x v_x t) } )
        -> ProofOf(AugmentedCSub g g' x v_x t_x th') @-}


lem_add_var_csubst g (ConsT a k_a g') x v_x_ t_x p_vx_tx p_aenv_wf zth' den_aenv'_zth' 
= case den_aenv'_zth' of   
    (DExtT env' th' den_env'_th' _a _ka {-tavx-} t_a p_emp_ta {-den_th'tzvx_vz-})
      -> InsertInCS g (ConsT a k_a g') x v_x_ t_x zth' ath den_aenv_ath eq_funca1 eq_funca2
           where
             ath          = CConsT a t_a (th ? lem_binds_env_th env th den_env_th) 
             den_aenv_ath = DExtT env th den_env_th a k_a t_a p_emp_ta --den_thtz_vz
             (WFEBindT _ p_env_wf _ _) = p_aenv_wf
             p_xg_wf = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
             (WFEBind _ p_g_wf _ _ _ _) = p_xg_wf 
             env          = concatE (Cons x t_x g) g'
             {-@ eq_func1 :: p:Pred -> { pf:Proof | csubst th p == csubst th' (subFV x v_x_ p) } @-}
             {-@ eq_func2 :: t:Type -> { pf:Proof | ctsubst th t == ctsubst th' (tsubFV x v_x_ t) } @-}
             eq_func1 :: Expr -> Proof
             eq_func2 :: Type -> Proof 
             (InsertInCS _ _ _ _ _ _ th den_env_th eq_func1 eq_func2)
                          = lem_add_var_csubst g g' x v_x_ t_x p_vx_tx p_env_wf th' den_env'_th'
             -- csubst zth p  ==  csubst zth'  (subFV x v_x p)
             {-@ eq_funca1 :: p:Pred
                      -> { pf:Proof | csubst (CConsT a t_a th) p == csubst zth' (subFV x v_x_ p) } @-}
             eq_funca1 :: Expr -> Proof
             eq_funca1 p = () --    ? toProof ( csubst zth' (subFV x v_x_ p) 
                                            ? lem_binds_env_th env' th' den_env'_th'
                                            ? toProof ( zth' === CConsT a t_a th' )
--                                            === csubst th' (subFTV a t_a (subFV x v_x_ p))
                                            ? lem_tsubFV_notin x v_x_ t_a
--                                            === csubst th' (subFTV a (tsubFV x v_x_ t_a) (subFV x v_x_ p)) 
                                            ? lem_commute_subFV_subFTV  a t_a x
                                                     (v_x_ ? lem_fv_bound_in_env g v_x_ t_x p_vx_tx p_g_wf a) p
--                                            === csubst th' (subFV x v_x_ (subFTV a t_a p)) 
                                            ? eq_func1  (subFTV a t_a p)
--                                            === csubst th (subFTV a t_a p) ) 
             {-@ eq_funca2 :: t:Type 
                      -> { pf:Proof | ctsubst (CConsT a t_a th) t == ctsubst zth' (tsubFV x v_x_ t) } @-}
             eq_funca2 :: Type -> Proof
             eq_funca2 t = () --    ? toProof ( ctsubst zth' (tsubFV x v_x_ t) 
                                            ? lem_binds_env_th env' th' den_env'_th'
                                            ? toProof ( zth' === CConsT a t_a th' )
--                                            === ctsubst th' (tsubFTV a t_a (tsubFV x v_x_ t))
                                            ? lem_tsubFV_notin x v_x_ t_a
--                                            === ctsubst th' (tsubFTV a (tsubFV x v_x_ t_a) (tsubFV x v_x_ t)) 
                                            ? lem_commute_tsubFV_tsubFTV  a t_a x 
                                                     (v_x_ ? lem_fv_bound_in_env g v_x_ t_x p_vx_tx p_g_wf a) t
--                                            === ctsubst th' (tsubFV x v_x_ (tsubFTV a t_a t)) 
                                            ? eq_func2 (tsubFTV a t_a t)
--                                            === ctsubst th (tsubFTV a t_a t) ) 
             _            = zth'  