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

(*
  {-@ lem_remove_var_denote :: th:CSub -> t:Type -> { v:Value | Set_emp (fv v) }
      -> ProofOf(Denotes (ctsubst th t) v) -> { x:Vname | v_in_csubst x th && not (Set_mem x (free t)) } 
      -> ProofOf(Denotes (ctsubst (remove_fromCS th x) t) v) @-}
lem_remove_var_denote :: CSub -> Type -> Expr -> Denotes -> Vname -> Denotes
lem_remove_var_denote th t v den_tht_v x = den_tht_v ? lem_remove_ctsubst th x t

{-@ lem_remove_tvar_denote :: th:CSub -> t:Type -> { v:Value | Set_emp (ftv v) }
      -> ProofOf(Denotes (ctsubst th t) v) -> { a:Vname | tv_in_csubst a th && not (Set_mem a (freeTV t)) } 
      -> ProofOf(Denotes (ctsubst (remove_fromCS th a) t) v) @-}
lem_remove_tvar_denote :: CSub -> Type -> Expr -> Denotes -> Vname -> Denotes
lem_remove_tvar_denote th t v den_tht_v a = den_tht_v ? lem_remove_tv_ctsubst th a t

{-@ lem_remove_var_denote_env :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
       -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
       -> ProofOf(WFEnv (concatE g g'))
       -> th:CSub -> ProofOf(DenotesEnv (concatE (Cons x t_x g) g') th)
       -> ProofOf(DenotesEnv (concatE g g') (remove_fromCS th x )) @-}
lem_remove_var_denote_env :: Env -> Vname -> Type -> Env -> WFEnv -> CSub 
                                 -> DenotesEnv -> DenotesEnv
lem_remove_var_denote_env g x  t_x Empty           p_g'g_wf  th den_env_th = case den_env_th of
  (DExt env' th' den_env'_th' _ _tx v_x den_th'tx_vx) -> den_env'_th'
lem_remove_var_denote_env g x_ t_x (Cons z t_z g') p_zg'g_wf th den_env_th = case den_env_th of
  (DExt env' th' den_env'_th' _z _tz v_z den_th'tz_vz) -- env' == concatE (Cons x t_x g) g' 
    -> DExt (concatE g g') (remove_fromCS th' x) den_env''_th'' z t_z v_z den_th''tz_vz
      where
        (WFEBind _ p_g'g_wf _ _ k_z p_g'g_tz) = p_zg'g_wf
        x              = x_ ? lem_binds_env_th (concatE (Cons x_ t_x g) g') th' den_env'_th'
                            ? lem_in_env_concat g g' x_ 
                            ? lem_free_bound_in_env (concatE g g') t_z k_z p_g'g_tz x_
        den_env''_th'' = lem_remove_var_denote_env g x t_x g' p_g'g_wf th' den_env'_th'
        den_th''tz_vz  = lem_remove_var_denote th' t_z v_z den_th'tz_vz x
lem_remove_var_denote_env g x_ t_x (ConsT a k_a g') p_zg'g_wf th den_env_th = case den_env_th of
  (DExtT env' th' den_env'_th' _a _ka t_a p_emp_ta)
    -> DExtT (concatE g g') (remove_fromCS th' x) den_env''_th'' a k_a t_a p_emp_ta
      where
        (WFEBindT _ p_g'g_wf _ _) = p_zg'g_wf
        x              = x_ ? lem_binds_env_th (concatE (Cons x_ t_x g) g') th' den_env'_th'
                            ? lem_in_env_concat g g' x_ 
        den_env''_th'' = lem_remove_var_denote_env g x t_x g' p_g'g_wf th' den_env'_th'

{-@ lem_remove_tvar_denote_env :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
       -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
       -> ProofOf(WFEnv (concatE g g'))
       -> th:CSub -> ProofOf(DenotesEnv (concatE (ConsT a k_a g) g') th)
       -> ProofOf(DenotesEnv (concatE g g') (remove_fromCS th a )) @-}
lem_remove_tvar_denote_env :: Env -> Vname -> Kind -> Env -> WFEnv -> CSub 
                                 -> DenotesEnv -> DenotesEnv
lem_remove_tvar_denote_env g a  k_a Empty           p_g'g_wf  th den_env_th = case den_env_th of 
  (DExtT env' th' den_env'_th' _ _ t_a p_emp_ta) -> den_env'_th'
lem_remove_tvar_denote_env g a_ k_a (Cons z t_z g') p_ag'g_wf th den_env_th = case den_env_th of
  (DExt env' th' den_env'_th' _z _tz v_z den_th'tz_vz) -- env' == concatE (Cons x t_x g) g' 
    -> DExt (concatE g g') (remove_fromCS th' a) den_env''_th'' z t_z v_z den_th''tz_vz
      where
        (WFEBind _ p_g'g_wf _ _ k_z p_g'g_tz) = p_ag'g_wf
        a              = a_ ? lem_binds_env_th (concatE (ConsT a_ k_a g) g') th' den_env'_th'
                            ? lem_in_env_concat g g' a_ 
                            ? lem_free_bound_in_env (concatE g g') t_z k_z p_g'g_tz a_
        den_env''_th'' = lem_remove_tvar_denote_env g a k_a g' p_g'g_wf th' den_env'_th'
        den_th''tz_vz  = lem_remove_tvar_denote th' t_z v_z den_th'tz_vz a
lem_remove_tvar_denote_env g a_ k_a (ConsT a1 k1 g') p_a1g'g_wf th den_env_th = case den_env_th of
  (DExtT env' th' den_env'_th' _a1 _k1 t_a1 p_emp_ta1)
    -> DExtT (concatE g g') (remove_fromCS th' a) den_env''_th'' a1 k1 t_a1 p_emp_ta1
      where
        (WFEBindT _ p_g'g_wf _ _) = p_a1g'g_wf
        a              = a_ ? lem_binds_env_th (concatE (ConsT a_ k_a g) g') th' den_env'_th'
                            ? lem_in_env_concat g g' a_ 
        den_env''_th'' = lem_remove_tvar_denote_env g a k_a g' p_g'g_wf th' den_env'_th'
  *)
