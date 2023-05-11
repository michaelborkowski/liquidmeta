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
  - (* CConsT *) apply lem_wftype_islct in H2; assumption. 
  Qed.

Lemma lem_denotesenv_closed : forall (g:env) (th:csub), 
    DenotesEnv g th -> closed th.
Proof. intros; induction H; simpl; trivial.
  - (* CCons *) apply lem_den_hasftype in H1;
    apply lem_fv_subset_bindsF in H1; repeat split;
    try apply IHDenotesEnv; apply no_elem_empty; intuition.
  - (* CConsT *) apply lem_free_subset_binds in H2;repeat split;
    try apply IHDenotesEnv; apply no_elem_empty; intuition.
  Qed.

Lemma lem_denotesenv_substitutable : forall (g:env) (th:csub), 
    DenotesEnv g th -> substitutable th.
Proof. intros; induction H; simpl; try split; trivial.
  apply lem_den_isvalue with (ctsubst th t); apply H1. Qed.

Lemma lem_denotesenv_uniqueC : forall (g:env) (th:csub),
    DenotesEnv g th -> uniqueC th.
Proof. intros g th; revert g; induction th; simpl; trivial.
  - intros; split; inversion H.
  pose proof lem_binds_env_th. ...... 


Lemma lem_bound_in_denotesenv : 
  forall (x:vname) (t:type) (g:env) (th:csub),
    bound_in x t g -> DenotesEnv g th 
        -> Denotes (ctsubst th t) (csubst th (FV x)).
Proof. 



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
        try split; trivial;
        rewrite lem_ctsubst_self_FTV with th a (TRefn (FTV a) ps) v k;
        try apply lem_denotes_tsubFTV_self;
        try apply lem_subFTV_notin;
        try apply lem_csubst_isLC;
        assert (ftv (csubst th v) = empty)
          by (apply lem_csubst_pres_noftv; trivial);
        try rewrite H11; simpl; auto.
        rewrite <- lem_unroll_ctsubst_tv_left;
        unfold csubst in H10; fold csubst in H10;
        assert (subFTV a t_a v = v)
          by (apply lem_subFTV_notin; rewrite H6; auto);
          rewrite H13 in H10; try apply H10; intuition.
      + rewrite lem_unroll_ctsubst_tv_left;
        try split; trivial;
        rewrite lem_ctsubst_self_FTV with th a (TExists t0_1 t0_2) v k;
        try apply lem_denotes_tsubFTV_self;
        try apply lem_subFTV_notin;
        try apply lem_csubst_isLC;
        assert (ftv (csubst th v) = empty)
          by (apply lem_csubst_pres_noftv; trivial);
        try rewrite H13;  
        try rewrite <- lem_unroll_ctsubst_tv_left;
        unfold csubst in H10; fold csubst in H10;
        assert (subFTV a t_a v = v)
          by (apply lem_subFTV_notin; rewrite H6; auto);
        try rewrite H14 in H10; 
        try apply H10;
        simpl; auto.
    * (* No *) simpl; rewrite lem_tsubFTV_self_noFTV;
      try apply IHth; simpl in H10; 
      assert (subFTV a t_a v = v)
          by (apply lem_subFTV_notin; rewrite H6; auto);
      try apply H10; try rewrite H12; trivial.
  Qed.
