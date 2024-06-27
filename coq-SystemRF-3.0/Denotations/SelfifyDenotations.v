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
Require Import Denotations.PrimitivesSemantics.
Require Import Denotations.PrimitivesDenotations.

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
