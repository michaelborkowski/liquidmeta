Require Import Arith.

Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.LocalClosure.
Require Import SystemRF.Strengthenings.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.BasicPropsWellFormedness.
Require Import SystemRF.Typing.
Require Import SystemRF.LemmasWeakenWF.
Require Import SystemRF.LemmasWellFormedness.
Require Import SystemRF.SubstitutionLemmaWF.
Require Import SystemRF.LemmasTyping.
Require Import SystemRF.LemmasWeakenTyp.
Require Import SystemRF.LemmasWeakenTypTV.
Require Import SystemRF.LemmasExactness. 

Lemma lem_subst_typ' : ( forall (g'xg : env) (e : expr) (t : type),
    Hastype g'xg e t -> ( forall (g g':env) (x:vname) (v_x:expr) (t_x:type),
        g'xg = concatE (Cons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> isValue v_x -> Hastype g v_x t_x -> WFEnv g
            -> Hastype (concatE g (esubFV x v_x g')) (subFV x v_x e) (tsubFV x v_x t ) )) /\ (
  forall (g'xg : env) (t : type) (t' : type),
    Subtype g'xg t t' -> ( forall (g g':env) (x:vname) (v_x:expr) (t_x:type),
      g'xg = concatE (Cons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> isValue v_x -> Hastype g v_x t_x -> WFEnv g
            -> Subtype (concatE g (esubFV x v_x g')) (tsubFV x v_x t) (tsubFV x v_x t') )).
Proof. apply ( judgments_mutind 
  (fun (g'xg : env) (e : expr) (t : type) (p_e_t : Hastype g'xg e t) => 
    forall (g g':env) (x:vname) (v_x:expr) (t_x:type),
      g'xg = concatE (Cons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> isValue v_x -> Hastype g v_x t_x -> WFEnv g
            -> Hastype (concatE g (esubFV x v_x g')) (subFV x v_x e) (tsubFV x v_x t ) )
  (fun (g'xg : env) (t : type) (t' : type) (p_t_t' : Subtype g'xg t t') => 
    forall (g g':env) (x:vname) (v_x:expr) (t_x:type),
      g'xg = concatE (Cons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> isValue v_x -> Hastype g v_x t_x -> WFEnv g
            -> Subtype (concatE g (esubFV x v_x g')) (tsubFV x v_x t) (tsubFV x v_x t') ));
  intro env; intros; subst env.
  - (* TBC *) rewrite lem_tsubFV_tybc; try apply TBC; assumption.
  - (* TIC *) rewrite lem_tsubFV_tyic; try apply TIC; assumption.
  - (* TVar *) rewrite lem_tsubFV_self; destruct (Nat.eqb x0 x) eqn:X.
    * simpl; rewrite X; apply Nat.eqb_eq in X; subst x0;
      apply lem_boundin_concat in b; simpl in b; destruct b; try destruct H;
      try ( apply lem_boundin_inenv in H; apply vbinds_subset in H;
            contradiction ); destruct H; subst t.
      apply lem_weaken_many_typ;
      try apply lem_exact_type;
      pose proof lem_subFV_notin as H'; destruct H' as [H'0 H'1];
      destruct H'1 as [H'1 H'2]; try rewrite H'1;
      try apply lem_typing_wf in H6 as Htx;
      assert (g = concatE g Empty) as Hg by reflexivity; try rewrite Hg;
      destruct k; try apply lem_strengthen_wftype_base with x t_x; simpl;
      try apply lem_strengthen_many_wftype_base with g';
      try apply lem_weaken_wf_top;
      try apply intersect_names_add_intro_l;
      try apply lem_free_bound_in_env with g Star ;
      try apply esubFV_unique; try rewrite esubFV_binds;
      try apply intersect_empty_r; unfold unique;
      intuition.
    * simpl; rewrite X; apply TVar; try apply lem_subst_wf with t_x;
      try apply lem_typing_hasftype; trivial;
      apply lem_boundin_concat in b; simpl in b; destruct b; try destruct H;
      apply lem_boundin_concat.
      + (* x = x0 *) destruct H; subst x0; apply Nat.eqb_neq in X; contradiction.
      + (* x in g *) left; pose proof lem_subFV_notin; destruct H8; destruct p; rewrite e0;
        try apply lem_free_bound_in_env with g Star;
        try apply boundin_wfenv_wftype with x; assumption.
      + (* x in g' *) right; apply lem_boundin_esubFV; assumption.
  - (* TPrm *) rewrite lem_tsubFV_ty; simpl; try apply TPrm; assumption.
  - (* TAbs *) simpl; apply TAbs with k_x (names_add x (union nms (binds (concatE g g'))));
    try apply lem_subst_wf with t_x0; try apply lem_typing_hasftype;
    try assumption; intros;
    apply not_elem_names_add_elim in H0; destruct H0;
    apply not_elem_union_elim in H9; destruct H9;
    apply not_elem_concat_elim in H10; destruct H10;
    assert (Cons y (tsubFV x v_x t_x) (concatE g (esubFV x v_x g')) 
            = concatE g (esubFV x v_x (Cons y t_x g')))
      by reflexivity; rewrite H12;
    rewrite <- lem_commute_subFV_unbind;
    try rewrite <- lem_commute_tsubFV_unbindT;
    try apply H with t_x0;
    try apply intersect_names_add_intro_r;
    try apply lem_typ_islc with g t_x0;
    unfold in_env; try apply not_elem_names_add_intro;
    simpl; intuition.
  - (* TApp *) simpl; apply TApp; simpl in H; 
    apply H with t_x0 || apply H0 with t_x0; trivial.
  - (* TAbsT *) simpl; apply TAbsT with (names_add x (union nms (binds (concatE g g'))));
    intros; apply not_elem_names_add_elim in H0; destruct H0;
    apply not_elem_union_elim in H9; destruct H9;
    apply not_elem_concat_elim in H10; destruct H10;
    assert (ConsT a' k (concatE g (esubFV x v_x g')) = concatE g (esubFV x v_x (ConsT a' k g')))
      by reflexivity; rewrite H12;
    try rewrite <- lem_commute_subFV_unbind_tv;
    try rewrite <- lem_commute_tsubFV_unbind_tvT;
    try apply H with t_x;
    try apply intersect_names_add_intro_r;
    try apply lem_typ_islc with g t_x;
    unfold in_env; try apply not_elem_names_add_intro; simpl; intuition.
  - (* TAppT *) rewrite lem_commute_tsubFV_tsubBTV; simpl;
    try apply TAppT with k; simpl in H;
    try apply H with t_x;
    try apply lemma_tsubFV_noExists;
    try apply lem_subst_wf with t_x;
    try apply lem_typing_hasftype;
    try apply lem_typ_islc with g t_x; trivial.
  - (* TLet *) simpl; apply TLet with (tsubFV x v_x t_x) k
                  (names_add x (union nms (binds (concatE g g'))));
    try apply lem_subst_wf with t_x0; try apply lem_typing_hasftype;
    try apply H with t_x0; trivial; intros;
    apply not_elem_names_add_elim in H1; destruct H1;
    apply not_elem_union_elim in H10; destruct H10;
    apply not_elem_concat_elim in H11; destruct H11;
    assert (Cons y (tsubFV x v_x t_x) (concatE g (esubFV x v_x g')) 
            = concatE g (esubFV x v_x (Cons y t_x g')))
      by reflexivity; rewrite H13;
    rewrite <- lem_commute_subFV_unbind;
    try rewrite <- lem_commute_tsubFV_unbindT;
    try apply H0 with t_x0;
    try apply intersect_names_add_intro_r;
    try apply lem_typ_islc with g t_x0;
    try apply not_elem_names_add_intro; simpl; auto.
  - (* TAnn *) simpl; apply TAnn; try apply lemma_tsubFV_noExists;
    try apply H with t_x; trivial.
  - (* TIf *) simpl; apply TIf with (psubFV x v_x ps) k 
                                    (names_add x (union nms (binds (concatE g g'))));
    simpl in H; try apply H with t_x;
    try apply lem_subst_wf with t_x;
    try apply lem_typing_hasftype; intros;
    try apply not_elem_names_add_elim in H2; try destruct H2;
    try apply not_elem_union_elim in H11; try destruct H11; 
    try apply not_elem_concat_elim in H12; try destruct H12;
    try assert (Cons y (self (TRefn TBool (psubFV x v_x ps)) (Bc true) Base) (concatE g (esubFV x v_x g')) 
            = concatE g (esubFV x v_x (Cons y (self (TRefn TBool ps) (Bc true) Base) g')))
      by reflexivity; try rewrite H14;
    try assert (Cons y (self (TRefn TBool (psubFV x v_x ps)) (Bc false) Base) (concatE g (esubFV x v_x g')) 
            = concatE g (esubFV x v_x (Cons y (self (TRefn TBool ps) (Bc false) Base) g')))
      by reflexivity; try rewrite H15; 
    try apply H0 with y t_x; try apply H1 with y t_x; 
    try apply not_elem_names_add_intro;
    try apply intersect_names_add_intro_r;
    simpl; try split; auto.
  - (* TSub *) apply TSub with (tsubFV x v_x s) k; 
    try apply H with t_x; try apply lem_subst_wf with t_x;
    try apply lem_typing_hasftype;
    try apply H0 with t_x; trivial.
  - (* SBase *) simpl; apply SBase with (names_add x (union nms (binds (concatE g g'))));
    intros; repeat rewrite <- lem_commute_psubFV_unbindP; 
    assert ( Cons y (TRefn b PEmpty) (concatE g (esubFV x v_x g'))
              = concatE g (esubFV x v_x (Cons y (TRefn b PEmpty) g')) )
      as Henv by reflexivity; try rewrite Henv;
    try apply ISub with t_x; simpl; try apply i;
    apply not_elem_names_add_elim in H; destruct H;
    apply not_elem_union_elim in H8; destruct H8;
    apply not_elem_concat_elim in H9; destruct H9;
    try apply lem_typ_islc with g t_x;
    try apply not_elem_names_add_intro;
    try apply intersect_names_add_intro_r;
    simpl; try split; intuition.
  - (* SFunc *) simpl; apply SFunc with (names_add x (union nms (binds (concatE g g'))));
    try apply H with t_x; trivial; intros;
    apply not_elem_names_add_elim in H1; destruct H1;
    apply not_elem_union_elim in H10; destruct H10;
    apply not_elem_concat_elim in H11; destruct H11;
    repeat rewrite <- lem_commute_tsubFV_unbindT;
    assert (Cons y (tsubFV x v_x s2) (concatE g (esubFV x v_x g')) 
            = concatE g (esubFV x v_x (Cons y s2 g')))
      by reflexivity; try rewrite H13;
    try apply H0 with t_x;
    try apply intersect_names_add_intro_r;  
    try apply lem_typ_islc with g t_x;
    try apply not_elem_names_add_intro; simpl; intuition.
  - (* SWitn *) simpl; apply SWitn with (subFV x v_x0 v_x);
    try apply lem_subFV_value; try apply H with t_x0;
    try rewrite <- lem_commute_tsubFV_tsubBV;
    try apply H0 with t_x0; try apply lem_typ_islc with g t_x0; trivial.
  - (* SBind *) simpl; apply SBind with (names_add x (union nms (binds (concatE g g'))));
    try apply lem_islc_at_subFV; try apply lem_typ_islc with g t_x0;
    trivial; intros;
    apply not_elem_names_add_elim in H0; destruct H0;
    apply not_elem_union_elim in H9; destruct H9;
    apply not_elem_concat_elim in H10; destruct H10;
    try rewrite <- lem_commute_tsubFV_unbindT;
    assert (Cons y (tsubFV x v_x t_x) (concatE g (esubFV x v_x g')) 
            = concatE g (esubFV x v_x (Cons y t_x g')))
      by reflexivity; try rewrite H12;
    try apply H with t_x0;
    try apply intersect_names_add_intro_r;  
    try apply lem_typ_islc with g t_x0;
    try apply not_elem_names_add_intro; simpl; intuition.
  - (* SPoly *) simpl; apply SPoly with (names_add x (union nms (binds (concatE g g'))));
    intros; apply not_elem_names_add_elim in H0; destruct H0;
    apply not_elem_union_elim in H9; destruct H9;
    apply not_elem_concat_elim in H10; destruct H10;
    repeat rewrite <- lem_commute_tsubFV_unbind_tvT;
    assert (ConsT a k (concatE g (esubFV x v_x g')) 
              = concatE g (esubFV x v_x (ConsT a k g')))
        by reflexivity; try rewrite H12;
    try apply H with t_x;
    try apply lem_typ_islc with g t_x; 
    try apply not_elem_names_add_intro;
    try apply intersect_names_add_intro_r; simpl; try split; intuition.
  Qed.

Lemma lem_subst_typ : forall (g g':env) (x:vname) (v_x:expr) (t_x:type) (e:expr) (t:type),
    Hastype (concatE (Cons x t_x g) g') e t 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> isValue v_x -> Hastype g v_x t_x -> WFEnv g
            -> Hastype (concatE g (esubFV x v_x g')) (subFV x v_x e) (tsubFV x v_x t ).
Proof. intros; pose proof lem_subst_typ'; destruct H8 as [Htyp Hsub];
  apply Htyp with (concatE (Cons x t_x g) g') t_x; trivial. Qed.

Lemma lem_subst_typ_top : forall (g:env) (x:vname) (v_x:expr) (t_x:type) (e:expr) (t:type),
    Hastype (Cons x t_x g) e t 
            -> unique g -> ~ (in_env x g) 
            -> isValue v_x -> Hastype g v_x t_x -> WFEnv g
            -> Hastype g (subFV x v_x e) (tsubFV x v_x t ).
Proof. intros; assert (g = concatE g (esubFV x v_x Empty)) by reflexivity;
  rewrite H5; apply lem_subst_typ with t_x; try apply intersect_empty_r; 
  unfold unique; intuition. Qed.

Lemma lem_subst_subtype : forall (g g':env) (x:vname) (v_x:expr) (t_x:type) (t t':type),
        Subtype (concatE (Cons x t_x g) g') t t' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> isValue v_x -> Hastype g v_x t_x -> WFEnv g
            -> Subtype (concatE g (esubFV x v_x g')) (tsubFV x v_x t) (tsubFV x v_x t').
Proof. intros; pose proof lem_subst_typ'; destruct H8 as [Htyp Hsub];
  apply Hsub with (concatE (Cons x t_x g) g') t_x; trivial. Qed.

Lemma lem_subst_subtype_top : forall (g:env) (x:vname) (v_x:expr) (t_x:type) (t t':type),
        Subtype (Cons x t_x g) t t' 
            -> unique g -> ~ (in_env x g) 
            -> isValue v_x -> Hastype g v_x t_x -> WFEnv g
            -> Subtype g (tsubFV x v_x t) (tsubFV x v_x t').
Proof. intros; assert (g = concatE g (esubFV x v_x Empty)) by reflexivity;
  rewrite H5; apply lem_subst_subtype with t_x; try apply intersect_empty_r; 
  unfold unique; intuition. Qed.