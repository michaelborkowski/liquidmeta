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
Require Import SystemRF.LemmasWeakenWFTV.
Require Import SystemRF.LemmasWellFormedness.
Require Import SystemRF.SubstitutionLemmaWFTV.
Require Import SystemRF.LemmasTyping.
Require Import SystemRF.LemmasWeakenTypTV.
Require Import SystemRF.LemmasSubtyping.
Require Import SystemRF.LemmasExactness.
Require Import SystemRF.LemmasExactnessSubst. 

Lemma lem_subst_tv_typ' : ( forall (g'ag : env) (e : expr) (t : type),
    Hastype g'ag e t -> ( forall (g g':env) (a:vname) (t_a:type) (k_a:kind),
        g'ag = concatE (ConsT a k_a g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env a g) -> ~ (in_env a g') 
            -> noExists t_a -> WFtype g t_a k_a -> WFEnv g
            -> Hastype (concatE g (esubFTV a t_a g')) (subFTV a t_a e) (tsubFTV a t_a t ) )) /\ (
  forall (g'ag : env) (t : type) (t' : type),
    Subtype g'ag t t' -> ( forall (g g':env) (a:vname) (t_a:type) (k_a:kind),
    g'ag = concatE (ConsT a k_a g) g'  
        -> unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> ~ (in_env a g) -> ~ (in_env a g') 
        -> noExists t_a -> WFtype g t_a k_a -> WFEnv g
        -> Subtype (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) (tsubFTV a t_a t') )).
Proof. apply ( judgments_mutind 
  (fun (g'ag : env) (e : expr) (t : type) (p_e_t : Hastype g'ag e t) => 
    forall (g g':env) (a:vname) (t_a:type) (k_a:kind),
      g'ag = concatE (ConsT a k_a g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env a g) -> ~ (in_env a g') 
            -> noExists t_a -> WFtype g t_a k_a -> WFEnv g
            -> Hastype (concatE g (esubFTV a t_a g')) (subFTV a t_a e) (tsubFTV a t_a t ) )
  (fun (g'ag : env) (t : type) (t' : type) (p_t_t' : Subtype g'ag t t') => 
    forall (g g':env) (a:vname) (t_a:type) (k_a:kind),
      g'ag = concatE (ConsT a k_a g) g'  
        -> unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> ~ (in_env a g) -> ~ (in_env a g') 
        -> noExists t_a -> WFtype g t_a k_a -> WFEnv g
        -> Subtype (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) (tsubFTV a t_a t') ) );
  intro env; intros; subst env.
  - (* TBC *) rewrite lem_tsubFTV_tybc; try apply TBC; assumption.
  - (* TIC *) rewrite lem_tsubFTV_tyic; try apply TIC; assumption.
  - (* TVar *) apply lem_boundin_concat in b; simpl in b; simpl; destruct k.
    * (* Base *) apply TSub with (self (tsubFTV a t_a t) (FV x) Base) Base;
      try apply TVar; try apply lem_boundin_concat; 
      try ( apply lem_subst_tv_wf' with k_a; try apply lem_selfify_wf);
      try apply lem_self_subst_tv_sub; try apply lem_subst_tv_wf' with k_a;
      try (apply lem_wftype_islct with g k_a; assumption);
      try apply lem_wftype_islct with (concatE (ConsT a k_a g) g') Base;
      try apply FTVar; try apply boundin_erase_env; try rewrite lem_boundin_concat;
      destruct b;
      try apply (boundin_wfenv_wftype x t g H) in H7 as p_g_t;
      try ( left; pose proof lem_subFTV_notin; destruct H8; destruct p; rewrite e0;
            try apply H; apply lem_free_bound_in_env with g Star );
      try ( right; apply lem_boundin_esubFTV ); simpl; intuition.
    * (* Star *) rewrite lem_self_star; 
      rewrite <- lem_self_star with (tsubFTV a t_a t) (FV x); apply TVar;
      try apply lem_boundin_concat; destruct b; 
      try ( left; pose proof lem_subFTV_notin; destruct H8; destruct p; rewrite e0;
            try apply H; apply lem_free_bound_in_env with g Star );
      try ( right; apply lem_boundin_esubFTV );
      try apply lem_subst_tv_wf' with k_a;
      try (apply boundin_wfenv_wftype with x; assumption); assumption.
  - (* TPrm *) rewrite lem_tsubFTV_ty; simpl; try apply TPrm; assumption.
  - (* TAbs *) simpl; apply TAbs with k_x (names_add a (union nms (binds (concatE g g'))));
    try apply lem_subst_tv_wf' with k_a; try assumption; intros;
    apply not_elem_names_add_elim in H0; destruct H0;
    apply not_elem_union_elim in H9; destruct H9;
    apply not_elem_concat_elim in H10; destruct H10;
    assert (Cons y (tsubFTV a t_a t_x) (concatE g (esubFTV a t_a g')) 
            = concatE g (esubFTV a t_a (Cons y t_x g')))
      by reflexivity; rewrite H12;
    rewrite <- lem_commute_subFTV_unbind;
    try rewrite <- lem_commute_tsubFTV_unbindT;
    try apply H with k_a;
    try apply intersect_names_add_intro_r;  
    try apply lem_wftype_islct with g k_a;
    unfold in_env; try apply not_elem_names_add_intro;
    simpl; intuition.
  - (* TApp *) simpl; apply TApp; simpl in H; 
    apply H with k_a || apply H0 with k_a; trivial.
  - (* TAbsT *) simpl; apply TAbsT with (names_add a (union nms (binds (concatE g g'))));
    intros; apply not_elem_names_add_elim in H0; destruct H0;
    apply not_elem_union_elim in H9; destruct H9;
    apply not_elem_concat_elim in H10; destruct H10;
    assert (ConsT a' k (concatE g (esubFTV a t_a g')) = concatE g (esubFTV a t_a (ConsT a' k g')))
      by reflexivity; rewrite H12;
    try rewrite <- lem_commute_subFTV_unbind_tv;
    try rewrite <- lem_commute_tsubFTV_unbind_tvT;
    try apply H with k_a;
    try apply intersect_names_add_intro_r;
    try apply lem_wftype_islct with g k_a;
    unfold in_env; try apply not_elem_names_add_intro; simpl; intuition.
  - (* TAppT *) rewrite lem_commute_tsubFTV_tsubBTV; simpl;
    try apply TAppT with k; simpl in H;
    try apply H with k_a;
    try apply lemma_tsubFTV_noExists;
    try apply lem_subst_tv_wf' with k_a;
    try apply lem_wftype_islct with g k_a; trivial.
  - (* TLet *) simpl; apply TLet with (tsubFTV a t_a t_x) k
                  (names_add a (union nms (binds (concatE g g'))));
    try apply lem_subst_tv_wf' with k_a;
    try apply H with k_a; trivial; intros;
    apply not_elem_names_add_elim in H1; destruct H1;
    apply not_elem_union_elim in H10; destruct H10;
    apply not_elem_concat_elim in H11; destruct H11;
    assert (Cons y (tsubFTV a t_a t_x) (concatE g (esubFTV a t_a g')) 
            = concatE g (esubFTV a t_a (Cons y t_x g')))
      by reflexivity; rewrite H13;
    rewrite <- lem_commute_subFTV_unbind;
    try rewrite <- lem_commute_tsubFTV_unbindT;
    try apply H0 with k_a;
    try apply intersect_names_add_intro_r;
    try apply lem_wftype_islct with g k_a;
    try apply not_elem_names_add_intro; simpl; auto.
  - (* TAnn *) simpl; apply TAnn; try apply lemma_tsubFTV_noExists;
    try apply H with k_a; trivial.
  - (* TIf *) simpl; apply TIf with (psubFTV a t_a ps) k 
                                    (names_add a (union nms (binds (concatE g g'))));
    simpl in H; try apply H with k_a;
    try apply lem_subst_tv_wf with k_a;
    try apply lem_typing_hasftype; intros;
    try apply not_elem_names_add_elim in H2; try destruct H2;
    try apply not_elem_union_elim in H11; try destruct H11; 
    try apply not_elem_concat_elim in H12; try destruct H12;     
    try assert (Cons y (TRefn TBool (PCons (BV 0) (psubFTV a t_a ps))) 
                       (concatE g (esubFTV a t_a g')) 
            = concatE g (esubFTV a t_a (Cons y (TRefn TBool (PCons (BV 0) ps)) g')))
      by reflexivity; try rewrite H14; 
    try assert (Cons y (TRefn TBool (PCons (App (Prim Not) (BV 0)) (psubFTV a t_a ps))) 
                       (concatE g (esubFTV a t_a g')) 
            = concatE g (esubFTV a t_a (Cons y (TRefn TBool (PCons (App (Prim Not) (BV 0)) ps)) g')))
      by reflexivity; try rewrite H15; 
    try apply H0 with y k_a; try apply H1 with y k_a; 
    try apply lem_erase_env_wfenv;
    try apply not_elem_names_add_intro;
    try apply intersect_names_add_intro_r;
    simpl; try split; auto. 
  - (* TSub *) apply TSub with (tsubFTV a t_a s) k; 
    try apply H with k_a; try apply lem_subst_tv_wf' with k_a;
    try apply H0 with k_a; trivial.
  - (* SBase *) destruct b eqn:B; try destruct (Nat.eqb a a0) eqn:A; 
    simpl; try rewrite A;
    try ( apply SBase with (names_add a (union nms (binds (concatE g g'))));
          intros; repeat rewrite <- lem_commute_psubFTV_unbindP; try rewrite <- B;
          assert ( Cons y (TRefn b PEmpty) (concatE g (esubFTV a t_a g'))
                    = concatE g (esubFTV a t_a (Cons y (TRefn b PEmpty) g')) )
            as Henv by ( rewrite B; simpl; try rewrite A; reflexivity ); 
          try rewrite Henv;
          try apply ISubTV with k_a; try (rewrite B; apply i);
          apply not_elem_names_add_elim in H; destruct H;
          apply not_elem_union_elim in H8; destruct H8;
          apply not_elem_concat_elim in H9; destruct H9;
          try apply lem_wftype_islct with g k_a;
          try apply not_elem_names_add_intro;
          try apply intersect_names_add_intro_r;
          simpl; try split; intuition ).
    (* b = FTV a *) destruct t_a eqn:TA; try (simpl in H5; contradiction); simpl; 
    try ( apply lem_sub_refl with k_a; 
          rewrite <- TA; rewrite <- TA in H6;
          try apply lem_weaken_many_wf; 
          try apply esubFTV_unique; try rewrite esubFTV_binds; 
          trivial).
    apply SBase with (names_add a (union nms (binds (concatE g g')))); intros;
    apply not_elem_names_add_elim in H; destruct H;
    apply not_elem_union_elim in H8; destruct H8;
    apply not_elem_concat_elim in H9; destruct H9;
    repeat rewrite lem_unbindP_strengthen; apply IStren;
    try apply not_elem_concat_intro; try rewrite esubFTV_binds; trivial;
    repeat rewrite <- lem_commute_psubFTV_unbindP; try repeat rewrite <- TA;
    assert ( Nat.eqb a a = true ) as AA by (apply Nat.eqb_eq; reflexivity);
    assert ( Cons y t_a (concatE g (esubFTV a t_a g'))
                    = concatE g (esubFTV a t_a (Cons y (TRefn (FTV a) PEmpty) g')) )
      as Henv by (simpl; rewrite AA; rewrite lem_push_empty; try rewrite TA; trivial); 
      try rewrite Henv;
    try apply ISubTV with k_a; 
    simpl; apply Nat.eqb_eq in A; subst a0; try apply i;
    try rewrite TA; try apply lem_wftype_islct with g k_a;
    try apply intersect_names_add_intro_r; 
    try apply not_elem_names_add_intro; intuition.
  - (* SFunc *) simpl; apply SFunc with (names_add a (union nms (binds (concatE g g'))));
    try apply H with k_a; trivial; intros;
    apply not_elem_names_add_elim in H1; destruct H1;
    apply not_elem_union_elim in H10; destruct H10;
    apply not_elem_concat_elim in H11; destruct H11;
    repeat rewrite <- lem_commute_tsubFTV_unbindT;
    assert (Cons y (tsubFTV a t_a s2) (concatE g (esubFTV a t_a g')) 
            = concatE g (esubFTV a t_a (Cons y s2 g')))
      by reflexivity; try rewrite H13;
    try apply H0 with k_a;
    try apply intersect_names_add_intro_r;  
    try apply lem_wftype_islct with g k_a;
    try apply not_elem_names_add_intro; simpl; intuition.
  - (* SWitn *) simpl; apply SWitn with (subFTV a t_a v_x);
    try apply lem_subFTV_value; try apply H with k_a;
    try rewrite <- lem_commute_tsubFTV_tsubBV;
    try apply H0 with k_a; try apply lem_wftype_islct with g k_a;    
    trivial.
  - (* SBind *) simpl; apply SBind with (names_add a (union nms (binds (concatE g g'))));
    try apply lem_islc_at_subFTV; try apply (lem_wftype_islct g t_a) with k_a;
    trivial; intros;
    apply not_elem_names_add_elim in H0; destruct H0;
    apply not_elem_union_elim in H9; destruct H9;
    apply not_elem_concat_elim in H10; destruct H10;
    try rewrite <- lem_commute_tsubFTV_unbindT;
    assert (Cons y (tsubFTV a t_a t_x) (concatE g (esubFTV a t_a g')) 
            = concatE g (esubFTV a t_a (Cons y t_x g')))
      by reflexivity; try rewrite H12;
    try apply H with k_a;
    try apply intersect_names_add_intro_r;  
    try apply lem_wftype_islct with g k_a;
    try apply not_elem_names_add_intro; simpl; intuition.
  - (* SPoly *) simpl; apply SPoly with (names_add a (union nms (binds (concatE g g'))));
    intros; apply not_elem_names_add_elim in H0; destruct H0;
    apply not_elem_union_elim in H9; destruct H9;
    apply not_elem_concat_elim in H10; destruct H10;
    repeat rewrite <- lem_commute_tsubFTV_unbind_tvT;
    assert (ConsT a0 k (concatE g (esubFTV a t_a g')) 
              = concatE g (esubFTV a t_a (ConsT a0 k g')))
        by reflexivity; try rewrite H12;
    try apply H with k_a;
    try apply lem_wftype_islct with g k_a; 
    try apply not_elem_names_add_intro;
    try apply intersect_names_add_intro_r; simpl; try split; intuition.
  Qed.

Lemma lem_subst_tv_typ : forall (g g':env) (a:vname) (t_a:type) (k_a:kind) (e:expr) (t:type),
    Hastype (concatE (ConsT a k_a g) g') e t 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env a g) -> ~ (in_env a g') 
            -> noExists t_a -> WFtype g t_a k_a -> WFEnv g
            -> Hastype (concatE g (esubFTV a t_a g')) (subFTV a t_a e) (tsubFTV a t_a t ).
Proof. intros; pose proof lem_subst_tv_typ'; destruct H8 as [Htyp Hsub];
  apply Htyp with (concatE (ConsT a k_a g) g') k_a; trivial. Qed.

Lemma lem_subst_tv_typ_top : forall (g:env) (a:vname) (t_a:type) (k_a:kind) (e:expr) (t:type),
    Hastype (ConsT a k_a g) e t 
            -> unique g -> ~ (in_env a g) 
            -> noExists t_a -> WFtype g t_a k_a -> WFEnv g
            -> Hastype g (subFTV a t_a e) (tsubFTV a t_a t).
Proof. intros; assert (g = concatE g (esubFTV a t_a Empty)) by reflexivity;
  rewrite H5; apply lem_subst_tv_typ with k_a; try apply intersect_empty_r; 
  unfold unique; intuition. Qed.

Lemma lem_subst_tv_subtype : forall (g g':env) (a:vname) (t_a:type) (k_a:kind) (t t':type),
        Subtype (concatE (ConsT a k_a g) g') t t' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env a g) -> ~ (in_env a g') 
            -> noExists t_a -> WFtype g t_a k_a -> WFEnv g
            -> Subtype (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) (tsubFTV a t_a t').
Proof. intros; pose proof lem_subst_tv_typ'; destruct H8 as [Htyp Hsub];
  apply Hsub with (concatE (ConsT a k_a g) g') k_a; trivial. Qed.

Lemma lem_subst_tv_subtype_top : forall (g:env) (a:vname) (t_a:type) (k_a:kind) (t t':type),
        Subtype (ConsT a k_a g) t t' 
            -> unique g -> ~ (in_env a g) 
            -> noExists t_a -> WFtype g t_a k_a -> WFEnv g
            -> Subtype g (tsubFTV a t_a t) (tsubFTV a t_a t').
Proof. intros; assert (g = concatE g (esubFTV a t_a Empty)) by reflexivity;
  rewrite H5; apply lem_subst_tv_subtype with k_a; try apply intersect_empty_r; 
  unfold unique; intuition. Qed.