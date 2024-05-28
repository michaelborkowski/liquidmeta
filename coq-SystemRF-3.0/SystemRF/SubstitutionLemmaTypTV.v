Require Import Arith.
Require Import ZArith.

Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.LocalClosure.
Require Import SystemRF.Strengthenings.
Require Import SystemRF.SystemFWellFormedness.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.BasicPropsWellFormedness.
Require Import SystemRF.Typing.
Require Import SystemRF.LemmasWeakenWF.
Require Import SystemRF.LemmasWeakenWFTV.
Require Import SystemRF.LemmasWellFormedness.
Require Import SystemRF.SubstitutionLemmaWF.
Require Import SystemRF.SubstitutionLemmaWFTV.
Require Import SystemRF.LemmasTyping.
Require Import SystemRF.LemmasWeakenTypTV.
Require Import SystemRF.LemmasSubtyping.
Require Import SystemRF.LemmasExactness.
Require Import SystemRF.LemmasExactnessSubst. 

Lemma lem_subst_tv_typ' : ( forall (g'ag : env) (e : expr) (t : type),
    Hastype g'ag e t -> ( forall (g g':env) (a:vname) (t_a:type) (k_a:kind),
        g'ag = concatE (EConsT a k_a g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env a g) -> ~ (in_env a g') 
            -> isMono t_a -> noExists t_a -> WFtype g t_a k_a -> WFEnv (concatE (EConsT a k_a g) g')
            -> Hastype (concatE g (esubFTV a t_a g')) (subFTV a t_a e) (tsubFTV a t_a t ) )) /\ (
  forall (g'ag : env) (t : type) (t' : type),
    Subtype g'ag t t' -> ( forall (g g':env) (a:vname) (t_a:type) (k_a k_t k_t':kind),
    g'ag = concatE (EConsT a k_a g) g'  
        -> unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> ~ (in_env a g) -> ~ (in_env a g') 
        -> isMono t_a -> noExists t_a -> WFtype g t_a k_a
        -> WFEnv (concatE (EConsT a k_a g) g')
        -> WFtype (concatE (EConsT a k_a g) g') t  k_t
        -> WFtype (concatE (EConsT a k_a g) g') t' k_t'
        -> Subtype (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) (tsubFTV a t_a t') )).
Proof. apply ( judgments_mutind 
  (fun (g'ag : env) (e : expr) (t : type) (p_e_t : Hastype g'ag e t) => 
    forall (g g':env) (a:vname) (t_a:type) (k_a:kind),
      g'ag = concatE (EConsT a k_a g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env a g) -> ~ (in_env a g') 
            -> isMono t_a -> noExists t_a -> WFtype g t_a k_a -> WFEnv (concatE (EConsT a k_a g) g')
            -> Hastype (concatE g (esubFTV a t_a g')) (subFTV a t_a e) (tsubFTV a t_a t ) )
  (fun (g'ag : env) (t : type) (t' : type) (p_t_t' : Subtype g'ag t t') => 
    forall (g g':env) (a:vname) (t_a:type) (k_a k_t k_t':kind),
      g'ag = concatE (EConsT a k_a g) g'  
        -> unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> ~ (in_env a g) -> ~ (in_env a g') 
        -> isMono t_a -> noExists t_a -> WFtype g t_a k_a 
        -> WFEnv (concatE (EConsT a k_a g) g')
        -> WFtype (concatE (EConsT a k_a g) g') t  k_t
        -> WFtype (concatE (EConsT a k_a g) g') t' k_t'
        -> Subtype (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) (tsubFTV a t_a t') ) );
  intro env; intros; subst env.
  - (* TBC *) rewrite lem_tsubFTV_tybc; try apply TBC; assumption.
  - (* TIC *) rewrite lem_tsubFTV_tyic; try apply TIC; assumption.
  - (* TVar *) apply lem_boundin_concat in b; simpl in b; simpl; destruct k;
    apply lem_truncate_wfenv in H8 as H8'; inversion H8'; subst a0 k g0.
    * (* Base *) apply TSub with (self (tsubFTV a t_a t) (FV x) Base) Base;
      try apply TVar; try apply lem_boundin_concat; 
      try ( apply lem_subst_tv_wf' with k_a; try apply lem_selfify_wf);
      try apply lem_self_subst_tv_sub; try apply lem_subst_tv_wf' with k_a;
      try (apply lem_wftype_islct with g k_a; assumption);
      try apply lem_wftype_islct with (concatE (EConsT a k_a g) g') Base;
      try apply FTVar; try apply boundin_erase_env; try rewrite lem_boundin_concat;
      destruct b;
      try apply (boundin_wfenv_wftype x t g H) in H10 as p_g_t;
      try ( left; pose proof lem_subFTV_notin; destruct H9; destruct p; rewrite e0;
            try apply H; apply lem_free_bound_in_env with g Star );
      try ( right; apply lem_boundin_esubFTV ); simpl; auto.
    * (* Star *) rewrite lem_self_star; 
      rewrite <- lem_self_star with (tsubFTV a t_a t) (FV x); apply TVar;
      try apply lem_boundin_concat; destruct b; 
      try ( left; pose proof lem_subFTV_notin; destruct H9; destruct p; rewrite e0;
            try apply H; apply lem_free_bound_in_env with g Star );
      try ( right; apply lem_boundin_esubFTV );
      try apply lem_subst_tv_wf' with k_a;
      try (apply boundin_wfenv_wftype with x; assumption); assumption.
  - (* TPrm *) rewrite lem_tsubFTV_ty; simpl; try apply TPrm; assumption.
  - (* TAbs *) simpl; apply TAbs with k_x (names_add a (union nms (binds (concatE g g'))));
    apply lem_truncate_wfenv in H9 as H9'; inversion H9'; subst a0 k g0;
    try apply lem_subst_tv_wf' with k_a; try assumption; intros;
    apply not_elem_names_add_elim in H0; destruct H0;
    apply not_elem_union_elim in H10; destruct H10;
    apply not_elem_concat_elim in H12; destruct H12;
    assert (ECons y (tsubFTV a t_a t_x) (concatE g (esubFTV a t_a g')) 
            = concatE g (esubFTV a t_a (ECons y t_x g')))
      by reflexivity; rewrite H15;
    rewrite <- lem_commute_subFTV_unbind;
    try rewrite <- lem_commute_tsubFTV_unbindT;
    try apply H with k_a;
    try apply WFEBind with k_x; 
    try apply intersect_names_add_intro_r;  
    try apply lem_wftype_islct with g k_a;
    pose proof (lem_binds_concat (EConsT a k_a g) g');
    destruct H16; try apply not_elem_names_add_intro; trivial;
    try apply not_elem_subset with (union (binds (EConsT a k_a g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro;
    simpl; auto.
  - (* TApp *) simpl; apply TApp; simpl in H; 
    apply H with k_a || apply H0 with k_a; trivial.
  - (* TAbsT *) simpl; apply TAbsT with (names_add a (union nms (binds (concatE g g'))));
    apply lem_truncate_wfenv in H9 as H9'; inversion H9'; subst a0 k0 g0;
    intros; apply not_elem_names_add_elim in H0; destruct H0;
    apply not_elem_union_elim in H10; destruct H10;
    apply not_elem_concat_elim in H12; destruct H12;
    assert (EConsT a' k (concatE g (esubFTV a t_a g')) = concatE g (esubFTV a t_a (EConsT a' k g')))
      by reflexivity; rewrite H15;
    try rewrite <- lem_commute_subFTV_unbind_tv;
    try rewrite <- lem_commute_tsubFTV_unbind_tvT;
    try apply H with k_a; try apply WFEBindT;
    try apply intersect_names_add_intro_r;
    try apply lem_wftype_islct with g k_a;
    pose proof (lem_binds_concat (EConsT a k_a g) g');
    destruct H16; try apply not_elem_names_add_intro; trivial;
    try apply not_elem_subset with (union (binds (EConsT a k_a g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; simpl; auto.
  - (* TAppT *) rewrite lem_commute_tsubFTV_tsubBTV; simpl;
    apply lem_truncate_wfenv in H9 as H9'; inversion H9'; subst a0 k0 g0;
    try apply TAppT with k; simpl in H;
    try apply H with k_a;
    try apply lemma_tsubFTV_isMono;
    try apply lemma_tsubFTV_noExists;
    try apply lem_subst_tv_wf' with k_a;
    try apply lem_wftype_islct with g k_a; trivial.
  - (* TLet *) simpl; apply TLet with (tsubFTV a t_a t_x) k
                  (names_add a (union nms (binds (concatE g g'))));
    apply lem_truncate_wfenv in H10 as H10'; inversion H10'; subst a0 k0 g0;
    try apply lem_subst_tv_wf' with k_a;
    try apply H with k_a; trivial; intros;
    apply not_elem_names_add_elim in H1; destruct H1;
    apply not_elem_union_elim in H11; destruct H11;
    apply not_elem_concat_elim in H13; destruct H13;
    assert (ECons y (tsubFTV a t_a t_x) (concatE g (esubFTV a t_a g')) 
            = concatE g (esubFTV a t_a (ECons y t_x g')))
      by reflexivity; rewrite H16;
    rewrite <- lem_commute_subFTV_unbind;
    try rewrite <- lem_commute_tsubFTV_unbindT;
    try apply H0 with k_a; try apply WFEBind with Star;
    try apply intersect_names_add_intro_r;
    try apply lem_wftype_islct with g k_a;
    try apply not_elem_names_add_intro;
    pose proof (lem_binds_concat (EConsT a k_a g) g');
    destruct H17; trivial;
    try apply not_elem_subset with (union (binds (EConsT a k_a g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; 
    try apply lem_typing_wf with e_x;  
    simpl; auto.
  - (* TAnn *) simpl; apply TAnn; try apply lemma_tsubFTV_noExists;
    try apply H with k_a; trivial.
  - (* TIf *) simpl; apply TIf with (psubFTV a t_a ps) k 
                                    (names_add a (union nms (binds (concatE g g'))));
    apply lem_truncate_wfenv in H11 as H11'; inversion H11'; subst a0 k0 g0;
    simpl in H; try apply H with k_a;
    try apply lem_subst_tv_wf with k_a; 
    try apply lem_erase_env_wfenv; trivial; intros;
    apply not_elem_names_add_elim in H2; destruct H2;
    apply not_elem_union_elim in H12; destruct H12; 
    apply not_elem_concat_elim in H14; destruct H14;     
    try assert (ECons y (self (TRefn TBool (psubFTV a t_a ps)) (Bc true) Base) 
                       (concatE g (esubFTV a t_a g')) 
            = concatE g (esubFTV a t_a (ECons y (self (TRefn TBool ps) (Bc true) Base) g')))
      by reflexivity; try rewrite H17; 
    try assert (ECons y (self (TRefn TBool (psubFTV a t_a ps)) (Bc false) Base)  
                       (concatE g (esubFTV a t_a g')) 
            = concatE g (esubFTV a t_a (ECons y (self (TRefn TBool ps) (Bc false) Base) g')))
      by reflexivity; try rewrite H18; 
    try apply H0 with y k_a; try apply H1 with y k_a; 
    try apply WFEBind with Base; fold concatE;
    try apply lem_selfify_wf; try apply FTBC;
    try apply not_elem_names_add_intro;
    try apply intersect_names_add_intro_r;
    pose proof (lem_binds_concat (EConsT a k_a g) g');
    try destruct H19; trivial; 
    try apply not_elem_subset with (union (binds (EConsT a k_a g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; 
    simpl; try discriminate; try split; auto;
    apply lem_typing_wf in h; try apply H10; 
    inversion h; trivial.
  - (* TNil *) apply TNil with k; fold tsubFTV;
    try apply lemma_tsubFTV_isMono; try apply lemma_tsubFTV_noExists;
    try apply lem_subst_tv_wf with k_a; 
    apply lem_truncate_wfenv in H8; inversion H8; 
    try apply lem_erase_env_wfenv; trivial. 
  - (* TCons *) apply TCons; fold tsubFTV;
    try apply lemma_tsubFTV_isMono; try apply lemma_tsubFTV_noExists;
    try apply H with k_a; try apply H0 with k_a; trivial.
  - (* TSwitch *)   apply TSwit with (tsubFTV a t_a t) (psubFTV a t_a ps) 
                              k (names_add a (union nms (binds (concatE g g'))));
    try apply lemma_tsubFTV_isMono; try apply lemma_tsubFTV_noExists;
    fold subFTV; fold tsubFTV; fold psubFTV; 
    simpl in H; try apply H with k_a;
    try intros y z Hy Hz Hyz; try intros y Hy;
    try assert (ECons y (TList (tsubFTV a t_a t) 
                          (PCons (eq (Ic 0) (length (tsubFTV a t_a t) (BV 0))) 
                            (psubFTV a t_a ps))) (concatE g (esubFTV a t_a g')) 
              = concatE g (esubFTV a t_a 
                            (ECons y (TList t (PCons (eq (Ic 0) (length t (BV 0))) 
                                                ps)) g')))
      as Henv1 by reflexivity; try rewrite Henv1;
    try apply not_elem_names_add_elim in Hy; try destruct Hy as [Hya Hy]; 
    try apply not_elem_union_elim in Hy; try destruct Hy as [Hynms Hy];
    try apply not_elem_concat_elim in Hy as Hyenv; 
    try destruct Hyenv as [Hyg Hyg'];
    try apply not_elem_names_add_elim in Hz; try destruct Hz as [Hza Hz];   
    try apply not_elem_union_elim in Hz; try destruct Hz as [Hznms Hz];
    try apply not_elem_concat_elim in Hz as Hzenv; 
    try destruct Hzenv as [Hzg Hzg'];
    try assert (ECons z (TList (tsubFTV a t_a t) 
                          (PCons (eq (App (Prim Succ) (length (tsubFTV a t_a t) (FV y))) 
                                     (length (tsubFTV a t_a t) (BV 0))) PEmpty)) 
                  (ECons y (TList (tsubFTV a t_a t) (psubFTV a t_a ps)) 
                    (concatE g (esubFTV a t_a g')))
              = concatE g (esubFTV a t_a 
                  (ECons z (TList t (PCons (eq (App (Prim Succ) (length t (FV y))) 
                                               (length t (BV 0))) PEmpty)) 
                    (ECons y (TList t ps) g'))) )
      as Henv2 by reflexivity; try rewrite Henv2; 
    simpl in H1; 
    try apply H0 with y k_a; try apply H1 with z k_a;  
    try apply lem_subst_tv_wf with k_a; 
    try apply WFEBind with Star;
    try apply WFEBind with Star;
    apply lem_typing_wf in h as p_env_tps; try apply p_env_tps;
    try apply lem_wflist_len_zero; try assumption;          
    try apply lem_wflist_len_succ; simpl; try split; try split;

    try apply intersect_names_add_intro_r;  
    try apply intersect_names_add_intro_r;      
    unfold in_env; fold concatE;  simpl;
    try apply not_elem_concat_intro;  
    try apply not_elem_names_add_intro; try split;
    try apply not_elem_concat_intro;  
    try apply not_elem_names_add_intro; try split;
    apply lem_truncate_wfenv in H11 as p_xg; inversion p_xg; 
    try apply lem_erase_env_wfenv; 
    fold subFV; simpl;  try discriminate; auto.
  - (* TSub *) apply TSub with (tsubFTV a t_a s) k; 
    apply lem_truncate_wfenv in H10 as H10'; inversion H10'; subst a0 k0 g0;
    try apply H with k_a; try apply lem_subst_tv_wf' with k_a;
    try apply H0 with k_a Star k; 
    try apply lem_typing_wf with e; trivial.
  - (* SBase *) 
    apply lem_truncate_wfenv in H8 as H8'; inversion H8'; subst a0 k g0;
    destruct b eqn:B; try destruct (Nat.eqb a a0) eqn:A; 
    simpl; try rewrite A; 
    try ( apply SBase with (names_add a (union nms (binds (concatE g g'))));
          intros; repeat rewrite <- lem_commute_psubFTV_unbindP; try rewrite <- B;
          assert ( ECons y (TRefn b PEmpty) (concatE g (esubFTV a t_a g'))
                    = concatE g (esubFTV a t_a (ECons y (TRefn b PEmpty) g')) )
            as Henv by ( rewrite B; simpl; try rewrite A; reflexivity ); 
          try rewrite Henv;
          try apply ISubTV with k_a; try (rewrite B; apply i);
          apply not_elem_names_add_elim in H; destruct H;
          apply not_elem_union_elim in H11; destruct H11;
          apply not_elem_concat_elim in H13; destruct H13;
          try apply lem_wftype_islct with g k_a;
          try apply not_elem_names_add_intro;
          try apply intersect_names_add_intro_r;
          simpl; try split; intuition ).
    (* b = FTV a *) destruct t_a eqn:TA; try (simpl in H5; contradiction); simpl; 
    try ( apply lem_sub_refl with k_a; 
          rewrite <- TA; rewrite <- TA in H7;
          try apply lem_weaken_many_wf; 
          try apply esubFTV_unique; try rewrite esubFTV_binds; 
          trivial).
    apply SBase with (names_add a (union nms (binds (concatE g g')))); intros;
    apply not_elem_names_add_elim in H; destruct H;
    apply not_elem_union_elim in H11; destruct H11;
    apply not_elem_concat_elim in H13; destruct H13;
    repeat rewrite lem_unbindP_strengthen; apply IStren;
    try apply not_elem_concat_intro; try rewrite esubFTV_binds; trivial;
    repeat rewrite <- lem_commute_psubFTV_unbindP; try repeat rewrite <- TA;
    assert ( Nat.eqb a a = true ) as AA by (apply Nat.eqb_eq; reflexivity);
    assert ( ECons y t_a (concatE g (esubFTV a t_a g'))
                    = concatE g (esubFTV a t_a (ECons y (TRefn (FTV a) PEmpty) g')) )
      as Henv by (simpl; rewrite AA; rewrite lem_push_empty; try rewrite TA; trivial); 
      try rewrite Henv;
    try apply ISubTV with k_a; 
    simpl; apply Nat.eqb_eq in A; subst a0; try apply i;
    try rewrite TA; try apply lem_wftype_islct with g k_a;
    try apply lem_free_subset_binds in H7 as Hps; 
    simpl in Hps; destruct Hps as [Hps _];
    try apply intersect_names_add_intro_r; 
    try apply not_elem_names_add_intro; auto;
    try apply not_elem_subset with (vbinds g);
    try apply not_elem_subset with (binds g);
    try apply vbinds_subset; auto.
  - (* SFunc *)
    apply lem_truncate_wfenv in H10 as H10'; inversion H10'; subst a0 k g0;
    inversion H11; try inversion H1;
    inversion H12; try inversion H21;
    simpl; apply SFunc 
      with (names_add a (union (union nms0 nms1) (union nms (binds (concatE g g')))));
    try apply H with k_a k_x0 k_x; trivial; intros;
    apply not_elem_names_add_elim in H28; destruct H28;
    apply not_elem_union_elim in H29; destruct H29;
    apply not_elem_union_elim in H29; destruct H29;
    apply not_elem_union_elim in H30; destruct H30;
    apply not_elem_concat_elim in H32; destruct H32;
    repeat rewrite <- lem_commute_tsubFTV_unbindT;
    assert (ECons y (tsubFTV a t_a s2) (concatE g (esubFTV a t_a g')) 
            = concatE g (esubFTV a t_a (ECons y s2 g')))
      by reflexivity; try rewrite H34;
    try apply H0 with k_a k k0;    
    try apply H26; try apply H19 in H29 as H19';
    try apply lem_narrow_wf_top with s1; fold concatE;
    try apply intersect_names_add_intro_r;  
    try apply lem_wftype_islct with g k_a;
    try apply not_elem_names_add_intro; 
    try apply WFEBind with k_x0;
    pose proof (lem_binds_concat (EConsT a k_a g) g');
    try destruct H35; try apply not_elem_names_add_intro; trivial;
    try apply not_elem_subset with (union (binds (EConsT a k_a g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; 
    try apply unique_concat;
    try apply intersect_names_add_intro_l;
    try split; simpl; auto. 
  - (* SWitn *) simpl; apply SWitn with (subFTV a t_a v_x);
    apply lem_truncate_wfenv in H10 as H10'; inversion H10'; subst a0 k g0;
    try apply lem_subFTV_value; try apply H with k_a;
    try rewrite <- lem_commute_tsubFTV_tsubBV;
    try apply H0 with k_a k_t k_t';
    inversion H12; try inversion H1;
    pose proof (fresh_varT_not_elem nms (concatE (EConsT a k_a g) g') t') as Hy; 
    set (y := fresh_varT nms (concatE (EConsT a k_a g) g') t') in Hy; 
    destruct Hy as [Hyt' [_ [Hy Henv]]];
    try rewrite lem_tsubFV_unbindT with y v_x t'; 
    try apply lem_subst_wf_top with t_x;
    try apply H19; try apply WFKind; try apply H23;
    try apply lem_wftype_islct with g k_a;    
    try apply lem_typing_hasftype;
    try apply unique_concat; 
    try apply intersect_names_add_intro_l;
    simpl; try split; trivial.
  - (* SBind *) 
    apply lem_truncate_wfenv in H9 as H9'; inversion H9'; subst a0 k g0;
    inversion H10; try inversion H0; subst t0 k g0; simpl; 
    apply SBind with (names_add a (union (union nms nms0) (binds (concatE g g'))));
    try apply lem_islc_at_subFTV; try apply (lem_wftype_islct g t_a) with k_a;
    trivial; intros y Hy;
    apply not_elem_names_add_elim in Hy; destruct Hy;
    apply not_elem_union_elim in H14; destruct H14 as [H14 Hyg];
    apply not_elem_union_elim in H14; destruct H14;
    apply not_elem_concat_elim in Hyg; destruct Hyg;
    rewrite <- lem_commute_tsubFTV_unbindT;
    assert (ECons y (tsubFTV a t_a t_x) (concatE g (esubFTV a t_a g')) 
            = concatE g (esubFTV a t_a (ECons y t_x g'))) as Henv
      by reflexivity; try rewrite Henv;
    try apply H with k_a k_t k_t';
    try apply H18; destruct k_t; try apply WFKind; 
    try apply H22; try apply lem_weaken_wf_top;
    try apply WFEBind with k_x;
    try apply intersect_names_add_intro_r;  
    try apply lem_wftype_islct with g k_a;
    try apply not_elem_names_add_intro; 
    pose proof (lem_binds_concat (EConsT a k_a g) g') as Hbin;
    try destruct Hbin; trivial;
    try apply not_elem_subset with (union (binds (EConsT a k_a g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; simpl; auto. 
  - (* SPoly *) 
    apply lem_truncate_wfenv in H9 as H9'; inversion H9'; subst a0 k0 g0;
    inversion H10; try inversion H0;
    inversion H11; try inversion H19; simpl; 
    apply SPoly with (names_add a (union (union nms0 nms1) (union nms (binds (concatE g g')))));
    intros; apply not_elem_names_add_elim in H25; destruct H25;
    apply not_elem_union_elim in H26; destruct H26;
    apply not_elem_union_elim in H26; destruct H26;
    apply not_elem_union_elim in H27; destruct H27;
    apply not_elem_concat_elim in H29; destruct H29;
    repeat rewrite <- lem_commute_tsubFTV_unbind_tvT;
    assert (EConsT a0 k (concatE g (esubFTV a t_a g')) 
              = concatE g (esubFTV a t_a (EConsT a0 k g')))
        by reflexivity; try rewrite H31;
    try apply H with k_a k_t0 k_t1;
    try apply lem_wftype_islct with g k_a;
    try apply WFEBindT;
    try apply not_elem_names_add_intro;
    try apply intersect_names_add_intro_r; 
    pose proof (lem_binds_concat (EConsT a k_a g) g') as Hbin;
    try destruct Hbin; trivial;
    try apply not_elem_subset with (union (binds (EConsT a k_a g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; 
    simpl; try split; auto.
  - (* SList *)  
    apply lem_wflist_wftype in H10 as p_env_t1;
    apply lem_wflist_wftype in H11 as p_env_t2;
    apply SList with (names_add a (union nms (binds (concatE g g'))));
    fold tsubFTV; fold psubFTV; fold subFTV;
    try apply H with k_a Star Star; trivial; intros.
    assert (ECons y (TList (tsubFTV a t_a t1) PEmpty) (concatE g (esubFTV a t_a g')) 
              = concatE g (esubFTV a t_a (ECons y (TList t1 PEmpty) g')))
      by reflexivity; rewrite H12.
    apply not_elem_names_add_elim in H0; destruct H0; 
    apply not_elem_union_elim in H13; destruct H13;
    apply not_elem_concat_elim in H14; destruct H14.
    repeat rewrite <- lem_commute_psubFTV_unbindP;
    try apply ISubTV with k_a; 
    try apply lem_wftype_islct with g k_a;
    try apply not_elem_names_add_intro;
    try apply intersect_names_add_intro_r;
    apply lem_truncate_wfenv in H9 as p_ag; inversion p_ag; 
    simpl; auto.
  Qed.

Lemma lem_subst_tv_typ : forall (g g':env) (a:vname) (t_a:type) (k_a:kind) (e:expr) (t:type),
    Hastype (concatE (EConsT a k_a g) g') e t 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env a g) -> ~ (in_env a g') 
            -> isMono t_a -> noExists t_a -> WFtype g t_a k_a 
            -> WFEnv (concatE (EConsT a k_a g) g')
            -> Hastype (concatE g (esubFTV a t_a g')) (subFTV a t_a e) (tsubFTV a t_a t ).
Proof. intros; pose proof lem_subst_tv_typ'; destruct H9 as [Htyp Hsub];
  apply Htyp with (concatE (EConsT a k_a g) g') k_a; trivial. Qed.

Lemma lem_subst_tv_typ_top : forall (g:env) (a:vname) (t_a:type) (k_a:kind) (e:expr) (t:type),
    Hastype (EConsT a k_a g) e t 
            -> unique g -> ~ (in_env a g) 
            -> isMono t_a -> noExists t_a -> WFtype g t_a k_a -> WFEnv g
            -> Hastype g (subFTV a t_a e) (tsubFTV a t_a t).
Proof. intros; assert (g = concatE g (esubFTV a t_a Empty)) by reflexivity;
  rewrite H6; apply lem_subst_tv_typ with k_a; try apply intersect_empty_r; 
  try apply WFEBindT; unfold unique; auto. Qed.

Lemma lem_subst_tv_subtype : 
  forall (g g':env) (a:vname) (t_a:type) (k_a:kind) (t t':type) (k_t k_t':kind),
        Subtype (concatE (EConsT a k_a g) g') t t' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env a g) -> ~ (in_env a g') 
            -> isMono t_a -> noExists t_a -> WFtype g t_a k_a 
            -> WFEnv (concatE (EConsT a k_a g) g')
            -> WFtype (concatE (EConsT a k_a g) g') t  k_t
            -> WFtype (concatE (EConsT a k_a g) g') t' k_t'
            -> Subtype (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) (tsubFTV a t_a t').
Proof. intros; pose proof lem_subst_tv_typ'; destruct H11 as [Htyp Hsub];
  apply Hsub with (concatE (EConsT a k_a g) g') k_a k_t k_t'; trivial. Qed.

Lemma lem_subst_tv_subtype_top : 
  forall (g:env) (a:vname) (t_a:type) (k_a:kind) (t t':type) (k_t k_t':kind),
        Subtype (EConsT a k_a g) t t' 
            -> unique g -> ~ (in_env a g) 
            -> isMono t_a -> noExists t_a -> WFtype g t_a k_a -> WFEnv g
            -> WFtype (EConsT a k_a g) t  k_t
            -> WFtype (EConsT a k_a g) t' k_t'
            -> Subtype g (tsubFTV a t_a t) (tsubFTV a t_a t').
Proof. intros; assert (g = concatE g (esubFTV a t_a Empty)) by reflexivity;
  rewrite H8; apply lem_subst_tv_subtype with k_a k_t k_t'; 
  try apply intersect_empty_r; try apply WFEBindT;
  unfold unique; intuition. Qed.