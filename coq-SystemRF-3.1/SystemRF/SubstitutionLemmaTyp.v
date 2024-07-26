Require Import Arith.
Require Import ZArith.

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
        g'xg = concatE (ECons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> isValue v_x -> Hastype g v_x t_x -> WFEnv (concatE (ECons x t_x g) g')
            -> Hastype (concatE g (esubFV x v_x g')) (subFV x v_x e) (tsubFV x v_x t ) )) /\ (
  forall (g'xg : env) (t : type) (t' : type),
    Subtype g'xg t t' -> ( forall (g g':env) (x:vname) (v_x:expr) (t_x:type) (k_t k_t':kind),
      g'xg = concatE (ECons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> isValue v_x -> Hastype g v_x t_x -> WFEnv (concatE (ECons x t_x g) g')
            -> WFtype (concatE (ECons x t_x g) g') t  k_t
            -> WFtype (concatE (ECons x t_x g) g') t' k_t'
            -> Subtype (concatE g (esubFV x v_x g')) (tsubFV x v_x t) (tsubFV x v_x t') )).
Proof. apply ( judgments_mutind 
  (fun (g'xg : env) (e : expr) (t : type) (p_e_t : Hastype g'xg e t) => 
    forall (g g':env) (x:vname) (v_x:expr) (t_x:type),
      g'xg = concatE (ECons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> isValue v_x -> Hastype g v_x t_x -> WFEnv (concatE (ECons x t_x g) g')
            -> Hastype (concatE g (esubFV x v_x g')) (subFV x v_x e) (tsubFV x v_x t ) )
  (fun (g'xg : env) (t : type) (t' : type) (p_t_t' : Subtype g'xg t t') => 
    forall (g g':env) (x:vname) (v_x:expr) (t_x:type) (k_t k_t':kind),
      g'xg = concatE (ECons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> isValue v_x -> Hastype g v_x t_x -> WFEnv (concatE (ECons x t_x g) g')
            -> WFtype (concatE (ECons x t_x g) g') t  k_t
            -> WFtype (concatE (ECons x t_x g) g') t' k_t'
            -> Subtype (concatE g (esubFV x v_x g')) (tsubFV x v_x t) (tsubFV x v_x t') ));
  intro env; intros; subst env.
  - (* TBC *) rewrite lem_tsubFV_tybc; try apply TBC; assumption.
  - (* TIC *) rewrite lem_tsubFV_tyic; try apply TIC; assumption.
  - (* TVar *) rewrite lem_tsubFV_self; destruct (Nat.eqb x0 x) eqn:X;
    apply lem_truncate_wfenv in H7 as H7'; inversion H7'; subst x1 t0 g0.
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
      try apply lem_subst_wfenv with t_x;
      try apply lem_typing_hasftype;
      try apply intersect_names_add_intro_l;
      try apply lem_free_bound_in_env with g Star ;
      try apply esubFV_unique; try rewrite esubFV_binds;
      try apply intersect_empty_r; unfold unique; intuition.
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
    apply lem_truncate_wfenv in H8 as H8'; inversion H8'; subst x0 t0 g0;
    try apply lem_subst_wf with t_x0; try apply lem_typing_hasftype;
    try assumption; intros.
    apply not_elem_names_add_elim in H0; destruct H0;
    apply not_elem_union_elim in H9; destruct H9;
    apply not_elem_concat_elim in H10; destruct H10;
    assert (ECons y (tsubFV x v_x t_x) (concatE g (esubFV x v_x g')) 
            = concatE g (esubFV x v_x (ECons y t_x g')))
      by reflexivity; rewrite H15;
    rewrite <- lem_commute_subFV_unbind;
    try rewrite <- lem_commute_tsubFV_unbindT;
    try apply H with t_x0;
    try apply WFEBind with k_x;
    try apply intersect_names_add_intro_r;
    try apply lem_typ_islc with g t_x0;
    unfold in_env; fold concatE;
    pose proof (lem_binds_concat (ECons x t_x0 g) g');
    destruct H16; try apply not_elem_names_add_intro; trivial;
    try apply not_elem_subset with (union (binds (ECons x t_x0 g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro;
    simpl; auto. 
  - (* TApp *) simpl; apply TApp; simpl in H; 
    apply H with t_x0 || apply H0 with t_x0; trivial.
  - (* TAbsT *) simpl; apply TAbsT with (names_add x (union nms (binds (concatE g g')))).
    apply lem_truncate_wfenv in H8 as H8'; inversion H8'; subst x0 t0 g0;
    intros; apply not_elem_names_add_elim in H0; destruct H0;
    apply not_elem_union_elim in H9; destruct H9;
    apply not_elem_concat_elim in H10; destruct H10;
    assert (EConsT a' k (concatE g (esubFV x v_x g')) = concatE g (esubFV x v_x (EConsT a' k g')))
      by reflexivity; rewrite H15;
    try rewrite <- lem_commute_subFV_unbind_tv;
    try rewrite <- lem_commute_tsubFV_unbind_tvT;
    try apply H with t_x; try apply WFEBindT;
    try apply intersect_names_add_intro_r;
    try apply lem_typ_islc with g t_x;
    unfold in_env; fold concatE;
    pose proof (lem_binds_concat (ECons x t_x g) g');
    destruct H16; try apply not_elem_names_add_intro; trivial;
    try apply not_elem_subset with (union (binds (ECons x t_x g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; simpl; intuition.
  - (* TAppT *) rewrite lem_commute_tsubFV_tsubBTV; simpl;
    apply lem_truncate_wfenv in H8 as H8'; inversion H8'; subst x0 t0 g0;
    try apply TAppT with k; simpl in H;
    try apply H with t_x;
    try apply lemma_tsubFV_isMono;
    try apply lemma_tsubFV_noExists;
    try apply lem_subst_wf with t_x;
    try apply lem_typing_hasftype;
    try apply lem_typ_islc with g t_x; 
    trivial.
  - (* TLet *) simpl; apply TLet with (tsubFV x v_x t_x) k
                  (names_add x (union nms (binds (concatE g g'))));
    apply lem_truncate_wfenv in H9 as H9'; inversion H9'; subst x0 t0 g0;
    try apply lem_subst_wf with t_x0; try apply lem_typing_hasftype;
    try apply H with t_x0; trivial; intros;
    apply not_elem_names_add_elim in H1; destruct H1;
    apply not_elem_union_elim in H10; destruct H10;
    apply not_elem_concat_elim in H11; destruct H11;
    assert (ECons y (tsubFV x v_x t_x) (concatE g (esubFV x v_x g')) 
            = concatE g (esubFV x v_x (ECons y t_x g')))
      by reflexivity; rewrite H16;
    rewrite <- lem_commute_subFV_unbind;
    try rewrite <- lem_commute_tsubFV_unbindT;
    try apply H0 with t_x0;
    try apply WFEBind with Star; fold concatE;
    try apply lem_typing_wf with e_x;
    try apply intersect_names_add_intro_r;
    try apply lem_typ_islc with g t_x0;
    pose proof (lem_binds_concat (ECons x t_x0 g) g');
    destruct H17; try apply not_elem_names_add_intro; trivial;
    try apply not_elem_subset with (union (binds (ECons x t_x0 g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; simpl; auto.
  - (* TAnn *) simpl; apply TAnn; try apply lemma_tsubFV_noExists;
    try apply H with t_x; trivial.
  - (* TIf *) simpl; apply TIf with (psubFV x v_x ps) k 
                                    (names_add x (union nms (binds (concatE g g'))));
    apply lem_truncate_wfenv in H10 as H10'; inversion H10'; subst x0 t0 g0;
    simpl in H; try apply H with t_x;
    try apply lem_subst_wf with t_x;
    try apply lem_typing_hasftype; intros;
    try apply not_elem_names_add_elim in H2; try destruct H2;
    try apply not_elem_union_elim in H11; try destruct H11; 
    try apply not_elem_concat_elim in H12; try destruct H12;
    try assert (ECons y (self (TRefn TBool (psubFV x v_x ps)) (Bc true) Base) (concatE g (esubFV x v_x g')) 
            = concatE g (esubFV x v_x (ECons y (self (TRefn TBool ps) (Bc true) Base) g')))
      by reflexivity; try rewrite H17;
    try assert (ECons y (self (TRefn TBool (psubFV x v_x ps)) (Bc false) Base) (concatE g (esubFV x v_x g')) 
            = concatE g (esubFV x v_x (ECons y (self (TRefn TBool ps) (Bc false) Base) g')))
      by reflexivity; try rewrite H18;
    try apply H0 with y t_x; try apply H1 with y t_x;
    try apply WFEBind with Base; fold concatE;
    try apply lem_selfify_wf; try apply FTBC;
    try apply not_elem_names_add_intro;
    try apply intersect_names_add_intro_r;
    pose proof (lem_binds_concat (ECons x t_x g) g');
    try destruct H19; try apply not_elem_names_add_intro; trivial;
    try apply not_elem_subset with (union (binds (ECons x t_x g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; 
    simpl; try discriminate; try split; auto;
    apply lem_typing_wf in h; try apply H10; 
    inversion h; trivial.
  - (* TNil *) apply TNil with k; fold tsubFV;
    try apply lemma_tsubFV_isMono; try apply lemma_tsubFV_noExists;
    try apply lem_subst_wf with t_x;
    try apply lem_typing_hasftype;
    apply lem_truncate_wfenv in H7; inversion H7; trivial. 
  - (* TCons *) apply TCons; fold tsubFV;
    try apply lemma_tsubFV_isMono; try apply lemma_tsubFV_noExists;
    try apply H with t_x; try apply H0 with t_x; trivial.
  - (* TSwitch *) apply TSwit with (tsubFV x v_x t) (psubFV x v_x ps) 
                              k (names_add x (union nms (binds (concatE g g'))));
    try apply lemma_tsubFV_isMono; try apply lemma_tsubFV_noExists;
    simpl in H; try apply H with t_x; 
    try intros y z Hy Hz Hyz; try intros y Hy;
    try assert (ECons y (TList (tsubFV x v_x t) 
                          (PCons (eq (Ic 0) (length (tsubFV x v_x t) (BV 0))) 
                            (psubFV x v_x ps))) (concatE g (esubFV x v_x g')) 
              = concatE g (esubFV x v_x 
                            (ECons y (TList t (PCons (eq (Ic 0) (length t (BV 0))) 
                                                ps)) g')))
      as Henv1 by reflexivity; try rewrite Henv1;
    try apply not_elem_names_add_elim in Hy; try destruct Hy as [Hyx Hy]; 
    try apply not_elem_union_elim in Hy; try destruct Hy as [Hynms Hy];
    try apply not_elem_concat_elim in Hy as Hyenv; 
    try destruct Hyenv as [Hyg Hyg'];
    try apply not_elem_names_add_elim in Hz; try destruct Hz as [Hzx Hz];   
    try apply not_elem_union_elim in Hz; try destruct Hz as [Hznms Hz];
    try apply not_elem_concat_elim in Hz as Hzenv; 
    try destruct Hzenv as [Hzg Hzg'];
    try apply Nat.neq_sym in Hyx;
    try apply Nat.eqb_neq in Hyx as Hneqb; fold subFV;
    try assert (
      ECons z (TList (tsubFV x v_x t) 
                (PCons (eq (App (Prim Succ) (length (tsubFV x v_x t) (FV y))) 
                           (length (tsubFV x v_x t) (BV 0))) (psubFV x v_x ps))) 
        (ECons y (TList (tsubFV x v_x t) PEmpty) 
          (concatE g (esubFV x v_x g')))
      = concatE g (esubFV x v_x
          (ECons z (TList t (PCons (eq (App (Prim Succ) (length t (FV y))) 
                                  (length t (BV 0))) ps)) 
            (ECons y (TList t PEmpty) g'))) 
    ) as Henv2 by (simpl; rewrite Hneqb; reflexivity); try rewrite Henv2;
    try assert ((TFunc (tsubFV x v_x t) 
                  (TFunc (TList (tsubFV x v_x t) 
                          (PCons (eq (length (tsubFV x v_x t) (FV y)) 
                                     (length (tsubFV x v_x t) (BV 0))) PEmpty)) 
                         (tsubFV x v_x t')))
              = (tsubFV x v_x (TFunc t (TFunc (TList t (PCons (eq (length t (FV y)) 
                                                                  (length t (BV 0)))
                                                              PEmpty)) t'))))
      as Htyp by (simpl; rewrite Hneqb; reflexivity); try rewrite Htyp;
    try apply H0 with y t_x; try apply H1 with z t_x;
    try apply lem_subst_wf with t_x; 
    try apply WFEBind with Star;
    try apply WFEBind with Star;
    apply lem_typing_wf in h as p_env_tps; try apply p_env_tps;
    try apply lem_wflist_len_zero; try assumption;          
    try apply lem_wflist_len_succ; trivial; fold concatE;
    try (inversion p_env_tps; try subst ps; 
         try inversion H2; assumption);

    try apply lem_typing_hasftype; simpl; try split;  try split;
    try apply intersect_names_add_intro_r;  
    try apply intersect_names_add_intro_r;      
    unfold in_env; fold concatE;  simpl;
    try apply not_elem_concat_intro;  
    try apply not_elem_names_add_intro; try split;
    try apply not_elem_concat_intro;  
    try apply not_elem_names_add_intro; try split;
    apply lem_truncate_wfenv in H10 as p_xg; inversion p_xg; 
    fold subFV; simpl;  try discriminate; auto.
  - (* TSub *)   
    apply TSub with (tsubFV x v_x s) k; 
    apply lem_truncate_wfenv in H9 as H9'; inversion H9'; subst x0 t0 g0;
    try apply H with t_x; try apply lem_subst_wf with t_x;
    try apply lem_typing_hasftype;
    try apply H0 with t_x Star k; 
    try apply lem_typing_wf with e; trivial.
  - (* SBase *) simpl; apply SBase with (names_add x (union nms (binds (concatE g g'))));
    apply lem_truncate_wfenv in H7 as H7'; inversion H7'; subst x0 t g0;
    intros; repeat rewrite <- lem_commute_psubFV_unbindP; 
    assert ( ECons y (TRefn b PEmpty) (concatE g (esubFV x v_x g'))
              = concatE g (esubFV x v_x (ECons y (TRefn b PEmpty) g')) )
      as Henv by reflexivity; try rewrite Henv;
    try apply ISub with t_x; simpl; try apply i;
    apply not_elem_names_add_elim in H; destruct H;
    apply not_elem_union_elim in H10; destruct H10;
    apply not_elem_concat_elim in H11; destruct H11;
    try apply lem_typ_islc with g t_x;
    try apply not_elem_names_add_intro;
    try apply intersect_names_add_intro_r;
    simpl; try split; intuition.
  - (* SFunc *) 
    apply lem_truncate_wfenv in H9 as H9'; inversion H9'; subst x0 t g0;
    inversion H10; try inversion H1; 
    inversion H11; try inversion H21;
    simpl; apply SFunc 
      with (names_add x (union (union nms0 nms1) (union nms (binds (concatE g g')))));
    try apply H with t_x k_x0 k_x; trivial; intros;
    apply not_elem_names_add_elim in H28; destruct H28;
    apply not_elem_union_elim in H29; destruct H29;
    apply not_elem_union_elim in H29; destruct H29;
    apply not_elem_union_elim in H30; destruct H30;
    apply not_elem_concat_elim in H32; destruct H32;
    repeat rewrite <- lem_commute_tsubFV_unbindT;
    assert (ECons y (tsubFV x v_x s2) (concatE g (esubFV x v_x g')) 
            = concatE g (esubFV x v_x (ECons y s2 g')))
      by reflexivity; try rewrite H34;
    try apply H0 with t_x k0 k1;
    try apply H26; try apply H19 in H29 as H19';
    try apply lem_narrow_wf_top with s1; fold concatE;
    try apply intersect_names_add_intro_r; fold binds;
    try apply lem_typ_islc with g t_x;
    try apply not_elem_names_add_intro;
    try apply WFEBind with k_x0;
    pose proof (lem_binds_concat (ECons x t_x g) g');
    try destruct H35; try apply not_elem_names_add_intro; trivial;
    try apply not_elem_subset with (union (binds (ECons x t_x g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; 
    try apply unique_concat;
    try apply intersect_names_add_intro_l;
    try split; simpl; auto. 
  - (* SWitn *) simpl; apply SWitn with (subFV x v_x0 v_x);
    apply lem_truncate_wfenv in H9 as H9'; inversion H9'; subst x0 t0 g0;
    try apply lem_subFV_value; try apply H with t_x0;
    try rewrite <- lem_commute_tsubFV_tsubBV;
    try apply H0 with t_x0 k_t k_t'; 
    inversion H11; try inversion H1;
    pose proof (fresh_varT_not_elem nms (concatE (ECons x t_x0 g) g') t') as Hy; 
    set (y := fresh_varT nms (concatE (ECons x t_x0 g) g') t') in Hy; 
    destruct Hy as [Hyt' [_ [Hy Henv]]];
    try rewrite lem_tsubFV_unbindT with y v_x t';
    try apply lem_subst_wf_top with t_x;
    try apply H19; try apply WFKind; try apply H23;
    try apply lem_typ_islc with g t_x0; 
    try apply lem_typing_hasftype;
    try apply unique_concat; 
    try apply intersect_names_add_intro_l;
    simpl; try split; trivial.
  - (* SBind *) 
    apply lem_truncate_wfenv in H8 as H8'; inversion H8'; subst x0 t0 g0;
    inversion H9; try inversion H0; subst t0 k0 g0; simpl;

    apply SBind with (names_add x (union (union nms nms0) (binds (concatE g g'))));
    try apply lem_islc_at_subFV; try apply lem_typ_islc with g t_x0;
    trivial; intros y Hy;
    apply not_elem_names_add_elim in Hy; destruct Hy;
    apply not_elem_union_elim in H12; destruct H12 as [H12 Hyg];
    apply not_elem_union_elim in H12; destruct H12;
    apply not_elem_concat_elim in Hyg; destruct Hyg;
    try rewrite <- lem_commute_tsubFV_unbindT;
    assert (ECons y (tsubFV x v_x t_x) (concatE g (esubFV x v_x g')) 
            = concatE g (esubFV x v_x (ECons y t_x g'))) as Henv
      by reflexivity; try rewrite Henv;
    try apply H with t_x0 k_t k_t';
    try apply H18; destruct k_t; try apply WFKind; 
    try apply H22; try apply lem_weaken_wf_top;
    try apply WFEBind with k_x; fold concatE;
    try apply intersect_names_add_intro_r;  
    try apply lem_typ_islc with g t_x0;
    try apply not_elem_names_add_intro; 
    pose proof (lem_binds_concat (ECons x t_x0 g) g') as Hbin;
    try destruct Hbin; trivial;
    try apply not_elem_subset with (union (binds (ECons x t_x0 g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; 
    try apply unique_concat;
    try apply intersect_names_add_intro_l; simpl; auto.
  - (* SPoly *) 
    apply lem_truncate_wfenv in H8 as H8'; inversion H8'; subst x0 t g0;
    inversion H9; try inversion H0;
    inversion H10; try inversion H19;
    simpl; apply SPoly 
      with (names_add x (union (union nms0 nms1) (union nms (binds (concatE g g')))));
    intros; apply not_elem_names_add_elim in H25; destruct H25;
    apply not_elem_union_elim in H26; destruct H26;
    apply not_elem_union_elim in H26; destruct H26;
    apply not_elem_union_elim in H27; destruct H27;
    apply not_elem_concat_elim in H29; destruct H29;
    repeat rewrite <- lem_commute_tsubFV_unbind_tvT;
    assert (EConsT a k (concatE g (esubFV x v_x g')) 
              = concatE g (esubFV x v_x (EConsT a k g')))
        by reflexivity; try rewrite H31;
    try apply H with t_x k_t0 k_t1; simpl;
    try apply lem_typ_islc with g t_x;
    try apply WFEBindT;
    try apply not_elem_names_add_intro;
    try apply intersect_names_add_intro_r;
    pose proof (lem_binds_concat (ECons x t_x g) g') as Hbin;
    try destruct Hbin; trivial;
    try apply not_elem_subset with (union (binds (ECons x t_x g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; 
    simpl; try split; auto.
  - (* SList *) 
    apply lem_wflist_wftype in H9 as p_env_t1;
    apply lem_wflist_wftype in H10 as p_env_t2;
    apply SList with (names_add x (union nms (binds (concatE g g'))));
    fold tsubFV; fold psubFV; fold subFV;
    try apply H with t_x Star Star; trivial; intros.
    assert (ECons y (TList (tsubFV x v_x t1) PEmpty) (concatE g (esubFV x v_x g')) 
              = concatE g (esubFV x v_x (ECons y (TList t1 PEmpty) g')))
      by reflexivity; rewrite H11.
    apply not_elem_names_add_elim in H0; destruct H0; 
    apply not_elem_union_elim in H12; destruct H12;
    apply not_elem_concat_elim in H13; destruct H13.
    repeat rewrite <- lem_commute_psubFV_unbindP;
    try apply ISub with t_x;
    try apply lem_typ_islc with g t_x;
    try apply not_elem_names_add_intro;
    try apply intersect_names_add_intro_r;
    apply lem_truncate_wfenv in H8 as p_xg; inversion p_xg; 
    simpl; auto.  
  Qed.

Lemma lem_subst_typ : forall (g g':env) (x:vname) (v_x:expr) (t_x:type) (e:expr) (t:type),
    Hastype (concatE (ECons x t_x g) g') e t 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> isValue v_x -> Hastype g v_x t_x -> WFEnv (concatE (ECons x t_x g) g')
            -> Hastype (concatE g (esubFV x v_x g')) (subFV x v_x e) (tsubFV x v_x t ).
Proof. intros; pose proof lem_subst_typ'; destruct H8 as [Htyp Hsub];
  apply Htyp with (concatE (ECons x t_x g) g') t_x; trivial. Qed.

Lemma lem_subst_typ_top : forall (g:env) (x:vname) (v_x:expr) (t_x:type) (e:expr) (t:type),
    Hastype (ECons x t_x g) e t 
            -> unique g -> ~ (in_env x g) 
            -> isValue v_x -> Hastype g v_x t_x -> WFEnv g
            -> Hastype g (subFV x v_x e) (tsubFV x v_x t ).
Proof. intros; assert (g = concatE g (esubFV x v_x Empty)) by reflexivity;
  rewrite H5; apply lem_subst_typ with t_x; try apply intersect_empty_r; 
  try apply WFEBind with Star; try apply lem_typing_wf with v_x;
  unfold unique; intuition. Qed.

Lemma lem_subst_subtype : 
  forall (g g':env) (x:vname) (v_x:expr) (t_x:type) (t t':type) (k_t k_t':kind),
        Subtype (concatE (ECons x t_x g) g') t t' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> isValue v_x -> Hastype g v_x t_x -> WFEnv (concatE (ECons x t_x g) g')
            -> WFtype (concatE (ECons x t_x g) g') t  k_t
            -> WFtype (concatE (ECons x t_x g) g') t' k_t'
            -> Subtype (concatE g (esubFV x v_x g')) (tsubFV x v_x t) (tsubFV x v_x t').
Proof. intros; pose proof lem_subst_typ'; destruct H10 as [Htyp Hsub];
  apply Hsub with (concatE (ECons x t_x g) g') t_x k_t k_t'; trivial. Qed.

Lemma lem_subst_subtype_top : 
  forall (g:env) (x:vname) (v_x:expr) (t_x:type) (t t':type) (k_t k_t':kind),
        Subtype (ECons x t_x g) t t' 
            -> unique g -> ~ (in_env x g) 
            -> isValue v_x -> Hastype g v_x t_x -> WFEnv g
            -> WFtype (ECons x t_x g) t  k_t
            -> WFtype (ECons x t_x g) t' k_t'
            -> Subtype g (tsubFV x v_x t) (tsubFV x v_x t').
Proof. intros; assert (g = concatE g (esubFV x v_x Empty)) by reflexivity;
  rewrite H7; apply lem_subst_subtype with t_x k_t k_t'; 
  try apply intersect_empty_r; try apply WFEBind with Star; 
  try apply lem_typing_wf with v_x; unfold unique; intuition. Qed.