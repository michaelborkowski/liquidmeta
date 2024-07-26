Require Import ZArith.

Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.BasicPropsWellFormedness.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.Typing.
Require Import SystemRF.LemmasWeakenWF.
Require Import SystemRF.LemmasWeakenWFTV.
Require Import SystemRF.LemmasWellFormedness.
Require Import SystemRF.SubstitutionLemmaWF.
Require Import SystemRF.LemmasTyping.
Require Import SystemRF.LemmasSubtyping.
Require Import SystemRF.LemmasWeakenTyp.
Require Import SystemRF.LemmasWeakenTypTV.
Require Import SystemRF.LemmasExactness. 

Lemma lem_narrow_typ' : ( forall (g'xg : env) (e : expr) (t : type),
    Hastype g'xg e t -> ( forall (g g':env) (x:vname) (s_x t_x:type) (k_sx k_tx:kind),
        g'xg = concatE (ECons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x 
            -> WFEnv (concatE (ECons x s_x g) g')
            -> Hastype (concatE (ECons x s_x g) g') e t )) /\ (
  forall (g'xg : env) (t : type) (t' : type),
    Subtype g'xg t t' -> ( forall (g g':env) (x:vname) (s_x t_x:type) (k_sx k_tx k_t k_t':kind),
      g'xg = concatE (ECons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x 
            -> WFEnv (concatE (ECons x s_x g) g')
            -> WFtype (concatE (ECons x s_x g) g') t  k_t
            -> WFtype (concatE (ECons x s_x g) g') t' k_t'
            -> Subtype (concatE (ECons x s_x g) g') t t' )).
Proof. apply ( judgments_mutind 
  (fun (g'xg : env) (e : expr) (t : type) (p_e_t : Hastype g'xg e t) => 
    forall (g g':env) (x:vname) (s_x t_x:type) (k_sx k_tx:kind),
      g'xg = concatE (ECons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x 
            -> WFEnv (concatE (ECons x s_x g) g')
            -> Hastype (concatE (ECons x s_x g) g') e t )
  (fun (g'xg : env) (t : type) (t' : type) (p_t_t' : Subtype g'xg t t') => 
    forall (g g':env) (x:vname) (s_x t_x:type) (k_sx k_tx k_t k_t':kind),
      g'xg = concatE (ECons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x 
            -> WFEnv (concatE (ECons x s_x g) g')
            -> WFtype (concatE (ECons x s_x g) g') t  k_t
            -> WFtype (concatE (ECons x s_x g) g') t' k_t'            
            -> Subtype (concatE (ECons x s_x g) g') t t' ));
  intro env; intros; subst env.
  - (* TBC *) apply TBC.
  - (* TIC *) apply TIC.
  - (* TVar *) 
    apply lem_truncate_wfenv in H8 as H8'; inversion H8'; subst x1 t0 g0;
    apply lem_boundin_concat in b; destruct b;
    try destruct H; try destruct H.
    * (* x = x0 *) subst x0; subst t; 
      apply TSub with (self s_x (FV x) k) k;
      try apply TVar; try (apply lem_boundin_concat; left);
      try apply lem_weaken_many_subtype with k(*_sx*) k(*_tx*);
      try apply lem_selfify_wf;
      try apply lem_weaken_many_wf;
      
      try apply lem_exact_subtype with k_sx;
      try apply lem_weaken_subtype_top with k_sx k_tx;
      try (apply lem_weaken_wf_top; assumption);
      try apply WFEBind with k_sx; 
      try rewrite lem_erase_concat; simpl;
      try rewrite lem_erase_subtype with g s_x t_x;
      try apply FTVar; try apply lem_boundinF_concatF;
      try apply intersect_names_add_intro_l; 
      unfold isLC; simpl;  auto;
      (* WFtype of s_x and t_x, possibly with other kinds *)
      apply lem_weaken_wf_top with g s_x k_sx x s_x in H5 as Hsx;
      apply lem_weaken_wf_top with g t_x k_tx x s_x in H6 as Htx; trivial;
      destruct k eqn:K; destruct k_sx eqn:KSX; destruct k_tx eqn:KTX;
      try assumption; try (apply WFKind; assumption);
      (* k_sx = Star but k_tx = Base and k = Base *)
      try ( apply lem_sub_pullback_wftype with t_x;
            try apply lem_weaken_subtype_top with Star Base; 
            try apply WFEBind with Star; trivial; reflexivity  );
      (* k_tx = Star but k_sx = Base and k = Base *)
      try ( apply lem_strengthen_many_wftype_base with g';
            try apply lem_narrow_wf with t_x;
            try apply intersect_names_add_intro_l; 
            unfold unique; auto; reflexivity );
      (* k_sx = Star and k_tx = Star but k = Base *)
      try apply lem_sub_pullback_wftype with t_x;
      try apply lem_strengthen_many_wftype_base with g'; 
      try apply lem_narrow_wf with t_x;
      try apply lem_weaken_subtype_top with Star Star; 
      try apply intersect_names_add_intro_l; 
      unfold unique; auto.
    * (* x in g  *) apply TVar; try apply lem_boundin_concat; simpl;
      try (left; right; apply H); apply lem_narrow_wf with t_x; assumption. 
    * (* x in g' *) apply TVar; try apply lem_boundin_concat; simpl;
      try (right; apply H); apply lem_narrow_wf with t_x; assumption.
  - (* TPrm *) apply TPrm.
  - (* TAbs *) apply TAbs with k_x (names_add x (union nms (binds (concatE g g')))); 
    try apply lem_narrow_wf with t_x0; trivial; intros;
    apply not_elem_names_add_elim in H0; destruct H0;
    apply not_elem_union_elim in H10; destruct H10;
    apply not_elem_concat_elim in H11; destruct H11;
    assert (ECons y t_x (concatE (ECons x s_x g) g') = concatE (ECons x s_x g) (ECons y t_x g'))
      as Henv by reflexivity; rewrite Henv; 
    apply H with t_x0 k_sx k_tx; 
    try apply WFEBind with k_x;
    try apply lem_narrow_wf with t_x0;
    try apply intersect_names_add_intro_r;  
    try apply not_elem_names_add_intro;
    pose proof (lem_binds_concat (ECons x s_x g) g') as Hc;
    destruct Hc; try apply not_elem_names_add_intro; trivial;
    try apply not_elem_subset with (union (binds (ECons x s_x g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; simpl; auto. 
  - (* TApp *) apply TApp;
    apply H with t_x0 k_sx k_tx || apply H0 with t_x0 k_sx k_tx; trivial.
  - (* TAbsT *) apply TAbsT with (names_add x (union nms (binds (concatE g g')))); intros;
    apply not_elem_names_add_elim in H0; destruct H0;
    apply not_elem_union_elim in H10; destruct H10;
    apply not_elem_concat_elim in H11; destruct H11;
    assert (EConsT a' k (concatE (ECons x s_x g) g') = concatE (ECons x s_x g) (EConsT a' k g'))
      as Henv by reflexivity; rewrite Henv; 
    apply H with t_x k_sx k_tx; try apply WFEBindT;
    try apply intersect_names_add_intro_r; 
    try apply not_elem_names_add_intro; 
    pose proof (lem_binds_concat (ECons x s_x g) g') as Hc;
    destruct Hc; try apply not_elem_names_add_intro; trivial;
    try apply not_elem_subset with (union (binds (ECons x s_x g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; simpl; auto.
  - (* TAppT *) apply TAppT with k; try apply H with t_x k_sx k_tx; 
    try apply lem_narrow_wf with t_x; trivial.
  - (* TLet *) apply TLet with t_x k (names_add x (union nms (binds (concatE g g'))));
    try apply lem_narrow_wf with t_x0;  
    try apply H with t_x0 k_sx k_tx; trivial; intros;
    apply not_elem_names_add_elim in H1; destruct H1;
    apply not_elem_union_elim in H11; destruct H11;
    apply not_elem_concat_elim in H12; destruct H12;
    assert (ECons y t_x (concatE (ECons x s_x g) g') = concatE (ECons x s_x g) (ECons y t_x g'))
      as Henv by reflexivity; rewrite Henv; 
    apply H0 with t_x0 k_sx k_tx; 
    try apply WFEBind with Star;
    try apply lem_typing_wf with e_x;
    try apply H with t_x0 k_sx k_tx; 
    try apply intersect_names_add_intro_r; 
    try apply not_elem_names_add_intro; 
    pose proof (lem_binds_concat (ECons x s_x g) g') as Hc;
    destruct Hc; try apply not_elem_names_add_intro; trivial;
    try apply not_elem_subset with (union (binds (ECons x s_x g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; simpl; auto.    
  - (* TAnn *) apply TAnn; try apply H with t_x k_sx k_tx; trivial.
  - (* TIf *) apply TIf with ps k (names_add x (union nms (binds (concatE g g'))));
    try apply H with t_x k_sx k_tx; 
    try apply lem_narrow_wf with t_x; intros;
    try apply not_elem_names_add_elim in H2; try destruct H2;
    try apply not_elem_union_elim in H12; try destruct H12;
    try apply not_elem_concat_elim in H13; try destruct H13;
    try assert (ECons y (self (TRefn TBool ps) (Bc true) Base) (concatE (ECons x s_x g) g') 
                  = concatE (ECons x s_x g) (ECons y (self (TRefn TBool ps) (Bc true) Base) g'))
      as Henv1 by reflexivity; try rewrite Henv1; 
    try assert (ECons y (self (TRefn TBool ps) (Bc false) Base) (concatE (ECons x s_x g) g') 
                  = concatE (ECons x s_x g) (ECons y (self (TRefn TBool ps) (Bc false) Base) g'))
      as Henv2 by reflexivity; try rewrite Henv2;     
    apply H with g g' x s_x t_x k_sx k_tx in H11 as H'; 
    try apply lem_typing_wf in H';  
    try apply H0 with y t_x k_sx k_tx; try apply H1 with y t_x k_sx k_tx;
    try apply WFEBind with Base;
    try apply lem_selfify_wf; try apply FTBC;
    try apply intersect_names_add_intro_r; 
    try apply not_elem_names_add_intro;
    pose proof (lem_binds_concat (ECons x s_x g) g') as Hc;
    try destruct Hc; try apply not_elem_names_add_intro; trivial;
    try apply not_elem_subset with (union (binds (ECons x s_x g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; 
    simpl; try discriminate; try split; auto;
    inversion H'; assumption.
  - (* TNil *) apply TNil with k; 
    try apply lem_narrow_wf with t_x; trivial.
  - (* TCons *) apply TCons; try apply H with t_x k_sx k_tx;
    try apply H0 with t_x k_sx k_tx; trivial.
  - (* TSwit *) 
    apply TSwit with t ps k (names_add x (union nms (binds (concatE g g'))));
    try apply H with t_x k_sx k_tx;
    try intros y z Hy Hz Hyz; try intros y Hy;
    try apply lem_narrow_wf with t_x;
    try apply not_elem_names_add_elim in Hy; try destruct Hy as [Hyx Hy]; 
    try apply not_elem_union_elim in Hy; try destruct Hy as [Hynms Hy];
    try apply not_elem_concat_elim in Hy as Hyenv; 
    try destruct Hyenv as [Hyg Hyg'];
    try apply not_elem_names_add_elim in Hz; try destruct Hz as [Hzx Hz];   
    try apply not_elem_union_elim in Hz; try destruct Hz as [Hznms Hz];
    try apply not_elem_concat_elim in Hz as Hzenv; 
    try destruct Hzenv as [Hzg Hzg'];       
    try assert (ECons y (TList t (PCons (eq (Ic 0) (length t (BV 0))) ps)) 
                      (concatE (ECons x s_x g) g') 
                  = concatE (ECons x s_x g) 
                            (ECons y (TList t (PCons (eq (Ic 0) (length t (BV 0))) ps)) g'))
      as Henv1 by reflexivity; try rewrite Henv1; 
    try assert (ECons z (TList t (PCons (eq (App (Prim Succ) (length t (FV y))) 
                                            (length t (BV 0))) ps)) 
                  (ECons y (TList t PEmpty) (concatE (ECons x s_x g) g'))
                = concatE (ECons x s_x g) 
                    (ECons z (TList t (PCons (eq (App (Prim Succ) (length t (FV y))) 
                                            (length t (BV 0))) ps)) 
                      (ECons y (TList t PEmpty) g')) )
      as Henv2 by reflexivity; try rewrite Henv2;     
    try apply H0 with y t_x k_sx k_tx;
    try apply H1 with z t_x k_sx k_tx; 
    try apply WFEBind with Star; 
    try apply WFEBind with Star;   unfold in_env;
    try apply lem_wflist_len_zero;         
    try apply lem_wflist_len_succ;   
    assert (WFtype (concatE(ECons x s_x g) g') (TList t ps) Star)
      as p_senv_tps by (apply lem_typing_wf with e;
                        try apply H with t_x k_sx k_tx; trivial);
    try (inversion p_senv_tps; try subst ps; 
         try inversion H2; assumption);
    simpl; try split; try split;
    try apply intersect_names_add_intro_r;  
    try apply intersect_names_add_intro_r;      
    unfold in_env; fold concatE;  simpl;
    try apply not_elem_concat_intro;  
    try apply not_elem_names_add_intro; try split;
    try apply not_elem_concat_intro;  
    try apply not_elem_names_add_intro; try split;
    fold subFV; simpl;  try discriminate; auto.
  - (* TSub *) apply TSub with s k;
    try apply H0 with t_x k_sx k_tx Star k; 
    try apply lem_typing_wf with e;
    try apply H with t_x k_sx k_tx;
    try apply lem_narrow_wf with t_x; trivial.
  - (* SBase *) try apply SBase with (names_add x (union nms (binds (concatE g g')))); 
    apply lem_truncate_wfenv in H8 as H8'; inversion H8'; subst x0 t g0;
    intros; assert (ECons y (TRefn b PEmpty) (concatE (ECons x s_x g) g') 
                      = concatE (ECons x s_x g) (ECons y (TRefn b PEmpty) g'))
      as Henv by reflexivity; rewrite Henv;
    apply not_elem_names_add_elim in H; destruct H;
    apply not_elem_union_elim in H11; destruct H11;
    apply not_elem_concat_elim in H12; destruct H12;
    apply INarrow with t_x k_sx k_tx; try apply i;
    try apply intersect_names_add_intro_r; try apply not_elem_names_add_intro;
    simpl; intuition.
  - (* SFunc *) inversion H11; try inversion H1;
    inversion H12; try inversion H19;
    apply SFunc 
      with (names_add x (union (union nms0 nms1) (union nms (binds (concatE g g')))));
    try apply H with t_x k_sx k_tx k_x0 k_x; trivial; intros;
    apply not_elem_names_add_elim in H26; destruct H26;
    apply not_elem_union_elim in H27; destruct H27;
    apply not_elem_union_elim in H27; destruct H27;
    apply not_elem_union_elim in H28; destruct H28;
    apply not_elem_concat_elim in H30; destruct H30;
    assert (ECons y s2 (concatE (ECons x s_x g) g') = concatE (ECons x s_x g) (ECons y s2 g'))
      as Henv by reflexivity; rewrite Henv;
    apply H0 with t_x k_sx k_tx k k0;
    try apply WFEBind with k_x0; 
    try apply intersect_names_add_intro_r; 
    try apply not_elem_names_add_intro; simpl; auto;
    try apply lem_narrow_wf_top with s1;
    try apply H with t_x k_sx k_tx k_x0 k_x; 
    pose proof (lem_binds_concat (ECons x s_x g) g') as Hc;
    try destruct Hc; trivial;
    try apply not_elem_subset with (union (binds (ECons x s_x g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; 
    try apply unique_concat;
    try apply intersect_names_add_intro_l;
    try split; simpl; auto.
  - (* SWitn *) apply SWitn with v_x;
    try apply H with t_x0 k_sx k_tx;
    try apply H0 with t_x0 k_sx k_tx k_t k_t'; trivial.
    inversion H12; try inversion H1;
    pose proof (fresh_varT_not_elem nms (concatE (ECons x s_x g) g') t') as Hy; 
    set (y := fresh_varT nms (concatE (ECons x s_x g) g') t') in Hy; 
    destruct Hy as [Hyt' [_ [Hy Henv]]];
    rewrite lem_tsubFV_unbindT with y v_x t';
    try apply lem_subst_wf_top with t_x;
    try apply H17; try apply WFKind; try apply H21;
    try apply lem_typ_islc with g t_x0; 
    try apply lem_typing_hasftype;
    try apply H with t_x0 k_sx k_tx;
    try apply unique_concat; 
    try apply intersect_names_add_intro_l;
    simpl; try split; trivial.
  - (* SBind *) inversion H10; try inversion H0; subst t0 k g0; simpl;
    apply SBind with (names_add x (union (union nms nms0) (binds (concatE g g'))));
    trivial; intros; apply not_elem_names_add_elim in H12; destruct H12;
    apply not_elem_union_elim in H13; destruct H13 as [H13 H19]; 
    apply not_elem_union_elim in H13; destruct H13;
    apply not_elem_concat_elim in H19; destruct H19;
    assert (ECons y t_x (concatE (ECons x s_x g) g') = concatE (ECons x s_x g) (ECons y t_x g'))
      as Henv by reflexivity; rewrite Henv;
    apply H with t_x0 k_sx k_tx k_t k_t';
    try apply H16; destruct k_t; 
    try apply WFKind; try apply H20;
    try apply lem_weaken_wf_top;
    try apply WFEBind with k_x;
    try apply intersect_names_add_intro_r; 
    try apply not_elem_names_add_intro; 
    pose proof (lem_binds_concat (ECons x s_x g) g') as Hbin;
    try destruct Hbin; trivial;
    try apply not_elem_subset with (union (binds (ECons x s_x g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; 
    try apply unique_concat;
    try apply intersect_names_add_intro_l; simpl; auto.
  - (* SPoly *) inversion H10; try inversion H0;
    inversion H11; try inversion H17;
    apply SPoly 
      with (names_add x (union (union nms0 nms1) (union nms (binds (concatE g g')))));
    trivial; intros;
    apply not_elem_names_add_elim in H23; destruct H23;
    apply not_elem_union_elim in H24; destruct H24;
    apply not_elem_union_elim in H24; destruct H24;
    apply not_elem_union_elim in H25; destruct H25;
    apply not_elem_concat_elim in H27; destruct H27;
    assert (EConsT a k (concatE (ECons x s_x g) g') = concatE (ECons x s_x g) (EConsT a k g'))
      as Henv by reflexivity; rewrite Henv;
    apply H with t_x k_sx k_tx k_t0 k_t1;
    try apply WFEBindT;
    try apply intersect_names_add_intro_r; 
    try apply not_elem_names_add_intro; 
    pose proof (lem_binds_concat (ECons x s_x g) g') as Hbin;
    try destruct Hbin; trivial;
    try apply not_elem_subset with (union (binds (ECons x s_x g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; 
    try apply unique_concat;
    try apply intersect_names_add_intro_l; simpl; auto.
  - (* SList *) apply SList with (names_add x (union nms (binds (concatE g g'))));
    try apply H with t_x k_sx k_tx Star Star; intros;
    try (apply lem_wflist_wftype with p1 k_t;  apply H10);
    try (apply lem_wflist_wftype with p2 k_t'; apply H11);
    try assert (ECons y (TList t1 PEmpty) (concatE (ECons x s_x g) g') 
                      = concatE (ECons x s_x g) (ECons y (TList t1 PEmpty) g'))
      as Henv by reflexivity; try rewrite Henv;
    try apply INarrow with t_x k_sx k_tx;
    try apply lem_truncate_wfenv in H9 as p_xg; try inversion p_xg; 
    try apply not_elem_names_add_elim in H0; try destruct H0;
    try apply not_elem_union_elim in H18; try destruct H18;
    try apply not_elem_concat_elim in H19; try destruct H19;
    try apply intersect_names_add_intro_r; 
    try apply not_elem_names_add_intro;
    simpl; try split; auto.
  Qed.

Lemma lem_narrow_typ : 
  forall (g g':env) (x:vname) (s_x t_x:type) (k_sx k_tx:kind) (e:expr) (t:type),
    Hastype (concatE (ECons x t_x g) g') e t
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x 
            -> WFEnv (concatE (ECons x s_x g) g')
            -> Hastype (concatE (ECons x s_x g) g') e t .
Proof. intros; pose proof lem_narrow_typ'; destruct H9 as [Htyp Hsub];
  apply Htyp with (concatE (ECons x t_x g) g') t_x k_sx k_tx; trivial. Qed.

Lemma lem_narrow_subtype :
  forall (g g':env) (x:vname) (s_x t_x:type) (k_sx k_tx:kind) (t t':type) (k_t k_t':kind),
    Subtype (concatE (ECons x t_x g) g') t t'
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x
            -> WFEnv (concatE (ECons x s_x g) g')
            -> WFtype (concatE (ECons x s_x g) g') t  k_t
            -> WFtype (concatE (ECons x s_x g) g') t' k_t'
            -> Subtype (concatE (ECons x s_x g) g') t t' .
Proof. intros; pose proof lem_narrow_typ'; destruct H11 as [Htyp Hsub].
  apply Hsub with (concatE (ECons x t_x g) g') t_x k_sx k_tx k_t k_t'; trivial. Qed.

Lemma lem_narrow_typ_top : 
  forall (g:env) (x:vname) (s_x t_x:type) (k_sx k_tx:kind) (e:expr) (t:type),
    Hastype (ECons x t_x g) e t
            -> unique g -> ~ (in_env x g) 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x -> WFEnv g
            -> Hastype (ECons x s_x g) e t .
Proof. intros; assert (ECons x s_x g = concatE (ECons x s_x g) Empty) by reflexivity;
  rewrite H6; apply lem_narrow_typ with t_x k_sx k_tx; 
  try apply intersect_empty_r; try apply WFEBind with k_sx;
  simpl; intuition. Qed.

Lemma lem_narrow_subtype_top :
  forall (g:env) (x:vname) (s_x t_x:type) (k_sx k_tx:kind) (t t':type) (k_t k_t':kind),
    Subtype (ECons x t_x g) t t'
            -> unique g -> ~ (in_env x g) 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x -> WFEnv g
            -> WFtype  (ECons x s_x g) t  k_t
            -> WFtype  (ECons x s_x g) t' k_t'
            -> Subtype (ECons x s_x g) t  t' .
Proof. intros; assert (ECons x s_x g = concatE (ECons x s_x g) Empty) by reflexivity;
  rewrite H8; apply lem_narrow_subtype with t_x k_sx k_tx k_t k_t'; 
  try apply intersect_empty_r; try apply WFEBind with k_sx;
  simpl; intuition. Qed.