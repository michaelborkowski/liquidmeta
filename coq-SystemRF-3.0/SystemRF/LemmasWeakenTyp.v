Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.BasicPropsWellFormedness.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.Typing.
Require Import SystemRF.LemmasWeakenWF.
Require Import SystemRF.LemmasWellFormedness.
Require Import SystemRF.SubstitutionLemmaWF.
Require Import SystemRF.LemmasTyping.

Require Import ZArith.

(*-----------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas     
-----------------------------------------------------------*)

Lemma lem_weaken_typ' : ( forall (g'g : env) (e : expr) (t : type),
    Hastype g'g e t -> ( forall (g g':env) (x:vname) (t_x:type),
        g'g = concatE g g' -> unique g -> unique g'
                           -> intersect (binds g) (binds g') = empty
                           -> ~ (in_env x g) -> ~ (in_env x g') -> WFEnv (concatE g g')
                           -> Hastype (concatE (ECons x t_x g) g') e t ) ) /\ (
  forall (g'g : env) (t : type) (t' : type),
    Subtype g'g t t' -> ( forall (g g':env) (x:vname) (t_x:type) (k_t k_t':kind),
        g'g = concatE g g' -> unique g -> unique g'
                           -> intersect (binds g) (binds g') = empty
                           -> ~ (in_env x g) -> ~ (in_env x g') -> WFEnv (concatE g g')
                           -> WFtype (concatE g g') t  k_t
                           -> WFtype (concatE g g') t' k_t'
                           -> Subtype (concatE (ECons x t_x g) g') t t') ).
Proof. apply ( judgments_mutind 
  (fun (g'g : env) (e : expr) (t : type) (p_e_t : Hastype g'g e t) => 
    forall (g g':env) (x:vname) (t_x:type),
      g'g = concatE g g' -> unique g -> unique g'
                         -> intersect (binds g) (binds g') = empty
                         -> ~ (in_env x g) -> ~ (in_env x g') -> WFEnv (concatE g g')
                         -> Hastype (concatE (ECons x t_x g) g') e t )
  (fun (g'g : env) (t : type) (t' : type) (p_t_t' : Subtype g'g t t') => 
    forall (g g':env) (x:vname) (t_x:type) (k_t k_t':kind),
      g'g = concatE g g' -> unique g -> unique g'
                         -> intersect (binds g) (binds g') = empty
                         -> ~ (in_env x g) -> ~ (in_env x g') -> WFEnv (concatE g g')
                         -> WFtype (concatE g g') t  k_t
                         -> WFtype (concatE g g') t' k_t'
                         -> Subtype (concatE (ECons x t_x g) g') t t')  
                         );
  intro env; intros; subst env.
  - (* TBC *) apply TBC.
  - (* TIC *) apply TIC.
  - (* TVar *) apply TVar; try apply lem_boundin_weaken;
    try apply lem_weaken_wf; assumption.
  - (* TPrm *) apply TPrm.
  - (* TAbs *) apply TAbs with k_x (names_add x (union nms (binds (concatE g g'))));
    try apply lem_weaken_wf; try assumption; intros;
    apply not_elem_names_add_elim in H0; destruct H0; 
    apply not_elem_union_elim in H7; destruct H7;
    apply not_elem_concat_elim in H8; destruct H8;
    assert (ECons y t_x (concatE (ECons x t_x0 g) g') = concatE (ECons x t_x0 g) (ECons y t_x g'))
      by reflexivity; rewrite H10;      
    apply H; try apply WFEBind with k_x;
    unfold in_env; simpl;
    pose proof (lem_binds_concat g g'); destruct H11;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; trivial;
    try apply not_elem_subset with (union (binds g) (binds g'));
    try apply not_elem_union_intro; auto.    
  - (* TApp *) apply TApp; apply H || apply H0; trivial.
  - (* TAbsT *) apply TAbsT with (names_add x (union nms (binds (concatE g g')))); intros;
    assert (EConsT a' k (concatE (ECons x t_x g) g') = concatE (ECons x t_x g) (EConsT a' k g'))
      by reflexivity; rewrite H7;
    apply not_elem_names_add_elim in H0; destruct H0; 
    apply not_elem_union_elim in H8; destruct H8;
    apply not_elem_concat_elim in H9; destruct H9;
    apply H; try apply WFEBindT;
    unfold in_env; simpl;
    pose proof (lem_binds_concat g g'); destruct H11;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; trivial;
    try apply not_elem_subset with (union (binds g) (binds g'));
    try apply not_elem_union_intro; auto. 
  - (* TAppT *) apply TAppT with k; try apply H; try apply lem_weaken_wf; trivial.
  - (* TLet *) apply TLet with t_x k (names_add x (union nms (binds (concatE g g'))));
    try apply H; try apply lem_weaken_wf; trivial; intros;
    assert (ECons y t_x (concatE (ECons x t_x0 g) g') = concatE (ECons x t_x0 g) (ECons y t_x g'))
      by reflexivity; rewrite H8;
    apply not_elem_names_add_elim in H1; destruct H1; 
    apply not_elem_union_elim in H9; destruct H9;
    apply not_elem_concat_elim in H10; destruct H10.
    apply H0; try apply WFEBind with Star;
    unfold in_env; simpl;
    try apply lem_typing_wf with e_x;
    pose proof (lem_binds_concat g g'); destruct H12;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; trivial;
    try apply not_elem_subset with (union (binds g) (binds g'));
    try apply not_elem_union_intro; auto. 
  - (* TAnn *) apply TAnn; try apply H; trivial.
  - (* TIf *) apply TIf with ps k (names_add x (union nms (binds (concatE g g')))); 
    try apply H; try apply lem_weaken_wf; trivial; intros;
    assert (ECons y (self (TRefn TBool ps) (Bc true) Base) (concatE (ECons x t_x g) g') 
              = concatE (ECons x t_x g) (ECons y (self (TRefn TBool ps) (Bc true) Base) g'))
      by reflexivity; try rewrite H9;
    assert (ECons y (self (TRefn TBool ps) (Bc false) Base) (concatE (ECons x t_x g) g') 
              = concatE (ECons x t_x g) (ECons y (self (TRefn TBool ps) (Bc false) Base) g'))
      by reflexivity; try rewrite H10;
    apply H0 with y || apply H1 with y; 
    try apply WFEBind with Base;
    try apply lem_selfify_wf; try apply FTBC;
    apply lem_typing_wf in h; 
    unfold in_env; simpl; try split;
    apply not_elem_names_add_elim in H2; destruct H2; 
    apply not_elem_union_elim in H11; destruct H11;
    apply not_elem_concat_elim in H12; destruct H12;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; trivial;
    pose proof (lem_binds_concat g g'); try destruct H14; 
    try apply not_elem_subset with (union (binds g) (binds g'));
    try apply not_elem_union_intro;
    inversion h; auto.
  - (* TNil *) apply TNil with k; try apply lem_weaken_wf; auto.
  - (* TCons *) apply TCons; try apply H; try apply H0; trivial.
  - (* TSwitch *) apply TSwit with t ps k (names_add x (union nms (binds (concatE g g'))));
    try apply H; intros; 
    try assert (ECons y (TList t (PCons (eq (length t (BV 0)) (Ic 0)) ps)) (concatE (ECons x t_x g) g') 
              = concatE (ECons x t_x g) (ECons y (TList t (PCons (eq (length t (BV 0)) (Ic 0)) ps)) g'))
      by reflexivity; try rewrite H9;
    try assert (ECons y (TList t ps) (concatE (ECons x t_x g) g') 
              = concatE (ECons x t_x g) (ECons y (TList t ps) g'))
      by reflexivity; try rewrite H10;
    try apply H0 with y; try apply H1;
    try apply lem_weaken_wf;
    try apply WFEBind with Star;
    apply lem_typing_wf in h;
    try apply lem_wflist_len_zero;
    try apply not_elem_names_add_elim in H2; try destruct H2; 
    try apply not_elem_union_elim in H11; try destruct H11;
    try apply not_elem_concat_elim in H12; try destruct H12;
    try apply intersect_names_add_intro_r;
    unfold in_env; fold concatE;
    try apply not_elem_names_add_intro;
    try apply not_elem_concat_intro;
    simpl; try split; try discriminate; auto. 
  - (* TSub *) apply TSub with s k; try apply H; try apply lem_weaken_wf;
    try apply H0 with Star k; try apply lem_typing_wf with e; trivial.

  - (* SBase *) 
    apply SBase 
      with (names_add x (union nms (binds (concatE g g')))); intros;
    apply not_elem_names_add_elim in H; destruct H; 
    apply not_elem_union_elim in H8; destruct H8;
    apply not_elem_concat_elim in H9; destruct H9;
    assert (ECons y (TRefn b PEmpty) (concatE (ECons x t_x g) g') 
              = concatE (ECons x t_x g) (ECons y (TRefn b PEmpty) g'))
      by reflexivity; rewrite H11;
    apply IWeak; try apply WFEBind with k_t;
    unfold in_env; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; trivial;
    assert (WFtype (concatE g g') (TRefn b PEmpty) k_t) as Hwf
      by (inversion H6; try inversion H12; try apply WFKind;
          try (apply WFBase; apply H16 || apply H18); try apply H14;
          try (apply WFVar; apply H16 || apply H20); try apply H18);
    assert (~ Elem x (binds (concatE g g')));
    try apply not_elem_concat_intro;
    try apply not_elem_union_intro; auto;

    apply lem_free_bound_in_env 
      with (concatE g g') (TRefn b p1) k_t x in H6;
    apply lem_free_bound_in_env 
      with (concatE g g') (TRefn b p2) k_t' x in H7;
    simpl in H6; simpl in H7; trivial;
    destruct H6; destruct H7;
    pose proof fv_unbind_elim as [_ [_ Hfv]];
    pose proof ftv_unbind_elim as [_ [_ Hftv]].

    apply not_elem_subset with (names_add y (fvP p1));
    try apply not_elem_names_add_intro; try split; auto.

    assert (~ Elem x (ftvP p1)).
      destruct b; try apply not_elem_names_add_elim in H13;
      try destruct H13 as [_ H13]; apply H13.
    apply not_elem_subset with (ftvP p1); apply H15 || apply Hftv.
    
    apply not_elem_subset with (names_add y (fvP p2));
    try apply not_elem_names_add_intro; try split; auto.

    assert (~ Elem x (ftvP p2)).
      destruct b; try apply not_elem_names_add_elim in H14;
      try destruct H14 as [_ H14]; apply H14.
    apply not_elem_subset with (ftvP p2); apply H15 || apply Hftv.
  - (* SFunc *) inversion H8; try inversion H1;
    inversion H9; try inversion H16.
    apply SFunc 
      with (names_add x (union (union nms (union nms0 nms1)) (binds (concatE g g'))));
    try apply H with k_x0 k_x; trivial; intros;
    assert (ECons y s2 (concatE (ECons x t_x g) g') = concatE (ECons x t_x g) (ECons y s2 g'))
      by reflexivity; rewrite H24;
    apply not_elem_names_add_elim in H23; destruct H23;  
    apply not_elem_union_elim in H25; destruct H25; 
    apply not_elem_union_elim in H25; destruct H25;
    apply not_elem_union_elim in H27; destruct H27; 
    apply not_elem_concat_elim in H26; destruct H26;
    apply H0 with k k0; try apply WFEBind with k_x0;
    unfold in_env; simpl; try apply H21;
    try apply lem_narrow_wf_top with s1;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; 
    try apply not_elem_concat_intro;
    try apply unique_concat; auto.
  - (* SWitn *) apply SWitn with v_x; try apply H; 
    try apply H0 with k_t k_t'; 
    inversion H9; try inversion H1;
    pose proof (fresh_varT_not_elem nms (concatE g g') t') as Hy; 
    set (y := fresh_varT nms (concatE g g') t') in Hy; 
    destruct Hy as [Hyt' [_ [Hy Henv]]];
    try rewrite lem_tsubFV_unbindT with y v_x t';
    try apply lem_subst_wf_top with t_x;
    try apply WFKind;
    try apply lem_typing_hasftype;
    try apply unique_concat; auto. 
  - (* SBind *)  inversion H7; try inversion H0;
    apply SBind with (names_add x (union (union nms nms0) (binds (concatE g g'))));
    try apply i; intros y Hy;
    assert (ECons y t_x (concatE (ECons x t_x0 g) g') = concatE (ECons x t_x0 g) (ECons y t_x g'))
      as Henv by reflexivity; rewrite Henv; 
    apply not_elem_names_add_elim in Hy; destruct Hy as [Hx Hy]; 
    apply not_elem_union_elim in Hy; destruct Hy as [Hy Hyg];
    apply not_elem_union_elim in Hy; destruct Hy;
    apply not_elem_concat_elim in Hyg; destruct Hyg;
    apply H with k_t k_t'; try apply WFEBind with k_x;
    destruct k_t; try apply H13; try apply WFKind;
    try apply H17; try apply lem_weaken_wf_top;
    unfold in_env; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; 
    try apply not_elem_concat_intro; auto.
  - (* SPoly *) inversion H7; try inversion H0;
    inversion H8; try inversion H14;  
    apply SPoly 
      with (names_add x (union (union nms (union nms0 nms1)) (binds (concatE g g')))); 
    intros;
    assert (EConsT a k (concatE (ECons x t_x g) g') = concatE (ECons x t_x g) (EConsT a k g'))
      by reflexivity; rewrite H21;
    apply not_elem_names_add_elim in H20; destruct H20; 
    apply not_elem_union_elim in H22; destruct H22;
    apply not_elem_union_elim in H22; destruct H22;
    apply not_elem_union_elim in H24; destruct H24;
    apply not_elem_concat_elim in H23; destruct H23;
    apply H with k_t0 k_t1; try apply WFEBindT;
    unfold in_env; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; 
    try apply not_elem_concat_intro;
    try apply unique_concat; auto.
  - (* SList *) apply lem_wflist_wftype in H7 as p_env_t1;
    apply lem_wflist_wftype in H8 as p_env_t2;
    apply SList with (names_add x (union nms (binds (concatE g g'))));
    try apply H with Star Star; trivial; intros.
        assert (ECons y (TList t1 PEmpty) (concatE (ECons x t_x g) g') 
              = concatE (ECons x t_x g) (ECons y (TList t1 PEmpty) g'))
      by reflexivity; rewrite H9.
    apply not_elem_names_add_elim in H0; destruct H0; 
    apply not_elem_union_elim in H10; destruct H10;
    apply not_elem_concat_elim in H11; destruct H11.
    apply lem_free_bound_in_env 
      with (concatE g g') (TList t1 p1) k_t x in H7 as H7';
    apply lem_free_bound_in_env 
      with (concatE g g') (TList t2 p2) k_t' x in H8;
    try apply not_elem_concat_intro; trivial;
    simpl in H7'; simpl in H8; destruct H7'; destruct H8.
    apply not_elem_union_elim in H8; destruct H8;
    apply not_elem_union_elim in H13; destruct H13;
    apply not_elem_union_elim in H14; destruct H14;
    apply not_elem_union_elim in H15; destruct H15;
    pose proof fv_unbind_elim as [_ [_ Hfv]];
    pose proof ftv_unbind_elim as [_ [_ Hftv]];
    apply IWeak; try apply WFEBind with Star;
    unfold in_env; simpl; fold concatE;
    try apply WFList with Star;   
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro;
    try apply not_elem_concat_intro;
    try split; auto. 

    apply not_elem_subset with (names_add y (fvP p1));
    try apply not_elem_names_add_intro; try split; auto.
    apply not_elem_subset with (ftvP p1); trivial.
    apply not_elem_subset with (names_add y (fvP p2));
    try apply not_elem_names_add_intro; try split; auto.
    apply not_elem_subset with (ftvP p2); trivial.
  Qed.

Lemma lem_weaken_typ : forall (g g':env) (e:expr) (t:type) (x:vname) (t_x:type),
    Hastype (concatE g g') e t 
                          -> unique g -> unique g'
                          -> intersect (binds g) (binds g') = empty
                          -> ~ (in_env x g) -> ~ (in_env x g') -> WFEnv (concatE g g')
                          -> Hastype (concatE (ECons x t_x g) g') e t.
Proof. intros; apply lem_weaken_typ' with (concatE g g'); trivial. Qed.

Lemma lem_weaken_subtype : 
  forall (g g':env) (t:type) (t':type) (x:vname) (t_x:type) (k_t k_t':kind),
    Subtype (concatE g g') t t' 
                          -> unique g -> unique g'
                          -> intersect (binds g) (binds g') = empty
                          -> ~ (in_env x g) -> ~ (in_env x g') -> WFEnv (concatE g g')
                          -> WFtype (concatE g g') t  k_t
                          -> WFtype (concatE g g') t' k_t'
                          -> Subtype (concatE (ECons x t_x g) g') t t'.
Proof. intros; pose proof lem_weaken_typ' as [_ Hweaken]; 
  apply Hweaken with (concatE g g') k_t k_t'; trivial. Qed.

Lemma lem_weaken_typ_top : forall (g:env) (e:expr) (t:type) (x:vname) (t_x:type),
    Hastype g e t -> unique g -> ~ (in_env x g) -> WFEnv g
                  -> Hastype (ECons x t_x g) e t.
Proof. intros; assert (ECons x t_x g = concatE (ECons x t_x g) Empty) by reflexivity;
  rewrite H3; apply lem_weaken_typ; 
  try apply intersect_empty_r; simpl; intuition. Qed.

Lemma lem_weaken_subtype_top : 
  forall (g:env) (t:type) (t':type) (x:vname) (t_x:type) (k_t k_t':kind),
    Subtype g t t'  -> unique g -> ~ (in_env x g) -> WFEnv g 
                    -> WFtype g t  k_t  -> WFtype g t' k_t'
                    -> Subtype (ECons x t_x g) t t'.
Proof. intros; assert (ECons x t_x g = concatE (ECons x t_x g) Empty) by reflexivity;
  rewrite H5; apply lem_weaken_subtype with k_t k_t'; 
  try apply intersect_empty_r; simpl; intuition. Qed.