Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.Typing.
Require Import SystemRF.LemmasWeakenWF.
Require Import SystemRF.LemmasWeakenWFTV.
Require Import SystemRF.LemmasWellFormedness.
Require Import SystemRF.SubstitutionLemmaWF.
Require Import SystemRF.LemmasTyping.
Require Import SystemRF.LemmasWeakenTyp.

(*-----------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
-----------------------------------------------------------*)

Lemma lem_weaken_tv_typ' : ( forall (g'g : env) (e : expr) (t : type),
    Hastype g'g e t -> ( forall (g g':env) (a:vname) (k_a:kind),
        g'g = concatE g g' -> unique g -> unique g'
                           -> intersect (binds g) (binds g') = empty
                           -> ~ (in_env a g) -> ~ (in_env a g') -> WFEnv (concatE g g')
                           -> Hastype (concatE (ConsT a k_a g) g') e t ) ) /\ (
  forall (g'g : env) (t : type) (t' : type),
    Subtype g'g t t' -> ( forall (g g':env) (a:vname) (k_a k_t k_t':kind),
        g'g = concatE g g' -> unique g -> unique g'
                           -> intersect (binds g) (binds g') = empty
                           -> ~ (in_env a g) -> ~ (in_env a g') -> WFEnv (concatE g g') 
                           -> WFtype (concatE g g') t  k_t
                           -> WFtype (concatE g g') t' k_t'
                           -> Subtype (concatE (ConsT a k_a g) g') t t') ).
Proof. apply ( judgments_mutind 
  (fun (g'g : env) (e : expr) (t : type) (p_e_t : Hastype g'g e t) => 
    forall (g g':env) (a:vname) (k_a:kind),
      g'g = concatE g g' -> unique g -> unique g'
                         -> intersect (binds g) (binds g') = empty
                         -> ~ (in_env a g) -> ~ (in_env a g') -> WFEnv (concatE g g')
                         -> Hastype (concatE (ConsT a k_a g) g') e t )
  (fun (g'g : env) (t : type) (t' : type) (p_t_t' : Subtype g'g t t') => 
    forall (g g':env) (a:vname) (k_a k_t k_t':kind),
      g'g = concatE g g' -> unique g -> unique g'
                         -> intersect (binds g) (binds g') = empty
                         -> ~ (in_env a g) -> ~ (in_env a g') -> WFEnv (concatE g g') 
                         -> WFtype (concatE g g') t  k_t
                         -> WFtype (concatE g g') t' k_t'
                         -> Subtype (concatE (ConsT a k_a g) g') t t')  
                         );
  intro env; intros; subst env.
  - (* TBC *) apply TBC.
  - (* TIC *) apply TIC.
  - (* TVar *) apply TVar; try apply lem_boundin_weaken_tv;
    try apply lem_weaken_tv_wf; assumption.
  - (* TPrm *) apply TPrm.
  - (* TAbs *) apply TAbs with k_x (names_add a (union nms (binds (concatE g g'))));
    try apply lem_weaken_tv_wf; try assumption; intros;
    apply not_elem_names_add_elim in H0; destruct H0; 
    apply not_elem_union_elim in H7; destruct H7;
    apply not_elem_concat_elim in H8; destruct H8;
    assert (Cons y t_x (concatE (ConsT a k_a g) g') = concatE (ConsT a k_a g) (Cons y t_x g'))
      by reflexivity; rewrite H10;      
    apply H; try apply WFEBind with k_x;
    unfold in_env; simpl;
    pose proof (lem_binds_concat g g'); destruct H11;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; trivial;
    try apply not_elem_subset with (union (binds g) (binds g'));
    try apply not_elem_union_intro; auto.  
  - (* TApp *) apply TApp; apply H || apply H0; trivial.
  - (* TAbsT *) apply TAbsT with (names_add a (union nms (binds (concatE g g')))); intros;
    assert (ConsT a' k (concatE (ConsT a k_a g) g') = concatE (ConsT a k_a g) (ConsT a' k g'))
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
  - (* TAppT *) apply TAppT with k; try apply H; try apply lem_weaken_tv_wf; trivial.
  - (* TLet *) apply TLet with t_x k (names_add a (union nms (binds (concatE g g'))));
    try apply H; try apply lem_weaken_tv_wf; trivial; intros;
    assert (Cons y t_x (concatE (ConsT a k_a g) g') = concatE (ConsT a k_a g) (Cons y t_x g'))
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
  - (* TIf *) apply TIf with ps k (names_add a (union nms (binds (concatE g g'))));
    try apply H; try apply lem_weaken_tv_wf; trivial; intros;
    assert (Cons y (self (TRefn TBool ps) (Bc true)  Base) (concatE (ConsT a k_a g) g') 
              = concatE (ConsT a k_a g) (Cons y (self (TRefn TBool ps) (Bc true)  Base) g'))
      by reflexivity; try rewrite H9;
    assert (Cons y (self (TRefn TBool ps) (Bc false) Base) (concatE (ConsT a k_a g) g') 
              = concatE (ConsT a k_a g) (Cons y (self (TRefn TBool ps) (Bc false) Base) g'))
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
  - (* TSub *) apply TSub with s k; try apply H; try apply lem_weaken_tv_wf;
    try apply H0 with Star k; try apply lem_typing_wf with e; trivial.
  - (* SBase *) apply SBase with (names_add a (union nms (binds (concatE g g')))); intros;
    apply not_elem_names_add_elim in H; destruct H; 
    apply not_elem_union_elim in H8; destruct H8;
    apply not_elem_concat_elim in H9; destruct H9;
    assert (Cons y (TRefn b PEmpty) (concatE (ConsT a k_a g) g') 
              = concatE (ConsT a k_a g) (Cons y (TRefn b PEmpty) g'))
      by reflexivity; rewrite H11;
    apply IWeakTV; try apply WFEBind with k_t;
    unfold in_env; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; trivial;
    assert (WFtype (concatE g g') (TRefn b PEmpty) k_t) as Hwf
      by (inversion H6; try inversion H12; try apply WFKind;
          try (apply WFBase; apply H16 || apply H18); try apply H14;
          try (apply WFVar; apply H16 || apply H20); try apply H18);
    pose proof (lem_binds_concat g g'); try destruct H12;
    try apply not_elem_subset with (union (binds g) (binds g'));
    try apply not_elem_union_intro; auto.
  - (* SFunc *) inversion H8; try inversion H1;
    inversion H9; try inversion H16.
    apply SFunc 
      with (names_add a (union (union nms (union nms0 nms1)) (binds (concatE g g'))));
    try apply H with k_x0 k_x; trivial; intros;
    assert (Cons y s2 (concatE (ConsT a k_a g) g') = concatE (ConsT a k_a g) (Cons y s2 g'))
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
  - (* SBind *) inversion H7; try inversion H0;
    apply SBind with (names_add a (union (union nms nms0) (binds (concatE g g'))));
    try apply i; intros y Hy;
    assert (Cons y t_x (concatE (ConsT a k_a g) g') = concatE (ConsT a k_a g) (Cons y t_x g'))
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
      with (names_add a (union (union nms (union nms0 nms1)) (binds (concatE g g')))); 
    intros;
    assert (ConsT a0 k (concatE (ConsT a k_a g) g') = concatE (ConsT a k_a g) (ConsT a0 k g'))
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
  Qed.

Lemma lem_weaken_tv_typ : forall (g g':env) (e:expr) (t:type) (a:vname) (k_a:kind),
    Hastype (concatE g g') e t 
                          -> unique g -> unique g'
                          -> intersect (binds g) (binds g') = empty
                          -> ~ (in_env a g) -> ~ (in_env a g') -> WFEnv (concatE g g')
                          -> Hastype (concatE (ConsT a k_a g) g') e t.
Proof. intros; apply lem_weaken_tv_typ' with (concatE g g'); trivial. Qed.

Lemma lem_weaken_tv_subtype : 
  forall (g g':env) (t:type) (t':type) (a:vname) (k_a k_t k_t':kind),
    Subtype (concatE g g') t t' 
                          -> unique g -> unique g'
                          -> intersect (binds g) (binds g') = empty
                          -> ~ (in_env a g) -> ~ (in_env a g') -> WFEnv (concatE g g')
                          -> WFtype (concatE g g') t  k_t
                          -> WFtype (concatE g g') t' k_t'
                          -> Subtype (concatE (ConsT a k_a g) g') t t'.
Proof. intros; pose proof lem_weaken_tv_typ' as [_ Hweaken]; 
  apply Hweaken with (concatE g g') k_t k_t'; trivial. Qed.

Lemma lem_weaken_tv_subtype_top : 
  forall (g:env) (t:type) (t':type) (a:vname) (k_a k_t k_t':kind),
    Subtype g t t'  -> unique g -> ~ (in_env a g) -> WFEnv g
                    -> WFtype g t k_t -> WFtype g t' k_t'
                    -> Subtype (ConsT a k_a g) t t'.
Proof. intros; assert (ConsT a k_a g = concatE (ConsT a k_a g) Empty) 
    by reflexivity; rewrite H5; 
  apply lem_weaken_tv_subtype with k_t k_t';
  try apply intersect_empty_r; unfold unique; auto. Qed.  

Lemma lem_weaken_many_typ : forall (g g':env) (e:expr) (t:type),
    Hastype g e t -> unique g -> unique g'
                  -> intersect (binds g) (binds g') = empty  
                  -> WFEnv (concatE g g')
                  -> Hastype (concatE g g') e t.     
Proof. intros; induction g'; simpl; try assumption; inversion H3;
  simpl in H1; destruct H1;
  simpl in H2; apply intersect_names_add_elim_r in H2; destruct H2;
  apply IHg' in H2 as H'; try assumption;
  apply lem_weaken_typ with (concatE g g') Empty e t x t0 in H'
    || apply lem_weaken_tv_typ with (concatE g g') Empty e t a k in H';
  simpl in H'; unfold in_env; simpl; 
  try (apply intersect_empty_r);
  try (apply unique_concat);
  try (apply not_elem_concat_intro; assumption);  
  intuition. Qed.

Lemma lem_weaken_many_subtype : 
  forall (g g':env) (t:type) (t':type) (k_t k_t':kind),
    Subtype g t t' -> unique g -> unique g'
                   -> intersect (binds g) (binds g') = empty   
                   -> WFEnv (concatE g g')
                   -> WFtype g t  k_t
                   -> WFtype g t' k_t'
                   -> Subtype (concatE g g') t t'.
Proof. intros; induction g'; simpl; try assumption;
  inversion H3; simpl in H1; destruct H1;
  simpl in H2; apply intersect_names_add_elim_r in H2; destruct H2;
  apply lem_weaken_subtype_top with k_t k_t'
    || apply lem_weaken_tv_subtype_top with k_t k_t';
  try apply IHg'; try apply lem_weaken_many_wf;
  try apply unique_concat; trivial. Qed.