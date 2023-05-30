Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.Typing.
Require Import SystemRF.LemmasWeakenWFTV.
Require Import SystemRF.LemmasWeakenTyp.

(*-----------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
-----------------------------------------------------------*)

Lemma lem_weaken_tv_typ' : ( forall (g'g : env) (e : expr) (t : type),
    Hastype g'g e t -> ( forall (g g':env) (a:vname) (k_a:kind),
        g'g = concatE g g' -> unique g -> unique g'
                           -> intersect (binds g) (binds g') = empty
                           -> ~ (in_env a g) -> ~ (in_env a g') -> WFEnv g 
                           -> Hastype (concatE (ConsT a k_a g) g') e t ) ) /\ (
  forall (g'g : env) (t : type) (t' : type),
    Subtype g'g t t' -> ( forall (g g':env) (a:vname) (k_a:kind),
        g'g = concatE g g' -> unique g -> unique g'
                           -> intersect (binds g) (binds g') = empty
                           -> ~ (in_env a g) -> ~ (in_env a g') -> WFEnv g 
                           -> Subtype (concatE (ConsT a k_a g) g') t t') ).
Proof. apply ( judgments_mutind 
  (fun (g'g : env) (e : expr) (t : type) (p_e_t : Hastype g'g e t) => 
    forall (g g':env) (a:vname) (k_a:kind),
      g'g = concatE g g' -> unique g -> unique g'
                         -> intersect (binds g) (binds g') = empty
                         -> ~ (in_env a g) -> ~ (in_env a g') -> WFEnv g
                         -> Hastype (concatE (ConsT a k_a g) g') e t )
  (fun (g'g : env) (t : type) (t' : type) (p_t_t' : Subtype g'g t t') => 
    forall (g g':env) (a:vname) (k_a:kind),
      g'g = concatE g g' -> unique g -> unique g'
                         -> intersect (binds g) (binds g') = empty
                         -> ~ (in_env a g) -> ~ (in_env a g') -> WFEnv g 
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
    apply H; unfold in_env; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; intuition.    
  - (* TApp *) apply TApp; apply H || apply H0; trivial.
  - (* TAbsT *) apply TAbsT with (names_add a (union nms (binds (concatE g g')))); intros;
    assert (ConsT a' k (concatE (ConsT a k_a g) g') = concatE (ConsT a k_a g) (ConsT a' k g'))
      by reflexivity; rewrite H7;
    apply not_elem_names_add_elim in H0; destruct H0; 
    apply not_elem_union_elim in H8; destruct H8;
    apply not_elem_concat_elim in H9; destruct H9;
    apply H; unfold in_env; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; intuition.
  - (* TAppT *) apply TAppT with k; try apply H; try apply lem_weaken_tv_wf; trivial.
  - (* TLet *) apply TLet with t_x k (names_add a (union nms (binds (concatE g g'))));
    try apply H; try apply lem_weaken_tv_wf; trivial; intros;
    assert (Cons y t_x (concatE (ConsT a k_a g) g') = concatE (ConsT a k_a g) (Cons y t_x g'))
      by reflexivity; rewrite H8;
    apply not_elem_names_add_elim in H1; destruct H1; 
    apply not_elem_union_elim in H9; destruct H9;
    apply not_elem_concat_elim in H10; destruct H10.
    apply H0; unfold in_env; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; intuition.
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
    unfold in_env; simpl; try split;
    apply not_elem_names_add_elim in H2; destruct H2; 
    apply not_elem_union_elim in H11; destruct H11;
    apply not_elem_concat_elim in H12; destruct H12;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; intuition.
  - (* TSub *) apply TSub with s k; try apply H; try apply lem_weaken_tv_wf;
    try apply H0; trivial.
  - (* SBase *) apply SBase with (names_add a (union nms (binds (concatE g g')))); intros;
    apply not_elem_names_add_elim in H; destruct H; 
    apply not_elem_union_elim in H6; destruct H6;
    apply not_elem_concat_elim in H7; destruct H7;
    assert (Cons y (TRefn b PEmpty) (concatE (ConsT a k_a g) g') 
              = concatE (ConsT a k_a g) (Cons y (TRefn b PEmpty) g'))
      by reflexivity; rewrite H9;
    apply IWeakTV; unfold in_env; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; intuition.
  - (* SFunc *) apply SFunc with (names_add a (union nms (binds (concatE g g'))));
    try apply H; trivial; intros;
    assert (Cons y s2 (concatE (ConsT a k_a g) g') = concatE (ConsT a k_a g) (Cons y s2 g'))
      by reflexivity; rewrite H8;
    apply not_elem_names_add_elim in H1; destruct H1; 
    apply not_elem_union_elim in H9; destruct H9;
    apply not_elem_concat_elim in H10; destruct H10;
    apply H0; unfold in_env; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; intuition.
  - (* SWitn *) apply SWitn with v_x; try apply H; try apply H0; trivial.
  - (* SBind *) apply SBind with (names_add a (union nms (binds (concatE g g'))));
    try apply i; intros;
    assert (Cons y t_x (concatE (ConsT a k_a g) g') = concatE (ConsT a k_a g) (Cons y t_x g'))
      by reflexivity; rewrite H7;
    apply not_elem_names_add_elim in H0; destruct H0; 
    apply not_elem_union_elim in H8; destruct H8;
    apply not_elem_concat_elim in H9; destruct H9;
    apply H; unfold in_env; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; intuition.
  - (* SPoly *) apply SPoly with (names_add a (union nms (binds (concatE g g')))); intros;
    assert (ConsT a0 k (concatE (ConsT a k_a g) g') = concatE (ConsT a k_a g) (ConsT a0 k g'))
      by reflexivity; rewrite H7;
    apply not_elem_names_add_elim in H0; destruct H0; 
    apply not_elem_union_elim in H8; destruct H8;
    apply not_elem_concat_elim in H9; destruct H9;
    apply H; unfold in_env; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; intuition.
  Qed.

Lemma lem_weaken_tv_typ : forall (g g':env) (e:expr) (t:type) (a:vname) (k_a:kind),
    Hastype (concatE g g') e t 
                          -> unique g -> unique g'
                          -> intersect (binds g) (binds g') = empty
                          -> ~ (in_env a g) -> ~ (in_env a g') -> WFEnv g
                          -> Hastype (concatE (ConsT a k_a g) g') e t.
Proof. intros; apply lem_weaken_tv_typ' with (concatE g g'); trivial. Qed.

Lemma lem_weaken_tv_subtype : forall (g g':env) (t:type) (t':type) (a:vname) (k_a:kind),
    Subtype (concatE g g') t t' 
                          -> unique g -> unique g'
                          -> intersect (binds g) (binds g') = empty
                          -> ~ (in_env a g) -> ~ (in_env a g') -> WFEnv g 
                          -> Subtype (concatE (ConsT a k_a g) g') t t'.
Proof. intros; apply lem_weaken_tv_typ' with (concatE g g'); trivial. Qed.

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

Lemma lem_weaken_many_subtype : forall (g g':env) (t:type) (t':type),
    Subtype g t t' -> unique g -> unique g'
                   -> intersect (binds g) (binds g') = empty   
                   -> WFEnv (concatE g g')
                   -> Subtype (concatE g g') t t'.
Proof. intros; induction g'; simpl; try assumption;
  inversion H3; simpl in H1; destruct H1;
  simpl in H2; apply intersect_names_add_elim_r in H2; destruct H2;
  apply IHg' in H2 as H'; try assumption;
  apply lem_weaken_subtype with (concatE g g') Empty t t' x t0 in H'
    || apply lem_weaken_tv_subtype with (concatE g g') Empty t t' a k in H';
  simpl in H'; unfold in_env; simpl; 
  try (apply intersect_empty_r);
  try (apply unique_concat);
  try (apply not_elem_concat_intro; assumption);  
  intuition. Qed.