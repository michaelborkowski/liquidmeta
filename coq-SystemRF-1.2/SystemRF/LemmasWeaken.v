Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.Typing.

(*-----------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas     
-----------------------------------------------------------*)

Lemma lem_weaken' : ( forall (g'g : env) (e : expr) (t : type),
    Hastype g'g e t -> ( forall (g g':env) (x:vname) (t_x:type),
        g'g = concatE g g' -> unique g -> unique g'
                           -> intersect (binds g) (binds g') = empty
                           -> ~ (in_env x g) -> ~ (in_env x g') 
                           -> Hastype (concatE (Cons x t_x g) g') e t ) ) /\ ((
  forall (g'g : env) (t : type) (t' : type),
    Subtype g'g t t' -> ( forall (g g':env) (x:vname) (t_x:type),
        g'g = concatE g g' -> unique g -> unique g'
                           -> intersect (binds g) (binds g') = empty
                           -> ~ (in_env x g) -> ~ (in_env x g') 
                           -> Subtype (concatE (Cons x t_x g) g') t t') ) /\ ((
  forall (g'g : env) (ps : preds),
    PHastype g'g ps -> ( forall (g g':env) (x:vname) (t_x:type),
        g'g = concatE g g' -> unique g -> unique g'
                           -> intersect (binds g) (binds g') = empty
                           -> ~ (in_env x g) -> ~ (in_env x g') 
                           -> PHastype (concatE (Cons x t_x g) g') ps) ) /\ (
  forall (g'g : env) (t : type) (k : kind),
    WFtype g'g t k -> ( forall (g g':env) (x:vname) (t_x:type),
        g'g = concatE g g' -> unique g -> unique g'
                           -> intersect (binds g) (binds g') = empty
                           -> ~ (in_env x g) -> ~ (in_env x g') 
                           -> WFtype (concatE (Cons x t_x g) g') t k ) ))).
Proof. apply ( judgments_mutind 
  (fun (g'g : env) (e : expr) (t : type) (p_e_t : Hastype g'g e t) => 
    forall (g g':env) (x:vname) (t_x:type),
      g'g = concatE g g' -> unique g -> unique g'
                         -> intersect (binds g) (binds g') = empty
                         -> ~ (in_env x g) -> ~ (in_env x g') 
                         -> Hastype (concatE (Cons x t_x g) g') e t )
  (fun (g'g : env) (t : type) (t' : type) (p_t_t' : Subtype g'g t t') => 
    forall (g g':env) (x:vname) (t_x:type),
      g'g = concatE g g' -> unique g -> unique g'
                         -> intersect (binds g) (binds g') = empty
                         -> ~ (in_env x g) -> ~ (in_env x g') 
                         -> Subtype (concatE (Cons x t_x g) g') t t' )  
  (fun (g'g : env) (ps : preds) (p_g'g_ps : PHastype g'g ps) => 
    forall (g g':env) (x:vname) (t_x:type),
      g'g = concatE g g' -> unique g -> unique g'
                         -> intersect (binds g) (binds g') = empty
                         -> ~ (in_env x g) -> ~ (in_env x g') 
                         -> PHastype (concatE (Cons x t_x g) g') ps  )
  (fun (g'g : env) (t : type) (k : kind) (p_t_k : WFtype g'g t k) => 
    forall (g g':env) (x:vname) (t_x:type),
      g'g = concatE g g' -> unique g -> unique g'
                         -> intersect (binds g) (binds g') = empty
                         -> ~ (in_env x g) -> ~ (in_env x g') 
                         -> WFtype (concatE (Cons x t_x g) g') t k  )
                         );
  intro env; intros; subst env.
  - (* TBC *) apply TBC.
  - (* TIC *) apply TIC.
  - (* TVar *) apply TVar; try apply lem_boundin_weaken;
    try apply H; trivial.
  - (* TPrm *) apply TPrm.
  - (* TAbs *) apply TAbs with k_x (names_add x (union nms (binds (concatE g g'))));
    try apply H; trivial; intros;
    apply not_elem_names_add_elim in H1; destruct H1; 
    apply not_elem_union_elim in H7; destruct H7;
    apply not_elem_concat_elim in H8; destruct H8;
    assert (Cons y t_x (concatE (Cons x t_x0 g) g') = concatE (Cons x t_x0 g) (Cons y t_x g'))
      by reflexivity; rewrite H10;      
    apply H0; unfold in_env; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; intuition.    
  - (* TApp *) apply TApp; apply H || apply H0; trivial.
  - (* TAbsT *) apply TAbsT with (names_add x (union nms (binds (concatE g g')))); intros;
    assert (ConsT a' k (concatE (Cons x t_x g) g') = concatE (Cons x t_x g) (ConsT a' k g'))
      by reflexivity; rewrite H6;
    apply not_elem_names_add_elim in H0; destruct H0; 
    apply not_elem_union_elim in H7; destruct H7;
    apply not_elem_concat_elim in H8; destruct H8;
    apply H; unfold in_env; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; intuition.
  - (* TAppT *) apply TAppT with k; try apply H; try apply H0; trivial.
  - (* TLet *) apply TLet with t_x k (names_add x (union nms (binds (concatE g g'))));
    try apply H; try apply H0; trivial; intros;
    assert (Cons y t_x (concatE (Cons x t_x0 g) g') = concatE (Cons x t_x0 g) (Cons y t_x g'))
      by reflexivity; rewrite H8;
    apply not_elem_names_add_elim in H2; destruct H2; 
    apply not_elem_union_elim in H9; destruct H9;
    apply not_elem_concat_elim in H10; destruct H10;
    apply H1; unfold in_env; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; intuition.
  - (* TAnn *) apply TAnn; try apply H; trivial.
  - (* TIf *) apply TIf with ps k (names_add x (union nms (binds (concatE g g')))); 
    try apply H; try apply H0; trivial; intros;
    assert (Cons y (self (TRefn TBool ps) (Bc true) Base) (concatE (Cons x t_x g) g') 
              = concatE (Cons x t_x g) (Cons y (self (TRefn TBool ps) (Bc true) Base) g'))
      by reflexivity; try rewrite H9;
    assert (Cons y (self (TRefn TBool ps) (Bc false) Base) (concatE (Cons x t_x g) g') 
              = concatE (Cons x t_x g) (Cons y (self (TRefn TBool ps) (Bc false) Base) g'))
      by reflexivity; try rewrite H10;
    apply H1 with y || apply H2 with y; 
    unfold in_env; simpl; try split;
    apply not_elem_names_add_elim in H3; destruct H3; 
    apply not_elem_union_elim in H11; destruct H11;
    apply not_elem_concat_elim in H12; destruct H12;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; intuition.
  - (* TSub *) apply TSub with s k; try apply H; try apply H0;
    try apply H1; trivial.
  - (* SBase *) apply SBase with (names_add x (union nms (binds (concatE g g')))); intros;
    apply not_elem_names_add_elim in H; destruct H; 
    apply not_elem_union_elim in H5; destruct H5;
    apply not_elem_concat_elim in H6; destruct H6;
    assert (Cons y (TRefn b PEmpty) (concatE (Cons x t_x g) g') 
              = concatE (Cons x t_x g) (Cons y (TRefn b PEmpty) g'))
      by reflexivity; rewrite H8;
    apply IWeak; unfold in_env; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; intuition.
  - (* SFunc *) apply SFunc with (names_add x (union nms (binds (concatE g g'))));
    try apply H; trivial; intros;
    assert (Cons y s2 (concatE (Cons x t_x g) g') = concatE (Cons x t_x g) (Cons y s2 g'))
      by reflexivity; rewrite H7;
    apply not_elem_names_add_elim in H1; destruct H1; 
    apply not_elem_union_elim in H8; destruct H8;
    apply not_elem_concat_elim in H9; destruct H9;
    apply H0; unfold in_env; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; intuition.
  - (* SWitn *) apply SWitn with v_x; try apply H; try apply H0; trivial.
  - (* SBind *) apply SBind with (names_add x (union nms (binds (concatE g g'))));
    try apply i; intros;
    assert (Cons y t_x (concatE (Cons x t_x0 g) g') = concatE (Cons x t_x0 g) (Cons y t_x g'))
      by reflexivity; rewrite H6;
    apply not_elem_names_add_elim in H0; destruct H0; 
    apply not_elem_union_elim in H7; destruct H7;
    apply not_elem_concat_elim in H8; destruct H8;
    apply H; unfold in_env; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; intuition.
  - (* SPoly *) apply SPoly with (names_add x (union nms (binds (concatE g g')))); intros;
    assert (ConsT a k (concatE (Cons x t_x g) g') = concatE (Cons x t_x g) (ConsT a k g'))
      by reflexivity; rewrite H6;
    apply not_elem_names_add_elim in H0; destruct H0; 
    apply not_elem_union_elim in H7; destruct H7;
    apply not_elem_concat_elim in H8; destruct H8;
    apply H; unfold in_env; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; intuition.
  - (* PTEmp *) apply PTEmp.
  - (* PTCons *) apply PTCons with qs; try apply H;
    try apply H0; intuition.
  - (* WFBase *) apply WFBase; assumption.
  - (* WFRefn *) apply WFRefn with (names_add x (union nms (binds (concatE g g')))); 
    try apply H; trivial; intros;
    apply not_elem_names_add_elim in H1; destruct H1;
    apply not_elem_union_elim in H7; destruct H7;
    apply not_elem_concat_elim in H8; destruct H8;
    assert (Cons y (TRefn b PEmpty) (concatE (Cons x t_x g) g')
            = concatE (Cons x t_x g) (Cons y (TRefn b PEmpty) g') )
      by reflexivity; rewrite H10;
    apply H0; simpl; 
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro;
    try split; intuition.
  - (* WFVar   *) try apply lem_tvboundin_weaken with a k g g' x t_x in t ;
    apply WFVar; assumption.
  - (* WFFunc  *) 
    apply WFFunc with k_x k (names_add x (union nms (binds (concatE g g'))));
    try apply H; trivial; intros;
    apply not_elem_names_add_elim in H1; destruct H1;
    apply not_elem_union_elim in H7; destruct H7;
    apply not_elem_concat_elim in H8; destruct H8;
    assert (Cons y t_x (concatE (Cons x t_x0 g) g') = concatE (Cons x t_x0 g) (Cons y t_x g'))
      by reflexivity; rewrite H10;
    try apply H0; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; try split; intuition.
  - (* WFExis  *) 
    apply WFExis with k_x (names_add x (union nms (binds (concatE g g'))));
    try apply H; trivial; intros;
    apply not_elem_names_add_elim in H1; destruct H1;
    apply not_elem_union_elim in H7; destruct H7;
    apply not_elem_concat_elim in H8; destruct H8;
    assert (Cons y t_x (concatE (Cons x t_x0 g) g') = concatE (Cons x t_x0 g) (Cons y t_x g'))
      by reflexivity; rewrite H10;
    try apply H0; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; try split; intuition.
  - (* WFPoly  *) 
    apply WFPoly with k_t (names_add x (union nms (binds (concatE g g')))); intros;
    apply not_elem_names_add_elim in H0; destruct H0;
    apply not_elem_union_elim in H6; destruct H6;
    apply not_elem_concat_elim in H7; destruct H7;
    apply (H a' H6 g (ConsT a' k g') x t_x); simpl;
    try apply intersect_names_add_intro_r;
    unfold in_env; try apply not_elem_names_add_intro;
    try split; intuition.
  - (* WFKind *) intros; apply WFKind; apply H; trivial. 
  Qed.

Lemma lem_weaken_typ : forall (g g':env) (e:expr) (t:type) (x:vname) (t_x:type),
    Hastype (concatE g g') e t 
                          -> unique g -> unique g'
                          -> intersect (binds g) (binds g') = empty
                          -> ~ (in_env x g) -> ~ (in_env x g') 
                          -> Hastype (concatE (Cons x t_x g) g') e t.
Proof. intros; apply lem_weaken' with (concatE g g'); trivial. Qed.

Lemma lem_weaken_subtype : forall (g g':env) (t:type) (t':type) (x:vname) (t_x:type),
    Subtype (concatE g g') t t' 
                          -> unique g -> unique g'
                          -> intersect (binds g) (binds g') = empty
                          -> ~ (in_env x g) -> ~ (in_env x g') 
                          -> Subtype (concatE (Cons x t_x g) g') t t'.
Proof. intros; apply lem_weaken' with (concatE g g'); trivial. Qed.

Lemma lem_weaken_wf : forall (g g' : env) (t : type) (k : kind) (x : vname) (t_x : type),
    WFtype (concatE g g') t k 
                          -> unique g -> unique g'
                          -> intersect (binds g) (binds g') = empty
                          -> ~ (in_env x g) -> ~ (in_env x g') 
                          -> WFtype (concatE (Cons x t_x g) g') t k.
Proof. intros; apply lem_weaken' with (concatE g g'); trivial. Qed.

Lemma lem_weaken_typ_top : forall (g:env) (e:expr) (t:type) (x:vname) (t_x:type),
    Hastype g e t -> unique g -> ~ (in_env x g) 
                  -> Hastype (Cons x t_x g) e t.
Proof. intros; assert (Cons x t_x g = concatE (Cons x t_x g) Empty) by reflexivity;
  rewrite H2; apply lem_weaken_typ; 
  try apply intersect_empty_r; simpl; intuition. Qed.

Lemma lem_weaken_subtype_top : forall (g:env) (t:type) (t':type) (x:vname) (t_x:type),
    Subtype g t t'  -> unique g -> ~ (in_env x g) 
                    -> Subtype (Cons x t_x g) t t'.
Proof. intros; assert (Cons x t_x g = concatE (Cons x t_x g) Empty) by reflexivity;
  rewrite H2; apply lem_weaken_subtype; 
  try apply intersect_empty_r; simpl; intuition. Qed.
  
Lemma lem_weaken_wf_top : forall (g : env) (t : type) (k : kind) (x : vname) (t_x : type),
    WFtype g t k    -> unique g -> ~ (in_env x g) 
                    -> WFtype (Cons x t_x g) t k.
Proof. intros; assert (Cons x t_x g = concatE (Cons x t_x g) Empty) by reflexivity;
  rewrite H2; apply lem_weaken_wf; simpl; try apply intersect_empty_r; intuition. Qed.