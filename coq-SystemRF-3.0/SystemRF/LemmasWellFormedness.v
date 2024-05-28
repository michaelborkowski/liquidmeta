Require Import Arith.
Require Import ZArith.
Require Import Lists.ListSet.

Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.LocalClosure.
Require Import SystemRF.Strengthenings.
Require Import SystemRF.SystemFWellFormedness.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.BasicPropsWellFormedness.
Require Import SystemRF.SystemFLemmasWellFormedness.
Require Import SystemRF.SystemFLemmasWeaken.
Require Import SystemRF.Typing.
Require Import SystemRF.LemmasWeakenWF.
Require Import SystemRF.LemmasWeakenWFTV.

(*------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas  -- first lem good SMT example 
------------------------------------------------------------------------------*)

Lemma lem_openFT_at_equals : forall (j:index) (a:vname) (t1:ftype) (t2:ftype),
    ~ Elem a (ffreeTV t1) -> ~ Elem a (ffreeTV t2) 
        -> openFT_at j a t1 = openFT_at j a t2 -> t1 = t2.
Proof. intros j a t1; revert j; induction t1. 
  - (* FTBasic *) destruct t2; destruct b; try destruct b0; simpl;
    try destruct (Nat.eqb j i) eqn:I; try destruct (Nat.eqb j i0) eqn:I0; 
    intros; try assumption; try discriminate H1;
    (* both BTV *)
    try apply Nat.eqb_eq in I; try apply Nat.eqb_eq in I0;
    try subst i; try subst i0; intuition;
    (* one BTV one FTV *)
    inversion H1; (apply H2 in H4) || (symmetry in H4; apply H2 in H4); contradiction.
  - (* FTFunc *)
    intros; destruct t2; simpl in H1; try destruct b; try destruct (Nat.eqb j i); 
    try discriminate H1; inversion H1; apply f_equal2; 
    simpl in H; apply not_elem_union_elim in H; destruct H;
    simpl in H0; apply not_elem_union_elim in H0; destruct H0;
    apply IHt1_1 with j || apply IHt1_2 with j; assumption.
  - (* FTPoly *)
    intros; destruct t2; simpl in H1; try destruct b; try destruct (Nat.eqb j i);
    try discriminate H1; inversion H1; f_equal;
    simpl in H; simpl in H0; apply IHt1 with (j+1); assumption.
  - (* FTList *)
    intros; destruct t2; simpl in H1; try destruct b; try destruct (Nat.eqb j i);
    try discriminate H1; inversion H1; apply f_equal; 
    apply IHt1 with j; assumption.
  Qed.
    
Lemma lem_unbindFT_equals : forall (a:vname) (t1:ftype) (t2:ftype),
    ~ Elem a (ffreeTV t1) -> ~ Elem a (ffreeTV t2) 
        -> unbindFT a t1 = unbindFT a t2 -> t1 = t2.
Proof. intros; apply lem_openFT_at_equals with 0 a; assumption. Qed.

(* -- LEMMA. If G |- s <: t, then if we erase the types then (erase s) == (erase t) *)
Lemma lem_erase_subtype : forall (g:env) (t1:type) (t2:type),
    Subtype g t1 t2 -> erase t1 = erase t2.
Proof. intros; induction H; simpl.
  - (* SBase *) reflexivity.
  - (* SFunc *) apply f_equal2; try (symmetry; apply IHSubtype).
    pose proof (fresh_not_elem nms);
    rewrite <- (lem_erase_unbind (fresh nms) t1);
    rewrite <- (lem_erase_unbind (fresh nms) t2); apply H1; apply H2.
  - (* SWitn *) rewrite IHSubtype; apply lem_erase_tsubBV.
  - (* SBind *) pose proof (fresh_not_elem nms);
    rewrite <- (lem_erase_unbind (fresh nms) t); apply H1; apply H2.
  - (* SPoly *) f_equal; pose proof (fresh_varFTs_not_elem nms g (erase t1) (erase t2));
    set (a := fresh_varFTs nms g (erase t1) (erase t2)) in H1; 
    destruct H1; destruct H2; destruct H3;
    apply lem_unbindFT_equals with a;
    try rewrite <- (lem_erase_unbind_tvT a t1);
    try rewrite <- (lem_erase_unbind_tvT a t2); try apply H0; assumption.
  - (* SList *) rewrite IHSubtype. reflexivity.
  Qed.

Lemma lem_eqlPred_ftyping : forall (g:env) (b:basic) (ps:preds) (e:expr) (y:vname),
    WFtype g (TRefn b ps) Base -> ~ in_env y g -> HasFtype (erase_env g) e (FTBasic b)
        -> HasFtype (FCons y (FTBasic b) (erase_env g)) 
                    (unbind y (eqlPred b ps e)) (FTBasic TBool).
Proof. intros. apply FTApp with (FTBasic b); 
  assert (0 =? 0 = true) as Z by auto; try rewrite Z;
  try apply FTApp with (FTBasic b);
  assert ( ftsubBV (erase (TRefn b PEmpty)) 
                   (FTFunc (FTBasic (BTV 0)) (FTFunc (FTBasic (BTV 0)) (FTBasic TBool)))
     = FTFunc (FTBasic b) (FTFunc (FTBasic b) (FTBasic TBool)) ) by reflexivity;
  try rewrite <- H2; try apply FTAppT with Base; try apply FTPrm;
  try apply FTVar; apply lem_ftyp_islc in H1 as H3;
  assert (open_at 0 y e = e) by (apply lem_open_at_lc_at with 0; assumption);
  fold open_at; try rewrite H4;
  assert (FCons y (FTBasic b) (erase_env g) = concatF (FCons y (FTBasic b) (erase_env g)) FEmpty)
    by reflexivity; try rewrite H5;
  try apply lem_erase_wftype in H as H'; simpl in H';
  try apply lem_weaken_wfft; try apply lem_weaken_ftyp;
  try apply intersect_empty_r; 
  unfold in_envF; try rewrite <- binds_erase_env;
  assert (WFtype g (TRefn b PEmpty) Base)
    by (inversion H; try subst ps; try subst b; try assumption);
  try apply lem_wftype_islct with g Base; try apply H6;
  try destruct b eqn:B; try apply subset_empty_l;
  try apply subset_sing_l; simpl; try rewrite <- tvbinds_erase_env;
  try apply lem_free_subset_binds in H6; destruct H6; simpl in H7;
  try apply subset_sing_l in H7; intuition.
  Qed.

Lemma lem_strengthen_ftyping : forall (g:fenv) (ps:preds) (rs:preds),
    PHasFtype g ps -> PHasFtype g rs -> PHasFtype g (strengthen ps rs).
Proof. intros g ps rs p_ps_bl p_rs_bl; induction p_ps_bl; simpl.
  - (* PFTEmp  *) apply p_rs_bl.
  - (* PFTCons *) apply PFTCons; 
      ( apply H || apply IHp_ps_bl; apply p_rs_bl). Qed.

Lemma lem_push_wf : forall (g:env) (t_a:type) (ps:preds) (nms:names),
    noExists t_a -> WFtype g t_a Base
        -> ( forall y:vname, ~ Elem y nms 
                 -> PHasFtype (FCons y (erase t_a) (erase_env g)) (unbindP y ps) )
        -> WFtype g (push ps t_a) Base.
Proof. intros g t_a; destruct t_a as [b rs|t_z t|t_z t|k' t|t rs] eqn:Hta;
  intros ps nms HnoEx p_g_ta mk_p_yg_ps_bl.
  - (* TRefn b rs *) destruct ps as [|p ps'] eqn:Hps.
    * (* PEmpty      *) simpl; apply p_g_ta.
    * (* PCons p ps' *) destruct rs as [|r rs'] eqn:Hrs.
      + (* PEmpty      *) simpl; rewrite lem_strengthen_empty; apply WFRefn with nms;
        try discriminate; intuition.
      + (* PCons r rs' *) unfold push; inversion p_g_ta;
        apply WFRefn with (union nms nms0);
        intros; try rewrite lem_unbindP_strengthen; 
        try apply H1; try (simpl; discriminate);
        try apply lem_strengthen_ftyping;
        apply mk_p_yg_ps_bl || apply H4; apply not_elem_union_elim in H5; intuition.
  - (* TFunc t_z t *) simpl; apply p_g_ta.
  - (* TExis t_z t *) simpl in HnoEx; try contradiction.
  - (* TPoly k' t  *) simpl; apply p_g_ta.
  - (* TList t ps *) inversion p_g_ta.
  Qed.

Lemma lem_selfify_wf : forall (g:env) (t:type) (k:kind) (e:expr),
    WFtype g t k  -> HasFtype (erase_env g) e (erase t)
                  -> WFtype g (self t e k) k. (* in LH this was induction on tsize *)
Proof. intros g t k e p_g_t; induction p_g_t; intros;
  assert (forall (b:basic) (ps:preds), 
            self (TRefn b ps) e Base = push (PCons (eqlPred b ps e) PEmpty) (TRefn b ps))
      as Hself by (intros; reflexivity); try rewrite Hself.
  - (* WFBase *) apply lem_push_wf with (binds g); simpl; intros;
    try apply PFTCons; fold open_at; try apply lem_eqlPred_ftyping; simpl in H0;
    try apply PFTEmp; try apply WFBase; intuition.
  - (* WFRefn *) apply lem_push_wf with (binds g); simpl; intros;
    try apply PFTCons; fold open_at; try apply lem_eqlPred_ftyping; simpl in H0;
    try apply PFTEmp; try apply WFRefn with nms; intuition.
  - (* WFVar *) destruct k; try rewrite Hself;
    try apply lem_push_wf with (binds g); simpl; intros;
    try apply PFTCons; fold open_at; try apply lem_eqlPred_ftyping; simpl in H0;
    try apply PFTEmp; try apply WFVar; intuition.
  - (* WFFunc *) simpl; apply WFFunc with k_x k nms; trivial.
  - (* WFExis *) destruct k; simpl; apply WFExis with k_x (union nms (binds g)); intros;
    try apply p_g_t; apply not_elem_union_elim in H2; destruct H2;
    try rewrite lem_unbindT_self; simpl in H0;
    try apply H0; simpl in H1; try rewrite lem_erase_unbind;
    assert (FCons y (erase t_x) (erase_env g) = concatF (FCons y (erase t_x) (erase_env g)) FEmpty)
      by reflexivity; try rewrite H4;
    try apply lem_weaken_ftyp; try apply intersect_empty_r;
    try apply lem_ftyp_islc with (erase_env g) (erase t);
    assert (self (unbindT y t) e Star = unbindT y t) by (destruct t; reflexivity);
    try rewrite H5 in H0; rewrite binds_erase_env in H3; intuition.
  - (* WFPoly *) simpl; apply WFPoly with k_t nms; trivial.
  - (* WFList *) simpl; apply WFList with k_t; apply p_g_t.
  - (* WFListR *) simpl; apply WFListR with nms; assumption.
  - (* WFKind *) apply WFKind; assert (self t e Star = t) by (destruct t; reflexivity);
    rewrite H0; apply p_g_t.
  Qed.

Lemma lem_wflist_wftype : forall (g:env) (t:type) (ps:preds) (k:kind),
  WFtype g (TList t ps) k -> WFtype g t Star.
Proof. intros; inversion H; try inversion H0; try destruct k_t;
  try apply H4; try (apply WFKind; apply H4); inversion H2;
  try contradiction; inversion H8; destruct k_t;
  try apply H10; apply WFKind; apply H10. Qed.

Lemma lem_wflist_len_zero : forall (g:env) (t:type) (ps:preds),
  isMono t -> noExists t -> WFtype g (TList t ps) Star 
      -> WFtype g (TList t (PCons (eq (Ic 0) (length t (BV 0))) ps)) Star.
Proof. intros. inversion H1; inversion H2; 
  apply WFListR with (union nms (binds g)) || apply WFListR with (binds g);
  try discriminate; apply lem_wflist_wftype in H1 as p_g_t;
  (* g |-w [t]{} : Star *) try apply WFList with Star; try apply p_g_t;
  intros; unfold unbindP; simpl; apply PFTCons;
  try apply PFTEmp; try apply H7;
  try apply not_elem_union_elim in H9; try destruct H9; try apply H9;
  (* y:[t],g |- length [t] y = 0 : bool  *) 
  apply FTApp with (FTBasic TInt);
  match goal with 
  | [ |- HasFtype _ _ (FTFunc _ _)] 
                      => apply FTApp with (FTBasic TInt)
  | [ |- HasFtype _ _ (FTBasic _)] 
                      => apply FTApp with (FTList (erase t))
  end;
  try apply FTPrm;
  apply lem_wftype_islct in p_g_t as Ht;
  try rewrite lem_unbindT_lct;
  assert (FTFunc (FTList (erase t)) (FTBasic TInt)
          = ftsubBV (erase t) (FTFunc (FTList (FTBasic (BTV 0))) (FTBasic TInt)))
    as Htype by (unfold ftsubBV; reflexivity);
  try rewrite Htype; try apply FTAppT with Star;
  pose proof (FTPrm (FCons y (FTList (erase t)) (erase_env g)) Length) as HLen;
  simpl in HLen; try apply HLen; simpl;
  try apply FTVar; try apply FTIC;
  assert (FCons y (FTList (erase t)) (erase_env g) 
          = concatF (FCons y (FTList (erase t)) (erase_env g)) FEmpty) 
        as Henv by reflexivity; try rewrite Henv;
  try apply lem_weaken_wfft; try apply lem_erase_wftype;
  (*destruct k; try apply H1; try apply WFKind;*) unfold in_envF;
  try rewrite <-   binds_erase_env;
  try rewrite <-  vbinds_erase_env;
  try rewrite <- tvbinds_erase_env;
  try apply subset_add_intro;
  apply lem_free_subset_binds in p_g_t as Hb; destruct Hb;
  simpl in H3; simpl in H4;
  try apply intersect_empty_r; simpl; auto.
Qed.

Lemma lem_wflist_len_succ : 
  forall (g:env) (y:vname) (t:type) (ps:preds),
    isMono t -> noExists t -> ~ (in_env y g)
      -> WFtype g (TList t ps) Star 
      -> WFtype (ECons y (TList t ps) g) 
            (TList t (PCons (eq (App (Prim Succ) (length t (FV y))) 
                                (length t (BV 0))) PEmpty)) Star.
Proof. intros. inversion H2; try (inversion H3; contradiction);
  try subst ps;
  try apply lem_wflist_wftype in H2 as p_t;  
  try apply lem_wftype_islct in p_t as Hlct;
  pose proof lem_open_at_lc_at as [_ [Hopt _]];
  try apply lem_free_subset_binds in p_t as Hsub;
  try destruct Hsub as [Hsub Hsub'];
  apply WFListR with (names_add y (union nms (binds g)))
    || apply WFListR with (names_add y (binds g));
  try discriminate; try apply lem_weaken_wf_top; try assumption;
  intros; unfold unbindP; simpl; apply PFTCons;
  try apply PFTEmp;
  try (apply not_elem_names_add_elim in H4; destruct H4 as [Hy Hy0]);
  try (apply not_elem_names_add_elim in H6; destruct H6 as [Hy Hy0g]);
  try (apply not_elem_union_elim in Hy0; destruct Hy0 as [Hy0n Hy0g]);
  try rewrite Hopt with t 0 0 y0;
  try apply FTApp with (FTBasic TInt);
  try match goal with 
  | [ |- HasFtype _ _ (FTFunc _ _)] 
                      => apply FTApp with (FTBasic TInt)
  | [ |- HasFtype _ _ (FTBasic _)] 
                      => apply FTApp with (FTList (erase t))
  end;
  try apply FTApp with (FTBasic TInt);
  try apply FTApp with (FTList (erase t));
  assert (FTFunc (FTList (erase t)) (FTBasic TInt)
      = ftsubBV (erase t) (FTFunc (FTList (FTBasic (BTV 0))) (FTBasic TInt)))
      as Hert by reflexivity; try rewrite Hert;
  try apply FTAppT with Star;
  try apply FTPrm; try apply FTVar;
  try repeat apply lem_weaken_wfft_top;
  try apply lem_erase_wftype;

  unfold in_envF;
  unfold tvbindsF; fold tvbindsF;   
  unfold bindsF; fold bindsF;
  unfold in_envF; unfold bound_inF;
  try apply subset_add_intro; try apply subset_add_intro;
  try rewrite <-   binds_erase_env;
  try rewrite <-  vbinds_erase_env;
  try rewrite <- tvbinds_erase_env;
  try apply not_elem_names_add_intro; try split;
  try apply not_elem_names_add_intro; auto. 
Qed.

Lemma boundin_wfenv_wftype : forall (x:vname) (t:type) (g:env),
  bound_in x t g -> WFEnv g -> WFtype g t Star.
Proof. intros x t g H p_wf_g; induction p_wf_g. simpl in H.
  - contradiction.
  - simpl in H; destruct H; apply lem_weaken_wf_top;
    try (destruct H; subst t0; destruct k; (apply H1 || apply WFKind; apply H1));
    try apply IHp_wf_g; intuition.
  - simpl in H; apply lem_weaken_tv_wf_top; intuition.
  Qed.

Lemma lem_narrow_wf' : forall (g'xg : env) (t : type) (k : kind),
    WFtype g'xg t k -> forall (g g' : env) (x : vname) (s_x:type) (t_x:type),
        g'xg = concatE (ECons x t_x g) g' 
                    -> unique g -> unique g'
                    -> intersect (binds g) (binds g') = empty
                    -> ~ (in_env x g) -> ~ (in_env x g') 
                    -> Subtype g s_x t_x
                    -> WFtype (concatE (ECons x s_x g) g') t k.
Proof. apply ( WFtype_ind
  (fun (g'xg : env) (t : type) (k : kind) =>
    forall (g g' : env) (x : vname) (s_x:type) (t_x:type),
        g'xg = concatE (ECons x t_x g) g' 
                    -> unique g -> unique g'
                    -> intersect (binds g) (binds g') = empty
                    -> ~ (in_env x g) -> ~ (in_env x g') 
                    -> Subtype g s_x t_x
                    -> WFtype (concatE (ECons x s_x g) g') t k) );
  intro env; intros; subst env.
  - (* WFBase *) apply WFBase; apply H.
  - (* WFRefn *) apply WFRefn with nms; try apply H0 with t_x; intros;
    rewrite lem_erase_concat in H2; simpl in H2;
    try rewrite lem_erase_concat; simpl; 
    apply lem_erase_subtype in H9 as Hsx; try rewrite Hsx; try apply H2; intuition.
  - (* WFVar *) apply WFVar. rewrite lem_tvboundin_concat in H; simpl in H;
    rewrite lem_tvboundin_concat; simpl; apply H.
  - (* WFFunc *) apply WFFunc with k_x k (names_add x (union nms (binds (concatE g g')))); 
    try apply H0 with t_x0; intros; trivial;
    assert (ECons y t_x (concatE (ECons x s_x g) g') = concatE (ECons x s_x g) (ECons y t_x g'))
      by reflexivity; rewrite H10;
    apply not_elem_names_add_elim in H3; destruct H3;
    apply not_elem_union_elim in H11; destruct H11;
    apply not_elem_concat_elim in H12; destruct H12;
    apply H2 with t_x0; unfold in_env; simpl;
    try apply not_elem_names_add_intro;
    try apply intersect_names_add_intro_r; intuition.
  - (* WFExis *) apply WFExis with k_x (names_add x (union nms (binds (concatE g g')))); 
    try apply H0 with t_x0; intros; trivial;
    assert (ECons y t_x (concatE (ECons x s_x g) g') = concatE (ECons x s_x g) (ECons y t_x g'))
      by reflexivity; rewrite H10;
    apply not_elem_names_add_elim in H3; destruct H3;
    apply not_elem_union_elim in H11; destruct H11;
    apply not_elem_concat_elim in H12; destruct H12;
    apply H2 with t_x0; unfold in_env; simpl;
    try apply not_elem_names_add_intro;
    try apply intersect_names_add_intro_r; intuition.
  - (* WFPoly *) apply WFPoly with k_t (names_add x (union nms (binds (concatE g g'))));
    intros; apply not_elem_names_add_elim in H1; destruct H1;
    apply not_elem_union_elim in H8; destruct H8;
    apply not_elem_concat_elim in H9; destruct H9.
    assert (EConsT a' k (concatE (ECons x s_x g) g') = concatE (ECons x s_x g) (EConsT a' k g'))
      by reflexivity; rewrite H11;
    apply H0 with t_x; unfold in_env; simpl;
    try apply not_elem_names_add_intro;
    try apply intersect_names_add_intro_r; intuition.
  - (* WFList *) apply WFList with k_t; apply H0 with t_x; trivial.
  - (* WFListR *) apply WFListR with (names_add x (union nms (binds (concatE g g'))));
    try apply H0 with t_x; intros; try apply H2;
    rewrite lem_erase_concat in H2; simpl in H2;
    try rewrite lem_erase_concat; simpl;
    apply lem_erase_subtype in H9 as Hsx; try rewrite Hsx; try apply H2;
    try apply not_elem_names_add_elim in H3; try destruct H3;
    try apply not_elem_union_elim in H10; try destruct H10;
    try apply not_elem_concat_elim in H11; try destruct H11; trivial.
  - (* WFKind *) apply WFKind; apply H0 with t_x; trivial.
  Qed.

Lemma lem_narrow_wf : forall (g g':env) (x:vname) (s_x:type) (t_x:type) (t:type) (k:kind),
    WFtype (concatE (ECons x t_x g) g') t k 
                    -> unique g -> unique g'
                    -> intersect (binds g) (binds g') = empty
                    -> ~ (in_env x g) -> ~ (in_env x g') 
                    -> Subtype g s_x t_x
                    -> WFtype (concatE (ECons x s_x g) g') t k.
Proof. intros; apply lem_narrow_wf' with (concatE (ECons x t_x g) g') t_x; trivial. Qed.

Lemma lem_narrow_wf_top : forall (g:env) (x:vname) (s_x:type) (t_x:type) (t:type) (k:kind),
    WFtype (ECons x t_x g) t k -> unique g 
                              -> ~ (in_env x g) 
                              -> Subtype g s_x t_x
                              -> WFtype (ECons x s_x g) t k.
Proof. intros; assert (ECons x s_x g = concatE (ECons x s_x g) Empty) by reflexivity;
  rewrite H3; apply lem_narrow_wf with t_x; try apply intersect_empty_r;
  simpl; intuition. Qed.
  
Lemma lem_strengthen_wftype_base' : forall (g'xg : env) (t : type) (k : kind),
    WFtype g'xg t k -> forall (g g' : env) (x : vname) (t_x:type),
        g'xg = concatE (ECons x t_x g) g' -> k = Base
                    -> unique g -> unique g'
                    -> intersect (binds g) (binds g') = empty
                    -> ~ (in_env x g) -> ~ (in_env x g') 
                    -> WFtype (concatE g g') t Star
                    -> WFtype (concatE g g') t Base.
Proof. apply ( WFtype_ind
  (fun (g'xg : env) (t : type) (k : kind) =>
    forall (g g' : env) (x : vname) (t_x:type),
        g'xg = concatE (ECons x t_x g) g' -> k = Base
                    -> unique g -> unique g'
                    -> intersect (binds g) (binds g') = empty
                    -> ~ (in_env x g) -> ~ (in_env x g') 
                    -> WFtype (concatE g g') t Star
                    -> WFtype (concatE g g') t Base) );    
  intro env; intros; subst env.
  - (* WFBase *) apply WFBase; apply H.
  - (* WFRefn *) inversion H10; try (subst ps; contradiction); apply H3.
  - (* WFVar *) subst k; inversion H7;
    apply lem_tvboundin_concat in H; simpl in H;
    rewrite <- lem_tvboundin_concat in H; apply WFVar; apply H.
  - (* WFFunc *) discriminate H4.
  - (* WFExis *) subst k; inversion H10; try apply H3;
    apply WFExis with k_x0 (names_add x (union (union nms nms0) (binds (concatE g g'))));
    try apply H12; intros;
    apply not_elem_names_add_elim in H15; destruct H15;
    apply not_elem_union_elim in H16; destruct H16;
    apply not_elem_union_elim in H16; destruct H16;
    apply not_elem_concat_elim in H17; destruct H17.
    assert (ECons y t_x (concatE g g') = concatE g (ECons y t_x g'))
      as H' by reflexivity; rewrite H';
    apply H2 with x t_x0; try apply H14; unfold in_env; simpl;
    try apply not_elem_names_add_intro;
    try apply intersect_names_add_intro_r; intuition.
  - (* WFPoly *) discriminate H2.
  - (* WFList *) discriminate.
  - (* WFListR *) discriminate.
  - (* WFKind *) apply H0 with x t_x; trivial.
  Qed.

Lemma lem_strengthen_wftype_base : forall (g g':env) (x:vname) (t_x:type) (t:type),
    WFtype (concatE (ECons x t_x g) g') t Base 
                    -> unique g -> unique g'
                    -> intersect (binds g) (binds g') = empty
                    -> ~ (in_env x g) -> ~ (in_env x g') 
                    -> WFtype (concatE g g') t Star
                    -> WFtype (concatE g g') t Base.
Proof. intros; apply lem_strengthen_wftype_base' with (concatE (ECons x t_x g) g') Base x t_x;
  trivial. Qed.                

Lemma lem_strengthen_tv_wftype_base' : forall (g'ag : env) (t : type) (k : kind),
    WFtype g'ag t k -> forall (g g' : env) (a : vname) (k_a : kind),
        g'ag = concatE (EConsT a k_a g) g' -> k = Base
                    -> unique g -> unique g'
                    -> intersect (binds g) (binds g') = empty
                    -> ~ (in_env a g) -> ~ (in_env a g') 
                    -> WFtype (concatE g g') t Star
                    -> WFtype (concatE g g') t Base.
Proof. apply ( WFtype_ind
  (fun (g'ag : env) (t : type) (k : kind) =>
    forall (g g' : env) (a : vname) (k_a : kind),
        g'ag = concatE (EConsT a k_a g) g' -> k = Base
                    -> unique g -> unique g'
                    -> intersect (binds g) (binds g') = empty
                    -> ~ (in_env a g) -> ~ (in_env a g') 
                    -> WFtype (concatE g g') t Star
                    -> WFtype (concatE g g') t Base) );    
  intro env; intros; subst env.
  - (* WFBase *) apply WFBase; apply H.
  - (* WFRefn *) inversion H10; try (subst ps; contradiction); apply H3.
  - (* WFVar *) subst k; inversion H7;  try apply H0;
    apply lem_tvboundin_concat in H; simpl in H;
    rewrite or_assoc in H; destruct H.
    * (* a = a0 => False *) destruct H; subst a0;
      apply lem_tvboundin_inenv in H8; apply tvbinds_subset in H8;
      apply lem_binds_concat in H8;
      apply set_union_elim in H8; destruct H8; contradiction.
    * (* a <> a0 *) rewrite <- lem_tvboundin_concat in H; apply WFVar; apply H.
  - (* WFFunc *) discriminate H4.
  - (* WFExis *) subst k; inversion H10; try apply H3;
    apply WFExis with k_x0 (names_add a (union (union nms nms0) (binds (concatE g g'))));
    try apply H12; intros;
    apply not_elem_names_add_elim in H15; destruct H15;
    apply not_elem_union_elim in H16; destruct H16;
    apply not_elem_union_elim in H16; destruct H16;
    apply not_elem_concat_elim in H17; destruct H17.
    assert (ECons y t_x (concatE g g') = concatE g (ECons y t_x g'))
      as H' by reflexivity; rewrite H';
    apply H2 with a k_a; try apply H14; unfold in_env; simpl;
    try apply not_elem_names_add_intro;
    try apply intersect_names_add_intro_r; intuition.
  - (* WFPoly *) discriminate H2.
  - (* WFList *) discriminate.
  - (* WFListR *) discriminate.
  - (* WFKind *) apply H0 with a k_a; trivial.
  Qed.

Lemma lem_strengthen_tv_wftype_base : forall (g g':env) (a:vname) (k_a:kind) (t:type),
    WFtype (concatE (EConsT a k_a g) g') t Base 
                    -> unique g -> unique g'
                    -> intersect (binds g) (binds g') = empty
                    -> ~ (in_env a g) -> ~ (in_env a g') 
                    -> WFtype (concatE g g') t Star
                    -> WFtype (concatE g g') t Base.
Proof. intros; apply lem_strengthen_tv_wftype_base' 
                  with (concatE (EConsT a k_a g) g') Base a k_a;
  trivial. Qed.     

Lemma lem_strengthen_many_wftype_base : forall (g g':env) (t:type),
    WFtype (concatE g g') t Base 
                    -> unique g -> unique g'
                    -> intersect (binds g) (binds g') = empty
                    -> WFtype g t Star
                    -> WFtype g t Base.
Proof. intros g g'; revert g; induction g'; intros; simpl in H; try assumption;
  simpl in H1; destruct H1;
  simpl in H2; apply intersect_names_add_elim_r in H2; destruct H2;
  apply IHg'; try assumption;
  assert (concatE g g' = concatE (concatE g g') Empty) by reflexivity;
  rewrite H6;
  try apply (lem_strengthen_wftype_base (concatE g g') Empty x t t0);
  try apply (lem_strengthen_tv_wftype_base (concatE g g') Empty a k t);
  simpl; try apply H; try apply lem_weaken_many_wf;
  try (apply intersect_empty_r);
  try (apply unique_concat);
  try (apply not_elem_concat_intro; assumption); simpl; intuition.
  Qed.