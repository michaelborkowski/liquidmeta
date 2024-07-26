Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.LocalClosure.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.BasicPropsWellFormedness.
Require Import SystemRF.SystemFLemmasWeaken.
Require Import SystemRF.Typing.
Require Import SystemRF.PrimitivesWFType.
Require Import SystemRF.LemmasWeakenWF.
Require Import SystemRF.LemmasWellFormedness.
Require Import SystemRF.SubstitutionLemmaWF.
Require Import SystemRF.LemmasTyping.
Require Import SystemRF.LemmasSubtyping. 

Require Import Arith.

(* New stuff used in TAppT case of lem_exact_type due to our
    declaring (Length [t]) a value *)
 
Fixpoint isExFunc (t : type) : Prop  :=
  match t with 
  | (TFunc   _ _) => True
  | (TExists _ t) => isExFunc t 
  | _             => False
  end.

Lemma lem_openT_at_isExFunc_elim : forall (t : type) (j:index) (y : vname) ,
    isExFunc (openT_at j y t) -> isExFunc t.
Proof. induction t; intros; try contradiction; simpl;
  simpl in H; try apply IHt2 with (j+1) y; apply H. Qed.

Lemma lem_openT_at_isExFunc_intro : forall (t : type) (j:index) (y : vname) ,
    isExFunc t -> isExFunc (openT_at j y t).
Proof. induction t; intros; try contradiction; simpl;
  simpl in H; try apply IHt2; apply H. Qed.

Lemma lem_open_tvT_at_isExFunc_elim : forall (t : type) (j:index) (a : vname) ,
    isExFunc (open_tvT_at j a t) -> isExFunc t.
Proof. induction t; intros; simpl in H; try contradiction; 
  simpl; try apply IHt2 with j a; try apply H. 
  destruct b; try destruct (j =? i); simpl in H; try contradiction.
  Qed.

Lemma lem_open_tvT_at_isExFunc_intro : forall (t :type) (j:index) (a : vname) ,
    isExFunc t -> isExFunc (open_tvT_at j a t).
Proof. induction t; intros; try contradiction; simpl;
  simpl in H; try apply IHt2; apply H. Qed.

Lemma lem_tsubBV_at_isExFunc_elim : forall (t : type) (j:index) (v_x : expr),
    isExFunc (tsubBV_at j v_x t) -> isExFunc t.
Proof. induction t; intros; try contradiction; simpl; 
  simpl in H; try apply IHt2 with (j+1) v_x; apply H. Qed.  

Lemma lem_tsubBV_at_isExFunc_intro : forall (t : type) (j:index) (v_x : expr),
    isExFunc t -> isExFunc (tsubBV_at j v_x t).
Proof. induction t; intros; try contradiction; simpl; 
  simpl in H; try apply IHt2; apply H. Qed.  

Lemma lem_sub_isExFunc : forall (g:env) (s t:type),
    Subtype g s t -> isExFunc s -> isExFunc t.
Proof. intros g s t H; induction H; try contradiction; simpl; intros.
  - apply I.
  - apply lem_tsubBV_at_isExFunc_elim with 0 v_x; apply IHSubtype; apply H2.
  - set (y := fresh nms). pose proof (fresh_not_elem nms).
    apply H1 with y; try apply lem_openT_at_isExFunc_intro; trivial.
  Qed.

Lemma lem_tsubBTV_at_isExFunc_intro : forall (s : type) (j:index) (t:type),
    isExFunc s -> isExFunc (tsubBTV_at j t s).
Proof. induction s; intros; try contradiction; simpl; simpl in H;
  try apply IHs2; apply H. Qed.

Lemma lem_self_isExFunc : forall (t : type) (e : expr) (k : kind),
    isExFunc t -> self t e k = t.
Proof. induction t; intros; try contradiction; destruct k;
  try reflexivity; simpl; simpl in H;
  apply f_equal; apply IHt2; apply H. Qed.

Fixpoint isExPolyExFunc (s : type) : Prop  :=
  match s with 
  | (TPoly   _ t) => isExFunc t
  | (TExists _ t) => isExPolyExFunc t 
  | _             => False
  end.

Lemma lem_openT_at_isExPolyExFunc_elim : forall (t : type) (j:index) (y : vname) ,
    isExPolyExFunc (openT_at j y t) -> isExPolyExFunc t.
Proof. induction t; intros; try contradiction; simpl;
  simpl in H; apply IHt2 in H || apply lem_openT_at_isExFunc_elim in H; 
  apply H. Qed.

Lemma lem_openT_at_isExPolyExFunc_intro : forall (t : type) (j:index) (y : vname) ,
    isExPolyExFunc t -> isExPolyExFunc (openT_at j y t).
Proof. induction t; intros; try contradiction; simpl;
  simpl in H; apply IHt2 || apply lem_openT_at_isExFunc_intro; apply H. Qed.

Lemma lem_tsubBV_at_isExPolyExFunc : forall (t : type) (j:index) (v_x : expr),
    isExPolyExFunc (tsubBV_at j v_x t) -> isExPolyExFunc t.
Proof. induction t; intros; try contradiction; simpl; 
  simpl in H; apply IHt2 in H || apply lem_tsubBV_at_isExFunc_elim in H;
  apply H. Qed.

Lemma lem_sub_isExPolyExFunc : forall (g:env) (s t:type),
    Subtype g s t -> isExPolyExFunc s -> isExPolyExFunc t.
Proof. intros g s t H; induction H; try contradiction; simpl; intros.
  - apply lem_tsubBV_at_isExPolyExFunc with 0 v_x;
    apply IHSubtype; apply H2.
  - set (y := fresh nms); pose proof (fresh_not_elem nms).
    apply H1 with y; try apply lem_openT_at_isExPolyExFunc_intro; trivial.
  - set (a := fresh nms); pose proof (fresh_not_elem nms).
    apply lem_open_tvT_at_isExFunc_elim with 0 a. 
    apply lem_sub_isExFunc with (EConsT a k g) (unbind_tvT a t1);
    try apply H; try apply lem_open_tvT_at_isExFunc_intro; trivial.
  Qed.

Lemma lem_length_polyExFunc : forall (g:env) (e:expr) (t:type),
    Hastype g e t -> e = Prim Length -> isExPolyExFunc t.
Proof. intros g e t H; induction H; try discriminate; intros;
  try injection H as H; try subst c; simpl; trivial.
  apply lem_sub_isExPolyExFunc with g s;
  try apply IHHastype; assumption. Qed.


Lemma lem_self_idempotent_upper : forall (g:env) (t:type) (k:kind) (e:expr),
    WFtype g t k -> HasFtype (erase_env g) e (erase t)
                 -> Subtype g (self t e k) (self (self t e k) e k).
Proof. intros g t k e p_g_t; induction p_g_t; intros p_e_t; simpl.
  - (* WFBase *) apply SBase with (binds g); intros. apply IRepeat.
  - (* WFRefn *) apply SBase with (binds g); intros. apply IRepeat.
  - (* WFVar  *) destruct k; simpl.
    * (* Base *) apply SBase with (binds g); intros. apply IRepeat.
    * (* Star *) apply lem_sub_refl with Star; apply WFVar; assumption.
  - (* WFFunc *) apply lem_sub_refl with Star; apply WFFunc with k_x k nms;
    assumption.
  - (* WFExis *) destruct k; simpl.
    * (* Base *) apply lem_subtype_in_exists with k_x (union nms (bindsF (erase_env g)));
      assert (TExists t_x (self (self t e Base) e Base) 
                = self (self (TExists t_x t) e Base) e Base) as HTEx by reflexivity;
        try rewrite HTEx;
      try apply lem_wftype_islct with g Base; 
      try apply lem_selfify_wf; try apply lem_selfify_wf; try apply WFExis with k_x nms;
      simpl; simpl in p_e_t; try rewrite lem_erase_self; try assumption; intros;
      repeat rewrite lem_unbindT_self; try apply H0;
      try rewrite lem_erase_unbind;
      assert (erase_env (ECons y t_x g) = concatF (FCons y (erase t_x) (erase_env g)) FEmpty)
        as Henv by reflexivity; try rewrite Henv;
      try apply lem_weaken_ftyp; simpl;
      apply not_elem_union_elim in H1; destruct H1;
      try apply intersect_empty_r;
      try apply lem_ftyp_islc with (erase_env g) (erase t); intuition.
    * (* Star *) apply lem_sub_refl with Star; apply WFExis with k_x nms; assumption.
  - (* WFPoly *) apply lem_sub_refl with Star; apply WFPoly with k_t nms; assumption.
  - (* WFList *) apply lem_sub_refl with Star; apply WFList with k_t; assumption.
  - (* WFListR *) apply lem_sub_refl with Star; apply WFListR with nms; assumption.
  - (* WFKind *) assert (self t e Star = t) as Hself by (destruct t; reflexivity);
    repeat rewrite Hself; apply lem_sub_refl with Base; apply p_g_t.
  Qed.

Lemma lem_exact_subtype : forall (g:env) (s:type) (k_s:kind) (t:type) (k:kind) (e:expr),
    Subtype g s t -> WFEnv g -> WFtype g s k_s -> WFtype g t k -> isLC e 
                  -> HasFtype (erase_env g) e (erase t)
                  -> Subtype g (self s e k) (self t e k).
Proof. intros g s k_x t k e p_s_t; induction p_s_t; intros p_g p_g_s p_g_t He p_e_t.
  - (* SBase *) destruct k; simpl; apply SBase with (union nms (binds g)); intros;
    apply not_elem_union_elim in H0; destruct H0.
    * (* Base *) assert (unbindP y (PCons (eqlPred b p2 e) p2)
                          = strengthen (unbindP y (PCons (eqlPred b p2 e) PEmpty)) (unbindP y p2) )
          as Hp2' by reflexivity; rewrite Hp2';
      apply IConj; try apply ICons1. apply ITrans with (unbindP y p1); 
      try apply ICons2; intuition.
    * (* Star *) intuition.
  - (* SFunc *) destruct k; simpl; apply SFunc with nms; trivial.
  - (* SWitn *) assert (self (TExists t_x t') e k = TExists t_x (self t' e k))
        as Hex by (destruct k; destruct t'; reflexivity); rewrite Hex;
    apply SWitn with v_x; try rewrite lem_tsubBV_self; try apply IHp_s_t;
    inversion p_g_t; try inversion H1;
    pose proof (fresh_var_not_elem nms g) as Hy; 
      set (y := fresh_var nms g) in Hy; destruct Hy as [Hy Hy'];
    try rewrite lem_erase_tsubBV;
    try rewrite lem_tsubFV_unbindT with y v_x t'; try apply lem_subst_wf_top with t_x; 
    try apply H6; try (apply WFKind; apply H10); simpl in p_e_t;
    pose proof (lem_free_bound_in_env g (TExists t_x t') k y p_g_t Hy') 
      as Ht'; simpl in Ht'; destruct Ht' as [Ht' Ht''];
    apply not_elem_union_elim in Ht'; destruct Ht';
    try apply wfenv_unique; try (apply p_e_t || apply lem_typing_hasftype); trivial. 
  - (* SBind *) inversion p_g_s; try inversion H2; 
    assert (self (TExists t_x t) e k = TExists t_x (self t e k))
        as Hex by (destruct k; destruct t; reflexivity); rewrite Hex;
    apply SBind with (union (union nms nms0) (binds g)); 
    try apply lem_self_islct; try apply lem_wftype_islct with g k; trivial; intros y Hy;
    apply not_elem_union_elim in Hy; destruct Hy as [Hy Hy''];
    apply not_elem_union_elim in Hy; destruct Hy as [Hy Hy'];
    rewrite lem_unbindT_self; try apply H1; simpl;
    try apply WFEBind with k_x0; try apply H7; 
    try (destruct k_x; try apply H11; try (apply WFKind; apply H11));
    try apply lem_weaken_wf_top; try apply lem_weaken_ftyp_top;
    try apply lem_ftyp_islc with (erase_env g) (erase t');
    unfold in_envF; try rewrite <- binds_erase_env; trivial.
  - (* SPoly *) destruct k; simpl; apply SPoly with nms; trivial.
  - (* SList *) destruct k; simpl; apply SList with nms; trivial.
  Qed.

Lemma lem_exact_type : forall (g:env) (v:expr) (t:type) (k:kind),
    isValue v -> Hastype g v t -> WFtype g t k -> WFEnv g -> Hastype g v (self t v k).
Proof. intros g v t k Hv p_v_t; induction p_v_t; intros p_g_t p_g.
  - (* TBC *) apply TSub with (tybc b) Base; try apply TBC; destruct k;
    try apply lem_selfify_wf; try apply lem_wf_tybc; try apply lem_tybc_exact;
    assert (self (tybc b) (Bc b) Star = tybc b) by reflexivity; try rewrite H;
    simpl; try apply FTBC; apply lem_sub_refl with Star; apply p_g_t.
  - (* TIC *) apply TSub with (tyic m) Base; try apply TIC; destruct k;
    try apply lem_selfify_wf; try apply lem_wf_tyic; try apply lem_tyic_exact;
    assert (self (tyic m) (Ic m) Star = tyic m) by reflexivity; try rewrite H;
    simpl; try apply FTIC; apply lem_sub_refl with Star; apply p_g_t.
  - (* TVar *) destruct k0.
    * apply TSub with (self t (FV x) Base) Base; try apply TVar; destruct k;
      try rewrite lem_self_star; try apply p_g_t;
      try apply lem_selfify_wf; try rewrite lem_erase_self;
      try apply lem_self_idempotent_upper; 
      try apply FTVar; try apply boundin_erase_env;
      try apply lem_sub_refl with Star; trivial.
    * rewrite lem_self_star; apply TVar; rewrite lem_self_star in p_g_t; trivial.
  - (* TPrm *) destruct k; try rewrite lem_self_star; try apply TPrm;
    destruct c; unfold ty in p_g_t; inversion p_g_t. 
  - (* TAbs *) destruct k; try inversion p_g_t; try rewrite lem_self_star;
    apply TAbs with k_x nms; intuition.
  - (* TApp *) inversion Hv.
  - (* TAbsT *) destruct k; try inversion p_g_t; try rewrite lem_self_star;
    apply TAbsT with nms; trivial.
  - (* TAppT *) inversion Hv. 
    assert (isExPolyExFunc (TPoly k0 s))
      by (apply lem_length_polyExFunc with g e; try symmetry; assumption);
    simpl in H2.
    rewrite lem_self_isExFunc; try apply lem_tsubBTV_at_isExFunc_intro;
    try apply H2. apply TAppT with k0; subst e; assumption.
  - (* TLet *) inversion Hv. 
  - (* TAnn *) inversion Hv.
  - (* TIf *) inversion Hv.
  - (* TNil *) destruct k; simpl; apply TNil with k0; assumption.
  - (* TCons *) destruct k; simpl; apply TCons; assumption.
  - (* TSwitch *) inversion Hv.
  - (* TSub *) apply TSub with (self s e k) Star; try apply IHp_v_t;
    try apply lem_exact_subtype with k; try apply lem_typ_islc with g s;
    apply lem_typing_wf in p_v_t as p_g_s; trivial;
    destruct k; try apply lem_sub_pullback_wftype with t;
    try apply lem_selfify_wf; try (apply WFKind; apply lem_selfify_wf);
    try rewrite <- lem_erase_subtype with g s t; try apply lem_typing_hasftype; trivial. 
  Qed.