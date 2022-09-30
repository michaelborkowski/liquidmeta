Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.Typing.
Require Import SystemRF.LemmasWeakenWF.
Require Import SystemRF.LemmasWeakenWFTV.
Require Import SystemRF.LemmasWellFormedness.
Require Import SystemRF.LemmasTyping.
Require Import SystemRF.LemmasSubtyping.
Require Import SystemRF.LemmasWeakenTyp.
Require Import SystemRF.LemmasWeakenTypTV.
Require Import SystemRF.LemmasExactness. (* 320 *)

Lemma lem_narrow_typ' : ( forall (g'xg : env) (e : expr) (t : type),
    Hastype g'xg e t -> ( forall (g g':env) (x:vname) (s_x t_x:type) (k_sx k_tx:kind),
        g'xg = concatE (Cons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x -> WFEnv g
            -> Hastype (concatE (Cons x s_x g) g') e t )) /\ (
  forall (g'xg : env) (t : type) (t' : type),
    Subtype g'xg t t' -> ( forall (g g':env) (x:vname) (s_x t_x:type) (k_sx k_tx:kind),
      g'xg = concatE (Cons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x -> WFEnv g
            -> Subtype (concatE (Cons x s_x g) g') t t' )).
Proof. apply ( judgments_mutind 
  (fun (g'xg : env) (e : expr) (t : type) (p_e_t : Hastype g'xg e t) => 
    forall (g g':env) (x:vname) (s_x t_x:type) (k_sx k_tx:kind),
      g'xg = concatE (Cons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x -> WFEnv g
            -> Hastype (concatE (Cons x s_x g) g') e t )
  (fun (g'xg : env) (t : type) (t' : type) (p_t_t' : Subtype g'xg t t') => 
    forall (g g':env) (x:vname) (s_x t_x:type) (k_sx k_tx:kind),
      g'xg = concatE (Cons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x -> WFEnv g
            -> Subtype (concatE (Cons x s_x g) g') t t' ));
  intro env; intros; subst env.
  - (* TBC *) apply TBC.
  - (* TIC *) apply TIC.
  - (* TVar *) apply lem_boundin_concat in b; destruct b;
    try destruct H; try destruct H.
    * (* x = x0 *) subst x0; subst t; 
      apply TSub with (self s_x (FV x) k) k;
      try apply TVar; try (apply lem_boundin_concat; left);
      try apply lem_selfify_wf;
      try apply lem_weaken_many_wf;
      try apply lem_weaken_many_subtype;
      try apply lem_exact_subtype with k_sx;
      try (apply lem_weaken_wf_top; assumption);
      try apply lem_weaken_subtype_top; try apply WFEBind with k_sx;
      try rewrite lem_erase_concat;
      simpl; try rewrite lem_erase_subtype with g s_x t_x; try apply FTVar;
      try apply lem_boundinF_concatF;
      try apply intersect_names_add_intro_l; 
      unfold isLC; simpl; intuition;
      (* WFtype of s_x and t_x, possibly with other kinds *)
      apply lem_weaken_wf_top with g s_x k_sx x s_x in H5 as Hsx;
      apply lem_weaken_wf_top with g s_x k_sx x t_x in H5 as Hsx';
      apply lem_weaken_wf_top with g t_x k_tx x t_x in H6 as Htx; trivial;
      apply lem_narrow_wf_top with g x s_x t_x t_x k_tx in Htx as Htx'; trivial;
      destruct k eqn:K; destruct k_sx eqn:KSX; destruct k_tx eqn:KTX;
      try assumption; try (apply WFKind; assumption);
      (* k_sx = Star but k_tx = Base and k = Base *)
      try ( apply lem_sub_pullback_wftype with t_x;
            try apply lem_weaken_subtype_top; try apply WFEBind with Star; trivial; reflexivity  );
      (* k_tx = Star but k = Base *)
      try ( apply lem_narrow_wf_top with t_x;
            try apply lem_strengthen_many_wftype_base with g';
            try apply intersect_names_add_intro_l; simpl; intuition; reflexivity );
      (* k_sx = Star and k_tx = Star but k = Base *)
      try apply lem_sub_pullback_wftype with t_x;
      try apply lem_narrow_wf_top with t_x;
      try apply lem_strengthen_many_wftype_base with g'; 
      try apply lem_weaken_subtype_top; try apply WFEBind with Star; 
      try apply intersect_names_add_intro_l; simpl; intuition.
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
    assert (Cons y t_x (concatE (Cons x s_x g) g') = concatE (Cons x s_x g) (Cons y t_x g'))
      as Henv by reflexivity; rewrite Henv; 
    apply H with t_x0 k_sx k_tx; 
    try apply intersect_names_add_intro_r; 
    try apply not_elem_names_add_intro; simpl; intuition.
  - (* TApp *) apply TApp;
    apply H with t_x0 k_sx k_tx || apply H0 with t_x0 k_sx k_tx; trivial.
  - (* TAbsT *) apply TAbsT with (names_add x (union nms (binds (concatE g g')))); intros;
    apply not_elem_names_add_elim in H0; destruct H0;
    apply not_elem_union_elim in H10; destruct H10;
    apply not_elem_concat_elim in H11; destruct H11;
    assert (ConsT a' k (concatE (Cons x s_x g) g') = concatE (Cons x s_x g) (ConsT a' k g'))
      as Henv by reflexivity; rewrite Henv; 
    apply H with t_x k_sx k_tx;
    try apply intersect_names_add_intro_r; 
    try apply not_elem_names_add_intro; simpl; intuition.
  - (* TAppT *) apply TAppT with k; try apply H with t_x k_sx k_tx; 
    try apply lem_narrow_wf with t_x; trivial.
  - (* TLet *) apply TLet with t_x k (names_add x (union nms (binds (concatE g g'))));
    try apply lem_narrow_wf with t_x0; 
    try apply H with t_x0 k_sx k_tx; trivial; intros;
    apply not_elem_names_add_elim in H1; destruct H1;
    apply not_elem_union_elim in H11; destruct H11;
    apply not_elem_concat_elim in H12; destruct H12;
    assert (Cons y t_x (concatE (Cons x s_x g) g') = concatE (Cons x s_x g) (Cons y t_x g'))
      as Henv by reflexivity; rewrite Henv; 
    apply H0 with t_x0 k_sx k_tx; 
    try apply intersect_names_add_intro_r; 
    try apply not_elem_names_add_intro; simpl; intuition.
  - (* TAnn *) apply TAnn; try apply H with t_x k_sx k_tx; trivial.
  - (* TSub *) apply TSub with s k; try apply H with t_x k_sx k_tx;
    try apply H0 with t_x k_sx k_tx; 
    try apply lem_narrow_wf with t_x; trivial.
  - (* SBase *) try apply SBase with (names_add x (union nms (binds (concatE g g')))); 
    intros; assert (Cons y (TRefn b PEmpty) (concatE (Cons x s_x g) g') 
                      = concatE (Cons x s_x g) (Cons y (TRefn b PEmpty) g'))
      as Henv by reflexivity; rewrite Henv;
    apply not_elem_names_add_elim in H; destruct H;
    apply not_elem_union_elim in H9; destruct H9;
    apply not_elem_concat_elim in H10; destruct H10;
    apply INarrow with t_x; try apply i;
    try apply intersect_names_add_intro_r; try apply not_elem_names_add_intro;
    simpl; intuition.
  - (* SFunc *) apply SFunc with (names_add x (union nms (binds (concatE g g'))));
    try apply H with t_x k_sx k_tx; trivial; intros;
    apply not_elem_names_add_elim in H1; destruct H1;
    apply not_elem_union_elim in H11; destruct H11;
    apply not_elem_concat_elim in H12; destruct H12;
    assert (Cons y s2 (concatE (Cons x s_x g) g') = concatE (Cons x s_x g) (Cons y s2 g'))
      as Henv by reflexivity; rewrite Henv;
    apply H0 with t_x k_sx k_tx;
    try apply intersect_names_add_intro_r; 
    try apply not_elem_names_add_intro; simpl; intuition.
  - (* SWitn *) apply SWitn with v_x;
    try apply H with t_x0 k_sx k_tx;
    try apply H0 with t_x0 k_sx k_tx; trivial.
  - (* SBind *) apply SBind with (names_add x (union nms (binds (concatE g g'))));
    trivial; intros; apply not_elem_names_add_elim in H0; destruct H0;
    apply not_elem_union_elim in H10; destruct H10;
    apply not_elem_concat_elim in H11; destruct H11;
    assert (Cons y t_x (concatE (Cons x s_x g) g') = concatE (Cons x s_x g) (Cons y t_x g'))
      as Henv by reflexivity; rewrite Henv;
    apply H with t_x0 k_sx k_tx;
    try apply intersect_names_add_intro_r; 
    try apply not_elem_names_add_intro; simpl; intuition.
  - (* SPoly *) apply SPoly with (names_add x (union nms (binds (concatE g g'))));
    trivial; intros; apply not_elem_names_add_elim in H0; destruct H0;
    apply not_elem_union_elim in H10; destruct H10;
    apply not_elem_concat_elim in H11; destruct H11;
    assert (ConsT a k (concatE (Cons x s_x g) g') = concatE (Cons x s_x g) (ConsT a k g'))
      as Henv by reflexivity; rewrite Henv;
    apply H with t_x k_sx k_tx;
    try apply intersect_names_add_intro_r; 
    try apply not_elem_names_add_intro; simpl; intuition.
  Qed.

Lemma lem_narrow_typ : 
  forall (g g':env) (x:vname) (s_x t_x:type) (k_sx k_tx:kind) (e:expr) (t:type),
    Hastype (concatE (Cons x t_x g) g') e t
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x -> WFEnv g
            -> Hastype (concatE (Cons x s_x g) g') e t .
Proof. intros; pose proof lem_narrow_typ'; destruct H9 as [Htyp Hsub];
  apply Htyp with (concatE (Cons x t_x g) g') t_x k_sx k_tx; trivial. Qed.

Lemma lem_narrow_subtype :
  forall (g g':env) (x:vname) (s_x t_x:type) (k_sx k_tx:kind) (t : type) (t' : type),
    Subtype (concatE (Cons x t_x g) g') t t'
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x -> WFEnv g
            -> Subtype (concatE (Cons x s_x g) g') t t' .
Proof. intros; pose proof lem_narrow_typ'; destruct H9 as [Htyp Hsub];
  apply Hsub with (concatE (Cons x t_x g) g') t_x k_sx k_tx; trivial. Qed.

Lemma lem_narrow_typ_top : 
  forall (g:env) (x:vname) (s_x t_x:type) (k_sx k_tx:kind) (e:expr) (t:type),
    Hastype (Cons x t_x g) e t
            -> unique g -> ~ (in_env x g) 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x -> WFEnv g
            -> Hastype (Cons x s_x g) e t .
Proof. intros; assert (Cons x s_x g = concatE (Cons x s_x g) Empty) by reflexivity;
  rewrite H6; apply lem_narrow_typ with t_x k_sx k_tx; 
  try apply intersect_empty_r; simpl; intuition. Qed.

Lemma lem_narrow_subtype_top :
  forall (g:env) (x:vname) (s_x t_x:type) (k_sx k_tx:kind) (t : type) (t' : type),
    Subtype (Cons x t_x g) t t'
            -> unique g -> ~ (in_env x g) 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x -> WFEnv g
            -> Subtype (Cons x s_x g) t t' .
Proof. intros; assert (Cons x s_x g = concatE (Cons x s_x g) Empty) by reflexivity;
  rewrite H6; apply lem_narrow_subtype with t_x k_sx k_tx; 
  try apply intersect_empty_r; simpl; intuition. Qed.