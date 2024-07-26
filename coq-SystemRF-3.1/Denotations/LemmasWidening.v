Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.Strengthenings.
Require Import SystemRF.LocalClosure.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.BasicPropsWellFormedness.
Require Import SystemRF.Typing.
Require Import SystemRF.LemmasWellFormedness.
Require Import SystemRF.LemmasTransitive.
Require Import Denotations.ClosingSubstitutions.
Require Import Denotations.Denotations.
Require Import Denotations.PrimitivesSemantics.
Require Import Denotations.BasicPropsCSubst.

Require Import Arith.
Require Import Lists.ListSet.

Lemma lem_widen_denotes : 
  forall (g g':env) (x:vname) (s_x t_x:type) (th:csub),
    unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> ~ (in_env x g) -> ~ (in_env x g') 
        -> (forall (v:expr) (th0:csub), isValue v -> DenotesEnv g th0
              -> Denotes (ctsubst th0 s_x) v -> Denotes (ctsubst th0 t_x) v)
        -> DenotesEnv (concatE (ECons x s_x g) g') th 
        -> DenotesEnv (concatE (ECons x t_x g) g') th.
Proof. intro g; induction g'; intros; simpl.
  - simpl in H5; inversion H5; apply DExt; try apply H4; 
    try apply lem_den_isvalue with (ctsubst th0 s_x); trivial.
  - simpl in H5; inversion H5; subst x1 t0 g0.
    apply DExt;  try apply IHg' with s_x;
    simpl in H0; destruct H0; 
    simpl in H1; apply intersect_names_add_elim_r in H1;
    destruct H1;
    unfold in_env in H3; simpl in H3; 
    apply not_elem_names_add_elim in H3; destruct H3;
    try apply not_elem_concat_intro; simpl; 
    try apply not_elem_names_add_intro; auto.
  - simpl in H5; inversion H5; subst a0 k0 g0;
    apply DExtT; try apply IHg' with s_x;
    simpl in H0; destruct H0; 
    simpl in H1; apply intersect_names_add_elim_r in H1;
    destruct H1;
    unfold in_env in H3; simpl in H3; 
    apply not_elem_names_add_elim in H3; destruct H3;
    try apply not_elem_concat_intro; simpl; 
    try apply not_elem_names_add_intro; auto.
  Qed.
  
Lemma lem_widen_wf' : forall (g'xg : env) (t : type) (k : kind),
    WFtype g'xg t k -> forall (g g' : env) (x : vname) (s_x:type) (t_x:type),
        g'xg = concatE (ECons x s_x g) g' 
                    -> unique g -> unique g'
                    -> intersect (binds g) (binds g') = empty
                    -> ~ (in_env x g) -> ~ (in_env x g') 
                    -> Subtype g s_x t_x
                    -> WFtype (concatE (ECons x t_x g) g') t k.
Proof. apply ( WFtype_ind
  (fun (g'xg : env) (t : type) (k : kind) =>
    forall (g g' : env) (x : vname) (s_x:type) (t_x:type),
        g'xg = concatE (ECons x s_x g) g' 
                    -> unique g -> unique g'
                    -> intersect (binds g) (binds g') = empty
                    -> ~ (in_env x g) -> ~ (in_env x g') 
                    -> Subtype g s_x t_x
                    -> WFtype (concatE (ECons x t_x g) g') t k) );
  intro env; intros; subst env.
  - (* WFBase *) apply WFBase; apply H.
  - (* WFRefn *) apply WFRefn with nms; try apply H0 with s_x; intros;
    rewrite lem_erase_concat in H2; simpl in H2;
    try rewrite lem_erase_concat; simpl;
    apply lem_erase_subtype in H9 as Hsx; try rewrite <- Hsx; try apply H2; intuition.
  - (* WFVar *) apply WFVar. rewrite lem_tvboundin_concat in H; simpl in H;
    rewrite lem_tvboundin_concat; simpl; apply H.
  - (* WFFunc *) apply WFFunc with k_x k (names_add x (union nms (binds (concatE g g')))); 
    try apply H0 with s_x; intros; trivial.
    assert (ECons y t_x (concatE (ECons x t_x0 g) g') = concatE (ECons x t_x0 g) (ECons y t_x g'))
      by reflexivity; rewrite H10;
    apply not_elem_names_add_elim in H3; destruct H3;
    apply not_elem_union_elim in H11; destruct H11;
    apply not_elem_concat_elim in H12; destruct H12;
    apply H2 with s_x; unfold in_env; simpl;
    try apply not_elem_names_add_intro;
    try apply intersect_names_add_intro_r; intuition.
  - (* WFExis *) apply WFExis with k_x (names_add x (union nms (binds (concatE g g')))); 
    try apply H0 with s_x; intros; trivial;
    assert (ECons y t_x (concatE (ECons x t_x0 g) g') = concatE (ECons x t_x0 g) (ECons y t_x g'))
      by reflexivity; rewrite H10;
    apply not_elem_names_add_elim in H3; destruct H3;
    apply not_elem_union_elim in H11; destruct H11;
    apply not_elem_concat_elim in H12; destruct H12;
    apply H2 with s_x; unfold in_env; simpl;
    try apply not_elem_names_add_intro;
    try apply intersect_names_add_intro_r; intuition.
  - (* WFPoly *) apply WFPoly with k_t (names_add x (union nms (binds (concatE g g'))));
    intros; apply not_elem_names_add_elim in H1; destruct H1;
    apply not_elem_union_elim in H8; destruct H8;
    apply not_elem_concat_elim in H9; destruct H9.
    assert (EConsT a' k (concatE (ECons x t_x g) g') = concatE (ECons x t_x g) (EConsT a' k g'))
      by reflexivity; rewrite H11;
    apply H0 with s_x; unfold in_env; simpl;
    try apply not_elem_names_add_intro;
    try apply intersect_names_add_intro_r; intuition.
  - (* WFList *) apply WFList with k_t; apply H0 with s_x; trivial.
  - (* WFListR *) apply WFListR with (names_add x (union nms (binds (concatE g g')))); 
    try apply H0 with s_x; intros; trivial;
    apply not_elem_names_add_elim in H3; destruct H3;
    apply not_elem_union_elim in H10; destruct H10;
    apply not_elem_concat_elim in H11; destruct H11;
    rewrite lem_erase_concat; rewrite lem_erase_concat in H2;
    simpl in *; apply lem_erase_subtype in H9; rewrite <- H9;
    apply H2; trivial. 
  - (* WFKind *) apply WFKind; apply H0 with s_x; trivial.
  Qed.

Lemma lem_widen_wf : forall (g g':env) (x:vname) (s_x t_x:type) (t:type) (k:kind),
    WFtype (concatE (ECons x s_x g) g') t k 
                    -> unique g -> unique g'
                    -> intersect (binds g) (binds g') = empty
                    -> ~ (in_env x g) -> ~ (in_env x g') 
                    -> Subtype g s_x t_x
                    -> WFtype (concatE (ECons x t_x g) g') t k.
Proof. intros; apply lem_widen_wf' with (concatE (ECons x s_x g) g') s_x; trivial. Qed.

Lemma lem_widen_wf_top : forall (g:env) (x:vname) (s_x t_x:type) (t:type) (k:kind),
    WFtype (ECons x s_x g) t k 
                    -> unique g -> ~ (in_env x g) 
                    -> Subtype g s_x t_x
                    -> WFtype (ECons x t_x g) t k.
Proof. intros; assert (ECons x t_x g = concatE (ECons x t_x g) Empty) by reflexivity;
  rewrite H3; apply lem_widen_wf with s_x; 
  try apply intersect_empty_r; simpl; intuition. Qed.
  
Lemma lem_widen_wfenv : forall (g g':env) (x:vname) (s_x t_x:type) (k_x:kind),
    WFtype g t_x k_x -> Subtype g s_x t_x 
        -> WFEnv (concatE (ECons x s_x g) g') 
        -> WFEnv (concatE (ECons x t_x g) g').
Proof. intro g; induction g'; simpl; intros.
  - (* Empty *) inversion H1; apply WFEBind with k_x; trivial.
  - (* ECons  *) inversion H1; apply WFEBind with k;
    try apply IHg' with s_x k_x;
    unfold in_env; unfold in_env in H6;
    pose proof (lem_binds_concat (ECons x0 t_x g) g');
    pose proof (lem_binds_concat (ECons x0 s_x g) g');
    destruct H8 as [H8 _]; destruct H9 as [_ H9];
    assert (binds (ECons x0 t_x g) = binds (ECons x0 s_x g))
      by reflexivity;
    try apply not_elem_subset 
      with (union (binds (ECons x0 t_x g)) (binds g'));
    try rewrite H10; try apply not_elem_subset
      with (binds (concatE (ECons x0 s_x g) g'));
    try apply lem_widen_wf with s_x;
    apply wfenv_unique in H1 as H'; simpl in H';
    destruct H' as [_ H'];
    apply concat_unique in H'; simpl in H';
    repeat destruct H'; destruct H11; destruct H12;
    apply intersect_names_add_elim_l in H14;
    destruct H14; trivial.
  - (* EConsT *) inversion H1; apply WFEBindT;
    try apply IHg' with s_x k_x;
    unfold in_env; unfold in_env in H6;
    pose proof (lem_binds_concat (ECons x t_x g) g');
    pose proof (lem_binds_concat (ECons x s_x g) g');
    destruct H7 as [H7 _]; destruct H8 as [_ H8];
    assert (binds (ECons x t_x g) = binds (ECons x s_x g))
      by reflexivity;
    try apply not_elem_subset 
      with (union (binds (ECons x t_x g)) (binds g'));
    try rewrite H10; try apply not_elem_subset
      with (binds (concatE (ECons x s_x g) g'));
    trivial.
  Qed.
