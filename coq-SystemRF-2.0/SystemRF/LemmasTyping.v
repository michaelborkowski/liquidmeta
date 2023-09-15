Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.SystemFWellFormedness.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.BasicPropsWellFormedness.
Require Import SystemRF.Typing.
Require Import SystemRF.LemmasWeakenWF.
Require Import SystemRF.LemmasWeakenWFTV.
Require Import SystemRF.LemmasWellFormedness.
Require Import SystemRF.SubstitutionLemmaWFTV.
Require Import SystemRF.PrimitivesWFType.

Require Import ZArith.

Lemma lem_tsubFV_tybc : forall (x:vname) (v_x:expr) (b:bool),
    isValue v_x ->  tsubFV x v_x (tybc b) = tybc b.
Proof. intros; destruct b; unfold tybc; reflexivity. Qed.

Lemma lem_tsubFV_tyic : forall (x:vname) (v_x:expr) (n:Z),
    isValue v_x-> tsubFV x v_x (tyic n) = tyic n.
Proof. intros; unfold tyic; reflexivity. Qed.

Lemma lem_tsubFV_ty : forall (x:vname) (v_x:expr) (c:prim),
    isValue v_x -> tsubFV x v_x (ty c) = ty c.
Proof. intros; destruct c; reflexivity. Qed.

Lemma lem_tsubFTV_tybc : forall (a:vname) (t_a:type) (b:bool),
    noExists t_a -> tsubFTV a t_a (tybc b) = tybc b.
Proof. intros; destruct b; unfold tybc; reflexivity. Qed.

Lemma lem_tsubFTV_tyic : forall (a:vname) (t_a:type) (n:Z),
    noExists t_a -> tsubFTV a t_a (tyic n) = tyic n.
Proof. intros; unfold tyic; reflexivity. Qed.

Lemma lem_tsubFTV_ty : forall (a:vname) (t_a:type) (c:prim),
    noExists t_a -> tsubFTV a t_a (ty c) = ty c.
Proof. intros; destruct c; reflexivity. Qed.

(*------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------*)

Lemma lem_typing_wf : forall (g:env) (e:expr) (t:type),
    Hastype g e t -> WFEnv g -> WFtype g t Star.
Proof. intros g e t p_e_t; induction p_e_t; intro p_g.
  - (* TBC *) apply WFKind; apply lem_wf_tybc.
  - (* TIC *) apply WFKind; apply lem_wf_tyic.
  - (* TVar *) destruct k;
    apply lem_selfify_wf || (apply WFKind; apply lem_selfify_wf);
    apply H0 || apply FTVar; apply boundin_erase_env; apply H.
  - (* TPrm *) apply lem_wf_ty.
  - (* TAbs *) apply WFFunc with k_x Star (union nms (binds g));
    apply H || (intros; apply H1);
    apply not_elem_union_elim in H2; destruct H2;
    apply H2 || apply WFEBind with k_x; trivial.
  - (* TApp *) apply IHp_e_t1 in p_g as IH'; inversion IH'.
    * apply WFExis with k_x nms; try apply H2; intros; destruct k;
      apply H3 || (apply WFKind; apply H3); assumption.
    * inversion H.
  - (* TAbsT *) apply WFPoly with Star (union nms (binds g)); intros;
    apply H0; apply not_elem_union_elim in H1; destruct H1;
    try apply WFEBindT; trivial.
  - (* TAppT *) apply IHp_e_t in p_g as IH'; inversion IH'; try inversion H2.
    pose proof (fresh_var_not_elem nms g); set (a := fresh_var nms g) in H7; destruct H7;
    assert (g = concatE g (esubFTV a t Empty)) by reflexivity; rewrite H9.
    rewrite lem_tsubFTV_unbind_tvT with a t s; try apply lem_subst_tv_wf with k;
    destruct k_t; try apply H4; try (apply WFKind; apply H4);
    try apply wfenv_unique; try apply WFEEmpty;
    try apply intersect_empty_r; try apply lem_erase_env_wfenv;
    try apply (lem_free_bound_in_env g (TPoly k s) Star a IH'); intuition.
  - (* TLet *) destruct k; apply H || (apply WFKind; apply H).
  - (* TAnn *) apply IHp_e_t; apply p_g.
  - (* TIf  *) destruct k; apply H || (apply WFKind; apply H).
  - (* TSub *) destruct k; apply H || (apply WFKind; apply H).
  Qed.

Lemma lem_typing_hasftype : forall (g:env) (e:expr) (t:type),
    Hastype g e t -> WFEnv g -> HasFtype (erase_env g) e (erase t).
Proof. intros g e t p_e_t; induction p_e_t; intro p_g.
  - (* TBC *) apply FTBC.
  - (* TIC *) apply FTIC.
  - (* TVar *) rewrite lem_erase_self; apply FTVar; apply boundin_erase_env; apply H.
  - (* TPrm *) assert (erase_ty c = erase (ty c)) as Hty
        by (destruct c; simpl; reflexivity); rewrite <- Hty.
    apply FTPrm.
  - (* TAbs *) apply FTAbs with k_x (union nms (binds g)); fold erase;
    try apply lem_erase_wftype; try apply H; intros; 
    apply not_elem_union_elim in H2; destruct H2;
    simpl in H1; rewrite <- lem_erase_unbind with y t; apply H1;
    try apply WFEBind with k_x; trivial.
  - (* TApp *) apply FTApp with (erase t_x); simpl; simpl in IHp_e_t1; intuition.
  - (* TAbsT *) apply FTAbsT with (union nms (binds g)); intros; fold erase;
    apply not_elem_union_elim in H1; destruct H1; simpl in H0;
    rewrite <- lem_erase_unbind_tvT; apply H0; try apply WFEBindT; trivial.
  - (* TAppT *) rewrite lem_erase_tsubBTV; try apply FTAppT with k;
    simpl in IHp_e_t; try apply IHp_e_t;
    try rewrite <- vbinds_erase_env; try rewrite <- tvbinds_erase_env;
    try apply lem_free_subset_binds with k;
    try apply lem_wftype_islct with g k; try apply lem_erase_wftype; trivial.
  - (* TLet *) apply FTLet with (erase t_x) (union nms (binds g)); 
    try apply IHp_e_t; try apply p_g; intros;
    apply not_elem_union_elim in H2; destruct H2; simpl in H1; 
    rewrite <- lem_erase_unbind with y t; apply H1; apply lem_typing_wf in p_e_t;
    try apply WFEBind with Star; trivial.
  - (* TAnn *) apply FTAnn;
    try rewrite <- vbinds_erase_env; try rewrite <- tvbinds_erase_env;
    try apply lem_free_subset_binds with Star; try apply lem_wftype_islct with g Star;
    try apply lem_typing_wf with e; try apply IHp_e_t; trivial.
  - (* TIf  *) simpl in IHp_e_t; apply FTIf; try apply IHp_e_t; try apply p_g;
    simpl in H1; simpl in H3; 
    assert (erase_env g = concatF (erase_env g) FEmpty) by reflexivity;
    rewrite H4; pose proof (fresh_varE_not_elem nms g (If e0 e1 e2)); 
    set (y := fresh_varE nms g (If e0 e1 e2));
    apply lem_strengthen_hasftype with y (FTBasic TBool);
    try apply H1; try apply H3; unfold in_envF; 
    try apply WFEBind with Base;
    apply lem_typing_wf in p_e_t as Hps; 
    try rewrite <- binds_erase_env;
    destruct H5; destruct H6; destruct H7; simpl in H5;
    apply not_elem_union_elim in H5; destruct H5;
    apply not_elem_union_elim in H9; destruct H9;
    try apply intersect_empty_r; intuition; 
    assert ( forall b : bool, (self (TRefn TBool ps) (Bc b) Base) 
                = TRefn TBool (PCons (eqlPred TBool ps (Bc b)) ps))
      as Hself by reflexivity; rewrite <- Hself;
    apply lem_selfify_wf; simpl; try apply FTBC;
    try inversion Hps; apply H12.
  - (* TSub *) rewrite <- lem_erase_subtype with g s t; try apply IHp_e_t; trivial.
  Qed.

Lemma lem_fv_subset_binds : forall (g:env) (e:expr) (t:type),
    Hastype g e t -> WFEnv g -> Subset (fv e) (vbinds g) /\ Subset (ftv e) (tvbinds g).
Proof. intros; rewrite vbinds_erase_env; rewrite tvbinds_erase_env;
  apply lem_fv_subset_bindsF with (erase t); apply lem_typing_hasftype; assumption. Qed.

Lemma lem_typ_islc : forall (g:env) (e:expr) (t:type),
    Hastype g e t -> WFEnv g -> isLC e.
Proof. intros; apply lem_ftyp_islc with (erase_env g) (erase t); 
  apply lem_typing_hasftype; assumption. Qed.