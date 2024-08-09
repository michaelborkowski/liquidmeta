Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.Strengthenings.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.PrimitivesFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import Denotations.ClosingSubstitutions.
Require Import Denotations.Denotations.
Require Import Denotations.BasicPropsCSubst.

Require Import ZArith.

Lemma lemma_strengthen_semantics : forall (ps qs:preds),
    PEvalsTrue ps -> PEvalsTrue qs -> PEvalsTrue (strengthen ps qs).
Proof. induction ps; simpl; trivial; intros.
  apply PECons; inversion H; try apply IHps; assumption. Qed.

Lemma lemma_semantics_strengthen : forall (ps qs:preds),
    PEvalsTrue (strengthen ps qs) -> PEvalsTrue ps /\ PEvalsTrue qs.
Proof. induction ps; simpl; intros; split;
  try apply PEEmp; try apply PECons; try apply H;
  inversion H; apply IHps in H3; destruct H3; assumption. Qed.  

  (* Lemma. If p ~> q then th(p) ~> th(q). *)

Lemma lem_csubst_isCompat : forall (c:prim) (w:expr) (th:csub),
    isCompat c w -> csubst th w = w.
Proof. intros; inversion H;
  try rewrite lem_csubst_bc; try rewrite lem_csubst_ic;
  reflexivity. Qed.

Lemma lem_csubst_delta : 
  forall (c:prim) (w:expr) (pf:isCompat c w) (th:csub),
    csubst th (delta c w pf) = delta c w pf.
Proof. intros; pose proof (delta_delta' c w pf);
  inversion pf; subst c; subst w; 
  try destruct b; unfold delta' in H; injection H as H;
  rewrite H; try rewrite lem_csubst_lambda;
  try rewrite lem_csubst_bc; try rewrite lem_csubst_ic; 
  try rewrite lem_csubst_prim;
  try rewrite lem_csubst_bv; try reflexivity. Qed.

Lemma lem_ctsubst_isCompatT : forall (c:prim) (t:type) (th:csub),
    isCompatT c t -> isCompatT c (ctsubst th t).
Proof. intros; inversion H.
  - apply isCptT_EqlB; apply lem_ctsubst_erase_basic; simpl; auto.
  - apply isCptT_EqlZ; apply lem_ctsubst_erase_basic; simpl; auto.
  - apply isCptT_LeqlB; apply lem_ctsubst_erase_basic; simpl; auto.
  - apply isCptT_LeqlZ; apply lem_ctsubst_erase_basic; simpl; auto.
  Qed.

Lemma lem_ctsubst_deltaT : 
  forall (th:csub) (c:prim) (t:type) (pf:isCompatT c t) (pf':isCompatT c (ctsubst th t)),
    csubst th (deltaT c t pf) = deltaT c (ctsubst th t) pf'.
Proof. intros; pose proof (deltaT_deltaT' c t pf);
  pose proof (deltaT_deltaT' c (ctsubst th t) pf');
  inversion pf; subst c; simpl in H; simpl in H0;
  apply (lem_ctsubst_erase_basic th) in H1 as H2; 
  rewrite H1 in H; try rewrite H2 in H0;
  injection H as H; try injection H0 as H0;
  try rewrite <- H; try rewrite <- H0;
  try rewrite lem_csubst_prim; simpl; try left; trivial. Qed.

Lemma lem_compatM_list : forall (c : prim) (v : expr),
    isCompatM c v -> isList v.
Proof. intros c v pf; induction pf; simpl; apply IHpf || exact I. Qed.

Lemma lem_csubst_isCompatM : forall (c:prim) (v:expr) (th:csub),
    isCompatM c v -> isCompatM c (csubst th v).
Proof. intro c; induction v; intros; inversion H;
  try rewrite lem_csubst_nil; try rewrite lem_csubst_cons;
  constructor; subst c; apply IHv2; apply H2. Qed.

Lemma lem_csubst_deltaM : 
  forall (th:csub) (c:prim) (v:expr) (pf:isCompatM c v) (pf':isCompatM c (csubst th v)),
    csubst th (deltaM c v pf) = deltaM c (csubst th v) pf'.
Proof. intros th c v; induction pf; intros; simpl in pf'; simpl.
  - assert (Some (csubst th (Ic 0)) = Some (deltaM Length (csubst th (Nil t)) pf'))
      by (rewrite deltaM_deltaM'; rewrite lem_csubst_ic;
          rewrite lem_csubst_nil; auto); injection H as H; trivial.
  - match goal with
    | [ |- ?lhs = ?rhs ] => assert (Some lhs = Some rhs)
        by (rewrite deltaM_deltaM'; rewrite lem_csubst_app; 
            rewrite lem_csubst_prim; rewrite lem_csubst_cons; simpl;
            rewrite lem_csubst_cons in pf'; inversion pf';
            rewrite <- deltaM_deltaM' with Length (csubst th es) H1;
            rewrite IHpf with H1; trivial)
    end.
    injection H as H; trivial.
  Qed.

Lemma lem_csubst_step : forall (th:csub) (p q:expr),
    loc_closed th -> substitutable th -> Step p q 
        -> Step (csubst th p) (csubst th q).
Proof. intros th p q Hlc Hth H; induction H.
  - (* EPrim *) rewrite lem_csubst_app; rewrite lem_csubst_prim;
    rewrite lem_csubst_isCompat with c w th; 
    try rewrite lem_csubst_delta; try apply EPrim; assumption.
  - (* EApp1 *) repeat rewrite lem_csubst_app; apply EApp1;
    apply IHStep.
  - (* EApp2 *) repeat rewrite lem_csubst_app; apply EApp2;
    try apply lem_csubst_value; try apply IHStep; assumption.
  - (* EAppAbs *) rewrite lem_csubst_app; rewrite lem_csubst_lambda;
    rewrite lem_csubst_subBV; try apply EAppAbs;
    try apply lem_csubst_value; assumption.
  - (* EPrimT *) rewrite lem_csubst_appT; rewrite lem_csubst_prim;
    apply lem_ctsubst_isCompatT with c t th in pf as pf';
    rewrite (lem_ctsubst_deltaT th c t pf pf'); apply EPrimT;
    apply lem_ctsubst_noExists; assumption.
  - (* EPrimM *) rewrite lem_csubst_app; rewrite lem_csubst_appT;
    rewrite lem_csubst_prim;
    apply lem_csubst_isCompatM with c w th in pf as pf';
    rewrite lem_csubst_deltaM with th c w pf pf'; apply EPrimM;
    apply lem_csubst_value; trivial.
  - (* EAppT *) repeat rewrite lem_csubst_appT; apply EAppT;
    try apply IHStep; apply lem_ctsubst_noExists; assumption.
  - (* EAppTAbs *) rewrite lem_csubst_appT; 
    rewrite lem_csubst_lambdaT; rewrite lem_csubst_subBTV;
    try apply EAppTAbs; try apply lem_ctsubst_noExists;
    assumption.
  - (* ELet *) repeat rewrite lem_csubst_let; apply ELet; apply IHStep.
  - (* ELetV *) rewrite lem_csubst_let; rewrite lem_csubst_subBV;
    try apply ELetV; try apply lem_csubst_value; assumption.
  - (* EAnn *) repeat rewrite lem_csubst_annot; apply EAnn; apply IHStep.
  - (* EAnnV *) rewrite lem_csubst_annot; apply EAnnV;
    apply lem_csubst_value; assumption. 
  - (* EIf *) repeat rewrite lem_csubst_if; apply EIf; apply IHStep.
  - (* EIfT *) rewrite lem_csubst_if; rewrite lem_csubst_bc; apply EIfT.
  - (* EIfF *) rewrite lem_csubst_if; rewrite lem_csubst_bc; apply EIfF.
  - (* ECons1 *) repeat rewrite lem_csubst_cons; apply ECons1; apply IHStep.
  - (* ECons2 *) repeat rewrite lem_csubst_cons; apply ECons2;
    try apply lem_csubst_value; trivial.
  - (* ESwitch *) repeat rewrite lem_csubst_switch; apply ESwitch; apply IHStep.
  - (* ESwitchN *) rewrite lem_csubst_switch; rewrite lem_csubst_nil;
    apply ESwitchN.
  - (* ESwitchC *) rewrite lem_csubst_switch; rewrite lem_csubst_cons;  
    repeat rewrite lem_csubst_app; apply ESwitchC; apply lem_csubst_value; trivial.
  Qed.

Lemma lem_csubst_evals : forall (th:csub) (p q:expr),
    loc_closed th -> substitutable th -> EvalsTo p q 
        -> EvalsTo (csubst th p) (csubst th q).
Proof. intros th p q H1 H2 Hpq; induction Hpq.
  - apply Refl.
  - apply AddStep with (csubst th e2); try apply lem_csubst_step;
    assumption. Qed.

Lemma lem_app_evals_val' : forall (e v:expr),
  EvalsTo e v -> (forall e1 e2, e = App e1 e2 -> isValue v -> 
    exists (v1 v2:expr), isValue v1 /\ isValue v2
                   /\ EvalsTo e1 v1 /\ EvalsTo e2 v2).
Proof. apply ( EvalsTo_ind 
  (fun (e v : expr) => forall (e1 e2 : expr),
      e = App e1 e2 -> isValue v -> 
          exists (v1 v2:expr), isValue v1 /\ isValue v2
                         /\ EvalsTo e1 v1 /\ EvalsTo e2 v2));
  [intros | intros e e' v st_ee' ev_e'v IH e1 e2]; intros.
  - (* Refl *) subst e; inversion H0.
  - (* AddStep *) subst e; inversion st_ee'.
    * (* EPrim *) exists e1, e2; repeat split; subst e1;
      try apply val_Prm; try apply Refl; trivial.
    * (* EApp1 *) symmetry in H1; apply IH in H1; try apply H0.
      destruct H1 as [v1 [v2 [val1 [val2 [ev_e'0_v1 ev_e2_v2]]]]];
      exists v1, v2; repeat split; try assumption;
      try apply AddStep with e'0;  trivial.
    * (* EApp2 *) exists e1; symmetry in H3; apply IH in H3;
      try apply H0; destruct H3 as [_ [v2 [_ [val2 [_ ev_e'0_v2]]]]].
      exists v2; repeat split; try apply Refl;
      try apply AddStep with e'0; trivial.
    * (* EAppAbs *) exists (Lambda e), e2; repeat split;
      try apply val_Lam; try apply Refl; trivial.
    * (* EPrimM *) exists e1, e2; repeat split; subst e1;
      try apply Refl; try apply H3; inversion pf; subst c;
      try apply val_Len.
  Qed.

Lemma lem_app_evals_val : forall (e1 e2 v:expr),
  EvalsTo (App e1 e2) v -> isValue v -> 
    exists (v1 v2:expr), isValue v1 /\ isValue v2
                   /\ EvalsTo e1 v1 /\ EvalsTo e2 v2.
Proof. intros; apply lem_app_evals_val' with (App e1 e2) v; trivial. Qed.

Lemma lem_appT_evals_val' : forall (e v:expr),
  EvalsTo e v -> (forall (e':expr) (t:type), 
    e = AppT e' t -> isValue v -> 
        exists (v':expr), isValue v' /\ EvalsTo e' v').
Proof. apply ( EvalsTo_ind 
  (fun (e v : expr) => forall (e' : expr) (t : type),
      e = AppT e' t -> isValue v -> 
        exists (v':expr), isValue v' /\ EvalsTo e' v'));
  [intros | intros e e1 v st_ee1 ev_e1v IH e' t]; intros.
  - (* Refl *) subst e; inversion H0;
    exists e'; split; subst e'; try apply Refl; apply val_Prm.
  - (* AddStep *) subst e; inversion st_ee1.
    * (* EPrimT *) exists e'; repeat split; subst e';
      try apply val_Prm; try apply Refl; trivial.
    * (* EAppT *) symmetry in H3; apply IH in H3; try apply H0.
      destruct H3 as [v' [val' ev_e'0_v']];
      exists v'; split; try assumption;
      try apply AddStep with e'0;  trivial.
    * (* EAppTAbs *) exists (LambdaT k e); split;
      try apply val_LamT; try apply Refl; trivial.
  Qed.

Lemma lem_appT_evals_val : forall (e' v:expr) (t : type),
  EvalsTo (AppT e' t) v -> isValue v -> 
    exists (v':expr), isValue v' /\ EvalsTo e' v'.
Proof. intros; apply lem_appT_evals_val' with (AppT e' t) v t; trivial. Qed.

Lemma lem_let_evals_val' : forall (e v:expr),
  EvalsTo e v -> (forall e1 e2, e = Let e1 e2 -> isValue v -> 
    exists (v1 : expr), isValue v1 
                   /\ EvalsTo e1 v1 /\ EvalsTo (subBV v1 e2) v).
Proof. apply ( EvalsTo_ind 
  (fun (e v : expr) => forall (e1 e2 : expr),
      e = Let e1 e2 -> isValue v -> 
          exists (v1 : expr), isValue v1 
                   /\ EvalsTo e1 v1 /\ EvalsTo (subBV v1 e2) v));
  [intros | intros e e' v st_ee' ev_e'v IH e1 e2]; intros.
  - (* Refl *) subst e; inversion H0.
  - (* AddStep *) subst e; inversion st_ee'.
    * (* ELet *) symmetry in H1; apply IH in H1; try apply H0.
      subst e_x e; destruct H1 as [v1 [val1 [ev_ex'_v1 ev_e2v1_v]]];
      exists v1; repeat split; try assumption;
      try apply AddStep with e_x';  trivial.
    * (* ELetV *) exists e1; repeat split; try assumption;
      try apply Refl; subst e'; trivial.
  Qed.

Lemma lem_let_evals_val : forall (e1 e2 v:expr),
  EvalsTo (Let e1 e2) v -> isValue v -> 
    exists (v1 : expr), isValue v1 
                   /\ EvalsTo e1 v1 /\ EvalsTo (subBV v1 e2) v.
Proof. intros; apply lem_let_evals_val' with (Let e1 e2); trivial. Qed.

Lemma lem_ann_evals_val' : forall (e v:expr),
  EvalsTo e v -> (forall (e':expr) (t:type), 
    e = Annot e' t -> isValue v -> 
        exists (v':expr), isValue v' /\ EvalsTo e' v').
Proof. apply ( EvalsTo_ind 
  (fun (e v : expr) => forall (e' : expr) (t : type),
      e = Annot e' t -> isValue v -> 
        exists (v':expr), isValue v' /\ EvalsTo e' v'));
  [intros | intros e e1 v st_ee1 ev_e1v IH e' t]; intros.
  - (* Refl *) subst e; inversion H0;
    exists e'; split; subst e'; try apply Refl; apply val_Prm.
  - (* AddStep *) subst e; inversion st_ee1.
    * (* EAnn *) symmetry in H1; apply IH in H1; try apply H0.
      destruct H1 as [v' [val' ev_e'0_v']];
      exists v'; split; try assumption;
      try apply AddStep with e'0;  trivial.
    * (* EAnnV *) exists e1; split; try apply Refl; trivial.
  Qed.

Lemma lem_ann_evals_val : forall (e' v:expr) (t : type),
  EvalsTo (Annot e' t) v -> isValue v -> 
    exists (v':expr), isValue v' /\ EvalsTo e' v'.
Proof. intros; apply lem_ann_evals_val' with (Annot e' t) v t; trivial. Qed.

Lemma lem_if_evals_val' : forall (e v:expr),
  EvalsTo e v -> (forall e0 e1 e2, e = If e0 e1 e2 -> isValue v -> 
    exists (v':expr), isValue v'
                /\ (   (EvalsTo e0 (Bc true)  /\ EvalsTo e1 v')
                    \/ (EvalsTo e0 (Bc false) /\ EvalsTo e2 v'))).
Proof. apply ( EvalsTo_ind 
  (fun (e v : expr) => forall (e0 e1 e2 : expr),
      e = If e0 e1 e2 -> isValue v -> 
        exists (v':expr), isValue v'
                /\ (   (EvalsTo e0 (Bc true)  /\ EvalsTo e1 v')
                    \/ (EvalsTo e0 (Bc false) /\ EvalsTo e2 v'))));
  [intros | intros e e' v st_ee' ev_e'v IH e0 e1 e2]; intros.
  - (* Refl *) subst e; inversion H0.
  - (* AddStep *) subst e; inversion st_ee'.
    * (* EIf *) symmetry in H1; apply IH in H1; try apply H0.
      destruct H1 as [v' [val' Hif]]; 
      destruct Hif as [[ev_e0_tt ev_e1_v'] | [ev_e0_ff ev_e2_v']].
      exists v'; split; try left; try split; try assumption;
      try apply AddStep with e0';  trivial.
      exists v'; split; try right; try split; try assumption;
      try apply AddStep with e0';  trivial.
    * (* EIfT *) subst e0 e'; exists v; split; 
      try left; try apply val_Bc; try split; try apply Refl; trivial.
    * (* EIfF *) subst e0 e'; exists v; split; 
      try right; try apply val_Bc; try split; try apply Refl; trivial.
Qed.
  
Lemma lem_if_evals_val : forall (e0 e1 e2 v:expr),
  EvalsTo (If e0 e1 e2) v -> isValue v -> 
    exists (v':expr), isValue v'
                /\ (   (EvalsTo e0 (Bc true)  /\ EvalsTo e1 v')
                    \/ (EvalsTo e0 (Bc false) /\ EvalsTo e2 v')).
Proof. intros; apply lem_if_evals_val' with (If e0 e1 e2) v; trivial. Qed.

Lemma lem_cons_evals_val' : forall (e v:expr),
  EvalsTo e v -> (forall t0 e1 e2, e = Cons t0 e1 e2 -> isValue v -> 
    exists (v1 v2:expr), isValue v1 /\ isValue v2
                   /\ EvalsTo e1 v1 /\ EvalsTo e2 v2).
Proof. apply ( EvalsTo_ind 
  (fun (e v : expr) => forall (t0:type) (e1 e2 : expr),
      e = Cons t0 e1 e2 -> isValue v -> 
          exists (v1 v2:expr), isValue v1 /\ isValue v2
                         /\ EvalsTo e1 v1 /\ EvalsTo e2 v2));
  [intros | intros e e' v st_ee' ev_e'v IH t0 e1 e2]; intros.
  - (* Refl *) subst e; inversion H0; exists e1, e2;
    repeat split; try apply Refl; trivial.
  - (* AddStep *) subst e; inversion st_ee'.
    * (* ECons1 *) symmetry in H1; apply IH in H1; try apply H0.
      destruct H1 as [v1 [v2 [val1 [val2 [ev_e'0_v1 ev_e2_v2]]]]];
      exists v1, v2; repeat split; try assumption;
      try apply AddStep with e'0;  trivial.
    * (* ECons2 *) exists e1; symmetry in H2; apply IH in H2;
      try apply H0; destruct H2 as [_ [v2 [_ [val2 [_ ev_e'0_v2]]]]].
      exists v2; repeat split; try apply Refl;
      try apply AddStep with e'0; trivial.
  Qed.

Lemma lem_cons_evals_val : forall (t0:type) (e1 e2 v:expr),
  EvalsTo (Cons t0 e1 e2) v -> isValue v -> 
    exists (v1 v2:expr), isValue v1 /\ isValue v2
                   /\ EvalsTo e1 v1 /\ EvalsTo e2 v2.
Proof. intros; apply lem_cons_evals_val' with (Cons t0 e1 e2) v t0; trivial. Qed.

Lemma lem_switch_evals_val' : forall (e v:expr),
  EvalsTo e v -> (forall e0 eN eC, e = Switch e0 eN eC -> isValue v -> 
    exists (v':expr), isValue v' 
       /\ (    (exists (t0:type), EvalsTo e0 (Nil t0) /\ EvalsTo eN v' )
            \/ (exists (t0:type) (v1 v2:expr), isValue v1 /\ isValue v2 
                        /\ EvalsTo e0 (Cons t0 v1 v2)
                        /\ EvalsTo (App (App eC v1) v2) v'))).
Proof. apply ( EvalsTo_ind 
  (fun (e v : expr) => forall e0 eN eC, 
    e = Switch e0 eN eC -> isValue v -> 
      exists (v':expr), isValue v' 
       /\ (    (exists (t0:type), EvalsTo e0 (Nil t0) /\ EvalsTo eN v' )
            \/ (exists (t0:type) (v1 v2:expr), isValue v1 /\ isValue v2 
                        /\ EvalsTo e0 (Cons t0 v1 v2)
                        /\ EvalsTo (App (App eC v1) v2) v'))));
  [intros | intros e e' v st_ee' ev_e'v IH e0 eN eC]; intros.
  - (* Refl *) subst e; inversion H0.
  - (* AddStep *) subst e; inversion st_ee'.
    * (* ESwitch *) symmetry in H1; apply IH in H1; try apply H0.
      destruct H1 as [v' [val' Hv']];
      destruct Hv' as [[t0 [ev_e0_nil ev_eN_v']] 
                     | [t0 [v1 [v2 [val1 [val2 [ev_e0_cn ev_eC_v']]]]]]];
      exists v'; split; try apply val'.
      left; exists t0; split; try assumption;
      apply AddStep with e'0;  trivial.
      right; exists t0, v1, v2; repeat split; try assumption;
      try apply AddStep with e'0;  trivial.
    * (* ESwitchN *) subst e0 e'; exists v; split; 
      try left; try exists t; try split; try apply Refl; trivial.
    * (* ESwitchC *) subst e0 e'; exists v; split; try right;
      try exists t, v1, v2; repeat split; try apply Refl; trivial.
Qed. 
  
Lemma lem_switch_evals_val : forall (e0 eN eC v:expr),
  EvalsTo (Switch e0 eN eC) v -> isValue v -> 
    exists (v':expr), isValue v' 
       /\ (    (exists (t0:type), EvalsTo e0 (Nil t0) /\ EvalsTo eN v' )
            \/ (exists (t0:type) (v1 v2:expr), isValue v1 /\ isValue v2 
                        /\ EvalsTo e0 (Cons t0 v1 v2)
                        /\ EvalsTo (App (App eC v1) v2) v')).
Proof. intros; apply lem_switch_evals_val' with (Switch e0 eN eC) v; 
  trivial. Qed.
