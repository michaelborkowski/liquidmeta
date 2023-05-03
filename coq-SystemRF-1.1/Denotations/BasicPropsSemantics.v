Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.Strengthenings.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import Denotations.ClosingSubstitutions.
Require Import Denotations.Denotations.
Require Import Denotations.BasicPropsCSubst.

Lemma lemma_strengthen_semantics : forall (ps qs:preds),
    PEvalsTrue ps -> PEvalsTrue qs -> PEvalsTrue (strengthen ps qs).
Proof. induction ps; simpl; trivial; intros.
  apply PECons; inversion H; try apply IHps; assumption. Qed.

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
  try destruct b; simpl in H; injection H as H;
  rewrite H; try rewrite lem_csubst_lambda;
  try rewrite lem_csubst_bc; try rewrite lem_csubst_prim;
  try rewrite lem_csubst_bv; reflexivity. Qed.

Lemma lem_csubst_step : forall (th:csub) (p q:expr),
    Step p q -> Step (csubst th p) (csubst th q).
Proof. intros th p q H; induction H.
  - (* EPrim *) rewrite lem_csubst_app; rewrite lem_csubst_prim;
    rewrite lem_csubst_isCompat with c w th; 
    try rewrite lem_csubst_delta; try apply EPrim; assumption.
  - (* EApp1 *) repeat rewrite lem_csubst_app; apply EApp1;
    apply IHStep.
  - (* EApp2 *) repeat rewrite lem_csubst_app; apply EApp2;
    try apply lem_csubst_value; apply IHStep.

    | EPrim : forall (c:prim) (w : expr) (pf : isCompat c w), 
          isValue w -> Step (App (Prim c) w) (delta c w pf)
    | EApp1 : forall (e e' e1 : expr),
          Step e e' -> Step (App e e1) (App e' e1)
    | EApp2 : forall (e e' v : expr),
          isValue v -> Step e e' -> Step (App v e) (App v e')
    | EAppAbs : forall (e v : expr),
          isValue v -> Step (App (Lambda e) v) (subBV v e)
    | EPrimT : forall (c : prim) (t : type) (pf : isCompatT c t),
          noExists t -> Step (AppT (Prim c) t) (deltaT c t pf) 
    | EAppT : forall (e e' : expr) (t : type),
          noExists t -> Step e e' -> Step (AppT e t) (AppT e' t)
    | EAppTAbs : forall (k : kind) (e : expr) (t : type),
          noExists t -> Step (AppT (LambdaT k e) t) (subBTV t e)
    | ELet  : forall (e_x e_x' e : expr),
          Step e_x e_x' -> Step (Let e_x e) (Let e_x' e)
    | ELetV : forall (v : expr) (e : expr), 
          isValue v -> Step (Let v e) (subBV v e)
    | EAnn  : forall (e e' : expr) (t : type),
          Step e e' -> Step (Annot e t) (Annot e' t)
    | EAnnV : forall (v : expr) (t : type),
          isValue v -> Step (Annot v t) v
    | EIf : forall (e0 e0' e1 e2 : expr),
          Step e0 e0' -> Step (If e0 e1 e2) (If e0' e1 e2)
    | EIfT : forall (e1 e2 : expr), Step (If (Bc true ) e1 e2) e1    
    | EIfF : forall (e1 e2 : expr), Step (If (Bc false) e1 e2) e2 .