Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.PrimitivesFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.Typing.
Require Import Denotations.ClosingSubstitutions.
Require Import Denotations.Denotations.
Require Import Denotations.BasicPropsCSubst.
Require Import Denotations.BasicPropsPEvalsTrue.
(*Require Import Denotations.PrimitivesDenotations.*)

(* Reminder: Inductive DImplies : env -> preds -> preds -> Prop :=
    | DImp : forall (g:env) (ps qs : preds),
        (forall (th:csub), DenotesEnv g th -> PEvalsTrue (cpsubst th ps) 
                                           -> PEvalsTrue (cpsubst th qs) )
            -> DImplies g ps qs.  *)

Lemma lem_dimplies_refl : forall (g:env) (ps:preds), DImplies g ps ps.
Proof. intros; apply DImp; intros; apply H0. Qed.

Lemma lem_dimplies_trans : forall (g:env) (ps:preds) (qs:preds) (rs:preds),
    DImplies g ps qs -> DImplies g qs rs -> DImplies g ps rs.
Proof. intros g ps qs rs imp_ps_qs imp_qs_rs; 
  apply DImp; intros. inversion imp_ps_qs; inversion imp_qs_rs.
  apply H5; try apply H1; assumption. Qed.

Lemma lem_dimplies_faithful : forall (g:env) (ps:preds), DImplies g ps PEmpty.
Proof. intros; apply DImp; intros; 
  rewrite lem_cpsubst_pempty; apply PEEmp. Qed. 

Lemma lem_dimplies_strengthen : forall (g:env) (ps qs rs:preds),
    DImplies g ps qs -> DImplies g ps rs -> DImplies g ps (strengthen qs rs).
Proof. intros; apply DImp; intros; rewrite lem_cpsubst_strengthen;
  apply lemma_strengthen_semantics; 
  inversion H; inversion H0; apply H3 || apply H7; assumption. Qed.

Lemma lem_dimplies_cons_elim : forall (g:env) (p:expr) (ps:preds), 
    DImplies g (PCons p ps) (PCons p PEmpty) /\ DImplies g (PCons p ps) ps.
Proof. intros; split; apply DImp; intros; 
    rewrite lem_cpsubst_pcons in H0; try rewrite lem_cpsubst_pcons;
    inversion H0; try apply PECons; 
    try rewrite lem_cpsubst_pempty; try assumption; apply PEEmp. Qed.

Lemma lem_dimplies_repetition : forall (g:env) (p:expr) (ps:preds), 
    DImplies g (PCons p ps) (PCons p (PCons p ps)).
Proof. intros; apply DImp; intro th; 
  repeat rewrite lem_cpsubst_pcons; intros;
  repeat apply PECons; inversion H0; assumption. Qed.

Lemma lem_dimplies_evals : forall (g:env) (p p':expr) (ps:preds),
    EvalsTo p p' -> DImplies g (PCons p ps) (PCons p' ps)
                    /\ DImplies g (PCons p' ps) (PCons p ps).
Proof. intros; split; apply DImp; intro th;
  repeat rewrite lem_cpsubst_pcons; intros;
  inversion H1; apply PECons;
  
  try assumption. Focus 2. 


    | INarrow : forall (g:env) (g':env) (x:vname) (s_x:type) (t_x:type) (ps:preds) (qs:preds),
          intersect (binds g) (binds g') = empty -> unique g -> unique g'
              -> ~ in_env x g -> ~ in_env x g'  -> Subtype g s_x t_x
              -> Implies (concatE (Cons x t_x g) g') ps qs
              -> Implies (concatE (Cons x s_x g) g') ps qs 
    | IWeak   : forall (g:env) (g':env) (ps:preds) (qs:preds) (x:vname) (t_x:type),
          intersect (binds g) (binds g') = empty -> unique g -> unique g' 
              -> ~ in_env x g -> ~ in_env x g'
              -> Implies (concatE g g') ps qs 
              -> Implies (concatE (Cons x t_x g) g') ps qs
    | IWeakTV : forall (g:env) (g':env) (ps:preds) (qs:preds) (a:vname) (k_a:kind),
          intersect (binds g) (binds g') = empty -> unique g -> unique g' 
              -> ~ in_env a g -> ~ in_env a g'
              -> Implies (concatE g g') ps qs 
              -> Implies (concatE (ConsT a k_a g) g') ps qs
    | ISub    : forall (g:env) (g':env) (x:vname) (v_x:expr) (t_x:type) (ps:preds) (qs:preds),
          intersect (binds g) (binds g') = empty -> unique g -> unique g' 
              -> ~ in_env x g -> ~ in_env x g' -> isValue v_x -> Hastype g v_x t_x
              -> Implies (concatE (Cons x t_x g) g') ps qs
              -> Implies (concatE g (esubFV x v_x g')) (psubFV x v_x ps) (psubFV x v_x qs)
    | ISubTV  : forall (g:env) (g':env) (a:vname) (t_a:type) (k_a:kind) (ps:preds) (qs:preds),
          intersect (binds g) (binds g') = empty -> unique g -> unique g' 
              -> ~ in_env a g -> ~ in_env a g' -> noExists t_a -> WFtype g t_a k_a
              -> Implies (concatE (ConsT a k_a g) g') ps qs
              -> Implies (concatE g (esubFTV a t_a g')) (psubFTV a t_a ps) (psubFTV a t_a qs)
    | IEqlSub : forall (g:env) (b:basic) (y:vname) (e:expr) (ps:preds),
          Implies g (PCons (App (App (AppT (Prim Eql) (TRefn b PEmpty)) e) (FV y)) PEmpty)
                    (PCons (App (App (AppT (Prim Eql) (TRefn b ps    )) e) (FV y)) PEmpty) 
    | IStren  : forall (y:vname) (b':basic) (qs:preds) (g:env) (p1s:preds) (p2s:preds),
          ~ in_env y g -> Implies (Cons y (TRefn b' qs)     g) p1s p2s
              -> Implies (Cons y (TRefn b' PEmpty) g) 
                         (strengthen p1s (unbindP y qs)) (strengthen p2s (unbindP y qs))
