Require Import Arith.
Require Import ZArith.

Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names. 
Require Import SystemRF.LocalClosure.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.

(*-----------------------------------------------------------------------------
----- | JUDGEMENTS : the Typing Relation and the Subtyping Relation
-----------------------------------------------------------------------------*)

Definition eqlPred (b : basic) (ps : preds) (e : expr) : expr :=
  App (App (AppT (Prim Eql) (TRefn b PEmpty)) e) (BV 0).     (* fv  p' ==  (fv  e) } *)

Lemma lem_eqlPred_islc_at : forall (b : basic) (ps : preds) (e : expr),
    isLCT (TRefn b PEmpty) -> isLC e -> isLC_at 1 0 (eqlPred b ps e).
Proof. intros; simpl; intuition; 
  try destruct b; simpl in H; try contradiction;
  try apply lem_islc_at_weaken with 0 0; intuition. Qed.

Lemma lem_unbind_eqlPred : forall (y : vname) (b : basic) (ps : preds) (e : expr),
    isLC e -> unbind y (eqlPred b ps e) 
                   = App (App (AppT (Prim Eql) (TRefn b PEmpty)) e) (FV y).
Proof. intros; unfold unbind; simpl; rewrite lem_unbind_lc; trivial. Qed.

Lemma lem_tsubFTV_eqlPred : forall (a:vname) (t_a:type) (b:basic) (ps:preds) (e:expr),
    noExists t_a  -> ~ (b = FTV a) -> ~ Elem a (ftv e)
                  -> subFTV a t_a (eqlPred b ps e) = eqlPred b ps e.
Proof. intros; destruct b eqn:B; simpl; try destruct (a =? a0) eqn:A;
  try (apply Nat.eqb_eq in A; subst a0; contradiction);
  unfold eqlPred; repeat f_equal; apply lem_subFTV_notin; apply H1. Qed.

Fixpoint self (t0 : type) (e : expr) (k : kind) : type :=
    match k with 
    | Base => match t0 with
              | (TRefn b ps)      =>  TRefn b (PCons  (eqlPred b ps e)  ps)
              | (TFunc    t_z t)  =>  TFunc   t_z t
              | (TExists  t_z t)  =>  TExists t_z (self t e Base)
              | (TPoly    k_a t)  =>  TPoly   k_a t
              end
    | Star => t0
    end.  (* { t':type | Set_sub (free t') (Set_cup (free t) (fv e)) &&
                  (isTRefn t => isTRefn t') && (noExists t => noExists t' )*)
Lemma self_trefn_is_push : forall (b : basic) (ps : preds) (e : expr), 
    self (TRefn b ps) e Base = push (PCons (eqlPred b ps e) PEmpty) (TRefn b ps).
Proof. intros; simpl; reflexivity. Qed.

Lemma lem_self_islct_at : forall (t:type) (e:expr) (k:kind) (j:index),
    isLCT_at j 0 t -> isLC e -> isLCT_at j 0 (self t e k).
Proof. induction t; intros; destruct k0 || destruct k; unfold self; try assumption.
  - (* TRefn b ps, Base *) destruct b eqn:B; simpl in H;
    (* no BTV *) try (destruct H; unfold lt in H; apply Nat.le_0_r in H; discriminate);
    simpl; repeat split; try apply H; 
    try apply lem_islc_at_weaken with 0 0; auto with *.
  - (* TExists, Base *) fold self; simpl; simpl in H; intuition. Qed.

Lemma lem_self_islct : forall (t : type) (e : expr) (k : kind),
    isLCT t -> isLC e -> isLCT (self t e k).
Proof. intros t e k; apply lem_self_islct_at. Qed. 

Lemma lem_openT_at_self : forall (j:index) (y:vname) (t:type) (e:expr) (k:kind),
    isLC e ->  openT_at j y (self t e k) = self (openT_at j y t) e k.
Proof. intros j y t; generalize dependent j; induction t; intros.
  - (* TRefn *) destruct k; simpl; unfold eqlPred;
    pose proof lem_open_at_lc_at; destruct H0;
    try rewrite (e0 e (j+1) 0 y); try destruct (j + 1 =? 0) eqn:J; 
    rewrite Nat.add_comm in J; simpl in J; try discriminate J;
    try apply lem_islc_at_weaken with 0 0; auto with *.
  - (* TFunc *) destruct k; simpl; reflexivity.
  - (* TExis *) destruct k; simpl; try rewrite IHt2; trivial.
  - (* TPoly *) destruct k0; simpl; reflexivity.
  Qed.

Lemma lem_unbindT_self : forall (y:vname) (t:type) (e:expr) (k:kind),
    isLC e ->  unbindT y (self t e k) = self (unbindT y t) e k.
Proof. intros; unfold unbindT; apply lem_openT_at_self; apply H. Qed. 

Lemma lem_tsubFV_self : forall (z:vname) (v_z:expr) (t:type) (e:expr) (k:kind),
    tsubFV z v_z (self t e k) = self (tsubFV z v_z t) (subFV z v_z e) k.
Proof. intros; induction t; destruct k; simpl; f_equal.
  - (* TExis *) apply IHt2. Qed.

Lemma lem_tsubBV_at_self : forall (j:index) (v_z:expr) (t:type) (e:expr) (k:kind),
    isValue v_z -> isLC e -> tsubBV_at j v_z (self t e k) = self (tsubBV_at j v_z t) e k.
Proof. intros j v_z t; generalize dependent j; induction t; intros.
  - (* TRefn *) destruct k; simpl; pose proof lem_subBV_at_lc_at; destruct H1;
    try rewrite e0 with e (j+1) v_z 0 0; try destruct (j + 1 =? 0) eqn:J;
    rewrite Nat.add_comm in J; simpl in J; try discriminate J; auto with *.
  - (* TFunc *) destruct k; simpl; reflexivity.
  - (* TExis *) destruct k; simpl; try rewrite IHt2; trivial.
  - (* TPoly *) destruct k0; simpl; reflexivity.
  Qed.
  
Lemma lem_tsubBV_self : forall (v_z:expr) (t:type) (e:expr) (k:kind),
    isValue v_z -> isLC e -> tsubBV v_z (self t e k) = self (tsubBV v_z t) e k.
Proof. intros; apply lem_tsubBV_at_self; apply H || apply H0. Qed.

Lemma lem_erase_self : forall (t:type) (e:expr) (k:kind),
    erase (self t e k) = erase t.
Proof. intros; destruct k; induction t; simpl; try apply IHt2; reflexivity. Qed.

Lemma lem_self_star : forall (t:type) (e:expr), self t e Star = t.
Proof. intros; destruct t; reflexivity. Qed.

(*------------------------------------------------------------------------------
----- | TYPING & SUBTYPING JUDGMENTS and UNINTERPRETED IMPLICATION 
------------------------------------------------------------------------------*)
 
Inductive Hastype : env -> expr -> type -> Prop :=
    | TBC   : forall (g:env) (b:bool), Hastype g (Bc b) (tybc b) 
    | TIC   : forall (g:env) (m:Z),  Hastype g (Ic m) (tyic m) 
    | TVar  : forall (g:env) (x:vname) (t:type) (k:kind),
          bound_in x t g -> WFtype g t k -> Hastype g (FV x) (self t (FV x) k)
    | TPrm  : forall (g:env) (c:prim), Hastype g (Prim c) (ty c)
    | TAbs  : forall (g:env) (t_x:type) (k_x:kind) (e:expr) (t:type) (nms:names),
          WFtype g t_x k_x
              -> (forall (y:vname), ~ Elem y nms -> Hastype (Cons y t_x g) (unbind y e) (unbindT y t)) 
              -> Hastype g (Lambda e) (TFunc t_x t) 
    | TApp  : forall (g:env) (e:expr) (t_x:type) (t:type) (e':expr),
          Hastype g e (TFunc t_x t) -> Hastype g e' t_x -> Hastype g (App e e') (TExists t_x t)
    | TAbsT : forall (g:env) (k:kind) (e:expr) (t:type) (nms:names),
          (forall (a':vname), ~ Elem a' nms 
                           -> Hastype (ConsT a' k g) (unbind_tv a' e) (unbind_tvT a' t))
              -> Hastype g (LambdaT k e) (TPoly k t)
    | TAppT : forall (g:env) (e:expr) (k:kind) (s:type) (t:type),
          Hastype g e (TPoly k s) -> isMono t -> noExists t -> WFtype g t k
              -> Hastype g (AppT e t) (tsubBTV t s)
    | TLet  : forall (g:env) (e_x:expr) (t_x:type) (e:expr) (t:type) (k:kind) (nms:names),
          WFtype g t k -> Hastype g e_x t_x
              -> (forall (y:vname), ~ Elem y nms 
                          -> Hastype (Cons y t_x g) (unbind y e) (unbindT y t)) 
              -> Hastype g (Let e_x e) t 
    | TAnn  : forall (g:env) (e:expr) (t:type), 
          noExists t -> Hastype g e t -> Hastype g (Annot e t) t
    | TIf   : forall (g:env) (e0 e1 e2 : expr) (ps: preds) (t:type) (k:kind) (nms:names),
          Hastype g e0 (TRefn TBool ps) -> WFtype  g t k 
            -> (forall (y:vname), ~ Elem y nms
                  -> Hastype (Cons y (self (TRefn TBool ps) (Bc true)  Base) g) e1 t )
            -> (forall (y:vname), ~ Elem y nms
                  -> Hastype (Cons y (self (TRefn TBool ps) (Bc false) Base) g) e2 t )
            -> Hastype g (If e0 e1 e2) t
    | TSub  : forall (g:env) (e:expr) (s:type) (t:type) (k:kind),
          Hastype g e s -> WFtype g t k -> Subtype g s t -> Hastype g e t

with Subtype : env -> type -> type -> Prop :=
    | SBase : forall (g:env) (b:basic) (p1:preds) (p2:preds) (nms:names),
          (forall (y:vname), ~ Elem y nms
                          -> Implies (Cons y (TRefn b PEmpty) g) (unbindP y p1) (unbindP y p2)) 
              -> Subtype g (TRefn b p1) (TRefn b p2) 
    | SFunc : forall (g:env) (s1:type) (s2:type) (t1:type) (t2:type) (nms:names),
          Subtype g s2 s1
              -> (forall (y:vname), ~ Elem y nms
                          -> Subtype (Cons y s2 g) (unbindT y t1) (unbindT y t2)) 
              -> Subtype g (TFunc s1 t1) (TFunc s2 t2) 
    | SWitn : forall (g:env) (v_x:expr) (t_x:type) (t:type) (t':type) ,
          isValue v_x -> Hastype g v_x t_x -> Subtype g t (tsubBV v_x t')
              -> Subtype g t (TExists t_x t')
    | SBind : forall (g:env) (t_x:type) (t:type) (t':type) (nms:names),
          isLCT t' -> (forall (y:vname), ~ Elem y nms -> Subtype (Cons y t_x g) (unbindT y t) t') 
              -> Subtype g (TExists t_x t) t' 
    | SPoly : forall (g:env) (k:kind) (t1:type) (t2:type) (nms:names),
              (forall (a:vname), ~ Elem a nms 
                          -> Subtype (ConsT a k g) (unbind_tvT a t1) (unbind_tvT a t2)) 
                  -> Subtype g (TPoly k t1) (TPoly k t2)

with Implies : env -> preds -> preds -> Prop := 
    | IRefl   : forall (g:env) (ps:preds), Implies g ps ps
    | ITrans  : forall (g:env) (ps:preds) (qs:preds) (rs:preds),
          Implies g ps qs -> Implies g qs rs -> Implies g ps rs
    | IFaith  : forall (g:env) (ps:preds), Implies g ps PEmpty
    | IConj   : forall (g:env) (ps:preds) (qs:preds) (rs:preds),
          Implies g ps qs -> Implies g ps rs -> Implies g ps (strengthen qs rs)
    | ICons1  : forall (g:env) (p:expr) (ps:preds), Implies g (PCons p ps) (PCons p PEmpty)
    | ICons2  : forall (g:env) (p:expr) (ps:preds), Implies g (PCons p ps) ps
    | IRepeat : forall (g:env) (p:expr) (ps:preds), Implies g (PCons p ps) (PCons p (PCons p ps))
    | INarrow : forall (g:env) (g':env) (x:vname) (s_x t_x:type) (k_sx k_tx:kind) (ps qs:preds),
          intersect (binds g) (binds g') = empty -> unique g -> unique g'
              -> ~ in_env x g -> ~ in_env x g' -> WFEnv g
              -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x
              -> Implies (concatE (Cons x t_x g) g') ps qs
              -> Implies (concatE (Cons x s_x g) g') ps qs 
    | IWeak   : forall (g:env) (g':env) (ps:preds) (qs:preds) (x:vname) (t_x:type),
          intersect (binds g) (binds g') = empty -> unique g -> unique g' 
              -> ~ in_env x g -> ~ in_env x g' -> WFEnv (concatE g g')
              -> ~ Elem x (fvP ps) -> ~ Elem x (ftvP ps) 
              -> ~ Elem x (fvP qs) -> ~ Elem x (ftvP qs)
              -> Implies (concatE g g') ps qs 
              -> Implies (concatE (Cons x t_x g) g') ps qs
    | IWeakTV : forall (g:env) (g':env) (ps:preds) (qs:preds) (a:vname) (k_a:kind),
          intersect (binds g) (binds g') = empty -> unique g -> unique g' 
              -> ~ in_env a g -> ~ in_env a g' -> WFEnv (concatE g g')
              -> ~ Elem a (fvP ps) -> ~ Elem a (ftvP ps) 
              -> ~ Elem a (fvP qs) -> ~ Elem a (ftvP qs)
              -> Implies (concatE g g') ps qs 
              -> Implies (concatE (ConsT a k_a g) g') ps qs
    | ISub    : forall (g:env) (g':env) (x:vname) (v_x:expr) (t_x:type) (ps:preds) (qs:preds),
          intersect (binds g) (binds g') = empty -> unique g -> unique g' 
              -> ~ in_env x g -> ~ in_env x g' -> WFEnv g
              -> isValue v_x -> Hastype g v_x t_x
              -> Implies (concatE (Cons x t_x g) g') ps qs
              -> Implies (concatE g (esubFV x v_x g')) (psubFV x v_x ps) (psubFV x v_x qs)
    | ISubTV  : forall (g:env) (g':env) (a:vname) (t_a:type) (k_a:kind) (ps:preds) (qs:preds),
          intersect (binds g) (binds g') = empty -> unique g -> unique g' 
              -> ~ in_env a g -> ~ in_env a g' -> WFEnv g
              -> isMono t_a -> noExists t_a -> WFtype g t_a k_a
              -> Implies (concatE (ConsT a k_a g) g') ps qs
              -> Implies (concatE g (esubFTV a t_a g')) (psubFTV a t_a ps) (psubFTV a t_a qs)
    | IEqlSub : forall (g:env) (b:basic) (y:vname) (e:expr) (ps:preds),
          Implies g (PCons (App (App (AppT (Prim Eql) (TRefn b PEmpty)) e) (FV y)) PEmpty)
                    (PCons (App (App (AppT (Prim Eql) (TRefn b ps    )) e) (FV y)) PEmpty) 
    | IStren  : forall (y:vname) (b':basic) (qs:preds) (g:env) (p1s:preds) (p2s:preds),
          ~ in_env y g -> ~ Elem y (fvP qs)
              -> Implies (Cons y (TRefn b' qs)     g) p1s p2s
              -> Implies (Cons y (TRefn b' PEmpty) g) 
                         (strengthen p1s (unbindP y qs)) (strengthen p2s (unbindP y qs))
    | IEvals  : forall (g:env) (p p':expr) (ps:preds),
          EvalsTo p p' -> Implies g (PCons p ps) (PCons p' ps)
    | IEvals2 : forall (g:env) (p p':expr) (ps:preds),
          EvalsTo p' p -> Implies g (PCons p ps) (PCons p' ps).

Scheme Hastype_mutind  := Induction for Hastype  Sort Prop
with   Subtype_mutind  := Induction for Subtype  Sort Prop.
Combined Scheme judgments_mutind from Hastype_mutind, Subtype_mutind.    

Scheme Hastype_mutind3 := Induction for Hastype  Sort Prop
with   Subtype_mutind3 := Induction for Subtype  Sort Prop
with   Implies_mutind3 := Induction for Implies  Sort Prop.
Combined Scheme judgments_mutind3 
    from Hastype_mutind3, Subtype_mutind3, Implies_mutind3.