Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.LemmasTransitive.
Require Import Denotations.ClosingSubstitutions.

Require Import Arith Program.
Require Import Coq.Wellfounded.Inverse_Image.

Fixpoint isMono (t0 : type) : Prop := 
    match t0 with         
    | (TRefn b ps)     => True  
    | (TFunc  t_x t)   => isMono t_x /\ isMono t
    | (TExists  t_x t) => isMono t_x /\ isMono t
    | (TPoly  k   t)   => False
    end.

Fixpoint quants (t : type) : nat :=
    match t with
    | (TRefn b ps)     => 0  
    | (TFunc  t_x t)   => max (quants t_x) (quants t)
    | (TExists  t_x t) => max (quants t_x) (quants t)
    | (TPoly  k   t)   => 1 + (quants t)
    end.

Definition quants_depth (t : type) : nat*nat := (quants t, depth t).

Definition lexico_lt (ns : nat*nat) (ms : nat*nat) : Prop :=
    match ns with
    | (n1, n2) => match ms with
                  | (m1, m2) => n1 < m1 \/ (n1 = m1 /\ n2 < m2)
                  end
    end.

Lemma strong_ind' (P : nat -> Prop) :
    (forall m, (forall (k : nat), lt k m -> P k) -> P m) 
        -> forall n, (forall (k : nat), lt k n -> P k).
Proof. intros H n; induction n.
  - (* 0 *) intros; unfold lt in H0. apply Nat.nle_succ_0 in H0; contradiction.
  - (* S n *) unfold lt; intros. apply Nat.succ_le_mono in H0.
    apply Nat.lt_eq_cases in H0; destruct H0.
      * apply IHn; assumption.
      * subst k; apply H; apply IHn.
  Qed. 

Lemma strong_ind (P : nat -> Prop) :
  (forall m, (forall (k : nat), lt k m -> P k) -> P m) -> forall n, P n.
Proof. intros; apply strong_ind' with P (S n) n in H; intuition. Qed.

Lemma lexico_ind (P : nat*nat -> Prop) :
  (forall ms, (forall (ks : nat*nat), lexico_lt ks ms -> P ks) -> P ms) -> forall ns, P ns.
Proof. intros H ns; destruct ns as [n1 n2]. revert n2; revert n1. 
  pose proof strong_ind (fun n => forall n', P (n,n')) as Ind1; simpl in Ind1.
  apply Ind1; intro n1.
  pose proof strong_ind (fun n' => P (n1, n')) as Ind2; simpl in Ind2.
  intro IH1; apply Ind2; intros n2 IH2.
  apply H; intros ks Hks; destruct ks as [k1 k2].
  unfold lexico_lt in Hks; destruct Hks as [Hk1 | Hks].
  - (* k1 < n1 *) apply IH1; apply Hk1.
  - (* k1 = n1 /\ k2 < n2*) destruct Hks as [Hk1 Hk2];
    subst k1; apply IH2; apply Hk2.
  Qed. 

Lemma wf_lexico_lt : well_founded lexico_lt.
Proof. (*pose proof lt_wf; unfold well_founded in H.*)
  unfold well_founded; intros; destruct a as [n1 n2]. 
  apply Acc_intro. 
  pose proof lexico_ind (Acc lexico_lt) as H.
  intros ks Hks. apply H. intros.
  apply Acc_intro; apply H0.
Qed.
  

Lemma quants_tsubBV_at : forall (j:index) (v:expr) (t:type),
    quants (tsubBV_at j v t) = quants t.
Proof. intros j v t; revert v; revert j; induction t; intros;
  simpl; reflexivity || f_equal; 
  apply IHt1 || apply IHt2 || apply IHt. Qed.

Lemma quants_tsubBV : forall (v:expr) (t:type),
    quants (tsubBV v t) = quants t.
Proof. intros; apply quants_tsubBV_at. Qed.

Lemma quants_mono : forall (t_a: type),
    isMono t_a -> quants t_a = 0.
Proof. induction t_a; intro H; simpl in H; try contradiction;
  simpl; try reflexivity; destruct H as [H1 H2];
  apply IHt_a1 in H1; apply IHt_a2 in H2;
  rewrite H1; rewrite H2; reflexivity. Qed.

Lemma quants_push : forall (ps:preds) (t_a:type),
    quants (push ps t_a) = quants t_a.
Proof. intros ps t_a; revert ps; induction t_a; intros; simpl;
  try rewrite IHt_a2; reflexivity. Qed.

Lemma quants_tsubBTV_at : forall (j:index) (t_a:type) (t:type),
    isMono t_a -> quants (tsubBTV_at j t_a t) = quants t.
Proof. intros j t_a t; revert t_a; revert j; induction t; intros;
  try destruct b; simpl; try destruct (j =? i); simpl;
  try rewrite quants_push; 
  try rewrite IHt1; try rewrite IHt2; try rewrite IHt;
  trivial. rewrite quants_mono; trivial. Qed.

Lemma quants_tsubBTV : forall (t_a:type) (t:type),
    isMono t_a -> quants (tsubBTV t_a t) = quants t.
Proof. intros; apply quants_tsubBTV_at; assumption. Qed.

(*------------------------------------------------------------------------------
----- | DENOTATIONAL SEMANTICS 
------------------------------------------------------------------------------*)

Inductive PEvalsTrue : preds -> Prop :=
    | PEEmp  : PEvalsTrue PEmpty
    | PECons : forall (p : expr) (ps : preds),
        EvalsTo p (Bc true) -> PEvalsTrue ps -> PEvalsTrue (PCons p ps).

Program Fixpoint Denotes (t : type) (v : expr) 
                         {measure (quants_depth t) lexico_lt} : Prop :=
  isValue v /\ HasFtype FEmpty v (erase t) /\ (
    match t with
    | (TRefn   b   ps) => PEvalsTrue (psubBV v ps) 
    | (TFunc   t_x t') => forall (v_x : expr),
        isValue v_x -> Denotes t_x v_x /\ (exists (v' : expr), 
            isValue v' /\ EvalsTo (App v v_x) v' /\ Denotes (tsubBV v_x t') v'
        )
    | (TExists t_x t') => exists (v_x : expr),
        isValue v_x /\ Denotes t_x v_x /\ Denotes (tsubBV v_x t') v
    | (TPoly   k   t') => forall (t_a : type) (pf : isMono t_a), 
        noExists t_a ->  WFtype Empty t_a k -> (exists (v' : expr),
          isValue v' -> EvalsTo (AppT v t_a) v' /\ Denotes (tsubBTV t_a t') v')
    end
  ). 
  Obligation 1.  (* quants_depth t_x "<" quants_depth t *) intros.
    pose proof Nat.le_max_l (quants t_x) (quants t') as Hq;
    pose proof Nat.le_max_l (depth  t_x) (depth  t') as Hd.
    apply Nat.lt_eq_cases in Hq; destruct Hq as [Hq|Hq]; simpl.
      * left. apply Hq.
      * right; split; try apply Hq. apply Nat.lt_succ_r; apply Hd.
  Qed.
  Obligation 2.  (* quants_depth (tsubBV v_x t') "<" quants_depth t *)
    pose proof Nat.le_max_r (quants t_x) (quants t') as Hq;
    pose proof Nat.le_max_r (depth  t_x) (depth  t') as Hd.
    rewrite depth_tsubBV; rewrite quants_tsubBV. 
    apply Nat.lt_eq_cases in Hq; destruct Hq as [Hq|Hq]; simpl.
      * left. apply Hq.
      * right; split; try apply Hq. apply Nat.lt_succ_r; apply Hd.
  Qed.
  Obligation 3.   (* quants_depth t_x "<" quants_depth t *)
    pose proof Nat.le_max_l (quants t_x) (quants t') as Hq;
    pose proof Nat.le_max_l (depth  t_x) (depth  t') as Hd.
    apply Nat.lt_eq_cases in Hq; destruct Hq as [Hq|Hq]; simpl.
      * left. apply Hq.
      * right; split; try apply Hq. apply Nat.lt_succ_r; apply Hd.
  Qed.
  Obligation 4.   (* quants_depth (tsubBV v_x t') "<" quants_depth t *)
    pose proof Nat.le_max_r (quants t_x) (quants t') as Hq;
    pose proof Nat.le_max_r (depth  t_x) (depth  t') as Hd.
    rewrite depth_tsubBV; rewrite quants_tsubBV. 
    apply Nat.lt_eq_cases in Hq; destruct Hq as [Hq|Hq]; simpl.
      * left. apply Hq.
      * right; split; try apply Hq. apply Nat.lt_succ_r; apply Hd.
  Qed.
  Obligation 5.   (* quants_depth (tsubBTV t_a t') "<" quants_depth t *)
    left; rewrite quants_tsubBTV; intuition. 
  Qed.
  Obligation 6.   (* well_foundedness *) 
    unfold MR. apply wf_inverse_image; apply wf_lexico_lt.
  Qed. (* Defined. *)

Example zero_den_tint : Denotes (TRefn TInt PEmpty) (Ic 0).
Proof. unfold Denotes at 1; unfold Denotes_func. unfold Fix_sub. 
  destruct Denotes_func_obligation_6. simpl.
  repeat split; try apply FTIC; unfold psubBV; simpl; apply PEEmp.
  Qed.

Lemma lem_den_isvalue : forall (v:expr) (t:type),
    Denotes t v -> isValue v.
Proof. unfold Denotes; unfold Denotes_func; unfold Fix_sub; intros v t.
  destruct (Denotes_func_obligation_6 (existT (fun _ : type => expr) t v)); 
  simpl; intros H; destruct H; assumption. Qed.

Lemma lem_den_hasftype : forall (v:expr) (t:type),
    Denotes t v -> HasFtype FEmpty v (erase t).
Proof. unfold Denotes; unfold Denotes_func; unfold Fix_sub; intros v t.
  destruct (Denotes_func_obligation_6 (existT (fun _ : type => expr) t v)); 
  simpl; intros; destruct H; destruct H0; assumption.
Qed.

(* Denotations of Environments, [[g]]. There are two cases:
--   1. [[ Empty ]] = { CEmpty }.
--   2. [[ Cons x t g ]] = { CCons x v_x th | Denotes th(t) v_x && th \in [[ g ]] } *)
Inductive DenotesEnv : env -> csub -> Prop :=
    | DEmp  : DenotesEnv Empty CEmpty
    | DExt  : forall (g:env) (th:csub) (x:vname) (t:type) (v:expr), 
        DenotesEnv g th -> ~ in_env x g -> Denotes (ctsubst th t) v
              -> DenotesEnv (Cons x t g) (CCons x v th)
    | DExtT : forall (g:env) (th:csub) (a:vname) (k:kind) (t:type),
        DenotesEnv g th -> ~ in_env a g -> noExists t -> WFtype Empty t k
              -> DenotesEnv (ConsT a k g) (CConsT a t th).
(* the following spec. in the LH follow from Denotes th(t) v:
    - isValue v
    - Set_emp (fv v) && Set_emp (ftv v) && Set_emp (freeBV v) && Set_emp (freeBTV v) 
   and the following follow from WFType Empty t k:
    - Set_emp (free t) && Set_emp (freeTV t) && Set_emp (tfreeBV t) && Set_emp (tfreeBTV t) *)

Lemma lem_binds_env_th : forall (g:env) (th:csub), 
    DenotesEnv g th -> binds g = bindsC th.
Proof. intros g th den_g_th; induction den_g_th; simpl;
  try rewrite IHden_g_th; reflexivity. Qed.

Lemma lem_vbinds_env_th : forall (g:env) (th:csub), 
    DenotesEnv g th -> vbinds g = vbindsC th.
Proof. intros g th den_g_th; induction den_g_th; simpl;
  try rewrite IHden_g_th; reflexivity. Qed.
  
Lemma lem_tvbinds_env_th : forall (g:env) (th:csub), 
    DenotesEnv g th -> tvbinds g = tvbindsC th.
Proof. intros g th den_g_th; induction den_g_th; simpl;
  try rewrite IHden_g_th; reflexivity. Qed.  

(*------------------------------------------------------------------------------
----- | IMPILICATION from DENOTATIONAL SEMANTICS 
------------------------------------------------------------------------------*)

Inductive DImplies : env -> preds -> preds -> Prop :=
    | DImp : forall (g:env) (ps qs : preds),
        (forall (th:csub), DenotesEnv g th -> PEvalsTrue (cpsubst th ps) 
                                           -> PEvalsTrue (cpsubst th qs) )
            -> DImplies g ps qs.

(* Is this really neccessary?   
Lemma lem_den_nofv : forall (v:expr) (t:type),
    Denotes t v -> fv v = empty /\ ftv v = empty.
Proof. intros v t den_t_v; apply lem_den_hasftype in den_t_v;
  apply lem_fv_subset_bindsF in den_t_v; simpl in den_t_v.
  .....  *)
(*
lem_den_nofv :: Expr -> Type -> Denotes -> Proof
lem_den_nofv v t den_t_v = lem_fv_subset_bindsF FEmpty v (erase t) pf_v_bt
  where
    pf_v_bt = get_ftyp_from_den t v den_t_v

{-@ lem_den_nobv :: v:Value -> t:Type -> ProofOf(Denotes t v) 
        -> { pf:_ | Set_emp (freeBV v) && Set_emp (freeBTV v) } @-}
lem_den_nobv :: Expr -> Type -> Denotes -> Proof
lem_den_nobv v t den_t_v = lem_freeBV_emptyB FEmpty v (erase t) pf_v_bt
  where
    pf_v_bt = get_ftyp_from_den t v den_t_v *)



            