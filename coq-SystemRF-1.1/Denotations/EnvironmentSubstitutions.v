Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.Strengthenings.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.Typing.
Require Import Denotations.ClosingSubstitutions.
Require Import Denotations.Denotations.
Require Import Denotations.BasicPropsCSubst.

Require Import Arith.

Lemma lem_concat_shift : forall (g:env) (x:vname) (t_x:type) (g':env),
    ~ (in_env x g) -> ~ (in_env x g') -> intersect (binds g) (binds g') = empty
        -> concatE (Cons x t_x g) g' = concatE g (concatE (Cons x t_x Empty) g').
Proof. intros g x t_x; induction g'; simpl; intros; try reflexivity;
  f_equal; apply IHg'; unfold in_env in H0; simpl in H0;
  apply not_elem_names_add_elim in H0; destruct H0; 
  apply intersect_names_add_elim_r in H1; destruct H1;  trivial. Qed.

Lemma lem_concat_shift_tv : forall (g:env) (a:vname) (k_a:kind) (g':env),
    ~ (in_env a g) -> ~ (in_env a g') -> intersect (binds g) (binds g') = empty
        -> concatE (ConsT a k_a g) g' = concatE g (concatE (ConsT a k_a Empty) g').
Proof. intros g a k_a; induction g'; simpl; intros; try reflexivity;
  f_equal; apply IHg'; unfold in_env in H0; simpl in H0;
  apply not_elem_names_add_elim in H0; destruct H0; 
  apply intersect_names_add_elim_r in H1; destruct H1;  trivial. Qed.

Lemma lem_csubst_env_empty : forall (th:csub),
    csubst_env th Empty = Empty.
Proof. induction th; simpl; reflexivity || apply IHth. Qed.

Lemma lem_csubst_cons_env : forall (th:csub) (x:vname) (t_x:type) (g:env),
    csubst_env th (Cons x t_x g) = Cons x (ctsubst th t_x) (csubst_env th g).
Proof. induction th; simpl; intros; reflexivity || apply IHth. Qed.

Lemma lem_csubst_consT_env : forall (th:csub) (a:vname) (k_a:kind) (g:env), 
    csubst_env th (ConsT a k_a g) = ConsT a k_a (csubst_env th g).
Proof. induction th; simpl; intros; reflexivity || apply IHth. Qed.

Lemma lem_esubFV_concat : forall (x:vname) (v:expr) (g g':env),
    esubFV x v (concatE g g') = concatE (esubFV x v g) (esubFV x v g').
Proof. intros; induction g'; simpl; try rewrite IHg'; reflexivity. Qed.

Lemma lem_esubFTV_concat : forall (a:vname) (t_a:type) (g g':env),
    esubFTV a t_a (concatE g g') = concatE (esubFTV a t_a g) (esubFTV a t_a g').
Proof. intros; induction g'; simpl; try rewrite IHg'; reflexivity. Qed.

Lemma lem_csubst_env_concat : forall (th:csub) (g g':env),
    csubst_env th (concatE g g') = concatE (csubst_env th g) (csubst_env th g').
Proof. induction th; simpl; intros; try rewrite lem_esubFV_concat;
  try rewrite lem_esubFTV_concat; apply IHth || reflexivity. Qed.

Lemma csubst_env_binds : forall (th:csub) (g:env),
    binds (csubst_env th g) = binds g.
Proof. induction th; intros; simpl; try rewrite IHth;
  try apply esubFV_binds; try apply esubFTV_binds; reflexivity. Qed.

Lemma csubst_env_unique : forall (th:csub) (g:env),
    unique g -> unique (csubst_env th g).
Proof. induction th; intros; simpl; try apply IHth;
  try apply esubFV_unique; try apply esubFTV_unique; apply H. Qed.

Lemma lem_commute_esubFV : forall (g:env) (x:vname) (v_x:expr) (y:vname) (v_y:expr),
    y <> x -> ~ Elem x (fv v_y) -> ~ Elem y (fv v_x)
        -> esubFV y v_y (esubFV x v_x g) = esubFV x (subFV y v_y v_x) (esubFV y v_y g).
Proof. induction g; simpl; intros; reflexivity || rewrite <- IHg;
  try rewrite lem_commute_tsubFV; 
  try rewrite lem_subFV_notin'; trivial. Qed.
  
Lemma lem_commute_esubFV_esubFTV : 
  forall (g:env) (a:vname) (t_a:type) (y:vname) (v_y:expr),
    noExists t_a -> isValue v_y -> ~ Elem a (ftv v_y) -> ~ Elem y (free t_a)
        -> esubFV y v_y (esubFTV a t_a g) =
                    esubFTV a (tsubFV y v_y t_a) (esubFV y v_y g).
Proof. induction g; simpl; intros; reflexivity || rewrite <- IHg;
  try rewrite lem_commute_tsubFV_tsubFTV;
  try rewrite (lem_tsubFV_notin t_a); trivial. Qed.
  
Lemma lem_unroll_csubst_env_left : forall (th:csub) (x:vname) (v_x:expr) (g:env),
    ~ in_csubst x th -> fv v_x = empty /\ ftv v_x = empty -> isValue v_x
        -> closed th -> substitutable th
        -> csubst_env (CCons x v_x th) g = esubFV x v_x (csubst_env th g).
Proof. induction th; simpl; intros; try reflexivity;
  unfold in_csubst in H; simpl in H; 
  apply not_elem_names_add_elim in H; destruct H;
  rewrite <- IHth; simpl; try f_equal;
  destruct H2; destruct H3; destruct H5; try destruct H6;
  trivial; destruct H0.
  - (* CCons *) rewrite lem_commute_esubFV;
    try rewrite lem_subFV_notin'; try apply Nat.neq_sym;
    try rewrite H0; try rewrite H2; auto.
  - (* CConsT *) rewrite lem_commute_esubFV_esubFTV;
    try rewrite lem_tsubFV_notin; 
    try rewrite H9; try rewrite H2; auto.
  Qed.

Lemma lem_unbind_tvT_equals : forall (i:index) (a:vname) (t1 t2:ftype),
    ~ Elem a (ffreeTV t1) -> ~ Elem a (ffreeTV t2) 
          -> openFT_at i a t1 = openFT_at i a t2 -> t1 = t2.
Proof. intros i a t1; revert i; induction t1; intros.
  - (* FTBasic *) destruct t2; unfold unbindFT in H1; 
    destruct b; try destruct b0; simpl in H1;
    try destruct (i =? i0) eqn:I0; try destruct (i =? i1) eqn:I1;
    try discriminate; try apply Nat.eqb_eq in I0; 
    try apply Nat.eqb_eq in I1;
    try subst i0; try subst i1; 
    try reflexivity; try apply H1;
    simpl in H; simpl in H0;
    injection H1 as H1; subst a0; intuition.
  - (* FTFunc *) destruct t2; unfold unbindFT in H1;
    try destruct b; simpl in H1; try destruct (i =? i0);
    try discriminate; injection H1 as H1;
    simpl in H; apply not_elem_union_elim in H;
    simpl in H0; apply not_elem_union_elim in H0;
    destruct H; destruct H0;
    apply IHt1_1 in H1; apply IHt1_2 in H2;
    try subst t2_1 t2_2; trivial.
  - (* FTPoly *) destruct t2; unfold unbindFT in H1;
    try destruct b; simpl in H1; try destruct (i =? i0); 
    try discriminate; injection H1 as H1;
    simpl in H; simpl in H0; f_equal; try apply H1;
    apply IHt1 with (i+1); trivial.
  Qed.

(* -- LEMMA 6. If G |- s <: t, then if we erase the types then (erase s) and (erase t)
   --               equiv up to alpha-renaming bound variables *)
Lemma lem_erase_subtype : forall (g:env) (t1 t2:type),
    Subtype g t1 t2 -> erase t1 = erase t2.
Proof. intros g t1 t2 p_t1_t2; induction p_t1_t2; simpl.
  - (* SBase *) reflexivity.
  - (* SFunc *) f_equal; try (symmetry; apply IHp_t1_t2);
    pose proof (fresh_not_elem nms) as Hy;
    set (y := fresh nms) in Hy;
    apply H0 in Hy as IH2;
    repeat rewrite lem_erase_unbind in IH2; apply IH2.
  - (* SWitn *) rewrite lem_erase_tsubBV in IHp_t1_t2;
    apply IHp_t1_t2.
  - (* SBind *) pose proof (fresh_not_elem nms) as Hy;
    set (y := fresh nms) in Hy;
    apply H1 in Hy as IH;
    rewrite lem_erase_unbind in IH; apply IH.
  - (* SPoly *) f_equal;
    pose proof (fresh_varFTs_not_elem nms g (erase t1) (erase t2)) as Ha;
    set (a := fresh_varFTs nms g (erase t1) (erase t2)) in Ha;
    destruct Ha as [Ht [Ht' [Ha Hg]]];
    apply H0 in Ha as IH2;
    repeat rewrite lem_erase_unbind_tvT in IH2;
    apply lem_unbind_tvT_equals with 0 a; trivial.
  Qed.
    
Lemma lem_erase_ctsubst : forall (th:csub) (t1 t2:type),
    substitutable th -> erase t1 = erase t2 
        -> erase (ctsubst th t1) = erase (ctsubst th t2).
Proof. induction th; simpl; intros.  
  - (* CEmpty *) apply H0.
  - (* CCons *) destruct H; apply IHth; 
    repeat rewrite lem_erase_tsubFV; assumption.
  - (* CConsT *) destruct H; destruct H1; apply IHth; 
    repeat rewrite lem_erase_tsubFTV; f_equal; assumption.
  Qed.