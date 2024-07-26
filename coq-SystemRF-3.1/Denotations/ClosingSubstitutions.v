Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.BasicPropsEnvironments.

Require Import Arith.
Require Import Lists.ListSet.

(*------------------------------------------------------------------------- 
----- | CLOSING SUBSTITUTIONS 
-------------------------------------------------------------------------*)

(* closing substitutions (i.e. th(x), th(e), th(t)) proceed from the top/right of
 *   the typing env downwards/leftwards. In order for a closing substitution to be
 *   "well formed" it must be an element of the denotation 
 *   of the corresponding enivornment *)

Inductive csub : Set :=
    | CEmpty
    | CCons  (x : vname) (v_x : expr) (th : csub)
    | CConsT (a : vname) (t_a : type) (th : csub).
  
Fixpoint bindsC (th : csub) : names := 
    match th with 
    | CEmpty            => empty
    | (CCons  x v_x th) => names_add x (bindsC th)
    | (CConsT a t_a th) => names_add a (bindsC th)
    end.

Fixpoint vbindsC (th : csub) : names := 
    match th with 
    | CEmpty            => empty
    | (CCons  x v_x th) => names_add x (vbindsC th)
    | (CConsT a t_a th) => vbindsC th
    end.

Fixpoint tvbindsC (th : csub) : names := 
    match th with 
    | CEmpty            => empty
    | (CCons  x v_x th) => tvbindsC th
    | (CConsT a t_a th) => names_add a (tvbindsC th)
    end.

Definition in_csubst (x : vname) (th : csub) : Prop := Elem x (bindsC th).

Lemma vbindsC_subset : forall (th : csub), Subset (vbindsC th) (bindsC th).
Proof. unfold Subset; induction th; simpl.
  - trivial.
  - apply subset_add_both_intro; assumption.
  - apply subset_add_intro; assumption. Qed.
  
Lemma tvbindsC_subset : forall (th : csub), Subset (tvbindsC th) (bindsC th).
Proof. unfold Subset; induction th; simpl.
  - trivial.
  - apply subset_add_intro; assumption.
  - apply subset_add_both_intro; assumption. Qed. 

Lemma in_csubst_CCons : forall (x y : vname) (v : expr) (th : csub),
   ~ in_csubst x (CCons y v th) -> x <> y /\ ~ in_csubst x th.
Proof. unfold in_csubst; simpl; intros; split; unfold not.
  - intro. apply set_add_intro2 with _ Nat.eq_dec x y (bindsC th) in H0; contradiction.
  - intro. apply set_add_intro1 with _ Nat.eq_dec x y (bindsC th) in H0; contradiction.
  Qed.

Lemma in_csubst_CConsT : forall (x a : vname) (t : type) (th : csub),
    ~ in_csubst x (CConsT a t th) -> x <> a /\ ~ in_csubst x th.
Proof. unfold in_csubst; simpl; intros; split; unfold not.
  - intro. apply set_add_intro2 with _ Nat.eq_dec x a (bindsC th) in H0; contradiction.
  - intro. apply set_add_intro1 with _ Nat.eq_dec x a (bindsC th) in H0; contradiction.
  Qed.

Fixpoint bound_inC (x : vname) (v_x : expr) (th : csub) : Prop := 
    match th with
    | CEmpty             => False
    | (CCons  y v_y th)  => (x = y /\ v_x = v_y) \/ bound_inC x v_x th
    | (CConsT a t_a th)  => bound_inC x v_x th
    end.

Lemma lem_boundinC_incsubst: forall (x:vname) (v_x:expr) (th:csub),
    bound_inC x v_x th -> in_csubst x th.
Proof. intros. induction th; simpl in H; simpl; try contradiction;
  try (apply set_add_intro); try (destruct H); try (apply IHg in H); intuition. 
Qed.

Lemma lem_vbindsC_boundinC : forall (x:vname) (th:csub),
    Elem x (vbindsC th) -> exists v_x, bound_inC x v_x th.
Proof. intro x; induction th; simpl; intros; try contradiction.
  - apply set_add_elim in H; destruct H.
    exists v_x; left; auto.
    apply IHth in H as [ta' H]; exists ta'; right; apply H.
  - apply IHth; apply H.
Qed.

Fixpoint tv_bound_inC (a : vname) (t_a : type) (th : csub) : Prop :=
    match th with
    | CEmpty               => False
    | (CCons  y  v_y  th)  => tv_bound_inC a t_a th
    | (CConsT a' t_a' th)  => (a = a' /\ t_a = t_a') \/ tv_bound_inC a t_a th
    end.

Lemma lem_tvboundinC_incsubst: forall (a:vname) (t_a:type) (th:csub),
    tv_bound_inC a t_a th -> in_csubst a th.
Proof. intros. induction th; simpl in H; simpl; try contradiction;
  try (apply set_add_intro); try (destruct H); try (apply IHg in H); intuition. 
Qed.

Lemma lem_tvbindsC_tvboundinC : forall (a:vname) (th:csub),
    Elem a (tvbindsC th) -> exists t_a, tv_bound_inC a t_a th.
Proof. intro a; induction th; simpl; intros; try contradiction.
  - apply IHth; apply H.
  - apply set_add_elim in H; destruct H.
    exists t_a; left; auto.
    apply IHth in H as [ta' H]; exists ta'; right; apply H.
Qed.

Fixpoint closed (th0 : csub) : Prop :=
    match th0 with
    | CEmpty            => True
    | (CCons  x v_x th) => fv v_x = empty /\ ftv v_x = empty /\ closed th
    | (CConsT a t   th) => free t = empty /\ freeTV t = empty /\ closed th
    end.  

Lemma lem_boundinC_closed: forall (x:vname) (v_x:expr) (th:csub),
    bound_inC x v_x th -> closed th -> fv v_x = empty /\ ftv v_x = empty.
Proof. intros. induction th; simpl in H; simpl; try contradiction;
  simpl in H0; destruct H0; destruct H1.
  - destruct H; try (destruct H; subst v_x0); intuition. 
  - apply IHth; auto.
Qed.

Lemma lem_tvboundinC_closed: forall (a:vname) (t_a:type) (th:csub),
    tv_bound_inC a t_a th -> closed th -> free t_a = empty /\ freeTV t_a = empty.
Proof. intros. induction th; simpl in H; simpl; try contradiction;
  simpl in H0; destruct H0; destruct H1. 
  - apply IHth; auto.
  - destruct H; try (destruct H; subst t_a0); intuition.
Qed.

Fixpoint loc_closed (th0 : csub) : Prop :=
    match th0 with
    | CEmpty            => True
    | (CCons  x v_x th) => isLC v_x /\ loc_closed th
    | (CConsT a t   th) => isLCT t  /\ loc_closed th
    end.  

Fixpoint substitutable (th0 : csub) : Prop :=
    match th0 with
    | CEmpty            => True
    | (CCons  x v_x th) => isValue v_x /\ substitutable th
    | (CConsT a t   th) => isMono t /\ noExists t /\ substitutable th
    end.  

Lemma lem_tvboundinC_substitutable: forall (a:vname) (t_a:type) (th:csub),
    tv_bound_inC a t_a th -> substitutable th 
        -> isMono t_a /\ noExists t_a.
Proof. intros. induction th; simpl in H; simpl; try contradiction;
  simpl in H0; destruct H0. 
  - apply IHth; auto.
  - destruct H; try (destruct H; subst t_a0); intuition.
Qed.

Fixpoint uniqueC (th0 : csub) : Prop :=
    match th0 with
    | CEmpty         => True
    | (CCons  x v_x th) => ~ in_csubst x th /\ uniqueC th
    | (CConsT a t_a th) => ~ in_csubst a th /\ uniqueC th
    end.   
    
Fixpoint csubst (th : csub) (e : expr) : expr := 
    match th with
    | CEmpty            => e
    | (CCons  x v_x th) => csubst th (subFV  x v_x e)
    | (CConsT a t_a th) => csubst th (subFTV a t_a e)
    end.

Fixpoint cpsubst (th : csub) (ps : preds) : preds := 
    match th with
    | CEmpty            => ps
    | (CCons  x v_x th) => cpsubst th (psubFV  x v_x ps)
    | (CConsT a t_a th) => cpsubst th (psubFTV a t_a ps)
    end.

Fixpoint ctsubst (th : csub) (t : type) : type :=
    match th with
    | CEmpty           => t
    | (CCons  x v  th) => ctsubst th (tsubFV x v t)
    | (CConsT a t' th) => ctsubst th (tsubFTV a t' t)
    end.

Fixpoint concatCS (th th'0 : csub) : csub :=
    match th'0 with
    | CEmpty           => th
    | (CCons  x v th') => CCons  x v (concatCS th th')
    | (CConsT a t th') => CConsT a t (concatCS th th')
    end.

Fixpoint remove_fromCS (th:csub) (x:vname) : csub := 
    match th with 
    | CEmpty          => CEmpty
    | (CCons  y v th) => if x =? y then th else CCons  y v (remove_fromCS th x)
    | (CConsT a t th) => if x =? a then th else CConsT a t (remove_fromCS th x)
    end.

Lemma not_incsubst_remove_fromCS : 
  forall (th : csub) (x : vname), 
      uniqueC th -> ~ in_csubst x (remove_fromCS th x).
Proof. induction th; intros; unfold in_csubst; simpl.
  - auto.
  - destruct (x0 =? x) eqn:X; simpl; simpl in H.
    * apply Nat.eqb_eq in X; subst x0; destruct H; trivial.
    * apply Nat.eqb_neq in X; apply not_elem_names_add_intro;
      destruct H; split; try apply IHth; trivial.
  - destruct (x =? a) eqn:X; simpl; simpl in H.
    * apply Nat.eqb_eq in X; subst a; destruct H; trivial.
    * apply Nat.eqb_neq in X; apply not_elem_names_add_intro;
      destruct H; split; try apply IHth; trivial. Qed.
  
Lemma bindsC_remove_fromCS_subset : 
  forall (th : csub) (x : vname), 
      uniqueC th -> Subset (bindsC (remove_fromCS th x)) (bindsC th).
Proof. induction th; intros; simpl; simpl in H.
  - apply subset_empty_l.
  - destruct (x0 =? x) eqn:X; simpl; destruct H.
    * apply subset_add_intro; apply subset_refl.
    * apply subset_add_both_intro; apply IHth; apply H0. 
  - destruct (x =? a) eqn:X; simpl; destruct H.
    * apply subset_add_intro; apply subset_refl.
    * apply subset_add_both_intro; apply IHth; apply H0.
Qed.

Lemma lem_vbindsC_add_remove : forall (th : csub) (x : vname), 
      uniqueC th -> 
        Subset (vbindsC th) (names_add x (vbindsC (remove_fromCS th x))).
Proof. induction th; intros; simpl; simpl in H.
  - apply subset_empty_l.
  - destruct (x0 =? x) eqn:X; simpl; destruct H.
    * apply Nat.eqb_eq in X; subst x0; apply subset_refl.
    * apply subset_trans 
        with (names_add x (names_add x0 (vbindsC (remove_fromCS th x0))));
      try apply subset_add_commute;
      apply subset_add_both_intro; apply IHth; apply H0.
  - destruct (x =? a) eqn:X; simpl; destruct H.
    * apply subset_add_intro; apply subset_refl.
    * apply IHth; apply H0.
Qed.
  
Lemma lem_tvbindsC_add_remove : forall (th : csub) (x : vname), 
      uniqueC th -> 
        Subset (tvbindsC th) (names_add x (tvbindsC (remove_fromCS th x))).
Proof. induction th; intros; simpl; simpl in H.
  - apply subset_empty_l.
  - destruct (x0 =? x) eqn:X; simpl; destruct H.
    * apply subset_add_intro; apply subset_refl.
    * apply IHth; apply H0.
  - destruct (x =? a) eqn:X; simpl; destruct H.
    * apply Nat.eqb_eq in X; subst a. apply subset_refl.
    * apply subset_trans 
        with (names_add a (names_add x (tvbindsC (remove_fromCS th x))));
      try apply subset_add_commute;
      apply subset_add_both_intro; apply IHth; apply H0.
Qed.
  
Lemma lem_remove_fromCS_closed : forall (th:csub) (x:vname),
    closed th -> closed (remove_fromCS th x).
Proof. induction th; intros; trivial;
  simpl in H; destruct H; destruct H0.
  - destruct (x0 =? x) eqn:X; simpl; rewrite X; simpl; auto.
  - destruct (x =? a) eqn:X; simpl; rewrite X; simpl; auto.
Qed.
  
Lemma lem_remove_fromCS_substitutable : forall (th:csub) (x:vname),
    substitutable th -> substitutable (remove_fromCS th x).
Proof. induction th; intros; trivial;
  simpl in H; destruct H; try destruct H0.
  - destruct (x0 =? x) eqn:X; simpl; rewrite X; simpl; auto.
  - destruct (x =? a) eqn:X; simpl; rewrite X; simpl; auto.
Qed.
    
Lemma lem_remove_fromCS_uniqueC : forall (th:csub) (x:vname),
    uniqueC th -> uniqueC (remove_fromCS th x).
Proof. induction th; intros; trivial;
  simpl in H; destruct H.
  - destruct (x0 =? x) eqn:X; simpl; rewrite X; simpl; try split;
    try apply IHth; try apply not_elem_subset with (bindsC th);
    try apply bindsC_remove_fromCS_subset; trivial.
  - destruct (x =? a) eqn:X; simpl; rewrite X; simpl; try split;
    try apply IHth; try apply not_elem_subset with (bindsC th);
    try apply bindsC_remove_fromCS_subset; trivial.
Qed.
    
Fixpoint csubst_env (th0:csub) (g:env) : env :=
    match th0 with  
    | CEmpty            => g 
    | (CCons  z v_z th) => csubst_env th (esubFV  z v_z g)
    | (CConsT a t_a th) => csubst_env th (esubFTV a t_a g)
    end.
    