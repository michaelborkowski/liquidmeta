Require Import Arith.

Require Import SystemF.BasicDefinitions.
Require Import SystemF.Names.

(* Lemmas. The set of Values is closed under substitution. *)
Lemma lem_subFV_value : forall (y:vname) (v_y v: expr),
    isValue v_y -> isValue v -> isValue (subFV y v_y v).
Proof. intros y v_y v val_vy val_v. 
  destruct v; simpl in val_v; try contradiction;
  simpl; try (destruct (Nat.eqb y x)); simpl; assumption. Qed.

Lemma lem_subFTV_value : forall (a:vname) (t_a: ftype) (v: expr),
    isValue v -> isValue (subFTV a t_a v).
Proof. intros a t_a v val_v. 
  destruct v; simpl in val_v; try contradiction;
  simpl; try (destruct (Nat.eqb y x)); simpl; assumption. Qed.

Lemma lem_ftsubFV_notin : forall (a:vname) (t_a:ftype) (t:ftype),
    ~ Elem a (ffreeTV t) ->  ftsubFV a t_a t = t.
Proof. intros; induction t; simpl.
  - destruct b; try destruct (a =? a0) eqn:A; intuition. 
    apply Nat.eqb_eq in A; symmetry in A; subst a0; simpl in H; intuition.
  - simpl in H; apply not_elem_union_elim in H; destruct H;
    rewrite IHt1; try rewrite IHt2; intuition. 
  - simpl in H; rewrite IHt; intuition.
  Qed.

Lemma lem_subFV_notin : forall (e:expr) (x:vname) (v:expr) ,
    isValue v -> ~ Elem x (fv e) -> subFV x v e = e.
Proof. induction e; simpl; try reflexivity; intros
  ; (* 1 IH *) try ( f_equal; apply IHe; assumption )
  ; (* 2 IH *) try ( apply f_equal2; apply IHe1 || apply IHe2;
      apply not_elem_union_elim in H0; destruct H0; assumption )
  ; (* FV *) try (intuition; destruct (Nat.eqb x0 x) eqn:Eq;
      (apply Nat.eqb_eq in Eq; symmetry in Eq; contradiction) 
      || reflexivity ).
  Qed.

Lemma lem_subFTV_notin : forall (e:expr) (a:vname) (t_a:ftype),
    ~ Elem a (ftv e) -> subFTV a t_a e = e.
Proof. induction e; intros; simpl; try reflexivity
  ; (* 1 IH *) try (f_equal; apply IHe || apply lem_ftsubFV_notin; 
                    try (simpl in H; trivial);
                    try apply not_elem_union_elim in H; try destruct H; trivial)
  ; (* 2 IH *) try (apply f_equal2; apply IHe1 || apply IHe2; simpl in H; 
                    apply not_elem_union_elim in H; destruct H; trivial).
  Qed.

(*---------------------------------------------------------------------------
-- | TECHNICAL LEMMAS: Reduction of Unbinding to (Bound) Substitution
---------------------------------------------------------------------------*)

Lemma lem_open_at_is_subBV_at :forall (e:expr) (j:index) (y:vname),
    open_at j y e = subBV_at j (FV y) e.
Proof. induction e; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( f_equal; apply IHe )
  ; (* 2 IH *) try ( apply f_equal2; apply IHe1 || apply IHe2 ).
  Qed.

Lemma lem_unbind_is_subBV : forall (y:vname) (e:expr),
    unbind y e = subBV (FV y) e. 
Proof. intros; apply lem_open_at_is_subBV_at. Qed.

Lemma lem_openFT_at_is_ftsubBV_at : forall (t:ftype) (j:index) (a:vname),
    openFT_at j a t = ftsubBV_at j (FTBasic (FTV a)) t.
Proof. intro t; induction t; intros; simpl.
  - (* FTBasic *) destruct b; try destruct (j =? i); reflexivity.
  - (* FTFunc *) apply f_equal2; apply IHt1 || apply IHt2.
  - (* FTPoly *) apply f_equal; apply IHt.
  Qed.

Lemma lem_open_tv_at_is_subBTV_at : forall (e:expr) (j:index) (a:vname),
    open_tv_at j a e = subBTV_at j (FTBasic (FTV a)) e.
Proof. induction e; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( f_equal; apply IHe || apply lem_openFT_at_is_ftsubBV_at )
  ; (* 2 IH *) try ( apply f_equal2; apply IHe1 || apply IHe2 ).
  Qed.

Lemma lem_unbind_tv_is_subBTV : forall (a:vname) (e:expr),
    unbind_tv a e = subBTV (FTBasic (FTV a)) e. 
Proof. intros; apply lem_open_tv_at_is_subBTV_at. Qed.

(*---------------------------------------------------------------------------
-- | TECHNICAL LEMMAS: Local Closure
---------------------------------------------------------------------------*)

Lemma lem_subBV_at_lc_at : forall (e:expr) (j:index) (v:expr) (kx:index) (ka:index),
    isValue v -> kx <= j -> isLC_at kx ka e -> subBV_at j v e = e.
Proof. induction e; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( f_equal; simpl in H1; try destruct H1; revert H1;  
                     apply IHe; try apply plus_le_compat_r; assumption)
  ; (* 2 IH *) try ( apply f_equal2; simpl in H1; destruct H1; 
                     (revert H1; apply IHe1) || (revert H2; apply IHe2); 
                     try apply plus_le_compat_r; assumption ).
  - (* BV *) destruct (j =? i) eqn:J; simpl in H1.
      * apply Nat.lt_le_trans with i kx j in H1; try assumption.
        apply Nat.lt_neq in H1; apply Nat.neq_sym in H1;
        apply Nat.eqb_neq in H1. rewrite J in H1. discriminate.
      * reflexivity.
  Qed.
  
Lemma lem_subBV_lc : forall (v:expr) (e:expr),
    isValue v -> isLC e -> subBV v e = e.
Proof. intros; apply lem_subBV_at_lc_at with 0 0; intuition. Qed.

Lemma lem_open_at_lc_at : forall (e:expr) (j k:index) (x:vname),
    isLC_at j k e -> open_at j x e = e.
Proof. intros; rewrite lem_open_at_is_subBV_at.
  apply lem_subBV_at_lc_at with j k; simpl; intuition. Qed.

Lemma lem_unbind_lc : forall (x:vname) (e:expr),
    isLC e -> unbind x e = e.
Proof. intros; rewrite lem_unbind_is_subBV; apply lem_subBV_lc; 
  simpl; trivial. Qed.

Lemma lem_islcft_at_ftsubBV_at : forall (t:ftype) (j:index) (t_j:ftype) (k:index),
    k <= j -> isLCFT_at k t ->  ftsubBV_at j t_j t = t. 
Proof. intros t; induction t; intros; simpl.
  - (* FTBasic *) destruct b; simpl in H0; try reflexivity. 
    apply lt_le_trans with i k j in H0; try assumption. 
    apply Nat.lt_neq in H0; apply Nat.neq_sym in H0;
    apply Nat.eqb_neq in H0; rewrite H0; reflexivity.
  - (* FTFunc *) simpl in H0; destruct H0.  
    apply (IHt1 j t_j k H) in H0; apply (IHt2 j t_j k H) in H1; 
    rewrite H0; rewrite H1; reflexivity.
  - (* FTPoly *) simpl in H0. apply plus_le_compat_r with k0 j 1 in H.
    apply (IHt (j+1) t_j (k0+1) H) in H0; rewrite H0; reflexivity.
  Qed.

Lemma lem_subBTV_at_lc_at : forall (e:expr) (j:index) (t_a:ftype) (kx:index) (ka:index),
    ka <= j -> isLC_at kx ka e -> subBTV_at j t_a e = e.
Proof. induction e; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( f_equal; simpl in H0; try destruct H0; 
                     (revert H0; apply IHe) 
                        || (revert H1; apply lem_islcft_at_ftsubBV_at); 
                     try apply plus_le_compat_r; assumption)
  ; (* 2 IH *) try ( apply f_equal2; simpl in H0; destruct H0; 
                     (revert H0; apply IHe1) || (revert H1; apply IHe2); 
                     try apply plus_le_compat_r; assumption ).
  Qed.

Lemma lem_subBTV_lc : forall (t_a:ftype) (e:expr),
    isLC e -> subBTV t_a e = e.
Proof. intros; apply lem_subBTV_at_lc_at with 0 0; intuition. Qed.

Lemma lem_unbind_tv_lc : forall (a:vname) (e:expr),
    isLC e -> unbind_tv a e = e.
Proof. intros; rewrite lem_unbind_tv_is_subBTV; apply lem_subBTV_lc; 
  simpl; trivial. Qed.

(*---------------------------------------------------------------------------
-- | BASIC PROPERTIES: Compositional Properties of SUBSTITUTION
---------------------------------------------------------------------------*)

Lemma lem_subFV_open_at : forall (e:expr) (j:index) (y:vname) (v:expr),
    isValue v -> ~ Elem y (fv e) -> subBV_at j v e = subFV y v (open_at j y e).
Proof. induction e; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H; assumption)
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0;
    apply not_elem_union_elim in H2; destruct H2; assumption ).
  - (* BV *) destruct (j =? i); simpl; 
    assert (y =? y = true) by (apply Nat.eqb_eq; reflexivity); try rewrite H1;
    reflexivity.
  - (* FV *) simpl in H0; intuition; apply Nat.neq_sym in H1; 
    apply Nat.eqb_neq in H1; rewrite H1; reflexivity.
  Qed.

Lemma lem_subFV_unbind : forall (y:vname) (v:expr) (e:expr),
    isValue v -> ~ Elem y (fv e) -> subBV v e = subFV y v (unbind y e).
Proof. intros; apply lem_subFV_open_at; assumption. Qed.

Lemma lem_subFTV_open_tv_at : (forall (e:expr) (j:index) (a:vname) (t_a:type),
    noExists t_a -> ~ Elem a (ftv e) 
                 -> subBTV_at j t_a e = subFTV a t_a (open_tv_at j a e) ) * ((
  forall (t:type) (j:index) (a:vname) (t_a:type),
    noExists t_a -> ~ Elem a (freeTV t) 
                 -> tsubBTV_at j t_a t = tsubFTV a t_a (open_tvT_at j a t) ) * (
  forall (ps:preds) (j:index) (a:vname) (t_a:type),
    noExists t_a -> ~ Elem a (ftvP ps) 
                 -> psubBTV_at j t_a ps = psubFTV a t_a (open_tvP_at j a ps) )).
Proof. apply ( syntax_mutind
  (fun e : expr => forall (j:index) (a:vname) (t_a:type),
      noExists t_a -> ~ Elem a (ftv e) 
                   -> subBTV_at j t_a e = subFTV a t_a (open_tv_at j a e))
  (fun t : type => forall (j:index) (a:vname) (t_a:type),
      noExists t_a -> ~ Elem a (freeTV t) 
                   -> tsubBTV_at j t_a t = tsubFTV a t_a (open_tvT_at j a t))
  (fun ps: preds => forall (j:index) (a:vname) (t_a:type),
      noExists t_a -> ~ Elem a (ftvP ps) 
                   -> psubBTV_at j t_a ps = psubFTV a t_a (open_tvP_at j a ps)))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H; assumption)
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0;
    apply not_elem_union_elim in H2; destruct H2; assumption ).
  - (* TRefn *) destruct b; simpl;
    try ( apply f_equal; apply H; assumption).
    * (* BTV *) destruct (j =? i); simpl;
      assert (a =? a = true) by (apply Nat.eqb_eq; reflexivity); try rewrite H2;
      apply f_equal2; try apply H; intuition.
    * (* FTV *) simpl in H1; apply not_elem_names_add_elim in H1;
      destruct H1; apply Nat.eqb_neq in H1; rewrite H1;
      apply f_equal2; try apply H; intuition.
  Qed.

Lemma lem_subFTV_unbind_tv : forall (a:vname) (t_a:type) (e:expr),
    noExists t_a -> ~ Elem a (ftv e) -> subBTV t_a e = subFTV a t_a (unbind_tv a e).
Proof. intros; apply lem_subFTV_open_tv_at; assumption. Qed.

(*---------------------------------------------------------------------------
-- | BASIC PROPERTIES: Commutative Properties of SUBSTITUTION with Itself
---------------------------------------------------------------------------*)

Lemma lem_commute_subFV_subBV_at : (forall (e:expr) (j:index) (v:expr) (y:vname) (v_y:expr),
    isValue v -> isValue v_y -> isLC v_y 
      -> subFV y v_y (subBV_at j v e) = subBV_at j (subFV y v_y v) (subFV y v_y e) ) * ((
  forall (t:type) (j:index) (v:expr) (y:vname) (v_y:expr),
    isValue v -> isValue v_y -> isLC v_y 
      -> tsubFV y v_y (tsubBV_at j v t) = tsubBV_at j (subFV y v_y v) (tsubFV y v_y t) ) * (
  forall (ps:preds) (j:index) (v:expr) (y:vname) (v_y:expr),
    isValue v -> isValue v_y -> isLC v_y 
      -> psubFV y v_y (psubBV_at j v ps) = psubBV_at j (subFV y v_y v) (psubFV y v_y ps) )).
Proof. apply ( syntax_mutind
  (fun e : expr => forall (j:index) (v:expr) (y:vname) (v_y:expr),
    isValue v -> isValue v_y -> isLC v_y 
      -> subFV y v_y (subBV_at j v e) = subBV_at j (subFV y v_y v) (subFV y v_y e) )
  (fun t : type => forall (j:index) (v:expr) (y:vname) (v_y:expr),
    isValue v -> isValue v_y -> isLC v_y 
      -> tsubFV y v_y (tsubBV_at j v t) = tsubBV_at j (subFV y v_y v) (tsubFV y v_y t) )
  (fun ps : preds => forall (j:index) (v:expr) (y:vname) (v_y:expr),
    isValue v -> isValue v_y -> isLC v_y 
      -> psubFV y v_y (psubBV_at j v ps) = psubBV_at j (subFV y v_y v) (psubFV y v_y ps) ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H; assumption)
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0; assumption ).
  - (* BV *) destruct (j =? i); simpl; reflexivity.
  - (* FV *) destruct (y =? x); try reflexivity. 
    apply lem_subFV_value with y v_y v in H; try assumption; symmetry.
    apply lem_subBV_at_lc_at with 0 0; intuition. Qed.
    
Lemma lem_commute_subFV_subBV : forall (v:expr) (y:vname) (v_y:expr) (e:expr),
    isValue v -> isValue v_y -> isLC v_y 
      -> subFV y v_y (subBV v e) = subBV (subFV y v_y v) (subFV y v_y e).
Proof. intros. apply lem_commute_subFV_subBV_at; assumption. Qed.
     
Lemma lem_commute_subFV_unbind : forall (y:vname) (x:vname) (v:expr) (e:expr),
    x <> y -> isValue v -> isLC v 
      -> subFV x v (unbind y e) = unbind y (subFV x v e).
Proof. intros; repeat rewrite lem_unbind_is_subBV.
  apply Nat.eqb_neq in H.
  assert (subFV x v (FV y) = FV y) as H2 by (simpl; rewrite H; reflexivity).
  rewrite lem_commute_subFV_subBV; try rewrite H2; simpl; trivial.
  Qed.


Lemma lem_commute_subFV_subBTV_at : (forall (e:expr) (j:index) (t_a:type) (y:vname) (v_y:expr),
    noExists t_a -> isValue v_y -> isLC v_y 
      -> subFV y v_y (subBTV_at j t_a e) = subBTV_at j (tsubFV y v_y t_a) (subFV y v_y e) ) * ((
  forall (t:type) (j:index) (t_a:type) (y:vname) (v_y:expr),
    noExists t_a -> isValue v_y -> isLC v_y 
      -> tsubFV y v_y (tsubBTV_at j t_a t) = tsubBTV_at j (tsubFV y v_y t_a) (tsubFV y v_y t) ) * (
  forall (ps:preds) (j:index) (t_a:type) (y:vname) (v_y:expr),
    noExists t_a -> isValue v_y -> isLC v_y 
      -> psubFV y v_y (psubBTV_at j t_a ps) = psubBTV_at j (tsubFV y v_y t_a) (psubFV y v_y ps) )).
Proof. apply ( syntax_mutind
  (fun e : expr => forall (j:index) (t_a:type) (y:vname) (v_y:expr),
    noExists t_a -> isValue v_y -> isLC v_y 
      -> subFV y v_y (subBTV_at j t_a e) = subBTV_at j (tsubFV y v_y t_a) (subFV y v_y e) )
  (fun t : type => forall (j:index) (t_a:type) (y:vname) (v_y:expr),
    noExists t_a -> isValue v_y -> isLC v_y 
      -> tsubFV y v_y (tsubBTV_at j t_a t) = tsubBTV_at j (tsubFV y v_y t_a) (tsubFV y v_y t) )
  (fun ps : preds => forall (j:index) (t_a:type) (y:vname) (v_y:expr),
    noExists t_a -> isValue v_y -> isLC v_y 
      -> psubFV y v_y (psubBTV_at j t_a ps) = psubBTV_at j (tsubFV y v_y t_a) (psubFV y v_y ps) ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H; assumption)
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0; assumption ).
  - (* FV *) destruct (y =? x); try reflexivity. 
    apply lemma_tsubFV_noExists with y v_y t_a in H; try assumption; symmetry.
    apply lem_subBTV_at_lc_at with 0 0; intuition.
  - (* TRefn *) destruct b; try destruct (j =? i) eqn:J; simpl;
    try apply f_equal; try apply H; try assumption.
    * (* BTV j *) rewrite <- H; try rewrite lem_subFV_push; trivial.
  Qed.

Lemma lem_commute_subFV_subBTV : forall (t_a:type) (y:vname) (v_y:expr) (e:expr),
    noExists t_a -> isValue v_y -> isLC v_y 
        -> subFV y v_y (subBTV t_a e) = subBTV (tsubFV y v_y t_a) (subFV y v_y e).
Proof. intros; apply lem_commute_subFV_subBTV_at; assumption. Qed.

Lemma lem_commute_subFV_unbind_tv : forall (a:vname) (x:vname) (v:expr) (e:expr),
    x <> a -> isValue v -> isLC v 
        -> subFV x v (unbind_tv a e) = unbind_tv a (subFV x v e).
Proof. intros; repeat rewrite lem_unbind_tv_is_subBTV.
  apply Nat.eqb_neq in H.
  assert (tsubFV x v (TRefn (FTV a) PEmpty) = (TRefn (FTV a) PEmpty)) by (reflexivity).
  rewrite lem_commute_subFV_subBTV; try rewrite H2; simpl; trivial.
  Qed. 


Lemma lem_commute_subFTV_subBV_at : (forall (e:expr) (j:index) (v:expr) (a:vname) (t_a:type),
    isValue v -> noExists t_a -> isLCT t_a
      -> subFTV a t_a (subBV_at j v e) = subBV_at j (subFTV a t_a v) (subFTV a t_a e) ) * ((
  forall (t:type) (j:index) (v:expr) (a:vname) (t_a:type),
    isValue v -> noExists t_a -> isLCT t_a 
      -> tsubFTV a t_a (tsubBV_at j v t) = tsubBV_at j (subFTV a t_a v) (tsubFTV a t_a t) ) * (
  forall (ps:preds) (j:index) (v:expr) (a:vname) (t_a:type),
    isValue v -> noExists t_a -> isLCT t_a
      -> psubFTV a t_a (psubBV_at j v ps) = psubBV_at j (subFTV a t_a v) (psubFTV a t_a ps) )).
Proof. apply ( syntax_mutind
  (fun e : expr => forall (j:index) (v:expr) (a:vname) (t_a:type),
    isValue v -> noExists t_a -> isLCT t_a
      -> subFTV a t_a (subBV_at j v e) = subBV_at j (subFTV a t_a v) (subFTV a t_a e) )
  (fun t : type => forall (j:index) (v:expr) (a:vname) (t_a:type),
    isValue v -> noExists t_a -> isLCT t_a
      -> tsubFTV a t_a (tsubBV_at j v t) = tsubBV_at j (subFTV a t_a v) (tsubFTV a t_a t) )
  (fun ps : preds => forall (j:index) (v:expr) (a:vname) (t_a:type),
    isValue v -> noExists t_a -> isLCT t_a
      -> psubFTV a t_a (psubBV_at j v ps) = psubBV_at j (subFTV a t_a v) (psubFTV a t_a ps) ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H; assumption)
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0; assumption ).
  - (* BV *) destruct (j =? i); reflexivity.
  - (* TRefn *) destruct b; try destruct (a =? a0) eqn:A; simpl;
    try apply f_equal; try apply H; try assumption.
    (* FTV a *) symmetry; rewrite lem_subBV_at_push; try rewrite <- H;
      try apply f_equal; try apply lem_subBV_at_lc_at with 0 0;
      try apply lem_subFTV_value; intuition. 
  Qed.
    
Lemma lem_commute_subFTV_subBV : forall (v:expr) (a:vname) (t_a:type) (e:expr),
    isValue v -> noExists t_a -> isLCT t_a 
        -> subFTV a t_a (subBV v e) = subBV (subFTV a t_a v) (subFTV a t_a e).
Proof. intros; apply lem_commute_subFTV_subBV_at; assumption. Qed.


Lemma lem_commute_subFTV_unbind : forall (x:vname) (a:vname) (t_a:type) (e:expr),
    a <> x -> noExists t_a -> isLCT t_a 
        -> subFTV a t_a (unbind x e) = unbind x (subFTV a t_a e).
Proof. intros; repeat rewrite lem_unbind_is_subBV.
  apply Nat.eqb_neq in H.
  assert (subFTV a t_a (FV x) = (FV x)) by (reflexivity).
  rewrite lem_commute_subFTV_subBV; try rewrite H2; simpl; trivial.
  Qed. 


Lemma lem_commute_subFTV_subBTV_at : (forall (e:expr) (j:index) (t_j:type) (a:vname) (t_a:type),
    noExists t_j -> noExists t_a -> isLCT t_a  
      -> subFTV a t_a (subBTV_at j t_j e) = subBTV_at j (tsubFTV a t_a t_j) (subFTV a t_a e) ) * ((
  forall (t:type) (j:index) (t_j:type) (a:vname) (t_a:type),
    noExists t_j -> noExists t_a -> isLCT t_a 
      -> tsubFTV a t_a (tsubBTV_at j t_j t) = tsubBTV_at j (tsubFTV a t_a t_j) (tsubFTV a t_a t) ) * (
  forall (ps:preds) (j:index) (t_j:type) (a:vname) (t_a:type),
    noExists t_j -> noExists t_a -> isLCT t_a 
      -> psubFTV a t_a (psubBTV_at j t_j ps) = psubBTV_at j (tsubFTV a t_a t_j) (psubFTV a t_a ps) )).
Proof. apply ( syntax_mutind
  (fun e : expr => forall (j:index) (t_j:type) (a:vname) (t_a:type),
    noExists t_j -> noExists t_a -> isLCT t_a 
      -> subFTV a t_a (subBTV_at j t_j e) = subBTV_at j (tsubFTV a t_a t_j) (subFTV a t_a e) )
  (fun t : type => forall (j:index) (t_j:type) (a:vname) (t_a:type),
    noExists t_j -> noExists t_a -> isLCT t_a 
      -> tsubFTV a t_a (tsubBTV_at j t_j t) = tsubBTV_at j (tsubFTV a t_a t_j) (tsubFTV a t_a t) )
  (fun ps : preds => forall (j:index) (t_j:type) (a:vname) (t_a:type),
    noExists t_j -> noExists t_a -> isLCT t_a 
      -> psubFTV a t_a (psubBTV_at j t_j ps) = psubBTV_at j (tsubFTV a t_a t_j) (psubFTV a t_a ps) ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H; assumption)
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0; assumption ).
  - (* TRefn *) destruct b eqn:B; simpl; try destruct (j =? i); try destruct (a =? a0); 
    simpl; try apply f_equal; try apply H; try assumption.
    * (* BTV j *) symmetry; rewrite lem_subFTV_push; try rewrite <- H; trivial.
    * (* FTV a *) symmetry; rewrite lem_subBTV_at_push; try rewrite <- H;
      try apply f_equal; try apply lem_subBTV_at_lc_at with 0 0;
      try apply lemma_tsubFTV_noExists; intuition.
  Qed.
  
Lemma lem_commute_subFTV_subBTV : forall (t':type) (a:vname) (t_a:type) (e:expr),
    noExists t' -> noExists t_a -> isLCT t_a 
        -> subFTV a t_a (subBTV t' e) = subBTV (tsubFTV a t_a t') (subFTV a t_a e).
Proof. intros; apply lem_commute_subFTV_subBTV_at; assumption. Qed.

Lemma lem_commute_subFTV_unbind_tv : forall (a':vname) (a:vname) (t_a:type) (e:expr),
    a <> a' -> noExists t_a -> isLCT t_a
        -> subFTV a t_a (unbind_tv a' e) = unbind_tv a' (subFTV a t_a e).
Proof. intros; repeat rewrite lem_unbind_tv_is_subBTV.
  apply Nat.eqb_neq in H.
  assert (tsubFTV a t_a (TRefn (FTV a') PEmpty) = (TRefn (FTV a') PEmpty)) 
    by (simpl; rewrite H; reflexivity).
  rewrite lem_commute_subFTV_subBTV; try rewrite H2; simpl; trivial.
  Qed. 

(*---------------------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of SUBSTITUTION for TYPE VARIABLES in SYSTEM F TYPES
---------------------------------------------------------------------------------------*)

Lemma lem_islcft_at_openFT_at : forall (t:ftype) (j:index) (a:vname) (k:index),
    k <= j -> isLCFT_at k t -> openFT_at j a t = t.
Proof. intros; rewrite lem_openFT_at_is_ftsubBV_at; 
  apply lem_islcft_at_ftsubBV_at with k; assumption. Qed.

Lemma lem_ftsubFV_openFT_at : forall (t:ftype) (j:index) (a':vname) (t_a:ftype),
    ~ Elem a' (ffreeTV t) -> ftsubBV_at j t_a t = ftsubFV a' t_a (openFT_at j a' t).
Proof. induction t; intros; simpl.
  - (* FTBasic *) destruct b; simpl; try reflexivity.
      * (* FTV *) destruct (j =? i); 
        assert (a' =? a' = true) by (apply Nat.eqb_eq; reflexivity); 
        simpl; try rewrite H0; reflexivity.
      * (* BTV *) simpl in H; intuition; apply Nat.neq_sym in H0;
        apply Nat.eqb_neq in H0; rewrite H0; reflexivity.
  - (* FTFunc *) rewrite <- IHt1; try rewrite <- IHt2;
      simpl in H; apply not_elem_union_elim in H; destruct H;   
      trivial.
  - (* FTPoly *) rewrite <- IHt; simpl in H; trivial.
  Qed.

Lemma lem_ftsubFV_unbindFT : forall (a':vname) (t_a:ftype) (t:ftype),
    ~ Elem a' (ffreeTV t) -> ftsubBV t_a t = ftsubFV a' t_a (unbindFT a' t).
Proof. intros. apply lem_ftsubFV_openFT_at; assumption. Qed.

Lemma lem_commute_ftsubFV_ftsubBV_at : 
  forall (t:ftype) (a:vname) (t_a:ftype) (j:index) (t_j:ftype),
    isLCFT t_a 
      -> ftsubFV a t_a (ftsubBV_at j t_j t) = ftsubBV_at j (ftsubFV a t_a t_j) (ftsubFV a t_a t).
Proof. induction t; intros; simpl.
  - (* FTBasic *) destruct b; simpl; try reflexivity.
      * destruct (j =? i); simpl; reflexivity.
      * destruct (a =? a0); simpl;       
        try symmetry; try apply lem_islcft_at_ftsubBV_at with 0; intuition.
  - (* FTFunc *) simpl; rewrite IHt1; try (rewrite IHt2); trivial.
  - (* FTPoly *) simpl. rewrite IHt; trivial.
  Qed. 

Lemma lem_commute_ftsubFV_ftsubBV : 
  forall (t_j:ftype) (a:vname) (t_a:ftype) (t:ftype),
    isLCFT t_a 
      -> ftsubFV a t_a (ftsubBV t_j t) = ftsubBV (ftsubFV a t_a t_j) (ftsubFV a t_a t).
Proof. intros; apply lem_commute_ftsubFV_ftsubBV_at; assumption. Qed.

Lemma lem_commute_ftsubFV_openFT_at : 
  forall (t:ftype) (a0:vname) (t_a0:ftype) (j:index) (a:vname),
    a0 <> a -> isLCFT t_a0 
            -> ftsubFV a0 t_a0 (openFT_at j a t) = openFT_at j a (ftsubFV a0 t_a0 t).
Proof. intros; repeat rewrite lem_openFT_at_is_ftsubBV_at;
  apply Nat.eqb_neq in H;
  assert (ftsubFV a0 t_a0 (FTBasic (FTV a)) = FTBasic (FTV a))
    by (simpl; rewrite H; reflexivity).
  rewrite lem_commute_ftsubFV_ftsubBV_at; try rewrite H1; trivial.
  Qed. 

Lemma lem_commute_ftsubFV_unbindFT : forall (a0:vname) (t_a0:ftype) (a:vname) (t:ftype),
    a0 <> a -> isLCFT t_a0
            -> ftsubFV a0 t_a0 (unbindFT a t) = unbindFT a (ftsubFV a0 t_a0 t) .
Proof. unfold unbindFT; intros; apply lem_commute_ftsubFV_openFT_at; assumption. Qed.