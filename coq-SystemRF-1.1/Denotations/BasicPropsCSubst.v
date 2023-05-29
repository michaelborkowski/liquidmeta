Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.Strengthenings.
Require Import SystemRF.LocalClosure.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.Typing.
Require Import Denotations.ClosingSubstitutions.

Require Import Arith.

  (* -- | More Properties of Substitution *)

Lemma lem_commute_subFV' : (forall (e:expr) (x:vname) (v:expr) (y:vname) (v_y:expr),
    y <> x -> ~ Elem x (fv v_y) -> ~ Elem y (fv v)
      -> subFV y v_y (subFV x v e) = subFV x v (subFV y v_y e) ) * ((
  forall (t:type) (x:vname) (v:expr) (y:vname) (v_y:expr),
    y <> x -> ~ Elem x (fv v_y) -> ~ Elem y (fv v)
      -> tsubFV y v_y (tsubFV x v t) = tsubFV x v (tsubFV y v_y t) ) * (
  forall (ps:preds) (x:vname) (v:expr) (y:vname) (v_y:expr),
    y <> x -> ~ Elem x (fv v_y) -> ~ Elem y (fv v)
      -> psubFV y v_y (psubFV x v ps) = psubFV x v (psubFV y v_y ps) )).
Proof. apply ( syntax_mutind
  (fun e : expr => forall (x:vname) (v:expr) (y:vname) (v_y:expr),
    y <> x -> ~ Elem x (fv v_y) -> ~ Elem y (fv v)
      -> subFV y v_y (subFV x v e) = subFV x v (subFV y v_y e) )
  (fun t : type => forall (x:vname) (v:expr) (y:vname) (v_y:expr),
    y <> x -> ~ Elem x (fv v_y) -> ~ Elem y (fv v)
      -> tsubFV y v_y (tsubFV x v t) = tsubFV x v (tsubFV y v_y t) )
  (fun ps : preds => forall (x:vname) (v:expr) (y:vname) (v_y:expr),
    y <> x -> ~ Elem x (fv v_y) -> ~ Elem y (fv v)
      -> psubFV y v_y (psubFV x v ps) = psubFV x v (psubFV y v_y ps) ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H; assumption)
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0; assumption ).
  - (* FV *) destruct (Nat.eqb x0 x) eqn:E0; 
    destruct (Nat.eqb y x) eqn:E; simpl;
    try rewrite E0; try rewrite E; try reflexivity;
    (* both E0 and E cannot be true *)
    try apply Nat.eqb_eq in E0; try apply Nat.eqb_eq in E;
    try rewrite E0 in H; try rewrite E in H; try contradiction;
    apply lem_subFV_notin || (symmetry; apply lem_subFV_notin); assumption.
  - (* If *) rewrite H; try rewrite H0; try rewrite H1; trivial.
  Qed.

Lemma lem_commute_subFV : forall (e:expr) (x:vname) (v:expr) (y:vname) (v_y:expr),
    y <> x -> ~ Elem x (fv v_y) -> ~ Elem y (fv v)
      -> subFV y v_y (subFV x v e) = subFV x v (subFV y v_y e).
Proof. intros; apply lem_commute_subFV'; assumption. Qed.

Lemma lem_commute_tsubFV : forall (t:type) (x:vname) (v:expr) (y:vname) (v_y:expr),
y <> x -> ~ Elem x (fv v_y) -> ~ Elem y (fv v)
  -> tsubFV y v_y (tsubFV x v t) = tsubFV x v (tsubFV y v_y t).
Proof. intros; apply lem_commute_subFV'; assumption. Qed.  

Lemma lem_commute_subFV_subFTV' : (forall (e:expr) (a:vname) (t_a:type) (y:vname) (v_y:expr),
    noExists t_a -> isValue v_y -> ~ Elem a (ftv v_y) -> ~ Elem y (free t_a)
      -> subFV y v_y (subFTV a t_a e) = subFTV a t_a (subFV y v_y e) ) * ((
  forall (t:type) (a:vname) (t_a:type) (y:vname) (v_y:expr),
    noExists t_a -> isValue v_y -> ~ Elem a (ftv v_y) -> ~ Elem y (free t_a)
      -> tsubFV y v_y (tsubFTV a t_a t) = tsubFTV a t_a (tsubFV y v_y t) ) * (
  forall (ps:preds) (a:vname) (t_a:type) (y:vname) (v_y:expr),
    noExists t_a -> isValue v_y -> ~ Elem a (ftv v_y) -> ~ Elem y (free t_a)
      -> psubFV y v_y (psubFTV a t_a ps) = psubFTV a t_a (psubFV y v_y ps) )).
Proof. apply ( syntax_mutind
  (fun e : expr => forall (a:vname) (t_a:type) (y:vname) (v_y:expr),
    noExists t_a -> isValue v_y -> ~ Elem a (ftv v_y) -> ~ Elem y (free t_a)
      -> subFV y v_y (subFTV a t_a e) = subFTV a t_a (subFV y v_y e) )
  (fun t : type => forall (a:vname) (t_a:type) (y:vname) (v_y:expr),
    noExists t_a -> isValue v_y -> ~ Elem a (ftv v_y) -> ~ Elem y (free t_a)
      -> tsubFV y v_y (tsubFTV a t_a t) = tsubFTV a t_a (tsubFV y v_y t) )
  (fun ps : preds => forall (a:vname) (t_a:type) (y:vname) (v_y:expr),
    noExists t_a -> isValue v_y -> ~ Elem a (ftv v_y) -> ~ Elem y (free t_a)
      -> psubFV y v_y (psubFTV a t_a ps) = psubFTV a t_a (psubFV y v_y ps) ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H; assumption)
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0; assumption ).
  - (* FV *) destruct (Nat.eqb y x) eqn:E; simpl;
    try rewrite E; try reflexivity;
    symmetry; apply lem_subFTV_notin; assumption.
  - (* If *) rewrite H; try rewrite H0; try rewrite H1; trivial.
  - (* TRefn *) destruct b eqn:Eb; simpl; try rewrite H; trivial.
    destruct (a =? a0); simpl; try rewrite lem_subFV_push;
    try rewrite H; try f_equal; try apply lem_subFV_notin; trivial.
  Qed. 

Lemma lem_commute_subFV_subFTV : forall (e:expr) (a:vname) (t_a:type) (y:vname) (v_y:expr),
    noExists t_a -> isValue v_y -> ~ Elem a (ftv v_y) -> ~ Elem y (free t_a)
      -> subFV y v_y (subFTV a t_a e) = subFTV a t_a (subFV y v_y e).
Proof.  intros; apply lem_commute_subFV_subFTV'; assumption. Qed.

Lemma lem_commute_tsubFV_tsubFTV : 
  forall (t:type) (a:vname) (t_a:type) (y:vname) (v_y:expr),
    noExists t_a -> isValue v_y -> ~ Elem a (ftv v_y) -> ~ Elem y (free t_a)
      -> tsubFV y v_y (tsubFTV a t_a t) = tsubFTV a t_a (tsubFV y v_y t).
Proof.  intros; apply lem_commute_subFV_subFTV'; assumption. Qed.

Lemma lem_commute_subFTV' : (
  forall (e:expr) (a:vname) (t_a:type) (a':vname) (t_a':type),
    noExists t_a -> noExists t_a' -> a' <> a 
      -> ~ Elem a (freeTV t_a') -> ~ Elem a' (freeTV t_a)
      -> subFTV a' t_a' (subFTV a t_a e) = subFTV a t_a (subFTV a' t_a' e) ) * ((
  forall (t:type) (a:vname) (t_a:type) (a':vname) (t_a':type),
    noExists t_a -> noExists t_a' -> a' <> a 
      -> ~ Elem a (freeTV t_a') -> ~ Elem a' (freeTV t_a)
      -> tsubFTV a' t_a' (tsubFTV a t_a t) = tsubFTV a t_a (tsubFTV a' t_a' t) ) * (
  forall (ps:preds) (a:vname) (t_a:type) (a':vname) (t_a':type),
    noExists t_a -> noExists t_a' -> a' <> a 
      -> ~ Elem a (freeTV t_a') -> ~ Elem a' (freeTV t_a)
      -> psubFTV a' t_a' (psubFTV a t_a ps) = psubFTV a t_a (psubFTV a' t_a' ps) )).
Proof. apply ( syntax_mutind
  (fun e : expr => forall (a:vname) (t_a:type) (a':vname) (t_a':type),
    noExists t_a -> noExists t_a' -> a' <> a 
      -> ~ Elem a (freeTV t_a') -> ~ Elem a' (freeTV t_a)
      -> subFTV a' t_a' (subFTV a t_a e) = subFTV a t_a (subFTV a' t_a' e) )
  (fun t : type => forall (a:vname) (t_a:type) (a':vname) (t_a':type),
    noExists t_a -> noExists t_a' -> a' <> a 
      -> ~ Elem a (freeTV t_a') -> ~ Elem a' (freeTV t_a)
      -> tsubFTV a' t_a' (tsubFTV a t_a t) = tsubFTV a t_a (tsubFTV a' t_a' t) )
  (fun ps : preds => forall (a:vname) (t_a:type) (a':vname) (t_a':type),
    noExists t_a -> noExists t_a' -> a' <> a 
      -> ~ Elem a (freeTV t_a') -> ~ Elem a' (freeTV t_a)
      -> psubFTV a' t_a' (psubFTV a t_a ps) = psubFTV a t_a (psubFTV a' t_a' ps) ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H; assumption)
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0; assumption ).
  - (* If *) rewrite H; try rewrite H0; try rewrite H1; trivial.
  - (* TRefn *) destruct b eqn:Eb; simpl; try rewrite H; trivial.
    destruct (a =? a0) eqn:Ea; destruct (a' =? a0) eqn:Ea'; 
    simpl; try rewrite Ea; try rewrite Ea';
    (* both E0 and E cannot be true *)
      try apply Nat.eqb_eq in Ea; try apply Nat.eqb_eq in Ea';
      try rewrite Ea in H2; try rewrite Ea' in H2; try contradiction;
    try rewrite lem_subFTV_push; try rewrite H; try f_equal;
    try apply lem_subFTV_notin; try (symmetry; apply lem_subFTV_notin);
    try subst a0; trivial.
  Qed.

Lemma lem_commute_subFTV : forall (e:expr) (a:vname) (t_a:type) (a':vname) (t_a':type),
    noExists t_a -> noExists t_a' -> a' <> a 
      -> ~ Elem a (freeTV t_a') -> ~ Elem a' (freeTV t_a)
      -> subFTV a' t_a' (subFTV a t_a e) = subFTV a t_a (subFTV a' t_a' e).
Proof. intros; apply lem_commute_subFTV'; assumption. Qed.  

Lemma lem_commute_tsubFTV : forall (t:type) (a:vname) (t_a:type) (a':vname) (t_a':type),
    noExists t_a -> noExists t_a' -> a' <> a 
      -> ~ Elem a (freeTV t_a') -> ~ Elem a' (freeTV t_a)
      -> tsubFTV a' t_a' (tsubFTV a t_a t) = tsubFTV a t_a (tsubFTV a' t_a' t).     
Proof. intros; apply lem_commute_subFTV'; assumption. Qed.  

  (* -- | Closing Substitution Properties *)

Lemma lem_unroll_csubst_left : forall (th:csub) (x:vname) (v_x e:expr),
    ~ in_csubst x th -> fv v_x = empty /\ ftv v_x = empty -> isValue v_x
        -> closed th -> substitutable th
        -> csubst (CCons x v_x th) e = subFV x v_x (csubst th e).
Proof. induction th; intros; simpl; try reflexivity;
  unfold in_csubst in H; simpl in H; 
  apply not_elem_names_add_elim in H; destruct H.
  - (* CCons *) rewrite <- IHth; simpl; try apply f_equal;
    try apply lem_commute_subFV; 
    simpl in H2; simpl in H3; try apply H0;
    destruct H0; destruct H2; destruct H6; destruct H3;
    try rewrite H0; try rewrite H2; intuition.
  - (* CConsT *) rewrite <- IHth; simpl; try apply f_equal;
    try symmetry; try apply lem_commute_subFV_subFTV;
    simpl in H2; simpl in H3; try apply H0;
    destruct H0; destruct H2; destruct H6; destruct H3;
    try rewrite H2; try rewrite H5; intuition.
  Qed.
    
Lemma lem_unroll_ctsubst_left : forall (th:csub) (x:vname) (v_x:expr) (t:type),
    ~ in_csubst x th -> fv v_x = empty /\ ftv v_x = empty -> isValue v_x
        -> closed th -> substitutable th
        -> ctsubst (CCons x v_x th) t = tsubFV x v_x (ctsubst th t).
Proof. induction th; intros; simpl; try reflexivity;
  unfold in_csubst in H; simpl in H; 
  apply not_elem_names_add_elim in H; destruct H.
  - (* CCons *) rewrite <- IHth; simpl; try apply f_equal;
    try apply lem_commute_tsubFV; 
    simpl in H2; simpl in H3; try apply H0;
    destruct H0; destruct H2; destruct H6; destruct H3;
    try rewrite H0; try rewrite H2; intuition.
  - (* CConsT *) rewrite <- IHth; simpl; try apply f_equal;
    try symmetry; try apply lem_commute_tsubFV_tsubFTV;
    simpl in H2; simpl in H3; try apply H0;
    destruct H0; destruct H2; destruct H6; destruct H3;
    try rewrite H2; try rewrite H5; intuition.
  Qed.       

Lemma lem_unroll_ctsubst_tv_left : forall (th:csub) (a:vname) (t_a t:type),
    ~ in_csubst a th -> free t_a = empty /\ freeTV t_a = empty -> noExists t_a
        -> closed th -> substitutable th
        -> ctsubst (CConsT a t_a th) t = tsubFTV a t_a (ctsubst th t).
Proof. induction th; intros; simpl; try reflexivity;
  unfold in_csubst in H; simpl in H; 
  apply not_elem_names_add_elim in H; destruct H.
  - (* CCons *) rewrite <- IHth; simpl; try apply f_equal;
    try apply lem_commute_tsubFV_tsubFTV;
    simpl in H2; simpl in H3; try apply H0;
    destruct H0; destruct H2; destruct H6; destruct H3;
    try rewrite H0; try rewrite H6; intuition.
  - (* CConsT *) rewrite <- IHth; simpl; try apply f_equal;
    try symmetry; try apply lem_commute_tsubFTV;
    simpl in H2; simpl in H3; try apply H0;
    destruct H0; destruct H2; destruct H6; destruct H3;
    try rewrite H5; try rewrite H6; intuition.
  Qed.         

  (* --- Various properties of csubst/ctsubst and free/bound variables *)

  Lemma lem_csubst_nofv : forall (th:csub) (e:expr),
  fv e = empty -> ftv e = empty -> csubst th e = e.

Proof. induction th; intros; simpl; try reflexivity;
rewrite IHth; try rewrite lem_subFV_notin';
try rewrite lem_subFTV_notin'; 
try apply empty_no_elem; trivial. Qed.

Lemma lem_ctsubst_nofree : forall (th:csub) (t:type),
  free t = empty -> freeTV t = empty -> ctsubst th t = t.
Proof. induction th; intros; simpl; try reflexivity;
rewrite IHth; try rewrite lem_tsubFV_notin; 
try rewrite lem_tsubFTV_notin; 
try apply empty_no_elem; trivial. Qed.

Lemma lem_csubst_value : forall (th:csub) (v:expr),
  isValue v -> substitutable th -> isValue (csubst th v).
Proof. induction th; simpl; intros; try apply H; 
destruct H0; try destruct H1;
try apply lem_subFV_value with x v_x v in H as H';
try apply lem_subFTV_value with a t_a v in H as H';
try apply IHth; assumption. Qed.

Lemma lem_ctsubst_isMono : forall (th:csub) (t_a:type),
  isMono t_a -> substitutable th -> isMono (ctsubst th t_a).
Proof. induction th; simpl; intros; try apply H; 
destruct H0; try destruct H1;
try apply lemma_tsubFV_isMono with x v_x t_a in H as H';
try apply lemma_tsubFTV_isMono with a t_a t_a0 in H as H';
try apply IHth; assumption. Qed.

Lemma lem_ctsubst_noExists : forall (th:csub) (t_a:type),
  noExists t_a -> substitutable th -> noExists (ctsubst th t_a).
Proof. induction th; simpl; intros; try apply H; 
destruct H0; try destruct H1;
try apply lemma_tsubFV_noExists with x v_x t_a in H as H';
try apply lemma_tsubFTV_noExists with a t_a t_a0 in H as H';
try apply IHth; assumption. Qed.

  (* --- various distributive properties of csubst and ctsubst *)

Lemma lem_csubst_bc : forall (th:csub) (b:bool) ,
    csubst th (Bc b) = Bc b.
Proof. induction th; simpl; apply IHth || reflexivity. Qed.

Lemma lem_csubst_ic : forall (th:csub) (n:nat),
    csubst th (Ic n) = Ic n.
Proof. induction th; simpl; apply IHth || reflexivity. Qed.

Lemma lem_csubst_prim : forall (th:csub) (c:prim),
    csubst th (Prim c) = Prim c.
Proof. induction th; simpl; apply IHth || reflexivity. Qed.

Lemma lem_csubst_bv : forall (th:csub) (y:vname),
    csubst th (BV y) = BV y.
Proof. induction th; simpl; apply IHth || reflexivity. Qed.

Lemma lem_csubst_fv : forall (th:csub) (y:vname),
    ~ in_csubst y th -> csubst th (FV y) = FV y.
Proof. induction th; unfold in_csubst; intros; simpl; 
  simpl in H; try apply not_elem_names_add_elim in H; 
  try destruct (x =? y) eqn:E;
  try apply Nat.eqb_eq in E; try rewrite E in H;
  try apply IHth; intuition. Qed.

Lemma lem_csubst_lambda : forall (th:csub) (e:expr),
    csubst th (Lambda e) = Lambda (csubst th e).
Proof. induction th; simpl; intro e; apply IHth || reflexivity. Qed.

Lemma lem_csubst_app : forall (th:csub) (e e':expr),
    csubst th (App e e') = App (csubst th e) (csubst th e').
Proof. induction th; simpl; intros e e'; apply IHth || reflexivity. Qed.

Lemma lem_csubst_lambdaT : forall (th:csub) (k:kind) (e:expr),
    csubst th (LambdaT k e) = LambdaT k (csubst th e).
Proof. induction th; simpl; intros k e; apply IHth || reflexivity. Qed.

Lemma lem_csubst_appT : forall (th:csub) (e:expr) (t:type),
    csubst th (AppT e t) = AppT (csubst th e) (ctsubst th t).
Proof. induction th; simpl; intros; apply IHth || reflexivity. Qed.
 
Lemma lem_csubst_let : forall (th:csub) (e_x e:expr), 
    csubst th (Let e_x e) = Let (csubst th e_x) (csubst th e).
Proof. induction th; simpl; intros; apply IHth || reflexivity. Qed.

Lemma lem_csubst_annot : forall (th:csub) (e:expr) (t:type),
    csubst th (Annot e t) = Annot (csubst th e) (ctsubst th t).
Proof. induction th; simpl; intros; apply IHth || reflexivity. Qed.

Lemma lem_csubst_if : forall (th:csub) (e0 e1 e2:expr), 
    csubst th (If e0 e1 e2) = If (csubst th e0) (csubst th e1) (csubst th e2).
Proof. induction th; simpl; intros; apply IHth || reflexivity. Qed.

Lemma lem_cpsubst_pempty : forall (th:csub), cpsubst th PEmpty = PEmpty.
Proof. induction th; simpl; apply IHth || reflexivity. Qed.

Lemma lem_cpsubst_pcons : forall (th:csub) (p:expr) (ps:preds),
    cpsubst th (PCons p ps) = PCons (csubst th p) (cpsubst th ps).
Proof. induction th; simpl; intros; apply IHth || reflexivity. Qed.
 
Lemma lem_cpsubst_strengthen : forall (th:csub) (ps qs:preds),
    cpsubst th (strengthen ps qs) = strengthen (cpsubst th ps) (cpsubst th qs).
Proof. induction th; simpl; intros; 
  try rewrite lem_psubFV_strengthen; try rewrite lem_psubFTV_strengthen; 
  try apply IHth || reflexivity. Qed.

Lemma lem_ctsubst_push : forall (th:csub) (ps:preds) (t_a:type),
    noExists t_a -> substitutable th
        -> ctsubst th (push ps t_a) = push (cpsubst th ps) (ctsubst th t_a).
Proof. induction th; simpl; intros;
  try rewrite lem_subFV_push; try rewrite lem_subFTV_push;
  try rewrite IHth; 
  try apply lemma_tsubFV_noExists; try apply lemma_tsubFTV_noExists;
  intuition. Qed.

Lemma lem_ctsubst_refn : forall (th:csub) (b:basic) (ps:preds),
    isClosedBasic b \/ isBTV b 
        -> ctsubst th (TRefn b ps) = TRefn b (cpsubst th ps).
Proof. induction th; intros b ps Hb; simpl;
  destruct b; simpl in Hb; try rewrite IHth; intuition. Qed.

Lemma lem_ctsubst_refn_tv_notin : forall (th:csub) (a:vname) (ps:preds),
    ~ in_csubst a th 
        -> ctsubst th (TRefn (FTV a) ps) = TRefn (FTV a) (cpsubst th ps).
Proof. induction th; intros a0 ps H; simpl.
  - (* CEmpty *) reflexivity.
  - (* CCons *) apply in_csubst_CCons in H; destruct H;
    apply IHth; apply H0.
  - (* CConsT *) apply in_csubst_CConsT in H; destruct H;
    apply Nat.neq_sym in H; apply Nat.eqb_neq in H;
    rewrite H; apply IHth; apply H0.
  Qed.

Lemma lem_ctsubst_refn_tv : forall (th:csub) (a:vname) (t_a:type) (ps:preds),
    tv_bound_inC a t_a th -> closed th -> substitutable th -> uniqueC th
        -> ctsubst th (TRefn (FTV a) ps) = push (cpsubst th ps) t_a.
Proof. induction th; simpl; intros.
  - (* CEmpty *) contradiction.
  - (* CCons *) apply IHth; intuition. 
  - (* CConsT *) destruct (a =? a0) eqn:A;
    destruct H0; destruct H1; destruct H2; destruct H3; destruct H4.
    * destruct H; try destruct H.
      + subst t_a0; rewrite lem_ctsubst_push;
        try rewrite lem_ctsubst_nofree; trivial.
      + apply Nat.eqb_eq in A; subst a0;
        apply lem_tvboundinC_incsubst in H; contradiction.
    * destruct H; try destruct H; apply Nat.eqb_neq in A.
      + subst a0; contradiction.
      + apply IHth; trivial.
  Qed.

(*
{-@ lem_ctsubst_refn_tv' :: th:csub -> { a:vname | tv_in_csubst a th } -> x:RVname -> p:preds
        -> { b:Basic | b == TBool || b == TInt } -> z:RVname
        -> { q:preds | (TRefn b z q) == csubst_tv th a }
        -> { pf:_ | ctsubst th (TRefn (FTV a) x p) == TRefn b z (strengthen (csubst th p) q) } @-}
lem_ctsubst_refn_tv' :: csub -> vname -> RVname -> expr -> Basic -> RVname -> expr -> Proof
lem_ctsubst_refn_tv' th a x p b z q = () ? lem_ctsubst_refn_tv th a x p

{-@ lem_ctsubst_refn_usertype :: g:Env -> th:csub -> ProofOf(DenotesEnv g th)
        -> b:Basic -> x:RVname -> p:preds -> ProofOf(WFType g (TRefn b x p) Base)
        -> { pf:_ | noExists (ctsubst th (TRefn b x p)) } @-}
lem_ctsubst_refn_usertype :: Env -> csub -> DenotesEnv -> Basic -> RVname -> expr -> WFType -> Proof
lem_ctsubst_refn_usertype g th den_g_th b x p p_g_t = case b of
  (FTV a) -> case ( csubst_tv th (a ? lem_wf_refn_tv_in_env g a x p Base p_g_t
                                    ? lem_binds_env_th g th den_g_th) ) of
    (TRefn b' z q_) -> () ? lem_ctsubst_refn_tv th a x p
                          ? toProof ( noExists (TRefn b' z (strengthen (csubst th p) q)) === True )
      where
        q = q_ ? lem_refn_is_pred (TRefn b' z q_) b' z q_
    (TFunc {})     -> () ? lem_ctsubst_refn_tv th a x p
    (TPoly {})     -> () ? lem_ctsubst_refn_tv th a x p 
  _       -> () ? lem_ctsubst_refn    th b x p 
*)

Lemma lem_ctsubst_func : forall (th:csub) (t_x t:type),
    ctsubst th (TFunc t_x t) = TFunc (ctsubst th t_x) (ctsubst th t).
Proof. induction th; simpl; intros; apply IHth || reflexivity. Qed.
  
Lemma lem_ctsubst_exis : forall (th:csub) (t_x t:type),
    ctsubst th (TExists t_x t) = TExists (ctsubst th t_x) (ctsubst th t).
Proof. induction th; simpl; intros; apply IHth || reflexivity. Qed.
  
Lemma lem_ctsubst_poly : forall (th:csub) (k:kind) (t:type),
    ctsubst th (TPoly k t) = TPoly k (ctsubst th t).
Proof. induction th; simpl; intros; apply IHth || reflexivity. Qed.

Lemma lem_ctsubst_erase_basic : forall (th:csub) (t:type) (b:basic), 
    erase t = FTBasic b -> isClosedBasic b \/ isBTV b 
        -> erase (ctsubst th t) = FTBasic b.
Proof. intro th; induction t; simpl; intros; try discriminate;
  try injection H as H; try subst b0;
  rewrite lem_ctsubst_refn || rewrite lem_ctsubst_exis;
  simpl; try apply IHt2; trivial. Qed.

Fixpoint isExFTV (t : type) : Prop :=
    match t with
    | (TRefn b ps)    => match b with
                         | (FTV a) => True
                         | _       => False
    end
    | (TFunc tx t')   => False
    | (TExists tx t') => isExFTV t'
    | (TPoly k t')    => False
    end.

Fixpoint matchesExFTV (a : vname) (t : type) : Prop :=
    match t with
    | (TRefn b ps)    => match b with
                         | (FTV a0) => a = a0
                         | _        => False
    end
    | (TFunc tx t')   => False
    | (TExists tx t') => matchesExFTV a t'
    | (TPoly k t')    => False
    end.

Lemma matchesExFTV_dec : forall (a:vname) (t:type),
    matchesExFTV a t \/ ~ matchesExFTV a t.
Proof. intro a; induction t; 
  try destruct b; try destruct (a =? a0) eqn:A;
  simpl; unfold not; intuition.
  - apply Nat.eqb_eq in A; left; apply A.
  - apply Nat.eqb_neq in A; right; apply A. Qed. 

Lemma lem_matchesExFTV_both : forall (a0 a:vname) (t:type),
    matchesExFTV a0 t -> matchesExFTV a t -> a0 = a.  
Proof. intros a0 a; induction t; simpl;
  try destruct b; intuition; subst a; apply H. Qed.

Lemma lem_isNotExFTV_no_match : forall (a:vname) (t:type),
    ~ isExFTV t -> ~ matchesExFTV a t.
Proof. intro a; induction t; simpl; try destruct b; intuition. Qed.

Lemma lem_tsubFV_matchesExFTV : forall (a x:vname) (v_x:expr) (t:type),
    matchesExFTV a t -> matchesExFTV a (tsubFV x v_x t).
Proof. intros a x v_x; induction t; simpl;
  try destruct b; trivial. Qed.

Lemma lem_tsubFTV_matchesExFTV : forall (a0 a:vname) (t_a t:type),
    a0 <> a 
        -> matchesExFTV a0 t -> matchesExFTV a0 (tsubFTV a t_a t).
Proof. intros a a0 t_a; induction t; simpl;
  try destruct b; trivial; intros; subst a1;
  apply Nat.neq_sym in H; apply Nat.eqb_neq in H;
  rewrite H; simpl; reflexivity. Qed.  

Lemma lem_tsubFV_isNotExFTV : forall (x:vname) (v_x:expr) (t:type),
    ~ isExFTV t -> ~ isExFTV (tsubFV x v_x t).
Proof. intros x v_x; induction t; simpl;
  try destruct b; trivial. Qed.

Lemma lem_tsubFTV_isNotExFTV : forall (a:vname) (t_a:type) (t:type),
    ~ isExFTV t -> ~ isExFTV (tsubFTV a t_a t).
Proof. intros a t_a; induction t; simpl;
  try destruct b; intuition. Qed.

Lemma lem_push_isNotExFTV : forall (ps:preds) (t_a:type),
    freeTV t_a = empty -> noExists t_a -> ~ isExFTV (push ps t_a).
Proof. intros ps; destruct t_a; simpl; 
  try destruct b; auto; intro H. 
  apply empty_no_elem with (names_add a (ftvP ps0)) a in H;
  apply not_elem_names_add_elim in H; intuition. Qed.

Lemma lem_tsubFTV_matches : forall (a:vname) (t_a t:type),
    freeTV t_a = empty -> noExists t_a
        -> matchesExFTV a t -> ~ isExFTV (tsubFTV a t_a t).
Proof. intros a t_a; induction t; simpl; 
  try destruct b; try apply IHt2;
  intros; try contradiction. 
  apply Nat.eqb_eq in H1; rewrite H1; 
  apply lem_push_isNotExFTV; assumption. Qed.

Lemma lem_tsubFTV_self_noFTV : forall (a:vname) (t_a t:type) (v:expr) (k:kind),
    ~ matchesExFTV a t 
      -> tsubFTV a t_a (self t v k) = self (tsubFTV a t_a t) (subFTV a t_a v) k.
Proof. intros a t_a; induction t; intros v k'; destruct k';
  try destruct b; simpl; try destruct (a =? a0) eqn:A; intro H;
  unfold eqlPred; f_equal; try apply IHt2; trivial;
  apply Nat.eqb_eq in A; subst a0; contradiction. Qed.

Lemma lem_ctsubst_self_noFTV : forall (th:csub) (t:type) (v:expr) (k:kind),
    ~ isExFTV t -> ctsubst th (self t v k) = self (ctsubst th t) (csubst th v) k.
Proof. induction th; simpl; intros; try reflexivity.
  - (* CCons *) rewrite lem_tsubFV_self; apply IHth.
    destruct t; try destruct b; simpl; simpl in H; trivial.
    apply lem_tsubFV_isNotExFTV; apply H. 
  - (* CConsT *) destruct t; destruct k; try destruct b; 
    simpl; simpl in H; try contradiction;
    try repeat rewrite lem_ctsubst_refn; 
    try        rewrite lem_ctsubst_func;
    try repeat rewrite lem_ctsubst_exis;
    try rewrite lem_ctsubst_poly; simpl; unfold eqlPred; 
    try rewrite lem_cpsubst_pcons;
    try repeat rewrite lem_csubst_app;
    try rewrite lem_csubst_appT; 
    try rewrite lem_csubst_prim;
    try rewrite lem_ctsubst_refn; 
    try rewrite lem_cpsubst_pempty;
    try rewrite lem_csubst_bv; simpl; auto; f_equal.
    rewrite lem_tsubFTV_self_noFTV; try apply IHth;
    try apply lem_tsubFTV_isNotExFTV;
    try apply lem_isNotExFTV_no_match; apply H. Qed.

Lemma lem_ctsubst_self_FTV : forall (th:csub) (a:vname) (t:type) (v:expr) (k:kind),
    matchesExFTV a t -> ~ in_csubst a th
        -> ctsubst th (self t v k) = self (ctsubst th t) (csubst th v) k.
Proof.  induction th; simpl; intros; try reflexivity.
  - (* CCons *) rewrite lem_tsubFV_self; apply IHth with a;
    unfold in_csubst in H0; simpl in H0; 
    apply not_elem_names_add_elim in H0; destruct H0;
    try apply lem_tsubFV_matchesExFTV; trivial.
  - (* CConsT *) apply in_csubst_CConsT in H0;  destruct H0;
    destruct t eqn:T; simpl in H; 
    try destruct b; try contradiction; try subst a1;
    rewrite lem_tsubFTV_self_noFTV ;
    try rewrite <- IHth with a0 (tsubFTV a t_a (TRefn (FTV a0) ps)) 
                              (subFTV a t_a v) k;
    try rewrite <- IHth with a0 (tsubFTV a t_a (TExists t0_1 t0_2)) 
                              (subFTV a t_a v) k;
    try assert (a =? a0 = false)
      by (apply Nat.eqb_neq; apply Nat.neq_sym; apply H0);    
    simpl; try rewrite H; simpl;
    try apply Nat.neq_sym;
    try apply lem_tsubFTV_matchesExFTV;
    trivial; unfold not; intros; apply H0;
    apply lem_matchesExFTV_both with t0_2; trivial.
  Qed.

  (* --- Commutative laws relating csubst/ctsubst and substitution operations *)

Lemma lem_csubst_subBV : forall (th:csub) (v e:expr),
    loc_closed th -> substitutable th
        -> csubst th (subBV v e) = subBV (csubst th v) (csubst th e).
Proof. induction th; simpl; intros; try reflexivity;
  try rewrite lem_commute_subFV_subBV;
  try rewrite lem_commute_subFTV_subBV;
  try apply IHth; destruct H; destruct H0; try destruct H2; assumption. Qed.

Lemma lem_csubst_subBTV : forall (th:csub) (t_a:type) (e:expr),
    loc_closed th -> substitutable th -> noExists t_a
          -> csubst th (subBTV t_a e) = subBTV (ctsubst th t_a) (csubst th e).
Proof. induction th; simpl; intros; try reflexivity;
  try rewrite lem_commute_subFV_subBTV;
  try rewrite lem_commute_subFTV_subBTV;
  destruct H; destruct H0; try apply IHth; try destruct H3; 
  try apply lemma_tsubFV_noExists;
  try apply lemma_tsubFTV_noExists; assumption. Qed.

Lemma lem_ctsubst_tsubBV : forall (th:csub) (v:expr) (t:type),
    loc_closed th -> substitutable th 
        -> ctsubst th (tsubBV v t) = tsubBV (csubst th v) (ctsubst th t).
Proof. induction th; simpl; intros; try reflexivity;
  try rewrite lem_commute_tsubFV_tsubBV;
  try rewrite lem_commute_tsubFTV_tsubBV;
  try apply IHth; destruct H; destruct H0; 
  try destruct H2; try assumption. Qed.

Lemma lem_ctsubst_tsubBTV : forall (th:csub) (t_a t:type),
    loc_closed th -> substitutable th -> noExists t_a
        -> ctsubst th (tsubBTV t_a t) = tsubBTV (ctsubst th t_a) (ctsubst th t).
Proof. induction th; simpl; intros; try reflexivity;
  try rewrite lem_commute_tsubFV_tsubBTV;
  try rewrite lem_commute_tsubFTV_tsubBTV;
  destruct H; destruct H0; try apply IHth; try destruct H3;
  try apply lemma_tsubFV_noExists;
  try apply lemma_tsubFTV_noExists; try assumption. Qed.

Lemma lem_cpsubst_psubBV : forall (th:csub) (v:expr) (ps:preds),
    loc_closed th -> substitutable th 
        -> cpsubst th (psubBV v ps) = psubBV (csubst th v) (cpsubst th ps).
Proof. induction th; simpl; intros; try reflexivity;
  try rewrite lem_commute_psubFV_psubBV;
  try rewrite lem_commute_psubFTV_psubBV;
  try apply IHth; destruct H; destruct H0; 
  try destruct H2; try assumption. Qed.

Lemma lem_cpsubst_psubBTV : forall (th:csub) (t_a:type) (ps:preds),
    loc_closed th -> substitutable th -> noExists t_a
        -> cpsubst th (psubBTV t_a ps) = psubBTV (ctsubst th t_a) (cpsubst th ps).
Proof. induction th; simpl; intros; try reflexivity;
  try rewrite lem_commute_psubFV_psubBTV;
  try rewrite lem_commute_psubFTV_psubBTV;
  destruct H; destruct H0; try apply IHth; try destruct H3;
  try apply lemma_tsubFV_noExists;
  try apply lemma_tsubFTV_noExists; try assumption. Qed.
  
(* --- Compositional Laws

{-@ lem_csubst_and_unbind :: x:vname -> y:vname 
           -> v:Value -> bt:FType -> ProofOf(HasFType FEmpty v bt)
           -> { th:csub | not (Set_mem y (bindsC th)) } -> { p:expr | not (Set_mem y (fv p)) }
           -> { pf:_ | csubst (CCons y v th) (unbind x y p) == subBV x v (csubst th p) } @-}
lem_csubst_and_unbind :: vname -> vname -> expr -> FType -> HasFType -> csub -> expr -> Proof
lem_csubst_and_unbind x y v b pf_v_b th p = () {-toProof ( 
       csubst (CCons y (v-}  ? lem_fv_subset_bindsF FEmpty v b pf_v_b{-) th) (unbind x y p) 
   === csubst th (subFV y v (unbind x y p))-}
     ? lem_subFV_unbind x y v p
--   === csubst th (subBV x v p)
     ? lem_csubst_subBV x v b pf_v_b th p
--   === subBV x v (csubst th p) )

{-@ lem_csubst_and_unbind_tv :: a:vname -> a':vname -> t_a:UserType -> k:kind -> ProofOf(WFType Empty t_a k)
        -> { th:csub | not (Set_mem a' (bindsC th)) } -> { p:expr | not (Set_mem a' (ftv p)) }
        -> { pf:_ | csubst (CConsT a' t_a th) (unbind_tv a a' p) == subBTV a t_a (csubst th p) } @-}
lem_csubst_and_unbind_tv :: vname -> vname -> type -> kind -> WFType -> csub -> expr -> Proof
lem_csubst_and_unbind_tv a a' t_a k pf_emp_ta th p 
  = () ? lem_free_subset_binds Empty t_a k pf_emp_ta  
       ? lem_tfreeBV_empty     Empty t_a k pf_emp_ta 
       ? lem_subFTV_unbind_tv  a a' t_a p
       ? lem_csubst_subBTV     a t_a k pf_emp_ta th p

{-@ lem_ctsubst_and_unbindT :: x:vname -> y:vname
           -> v:Value -> bt:FType -> ProofOf(HasFType FEmpty v bt)
           -> { th:csub | not (Set_mem y (bindsC th)) } -> { t:type | not (Set_mem y (free t)) }
           -> { pf:_ | ctsubst (CCons y v th) (unbindT x y t) == tsubBV x v (ctsubst th t) } @-}
lem_ctsubst_and_unbindT :: vname -> vname -> expr -> FType -> HasFType 
           -> csub -> type -> Proof
lem_ctsubst_and_unbindT x y v bt pf_v_b th t = () {-toProof ( 
       ctsubst (CCons y (v-} ? lem_fv_subset_bindsF FEmpty v bt pf_v_b{-) th) (unbindT x y t)
   === ctsubst th (tsubFV y v (unbindT x y t))-}
     ? lem_tsubFV_unbindT x y v t
--   === ctsubst th (tsubBV x v t)
     ? lem_ctsubst_tsubBV x v bt pf_v_b th t
--   === tsubBV x v (ctsubst th t) )

{-@ lem_ctsubst_and_unbind_tvT :: a1:vname -> a:vname -> t_a:UserType 
        -> k:kind -> ProofOf(WFType Empty t_a k)
        -> { th:csub | not (Set_mem a (bindsC th)) } -> { t:type | not (Set_mem a (freeTV t)) }
        -> { pf:_ | ctsubst (CConsT a t_a th) (unbind_tvT a1 a t) == tsubBTV a1 t_a (ctsubst th t) } @-}
lem_ctsubst_and_unbind_tvT :: vname -> vname -> type -> kind -> WFType  
           -> csub -> type -> Proof
lem_ctsubst_and_unbind_tvT a1 a t_a k p_emp_ta th t 
  = () ? lem_free_subset_binds  Empty t_a k p_emp_ta
       ? lem_tfreeBV_empty      Empty t_a k p_emp_ta 
       ? lem_tsubFTV_unbind_tvT a1 a t_a t   
       ? lem_ctsubst_tsubBTV    a1 t_a k p_emp_ta th t
*)
  (* --- After applying a closing substitution there are no more free variables remaining *)

Lemma lem_csubst_pres_noftv : forall (th:csub) (v:expr),
    closed th -> ftv v = empty -> ftv (csubst th v) = empty.
Proof. induction th; simpl; trivial; intros; destruct H; destruct H1.
  - (* CCons *) apply IHth. apply H2. 
    assert (Subset (ftv (subFV x v_x v)) (union (ftv v) (ftv v_x)))
      by apply ftv_subFV_elim;
    rewrite H1 in H3; rewrite H0 in H3;
    apply no_elem_empty; unfold not; intros. 
    apply H3 in H4; intuition.
  - (* CConsT *) assert (subFTV a t_a v = v) 
        by (apply lem_subFTV_notin; rewrite H0; auto);
    rewrite H3; apply IHth; assumption. 
  Qed.
(*
        -> { v_x:expr | Set_sub (fv v_x) (vbindsC th) && Set_sub (ftv v_x) (tvbindsC th) }
        -> { pf:_ | Set_emp (fv (csubst th v_x)) && Set_emp (ftv (csubst th v_x)) } @-}
lem_csubst_no_more_fv :: csub -> expr -> Proof
lem_csubst_no_more_fv CEmpty v_x            = ()
lem_csubst_no_more_fv (CCons  y v_y th) v_x = () ? lem_csubst_no_more_fv th (subFV y v_y v_x)
lem_csubst_no_more_fv (CConsT a t_a th) v_x = () ? lem_csubst_no_more_fv th (subFTV a t_a v_x)

{-@ lem_ctsubst_no_more_fv :: th:csub 
        -> { t:type | Set_sub (free t) (vbindsC th) && Set_sub (freeTV t) (tvbindsC th) }
        -> { pf:_ | Set_emp (free (ctsubst th t)) && Set_emp (freeTV (ctsubst th t)) } @-}
lem_ctsubst_no_more_fv :: csub -> type -> Proof
lem_ctsubst_no_more_fv CEmpty            t = ()
lem_ctsubst_no_more_fv (CCons  y v_y th) t = () ? lem_ctsubst_no_more_fv th (tsubFV y v_y t)
lem_ctsubst_no_more_fv (CConsT a t_a th) t = () ? lem_ctsubst_no_more_fv th (tsubFTV a t_a t)
*)
Lemma lem_csubst_isLC : forall (th:csub) (v:expr),
    loc_closed th -> substitutable th -> isLC v -> isLC (csubst th v).
Proof. induction th; simpl; trivial; intros; destruct H; destruct H0.
  - (* CCons *) apply IHth; try apply lem_islc_at_subFV; trivial. 
  - (* CConsT *) apply IHth; destruct H3;
    try apply lem_islc_at_subFTV; trivial.
  Qed.

Lemma lem_ctsubst_isLCT : forall (th:csub) (t:type),
    loc_closed th -> substitutable th -> isLCT t -> isLCT (ctsubst th t).
Proof. induction th; simpl; trivial; intros; destruct H; destruct H0.
  - (* CCons *) apply IHth; try apply lem_islc_at_subFV; trivial. 
  - (* CConsT *) apply IHth; destruct H3;
    try apply lem_islc_at_subFTV; trivial.
  Qed.  

(*
{-@ lem_csubst_subFV :: th:csub -> { x:vname | not (in_csubst x th) } 
        -> { v_x:Value | Set_sub (fv v_x) (vbindsC th) && Set_sub (ftv v_x) (tvbindsC th) } -> e:expr
        -> { pf:_ | csubst th (subFV x v_x e) == csubst th (subFV x (csubst th v_x) e) } @-}
lem_csubst_subFV :: csub -> vname -> expr -> expr -> Proof
lem_csubst_subFV  CEmpty            x v_x e = ()
lem_csubst_subFV  (CCons y v_y th)  x v_x e 
  = () -- ? toProof (
--        csubst (CCons y v_y th) (subFV x (csubst (CCons y v_y th) v_x ) e)
--    === csubst th (subFV y v_y  (subFV x (csubst (CCons y v_y th) v_x ) e)
        ? lem_commute_subFV x (csubst (CCons y v_y th) v_x ? lem_csubst_value (CCons y v_y th) v_x) 
                            y v_y e
--    === csubst th (subFV x (subFV y v_y (csubst (CCons y v_y th) v_x)) (subFV y v_y e))   
        ? lem_csubst_no_more_fv (CCons y v_y th) v_x
        ? lem_subFV_notin y v_y (csubst (CCons y v_y th) v_x)
--    === csubst th (subFV x (csubst (CCons y v_y th) v_x) (subFV y v_y e))
--    === csubst th (subFV x (csubst th (subFV y v_y v_x)) (subFV y v_y e))
        ? lem_csubst_subFV th x (subFV y v_y v_x) (subFV y v_y e)
--    === csubst th (subFV x (subFV y v_y v_x) (subFV y v_y e))
        ? lem_commute_subFV x v_x y v_y e 
--    === csubst th (subFV y v_y (subFV x v_x e))
--    === csubst (CCons y v_y th) (subFV x v_x e) )
lem_csubst_subFV  (CConsT a t_a th) x v_x e
    = () ? lem_commute_subFTV_subFV x (csubst (CConsT a t_a th) v_x ? lem_csubst_value (CConsT a t_a th) v_x)
                            a t_a e
         ? lem_csubst_no_more_fv (CConsT a t_a th) v_x
         ? lem_subFTV_notin a t_a (csubst (CConsT a t_a th) v_x)
         ? lem_csubst_subFV th x (subFTV a t_a v_x) (subFTV a t_a e)
         ? lem_commute_subFTV_subFV x v_x a t_a e
    
{-@ lem_ctsubst_tsubFV :: th:csub -> { x:vname | not (in_csubst x th) } 
        -> { v_x:Value | Set_sub (fv v_x) (vbindsC th) && Set_sub (ftv v_x) (tvbindsC th) } -> t:type
        -> { pf:_ | ctsubst th (tsubFV x v_x t) == ctsubst th (tsubFV x (csubst th v_x) t) } @-}
lem_ctsubst_tsubFV :: csub -> vname -> expr -> type -> Proof
lem_ctsubst_tsubFV  CEmpty            x v_x t = ()
lem_ctsubst_tsubFV  (CCons y v_y th)  x v_x t 
  = () -- ? toProof (
--        ctsubst (CCons y v_y th) (tsubFV x (csubst (CCons y v_y th) v_x) t)
--    === ctsubst th (tsubFV y v_y (tsubFV x (csubst (CCons y v_y th) v_x) t))
        ? lem_commute_tsubFV x (csubst (CCons y v_y th) v_x ? lem_csubst_value (CCons y v_y th) v_x) 
                             y v_y t
--    === ctsubst th (tsubFV x (subFV y v_y (csubst (CCons y v_y th) v_x)) (tsubFV y v_y t))   
        ? lem_csubst_no_more_fv (CCons y v_y th) v_x
        ? lem_subFV_notin y v_y (csubst (CCons y v_y th) v_x)
--    === ctsubst th (tsubFV x (csubst (CCons y v_y th) v_x) (tsubFV y v_y t))
--    === ctsubst th (tsubFV x (csubst th (subFV y v_y v_x)) (tsubFV y v_y t))
        ? lem_ctsubst_tsubFV th x (subFV y v_y v_x) (tsubFV y v_y t)
--    === ctsubst th (tsubFV x (subFV y v_y v_x) (tsubFV y v_y t))
        ? lem_commute_tsubFV x v_x y v_y t 
--    === ctsubst th (tsubFV y v_y (tsubFV x v_x t))
--    === ctsubst (CCons y v_y th) (tsubFV x v_x t) )
lem_ctsubst_tsubFV  (CConsT a t_a th) x v_x t 
    = () ? lem_commute_tsubFTV_tsubFV x 
                   (csubst (CConsT a t_a th) v_x ? lem_csubst_value (CConsT a t_a th) v_x)
                   a t_a t
         ? lem_csubst_no_more_fv (CConsT a t_a th) v_x
         ? lem_subFTV_notin a t_a (csubst (CConsT a t_a th) v_x)
         ? lem_ctsubst_tsubFV th x (subFTV a t_a v_x) (tsubFTV a t_a t)
         ? lem_commute_tsubFTV_tsubFV x v_x a t_a t

{-@ lem_csubst_subFTV :: th:csub -> { a:vname | not (in_csubst a th) } 
        -> { t_a:UserType | Set_sub (free t_a) (vbindsC th) && Set_sub (freeTV t_a) (tvbindsC th) } 
        -> e:expr -> { pf:_ | csubst th (subFTV a t_a e) == csubst th (subFTV a (ctsubst th t_a) e) } @-}
lem_csubst_subFTV :: csub -> vname -> type -> expr -> Proof
lem_csubst_subFTV  CEmpty            a t_a e = ()
lem_csubst_subFTV  (CCons y v_y th)  a t_a e 
  = ()  ? lem_commute_subFV_subFTV a (ctsubst (CCons y v_y th) t_a 
                                         ? lem_ctsubst_usertype (CCons y v_y th) t_a) y v_y e
        ? lem_ctsubst_no_more_fv (CCons y v_y th) t_a
        ? lem_tsubFV_notin y v_y (ctsubst (CCons y v_y th) t_a)
        ? lem_csubst_subFTV th a (tsubFV y v_y t_a) (subFV y v_y e)
        ? lem_commute_subFV_subFTV a t_a y v_y e 
lem_csubst_subFTV  (CConsT a' t_a' th) a t_a e
    = () ? lem_commute_subFTV a (ctsubst (CConsT a' t_a' th) t_a
                                    ? lem_ctsubst_usertype (CConsT a' t_a' th) t_a) a' t_a' e
         ? lem_ctsubst_no_more_fv (CConsT a' t_a' th) t_a
         ? lem_tsubFTV_notin a' t_a' (ctsubst (CConsT a' t_a' th) t_a)
         ? lem_csubst_subFTV th a (tsubFTV a' t_a' t_a) (subFTV a' t_a' e)
         ? lem_commute_subFTV a t_a a' t_a' e
    
{-@ lem_ctsubst_tsubFTV :: th:csub -> { a:vname | not (in_csubst a th) } 
        -> { t_a:UserType | Set_sub (free t_a) (vbindsC th) && Set_sub (freeTV t_a) (tvbindsC th) } 
        -> t:type -> {pf:_ | ctsubst th (tsubFTV a t_a t) == ctsubst th (tsubFTV a (ctsubst th t_a) t)} @-}
lem_ctsubst_tsubFTV :: csub -> vname -> type -> type -> Proof
lem_ctsubst_tsubFTV  CEmpty            a t_a t = ()
lem_ctsubst_tsubFTV  (CCons y v_y th)  a t_a t 
  = ()  ? lem_commute_tsubFV_tsubFTV a (ctsubst (CCons y v_y th) t_a 
                                         ? lem_ctsubst_usertype (CCons y v_y th) t_a) y v_y t
        ? lem_ctsubst_no_more_fv (CCons y v_y th) t_a
        ? lem_tsubFV_notin y v_y (ctsubst (CCons y v_y th) t_a)
        ? lem_ctsubst_tsubFTV th a (tsubFV y v_y t_a) (tsubFV y v_y t)
        ? lem_commute_tsubFV_tsubFTV a t_a y v_y t 
lem_ctsubst_tsubFTV  (CConsT a' t_a' th) a t_a t 
    = () ? lem_commute_tsubFTV a (ctsubst (CConsT a' t_a' th) t_a
                                    ? lem_ctsubst_usertype (CConsT a' t_a' th) t_a) a' t_a' t
         ? lem_ctsubst_no_more_fv (CConsT a' t_a' th) t_a
         ? lem_tsubFTV_notin a' t_a' (ctsubst (CConsT a' t_a' th) t_a)
         ? lem_ctsubst_tsubFTV th a (tsubFTV a' t_a' t_a) (tsubFTV a' t_a' t)
         ? lem_commute_tsubFTV a t_a a' t_a' t

  --- Closing Substitutions and Technical Operations

--        -> { e:expr | Set_sub (fv e) (bindsC th) && not (Set_mem x (fv e)) }
{-@ lem_remove_csubst :: th:csub -> { x:vname | v_in_csubst x th}
        -> { e:expr | not (Set_mem x (fv e)) }
        -> { pf:Proof | csubst th e == csubst (remove_fromCS th x) e } @-}
lem_remove_csubst :: csub -> vname -> expr -> Proof
lem_remove_csubst (CCons z v_z th) x e = case ( x == z ) of
  (True)  -> () ? lem_subFV_notin x v_z e
                  {- ? toProof ( csubst (remove_fromCS (CCons x v_z th) x) e
                   === csubst th e  
                   === csubst th (subFV x v_z e)
                   === csubst (CCons x v_z th) e) -}
  (False) -> () {- toProof ( csubst (remove_fromCS (CCons z v_z th) x) e
                   === csubst (CCons z v_z (remove_fromCS th x)) e-}
                     ? lem_remove_csubst th x (subFV z v_z e)
                {-   === csubst (CCons z v_z th) e )-}
lem_remove_csubst (CConsT a t_a th) x e = case ( x == a ) of
   (False) -> () ? lem_remove_csubst th x (subFTV a t_a e)

{-@ lem_remove_tv_csubst :: th:csub -> { a:vname | tv_in_csubst a th}
        -> { e:expr | not (Set_mem a (ftv e)) }
        -> { pf:Proof | csubst th e == csubst (remove_fromCS th a) e } @-}
lem_remove_tv_csubst :: csub -> vname -> expr -> Proof
lem_remove_tv_csubst (CCons z v_z th) a e = case ( a == z ) of
  (False) -> () {- toProof ( csubst (remove_fromCS (CCons z v_z th) x) e
                   === csubst (CCons z v_z (remove_fromCS th x)) e-}
                     ? lem_remove_tv_csubst th a (subFV z v_z e)
                {-   === csubst (CCons z v_z th) e )-}
lem_remove_tv_csubst (CConsT a' t_a th) a e = case ( a == a' ) of
   (True)  -> () ? lem_subFTV_notin a t_a e
   (False) -> () ? lem_remove_tv_csubst th a (subFTV a' t_a e)

{-@ lem_remove_ctsubst :: th:csub -> { x:vname | v_in_csubst x th}
        -> { t:type | not (Set_mem x (free t)) }
        -> { pf:Proof | ctsubst th t == ctsubst (remove_fromCS th x) t } @-}
lem_remove_ctsubst :: csub -> vname -> type -> Proof
lem_remove_ctsubst (CCons z v_z th) x t = case ( x == z ) of
  (True)  -> () ? lem_tsubFV_notin x v_z t
          {- toProof ( ctsubst (remove_fromCS (CCons x v_z th) x) t
                   === ctsubst th t  
                   === ctsubst th (tsubFV x v_z t)
                   === ctsubst (CCons x v_z th) t) -}
  (False) -> () {- toProof ( ctsubst (remove_fromCS (CCons z v_z th) x) t
                   === ctsubst (CCons z v_z (remove_fromCS th x)) t-}
                     ? lem_remove_ctsubst th x (tsubFV z v_z t)
                {-   === ctsubst (CCons z v_z th) t )-}
lem_remove_ctsubst (CConsT a t_a th) x t = case ( x == a ) of
  (False) -> () ? lem_remove_ctsubst th x (tsubFTV a t_a t)

{-@ lem_remove_tv_ctsubst :: th:csub -> { a:vname | tv_in_csubst a th}
        -> { t:type | not (Set_mem a (freeTV t)) }
        -> { pf:Proof | ctsubst th t == ctsubst (remove_fromCS th a) t } @-} 
lem_remove_tv_ctsubst :: csub -> vname -> type -> Proof
lem_remove_tv_ctsubst (CCons z v_z th) a t = case ( a == z ) of
  (False) -> () ? lem_remove_tv_ctsubst th a (tsubFV z v_z t)
lem_remove_tv_ctsubst (CConsT a' t_a th) a t = case ( a == a' ) of
  (True)  -> () ? lem_tsubFTV_notin a t_a t
  (False) -> () ? lem_remove_tv_ctsubst th a (tsubFTV a' t_a t)
*)