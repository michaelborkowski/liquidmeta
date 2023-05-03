Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.Strengthenings.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import Denotations.ClosingSubstitutions.

Require Import Arith.

  (* -- | More Properties of Substitution *)

Lemma lem_commute_subFV : (forall (e:expr) (x:vname) (v:expr) (y:vname) (v_y:expr),
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

Lemma lem_commute_subFV_subFTV : (forall (e:expr) (a:vname) (t_a:type) (y:vname) (v_y:expr),
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

Lemma lem_commute_subFTV : (
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

Lemma lem_unroll_ctsubst_tv_left : forall (th:csub) (a:vname) (t_a t:type),
    ~ in_csubst a th -> free t_a = empty /\ freeTV t_a = empty -> noExists t_a
        -> closed th -> substitutable th
        -> ctsubst (CConsT a t_a th) t = tsubFTV a t_a (ctsubst th t).
Proof. induction th; intros; simpl; try reflexivity;
  unfold in_csubst in H; simpl in H; 
  apply not_elem_names_add_elim in H; destruct H.
  - (* CCons *) rewrite <- IHth; simpl; try apply f_equal;
    try apply lem_commute_subFV_subFTV;
    simpl in H2; simpl in H3; try apply H0;
    destruct H0; destruct H2; destruct H6; destruct H3;
    try rewrite H0; try rewrite H6; intuition.
  - (* CConsT *) rewrite <- IHth; simpl; try apply f_equal;
    try symmetry; try apply lem_commute_subFTV;
    simpl in H2; simpl in H3; try apply H0;
    destruct H0; destruct H2; destruct H6; destruct H3;
    try rewrite H5; try rewrite H6; intuition.
  Qed.         

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
(* 33 *)
(*
{-@ lem_ctsubst_refn_tv :: th:csub -> { a:vname | tv_in_csubst a th } -> x:RVname -> p:preds
        -> { pf:_ | ctsubst th (TRefn (FTV a) x p) == push (csubst th p) (csubst_tv th a) } @-}
lem_ctsubst_refn_tv :: csub -> vname -> RVname -> expr -> Proof
lem_ctsubst_refn_tv (CEmpty)          a x p = ()
lem_ctsubst_refn_tv (CCons  y v_y th) a x p = () ? lem_ctsubst_refn_tv th a x (subFV y v_y p)
lem_ctsubst_refn_tv (CConsT a' t' th) a x p 
  | a == a'   = () ? lem_ctsubst_push th (subFTV a' t' p) t'
                   ? lem_ctsubst_nofree th t'
  | otherwise = () ? lem_ctsubst_refn_tv th a x (subFTV a' t' p)

{-@ lem_ctsubst_refn_tv' :: th:csub -> { a:vname | tv_in_csubst a th } -> x:RVname -> p:preds
        -> { b:Basic | b == TBool || b == TInt } -> z:RVname
        -> { q:preds | (TRefn b z q) == csubst_tv th a }
        -> { pf:_ | ctsubst th (TRefn (FTV a) x p) == TRefn b z (strengthen (csubst th p) q) } @-}
lem_ctsubst_refn_tv' :: csub -> vname -> RVname -> expr -> Basic -> RVname -> expr -> Proof
lem_ctsubst_refn_tv' th a x p b z q = () ? lem_ctsubst_refn_tv th a x p

{-@ lem_ctsubst_refn_tv_notin :: th:csub -> { a:vname | not (tv_in_csubst a th) } 
        -> x:RVname -> p:expr 
        -> { pf:_ | ctsubst th (TRefn (FTV a) x p) == TRefn (FTV a) x (csubst th p) } @-}
lem_ctsubst_refn_tv_notin :: csub -> vname -> RVname -> expr -> Proof
lem_ctsubst_refn_tv_notin (CEmpty)          a x p = ()
lem_ctsubst_refn_tv_notin (CCons  y v_y th) a x p 
              = () ? lem_ctsubst_refn_tv_notin th a x (subFV y v_y p)
lem_ctsubst_refn_tv_notin (CConsT a' t' th) a x p 
  | a == a'   = impossible ""
  | otherwise = () ? lem_ctsubst_refn_tv_notin th a x (subFTV a' t' p)

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

{-@ lem_ctsubst_func :: th:csub -> x:vname -> t_x:type -> t:type
        -> { pf:_ | ctsubst th (TFunc x t_x t) == TFunc x (ctsubst th t_x) (ctsubst th t) } @-}  
lem_ctsubst_func :: csub -> vname -> type -> type -> Proof
lem_ctsubst_func (CEmpty)       x t_x t = ()
lem_ctsubst_func (CCons y v th) x t_x t 
    = () ? lem_ctsubst_func th x (tsubFV y v t_x) (tsubFV y v t) 
lem_ctsubst_func (CConsT a t_a th) x t_x t 
    = () ? lem_ctsubst_func th x (tsubFTV a t_a t_x) (tsubFTV a t_a t)

{-@ lem_ctsubst_exis :: th:csub -> x:vname -> t_x:type -> t:type
        -> {pf:_ | ctsubst th (TExists x t_x t) == TExists x (ctsubst th t_x) (ctsubst th t)} @-}  
lem_ctsubst_exis :: csub -> vname -> type -> type -> Proof
lem_ctsubst_exis (CEmpty)       x t_x t = ()
lem_ctsubst_exis (CCons y v th) x t_x t 
    = () ? lem_ctsubst_exis th x (tsubFV y v t_x) (tsubFV y v t) 
lem_ctsubst_exis (CConsT a t_a th) x t_x t 
    = () ? lem_ctsubst_exis th x (tsubFTV a t_a t_x) (tsubFTV a t_a t)

{-@ lem_ctsubst_poly :: th:csub -> a:vname -> k:kind -> t:type
        -> { pf:_ | ctsubst th (TPoly a k t) == TPoly a k (ctsubst th t) } @-}  
lem_ctsubst_poly :: csub -> vname -> kind -> type -> Proof
lem_ctsubst_poly (CEmpty)           a k t = ()
lem_ctsubst_poly (CCons  y  v   th) a k t  
    = () ? lem_ctsubst_poly th a k (tsubFV y v t) 
lem_ctsubst_poly (CConsT a' t'  th) a k t 
    = () ? lem_ctsubst_poly th a k (tsubFTV a' t' t)

Lemma lem_ctsubst_erase_basic : forall (th:csub) (t:type) (b:basic), 
    erase t = FTBasic b -> isClosedBasic b \/ isBTV b 
        -> erase (ctsubst th t) = FTBasic b.
Proof. intro th; induction t; simpl; intros; try discriminate;
  rewrite <- H; rewrite lem_ctsubst_refn || rewrite lem_ctsubst_exis.
lem_ctsubst_erase_basic th (TRefn _b z p) b = case b of
  TBool -> () ? lem_ctsubst_refn th TBool z p
  TInt  -> () ? lem_ctsubst_refn th TInt  z p 
lem_ctsubst_erase_basic th (TExists z t_z t) b 
  = () ? lem_ctsubst_exis th z t_z t 
       ? lem_ctsubst_erase_basic th t b

    
{-@ lem_ctsubst_self :: th:csub -> t:type -> e:Term -> k:kind 
      -> { pf:_ | ctsubst th (self t e k) == self (ctsubst th t) (csubst th e) k } / [csubstSize th] @-}
lem_ctsubst_self :: csub -> type -> expr -> kind -> Proof
lem_ctsubst_self (CEmpty)          t e k = ()
lem_ctsubst_self (CCons  y v_y th) t e k
  = () ? lem_tsubFV_self  y v_y t e k 
       ? lem_ctsubst_self th (tsubFV y v_y t) (subFV y v_y e) k
lem_ctsubst_self (CConsT a t_a th) t e k
  = () ? lem_tsubFTV_self a t_a t e k
       ? lem_ctsubst_self th (tsubFTV a t_a t) (subFTV a t_a e) k

  --- Various properties of csubst/ctsubst and free/bound variables

{-@ lem_csubst_nofv :: th:csub -> { e:expr | Set_emp (fv e) && Set_emp (ftv e) }
        -> { pf:_ | csubst th e == e } @-}
lem_csubst_nofv :: csub -> expr -> Proof
lem_csubst_nofv (CEmpty)       e    = ()
lem_csubst_nofv (CCons x v th) e    = () ? lem_csubst_nofv th e
                                         ? lem_subFV_notin x v e
lem_csubst_nofv (CConsT a t_a th) e = () ? lem_csubst_nofv th e
                                         ? lem_subFTV_notin a t_a e 

{-@ lem_ctsubst_nofree :: th:csub -> { t:type | Set_emp (free t) && Set_emp (freeTV t) }
        -> { pf:_ | ctsubst th t == t } @-}
lem_ctsubst_nofree :: csub -> type -> Proof
lem_ctsubst_nofree (CEmpty)          t = ()
lem_ctsubst_nofree (CCons x v th)    t = () ? lem_ctsubst_nofree th t
                                            ? lem_tsubFV_notin x v t 
lem_ctsubst_nofree (CConsT a t_a th) t = () ? lem_ctsubst_nofree th t
                                            ? lem_tsubFTV_notin a t_a t 

{-{-@ lem_csubst_freeBV :: th:csub -> e:expr
        -> { pf:_ | freeBV (csubst th e) == freeBV e } @-}
lem_csubst_freeBV :: csub -> expr -> Proof
lem_csubst_freeBV (CEmpty)       e = ()
lem_csubst_freeBV (CCons x v th) e = () ? lem_csubst_freeBV th (subFV x v e)
                         ? toProof ( freeBV (subFV x v e) === freeBV e )
-}
{-@ lem_ctsubst_nofreeBV :: th:csub -> { t:type | Set_emp (tfreeBV t) }
        -> { pf:_ | Set_emp (tfreeBV (ctsubst th t)) } @-}
lem_ctsubst_nofreeBV :: csub -> type -> Proof
lem_ctsubst_nofreeBV (CEmpty)          t = ()
lem_ctsubst_nofreeBV (CCons x v th)    t = () ? lem_ctsubst_nofreeBV th (tsubFV x v t
                                                    ? lem_tsubFV_tfreeBV  x v   t)
lem_ctsubst_nofreeBV (CConsT a t_a th) t = () ? lem_ctsubst_nofreeBV th (tsubFTV a t_a t
                                                    ? lem_tsubFTV_tfreeBV a t_a t)
*)
Lemma lem_csubst_value : forall (th:csub) (v:expr),
    isValue v -> isValue (csubst th v).
Proof. induction th; intros; simpl. apply H.
  try apply lem_subFV_value with y v_y in H.

lem_csubst_value (CEmpty)          v = ()
lem_csubst_value (CCons y v_y th)  v = () ? lem_csubst_value th (subFV y v_y v)
lem_csubst_value (CConsT a t_a th) v = () ? lem_csubst_value th (subFTV a t_a v)
(*
{-@ lem_ctsubst_usertype :: th:csub -> t_a:UserType -> { pf:_ | noExists (ctsubst th t_a) } @-}
lem_ctsubst_usertype :: csub -> type -> Proof
lem_ctsubst_usertype (CEmpty)          t = ()
lem_ctsubst_usertype (CCons y v_y th)  t = () ? lem_ctsubst_usertype th (tsubFV y v_y t)
lem_ctsubst_usertype (CConsT a t_a th) t = () ? lem_ctsubst_usertype th (tsubFTV a t_a t)

{-@ lem_ctsubst_head_not_free :: x:vname 
        -> { v_x:Value | Set_emp (fv v_x) && Set_emp (ftv v_x) &&
                         Set_emp (freeBV v_x) && Set_emp (freeBTV v_x) } 
        -> { th:csub | not (Set_mem x (bindsC th)) }
        -> { t:type | not (Set_mem x (free t)) } 
        -> { pf:_ | ctsubst (CCons x v_x th) t == ctsubst th t } @-}
lem_ctsubst_head_not_free :: vname -> expr -> csub -> type -> Proof
lem_ctsubst_head_not_free x v_x th t = toProof ( ctsubst (CCons x v_x th) t
                                             === ctsubst th (tsubFV x v_x t)
                                             === ctsubst th t )

  --- Commutative laws relating csubst/ctsubst and substitution operations
  --- The first set of these laws involve [v/x] or [t_a/a] where v or t_a have no free vars

{-@ lem_csubst_subBV :: x:vname -> v:Value -> bt:FType 
           -> ProofOf(HasFType FEmpty v bt) -> th:csub -> p:expr
           -> { pf:_ | csubst th (subBV x v p) == subBV x v (csubst th p) } @-}
lem_csubst_subBV :: vname -> expr -> FType -> HasFType -> csub -> expr -> Proof
lem_csubst_subBV x v bt pf_v_b (CEmpty)         p = ()
lem_csubst_subBV x v bt pf_v_b (CCons y v_y th) p 
    = () ? lem_commute_subFV_subBV1 x v 
                   (y `withProof` lem_fv_bound_in_fenv FEmpty v bt pf_v_b y) v_y p
         ? lem_csubst_subBV x v bt pf_v_b th (subFV y v_y p)
lem_csubst_subBV x v bt pf_v_b (CConsT a t_a th) p
    = () ? lem_commute_subFTV_subBV1 x v
                   (a `withProof` lem_fv_bound_in_fenv FEmpty v bt pf_v_b a) t_a p
         ? lem_csubst_subBV x v bt pf_v_b th (subFTV a t_a p)

{-@ lem_csubst_subBTV :: a:vname -> t_a:UserType -> k:kind 
           -> ProofOf(WFType Empty t_a k) -> th:csub -> p:expr
           -> { pf:_ | csubst th (subBTV a t_a p) == subBTV a t_a (csubst th p) } @-}
lem_csubst_subBTV :: vname -> type -> kind -> WFType -> csub -> expr -> Proof
lem_csubst_subBTV a t_a k p_emp_ta (CEmpty)          p = ()
lem_csubst_subBTV a t_a k p_emp_ta (CCons y v_y th)  p 
  = () ? lem_commute_subFV_subBTV1 a t_a 
             (y ? lem_free_bound_in_env Empty t_a k p_emp_ta y) v_y p
       ? lem_csubst_subBTV a t_a k p_emp_ta th (subFV y v_y p)
lem_csubst_subBTV a t_a k p_emp_ta (CConsT a1 t1 th) p
  = () ? lem_commute_subFTV_subBTV1 a t_a 
             (a1 ? lem_free_bound_in_env Empty t_a k p_emp_ta a1) t1 p
       ? lem_csubst_subBTV a t_a k p_emp_ta th (subFTV a1 t1 p)

{-@ lem_ctsubst_tsubBV :: x:vname -> v:Value -> bt:FType
           -> ProofOf(HasFType FEmpty v bt) -> th:csub -> t:type
           -> { pf:_ | ctsubst th (tsubBV x v t) == tsubBV x v (ctsubst th t) } @-}
lem_ctsubst_tsubBV :: vname -> expr -> FType -> HasFType -> csub -> type -> Proof
lem_ctsubst_tsubBV x v bt pf_v_b (CEmpty)         t = ()
lem_ctsubst_tsubBV x v bt pf_v_b (CCons y v_y th) t 
    = () ? lem_commute_tsubFV_tsubBV1 x v 
                   (y `withProof` lem_fv_bound_in_fenv FEmpty v bt pf_v_b y) v_y t
         ? lem_ctsubst_tsubBV x v bt pf_v_b th (tsubFV y v_y t)
lem_ctsubst_tsubBV x v bt pf_v_b (CConsT a t_a th) t 
    = () ? lem_commute_tsubFTV_tsubBV1 x v
                   (a `withProof` lem_fv_bound_in_fenv FEmpty v bt pf_v_b a) t_a t
         ? lem_ctsubst_tsubBV x v bt pf_v_b th (tsubFTV a t_a t)

{-@ lem_ctsubst_tsubBTV :: a1:vname -> t_a:UserType -> k:kind 
        -> ProofOf(WFType Empty t_a k) -> th:csub -> t:type 
        -> { pf:_ | ctsubst th (tsubBTV a1 t_a t) == tsubBTV a1 t_a (ctsubst th t) } @-}
lem_ctsubst_tsubBTV :: vname -> type -> kind -> WFType -> csub -> type -> Proof
lem_ctsubst_tsubBTV a1 t_a k p_emp_ta (CEmpty)            t = ()
lem_ctsubst_tsubBTV a1 t_a k p_emp_ta (CCons y v_y th)    t
    = () ? lem_commute_tsubFV_tsubBTV1 a1 t_a
                   (y  ? lem_free_bound_in_env Empty t_a k p_emp_ta y)  v_y  t
         ? lem_ctsubst_tsubBTV a1 t_a k p_emp_ta th (tsubFV y v_y t)
lem_ctsubst_tsubBTV a1 t_a k p_emp_ta (CConsT a' t_a' th) t 
    = () ? lem_commute_tsubFTV_tsubBTV1 a1 t_a
                   (a' ? lem_free_bound_in_env Empty t_a k p_emp_ta a') t_a' t 
         ? lem_ctsubst_tsubBTV a1 t_a k p_emp_ta th (tsubFTV a' t_a' t)

  --- The second set of these laws are more general for [v/x] or [t_a/a] incl free vars

{-@ lem_commute_csubst_subBV :: th:csub -> x:vname -> v:Value -> e:expr
           -> { pf:_ | csubst th (subBV x v e) == subBV x (csubst th v) (csubst th e) } @-} 
lem_commute_csubst_subBV :: csub -> vname -> expr -> expr -> Proof
lem_commute_csubst_subBV (CEmpty)         x v e = () 
lem_commute_csubst_subBV (CCons y v_y th) x v e 
    = () ? lem_commute_subFV_subBV x v y v_y e
         ? lem_commute_csubst_subBV th x (subFV y v_y v) (subFV y v_y e)
lem_commute_csubst_subBV (CConsT a t_a th) x v e 
    = () ? lem_commute_subFTV_subBV x v a t_a e
         ? lem_commute_csubst_subBV th x (subFTV a t_a v) (subFTV a t_a e)

{-@ lem_commute_csubst_subBTV :: th:csub -> a:vname -> t_a:UserType -> e:expr
            -> { pf:_ | csubst th (subBTV a t_a e) == subBTV a (ctsubst th t_a) (csubst th e) } @-}
lem_commute_csubst_subBTV :: csub -> vname -> type -> expr -> Proof
lem_commute_csubst_subBTV (CEmpty)          a t_a e = ()
lem_commute_csubst_subBTV (CCons  y v_y th) a t_a e
    = () ? lem_commute_subFV_subBTV a t_a y v_y e
         ? lem_commute_csubst_subBTV th a (tsubFV y v_y t_a) (subFV y v_y e)
lem_commute_csubst_subBTV (CConsT a' t' th) a t_a e
    = () ? lem_commute_subFTV_subBTV a t_a a' t' e
         ? lem_commute_csubst_subBTV th a (tsubFTV a' t' t_a) (subFTV a' t' e)

{-@ lem_commute_ctsubst_tsubBV :: th:csub -> x:vname -> v:Value -> t:type
           -> { pf:_ | ctsubst th (tsubBV x v t) == tsubBV x (csubst th v) (ctsubst th t) } @-} 
lem_commute_ctsubst_tsubBV :: csub -> vname -> expr -> type -> Proof
lem_commute_ctsubst_tsubBV (CEmpty)         x v t = () 
lem_commute_ctsubst_tsubBV (CCons y v_y th) x v t 
    = () ? lem_commute_tsubFV_tsubBV x v y v_y t
         ? lem_commute_ctsubst_tsubBV th x (subFV y v_y v) (tsubFV y v_y t)
lem_commute_ctsubst_tsubBV (CConsT a t_a th) x v t 
    = () ? lem_commute_tsubFTV_tsubBV x v a t_a t
         ? lem_commute_ctsubst_tsubBV th x (subFTV a t_a v) (tsubFTV a t_a t)

{-@ lem_commute_ctsubst_tsubBTV :: th:csub -> a:vname -> t_a:UserType -> t:type 
        -> { pf:_ | ctsubst th (tsubBTV a t_a t) == tsubBTV a (ctsubst th t_a) (ctsubst th t) } @-}
lem_commute_ctsubst_tsubBTV :: csub -> vname -> type -> type -> Proof
lem_commute_ctsubst_tsubBTV (CEmpty)            a t_a t = ()
lem_commute_ctsubst_tsubBTV (CCons y v_y th)    a t_a t  
    = () ? lem_commute_tsubFV_tsubBTV a t_a y v_y t
         ? lem_commute_ctsubst_tsubBTV th a (tsubFV y v_y t_a) (tsubFV y v_y t)
lem_commute_ctsubst_tsubBTV (CConsT a' t_a' th) a t_a t  
    = () ? lem_commute_tsubFTV_tsubBTV a t_a a' t_a' t
         ? lem_commute_ctsubst_tsubBTV th a (tsubFTV a' t_a' t_a) (tsubFTV a' t_a' t)


  --- Compositional Laws

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

  --- After applying a closing substitution there are no more free variables remaining

{-@ lem_csubst_no_more_fv :: th:csub 
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
    
{-@ lem_csubst_no_more_bv :: th:csub 
        -> { v_x:expr | Set_emp (freeBV v_x) && Set_emp (freeBTV v_x) }
        -> { pf:_ | Set_emp (freeBV (csubst th v_x)) && Set_emp (freeBTV (csubst th v_x)) } @-}
lem_csubst_no_more_bv :: csub -> expr -> Proof
lem_csubst_no_more_bv CEmpty v_x            = ()
lem_csubst_no_more_bv (CCons  y v_y th) v_x = () ? lem_csubst_no_more_bv th (subFV y v_y v_x)
lem_csubst_no_more_bv (CConsT a t_a th) v_x = () ? lem_csubst_no_more_bv th (subFTV a t_a v_x)

{-@ lem_ctsubst_no_more_bv :: th:csub -> { t:type | Set_emp (tfreeBV t) && Set_emp (tfreeBTV t) }
        -> { pf:_ | Set_emp (tfreeBV (ctsubst th t)) && Set_emp (tfreeBTV (ctsubst th t)) } @-}
lem_ctsubst_no_more_bv :: csub -> type -> Proof
lem_ctsubst_no_more_bv CEmpty            t = ()
lem_ctsubst_no_more_bv (CCons  y v_y th) t = () ? lem_ctsubst_no_more_bv th (tsubFV y v_y t)
lem_ctsubst_no_more_bv (CConsT a t_a th) t = () ? lem_ctsubst_no_more_bv th (tsubFTV a t_a t)

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