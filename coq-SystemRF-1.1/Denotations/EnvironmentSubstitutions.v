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

(*
{-@ lem_unbind_tvT_equals :: a:Vname -> a':Vname -> { t1:FType | not (Set_mem a' (ffreeTV t1)) }
        -> { t2:FType | unbindFT a a' t1 == unbindFT a a' t2 && not (Set_mem a' (ffreeTV t2)) } 
        -> { pf:_ | t1 == t2 } @-}
lem_unbind_tvT_equals :: Vname -> Vname -> FType -> FType -> Proof
lem_unbind_tvT_equals a a' (FTBasic b) (FTBasic _) = case b of
  (BTV a) -> ()
  _       -> ()
lem_unbind_tvT_equals a a' (FTFunc t11 t12) (FTFunc t21 t22) 
  = () ? lem_unbind_tvT_equals a a' t11 t21
       ? lem_unbind_tvT_equals a a' t12 t22
lem_unbind_tvT_equals a a' (FTPoly a1 k t1') (FTPoly _ _ t2')
  = () ? lem_unbind_tvT_equals a a' t1' t2'

-- LEMMA 6. If G |- s <: t, then if we erase the types then (erase s) and (erase t)
--               equiv up to alpha-renaming bound variables
{-@ lem_erase_subtype :: g:Env -> t1:Type -> t2:Type -> ProofOf(Subtype g t1 t2)
               -> { pf:_ | erase t1 == erase t2 } @-}
lem_erase_subtype :: Env -> Type -> Type -> Subtype -> Proof
lem_erase_subtype g t1 t2 (SBase _g x1 b p1 x2 p2 y _) = ()
lem_erase_subtype g t1 t2 (SFunc _g x1 s1 x2 s2 p_s2_s1 t1' t2' y p_t1'_t2')
  = () ? lem_erase_subtype  g s2 s1 p_s2_s1
       ? lem_erase_tsubBV x1 (FV y) t1'
       ? lem_erase_tsubBV x2 (FV y) t2'
       ? lem_erase_subtype (Cons y s2 g) (unbindT x1 y t1') (unbindT x2 y t2') p_t1'_t2'
lem_erase_subtype g t1 t2 (SWitn _g v t_x p_v_tx _t1 x t' p_t1_t'v)
  = () ? lem_erase_subtype g t1 (tsubBV x v t') p_t1_t'v
       ? lem_erase_tsubBV x v t'
{- toProof ( erase t1 ? lem_erase_subtype g t1 (tsubBV x v t') p_t1_t'v
            === erase (tsubBV x v t') ? lem_erase_tsubBV x v t'
            === erase t' === erase (TExists x t_x t') ) -}
lem_erase_subtype g t1 t2 (SBind _g x t_x t _t2 y p_t_t')
  = () ? lem_erase_subtype (Cons y t_x g) (unbindT x y t) t2 p_t_t'
       ? lem_erase_tsubBV x (FV y) t
lem_erase_subtype g t1 t2 (SPoly _g a1 k t1' a2 t2' a p_ag_t1'_t2') 
  = () ? lem_erase_subtype (ConsT a k g) (unbind_tvT a1 a t1') (unbind_tvT a2 a t2')
                           p_ag_t1'_t2' 
       ? lem_erase_unbind_tvT a1 a t1'
       ? lem_erase_unbind_tvT a2 a t2'
       ? lem_unbind_tvT_equals a1 a (erase t1' ? lem_erase_freeTV t1') 
                                    (erase t2' ? lem_erase_freeTV t2')

{-@ lem_erase_ctsubst :: th:CSub -> t1:Type 
        -> { t2:Type | erase t1 == erase t2 }
        -> { pf:_ | erase (ctsubst th t1) == erase (ctsubst th t2) } @-}
lem_erase_ctsubst :: CSub -> Type -> Type -> Proof
lem_erase_ctsubst CEmpty             t1 t2 = () 
lem_erase_ctsubst (CCons  x v_x th') t1 t2 
    = () ? lem_erase_ctsubst  th' (tsubFV x v_x t1 ? lem_erase_tsubFV x v_x t1) 
                                  (tsubFV x v_x t2 ? lem_erase_tsubFV x v_x t2) 
         ? lem_unroll_ctsubst_left th' x v_x t1
         ? lem_erase_tsubFV x v_x (ctsubst th' t1)
         ? lem_unroll_ctsubst_left th' x v_x t2
         ? lem_erase_tsubFV x v_x (ctsubst th' t2)
lem_erase_ctsubst (CConsT a t_a th') t1 t2 
    = () ? lem_erase_ctsubst  th' (tsubFTV a t_a t1 ? lem_erase_tsubFTV a t_a t1)
                                  (tsubFTV a t_a t2 ? lem_erase_tsubFTV a t_a t2)
         ? lem_unroll_ctsubst_tv_left th' a t_a t1
         ? lem_erase_tsubFTV a t_a (ctsubst th' t1)
         ? lem_unroll_ctsubst_tv_left th' a t_a t2
         ? lem_erase_tsubFTV a t_a (ctsubst th' t2)



{-@ lem_csubst_fv_in ::  y:Vname -> { v:Value | Set_emp (fv v) && Set_emp (ftv v) &&
                                         Set_emp (freeBV v) && Set_emp (freeBTV v) }
                                 -> { th:CSub | not (in_csubst y th ) }
                                 -> { pf:_ | csubst (CCons y v th) (FV y) == v } @-}
lem_csubst_fv_in :: Vname -> Expr -> CSub -> Proof
lem_csubst_fv_in y v th = () ? lem_csubst_nofv th v
*)