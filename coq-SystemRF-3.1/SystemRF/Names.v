Require Import Arith.
Require Import Lists.ListSet.

Require Import SystemRF.BasicDefinitions.

  (* I. Basic Defs and Properties of our Name-set theory *)

Definition names := set vname.
Definition empty := empty_set vname.
Definition singleton (x:vname) := @set_add vname Nat.eq_dec x empty.

Definition names_add := @set_add vname Nat.eq_dec.
Definition names_rem := @set_remove vname Nat.eq_dec.
Definition names_mem := @set_mem vname Nat.eq_dec.
Definition union := @set_union vname Nat.eq_dec.
Definition intersect := @set_inter vname Nat.eq_dec.
Definition diff := @set_diff vname Nat.eq_dec.

Definition Elem := @set_In vname.
Definition Subset (xs : names) (ys: names) : Prop :=
    forall (x : vname), Elem x xs -> Elem x ys.

Lemma elem_dec : forall (x:vname) (xs : names),
    Elem x xs \/ ~ Elem x xs.
Proof. intros. destruct (set_In_dec Nat.eq_dec x xs); intuition. Qed.

Lemma no_elem_empty : forall (ys : names),
    (forall (x:vname), ~ Elem x ys) -> ys = empty.
Proof. intros. destruct ys.
  - reflexivity.
  - assert (List.In v (v :: ys)) by auto with *.
    apply H in H0; contradiction.
  Qed.

Lemma empty_no_elem : forall (ys : names),
    ys = empty -> forall (x : vname), ~ Elem x ys.
Proof. unfold not; intros; subst ys; unfold Elem in H0; contradiction. Qed. 

Lemma elem_sing : forall (x y : vname),
    Elem x (singleton y) <-> x = y.
Proof. intros; split; simpl; intro H.
  - destruct H; symmetry; (trivial || contradiction).
  - intuition. Qed.

Lemma not_elem_sing : forall (x y : vname),
    ~ Elem x (singleton y) <-> x <> y.
Proof.  intros; apply not_iff_compat; apply elem_sing.
Qed.
  
Lemma not_elem_subset : forall (x : vname) (xs ys : names),
    Subset xs ys -> ~ Elem x ys -> ~ Elem x xs.
Proof. unfold Subset; unfold not; intros; intuition. Qed.

Lemma not_elem_names_add_intro : forall (x y : vname) (ys : names),
    x <> y /\ ~ Elem x ys -> ~ Elem x (names_add y ys).
Proof. intros. unfold not; intro. apply set_add_elim in H0. intuition. Qed.

Lemma not_elem_names_add_elim : forall (x y : vname) (ys : names),
    ~ Elem x (names_add y ys) -> x <> y /\ ~ Elem x ys.
Proof. intros. pose proof (@set_add_intro vname Nat.eq_dec x y ys) as H1.
  split; unfold not; intros; intuition. Qed. 

Lemma not_elem_union_intro : forall (x : vname) (xs ys : names),
    ~ Elem x xs -> ~ Elem x ys -> ~ Elem x (union xs ys).
Proof. unfold not; intros; apply set_union_elim in H1;
  destruct H1; apply H in H1 || apply H0 in H1; contradiction. Qed.

Lemma not_elem_union_elim : forall (x : vname) (xs ys : names),
    ~ Elem x (union xs ys) -> ~ Elem x xs /\ ~ Elem x ys.
Proof. unfold not; intros; split; intro Hx;
  apply set_union_intro1 with vname Nat.eq_dec x xs ys in Hx ||
    apply set_union_intro2 with vname Nat.eq_dec x xs ys in Hx ;  
  intuition. Qed.

Lemma not_elem_diff_singleton : forall (x : vname) (xs : names),
    ~ Elem x (diff xs (singleton x)).
Proof. unfold not; intros. apply set_diff_iff in H;
  destruct H; simpl in H0; auto. Qed.

Lemma subset_refl : forall (xs : names),
    Subset xs xs.
Proof. unfold Subset; trivial. Qed.

Lemma subset_trans : forall (xs ys zs : names),
    Subset xs ys -> Subset ys zs -> Subset xs zs.
Proof. unfold Subset; intros xs ys zs H1 H2 x Hxs; 
  apply H2; apply H1; assumption. Qed.

Lemma subset_trans3 : forall (xs ys zs ws : names),
    Subset xs ys -> Subset ys zs -> Subset zs ws -> Subset xs ws.
Proof. intros; apply subset_trans with zs; try apply H1;
  apply subset_trans with ys; try apply H; apply H0. Qed.

Lemma subset_trans4 : forall (xs ys zs ws vs : names),
    Subset xs ys -> Subset ys zs -> Subset zs ws -> Subset ws vs -> Subset xs vs.
Proof. intros; apply subset_trans3 with zs ws; try apply H1; try apply H2;
  apply subset_trans with ys; try apply H; apply H0. Qed. 

Lemma subset_trans5 : forall (xs ys zs ws vs us : names),
    Subset xs ys -> Subset ys zs -> Subset zs ws 
        -> Subset ws vs -> Subset vs us -> Subset xs us.
Proof. intros; apply subset_trans3 with ys zs; try apply H; try apply H0;
  apply subset_trans3 with ws vs; assumption. Qed. 

Lemma subset_empty_l : forall (xs : names),
    Subset empty xs.
Proof. unfold Subset; intros; contradiction. Qed.

Lemma subset_sing_l : forall (x : vname) (xs : names),
    Subset (singleton x) xs <-> Elem x xs.
Proof. intros; split; unfold Subset.
  - intro. apply H; apply elem_sing; reflexivity.
  - intros; apply elem_sing in H0; subst x; assumption. Qed.

Lemma subset_sing_add : forall (x y : vname) (xs : names),
    Subset (singleton x) (names_add y xs) <-> x = y \/ Subset (singleton x) xs.
Proof. intros; split; intro.
  - apply subset_sing_l in H; apply ListSet.set_add_iff in H; destruct H;
    try (apply subset_sing_l in H); intuition.
  - apply subset_sing_l; apply ListSet.set_add_iff. destruct H;
    try (apply subset_sing_l in H); intuition. Qed.
 
Lemma subset_add_intro_l : forall (x : vname) ( xs ys : names ),
    Elem x ys -> Subset xs ys -> Subset (names_add x xs) ys.
Proof. unfold Subset; intros; apply set_add_elim in H1; destruct H1; 
    try subst x0; intuition. Qed.
    
Lemma subset_add_intro : forall (x : vname) ( xs ys : names ),
    Subset xs ys -> Subset xs (names_add x ys).
Proof. unfold Subset; intros; apply set_add_intro; apply H in H0; intuition. Qed.

Lemma subset_add_both_intro : forall (x : vname) ( xs ys : names ),
    Subset xs ys -> Subset (names_add x xs) (names_add x ys).
Proof. unfold Subset; intros. apply set_add_elim in H0; apply set_add_intro.
  destruct H0; try apply H in H0; intuition. Qed. 

Lemma subset_add_elim : forall (z : vname) (xs ys : names),
    ~ Elem z xs -> Subset xs (names_add z ys) -> Subset xs ys.
Proof. unfold Subset; intros; apply H0 in H1 as H2; apply set_add_elim in H2;
  destruct H2; (subst x; contradiction) || trivial. Qed.
 
Lemma subset_add_both_elim : forall (x : vname) ( xs ys : names ),
    ~ Elem x xs -> Subset (names_add x xs) (names_add x ys) -> Subset xs ys.
Proof. unfold Subset; intros. apply set_add_elim2 with Nat.eq_dec x.
  - apply H0. apply set_add_intro; intuition.
  - unfold not; intro; subst x; contradiction. Qed.

Lemma subset_add_commute : forall (x y : vname) (zs : names),
    Subset (names_add x (names_add y zs)) (names_add y (names_add x zs)).
Proof. unfold Subset; intros; apply set_add_intro; 
  apply set_add_elim in H; destruct H;
  try (right; apply set_add_intro2; apply H);
  apply set_add_elim in H; destruct H;
  try (left; apply H); right; apply set_add_intro1; apply H. Qed.

Lemma subset_add_to_diff : forall (xs ys : names) (y : vname),
    Subset xs (names_add y ys) -> Subset (diff xs (singleton y)) ys.
Proof. intros; unfold Subset; intros;
  apply set_diff_iff in H0; destruct H0;
  apply H in H0; apply set_add_elim in H0;
  destruct H0; try subst y; simpl in H1; intuition. Qed.

Lemma subset_diff_to_add : forall (xs ys : names) (y : vname),
    Subset (diff xs (singleton y)) ys -> Subset xs (names_add y ys).
Proof. intros; unfold Subset; intros;
  apply set_add_intro; destruct (x =? y) eqn:X;
  try apply Nat.eqb_eq in X; try (left; apply X);
  apply Nat.eqb_neq in X; right; apply H;
  apply set_diff_iff; split; simpl; intuition. Qed.

Lemma subset_diff_singleton : forall (x : vname) (xs ys : names),
    ~ Elem x xs -> Subset xs ys -> Subset xs (diff ys (singleton x)).
Proof. intros; unfold Subset; intros; apply set_diff_iff; split.
  - apply H0; apply H1.
  - unfold not; intros; apply elem_sing in H2; subst x0;
    apply H in H1; contradiction.
Qed.

Lemma union_empty_l : forall (ys : names), 
    Subset ys (union empty ys) /\ Subset (union empty ys) ys.
Proof. unfold Subset; split; intros.
  - apply set_union_intro2; assumption.
  - apply set_union_emptyL in H; assumption. Qed.

Lemma subset_union_intro_l : forall (xs ys zs : names),
    Subset xs zs -> Subset ys zs -> Subset (union xs ys) zs.
Proof. unfold Subset; intros; apply set_union_elim in H1;
  destruct H1; apply H in H1|| apply H0 in H1; assumption. Qed.

Lemma subset_union_intro_r : forall (xs zs : names),
    Subset xs (union xs zs) /\ Subset xs (union zs xs).
Proof. unfold Subset; split; intros;
  apply set_union_intro; intuition. Qed.

Lemma subset_union_elim_l : forall (xs ys zs : names),
    Subset (union xs ys) zs -> Subset xs zs /\ Subset ys zs.
Proof. unfold Subset; intros; split; intros; apply H;
  apply set_union_intro; [left | right]; apply H0. Qed.
  
Lemma subset_union_assoc : forall (xs ys zs : names),
    Subset (union (union xs ys) zs) (union xs (union ys zs)) /\
    Subset (union xs (union ys zs)) (union (union xs ys) zs).
Proof. unfold Subset; split; intros; apply set_union_elim in H;
  destruct H; try (apply set_union_elim in H; destruct H);
  apply set_union_intro;
  ( left;  apply H || apply set_union_intro; (left; apply H) || (right; apply H) ) || 
  ( right; apply H || apply set_union_intro; (left; apply H) || (right; apply H) ).
  Qed.

Lemma subset_union_commute : forall (xs ys : names),
    Subset (union xs ys) (union ys xs).
Proof. unfold Subset; intros; apply set_union_elim in H; 
  apply set_union_intro; intuition.
  Qed.  

Lemma subset_union_both : forall (xs ys xs' ys' : names),
    Subset xs xs' -> Subset ys ys' -> Subset (union xs ys) (union xs' ys').
Proof. unfold Subset; intros. apply set_union_elim in H1.
  destruct H1; apply H in H1 || apply H0 in H1.
  -  apply set_union_intro1; trivial.
  -  apply set_union_intro2; trivial. Qed.

Lemma subset_union_names_add_l : forall (xs ys : names) (x : vname),
    Subset (union (names_add x xs) ys) (names_add x (union xs ys)) /\
    Subset (names_add x (union xs ys)) (union (names_add x xs) ys).
Proof. unfold Subset; intros; split; intros.
  - apply set_union_elim in H. destruct H.
      * apply set_add_intro; apply set_add_elim in H; destruct H; 
        intuition; right. apply set_union_intro1; assumption.      
      * apply set_add_intro1; apply set_union_intro2; assumption.
  - apply set_add_elim in H; destruct H.
      * apply set_union_intro1; apply set_add_intro; intuition.  
      * apply set_union_elim in H; destruct H.
        apply set_union_intro1; apply set_add_intro1; assumption.
        apply set_union_intro2; assumption.  
  Qed.

Lemma subset_union_names_add_r : forall (xs ys : names) (y : vname),
    Subset (union xs (names_add y ys)) (names_add y (union xs ys)) /\
    Subset (names_add y (union xs ys)) (union xs (names_add y ys)).
Proof. unfold Subset; intros; split; intros.
  - apply set_union_elim in H. destruct H.
      * apply set_add_intro1; apply set_union_intro1; assumption.
      * apply set_add_intro; apply set_add_elim in H; destruct H; 
        intuition; right. apply set_union_intro2; assumption.
  - apply set_add_elim in H; destruct H.
      * apply set_union_intro2; apply set_add_intro; intuition.  
      * apply set_union_elim in H; destruct H.
        apply set_union_intro1; assumption. 
        apply set_union_intro2; apply set_add_intro1; assumption. 
  Qed.

Lemma subset_union_names_add_both : forall (xs ys : names) (z : vname),
    Subset (union (names_add z xs) (names_add z ys)) (names_add z (union xs ys)).
Proof. unfold Subset; intros.
  apply set_union_elim in H; destruct H; apply set_add_elim in H;
  apply set_add_intro; intuition; right; 
  (apply set_union_intro1; assumption) || (apply set_union_intro2; assumption). Qed.

Lemma intersect_empty_l : forall (xs : names), intersect empty xs = empty.
Proof. intro xs; apply no_elem_empty; unfold not; intros; 
  apply set_inter_elim in H; intuition. Qed.

Lemma intersect_empty_r : forall (xs : names), intersect xs empty = empty.
Proof. intro xs; apply no_elem_empty; unfold not; intros; 
  apply set_inter_elim in H; intuition. Qed.

Lemma intersect_names_add_intro_l : forall (x : vname) (xs ys : names),
    intersect xs ys = empty -> ~ Elem x ys -> intersect (names_add x xs) ys = empty.
Proof. intros; apply no_elem_empty; unfold not; intros.
  apply set_inter_elim in H1; destruct H1; 
  apply set_add_elim in H1; destruct H1.
  - subst x; contradiction.
  - apply set_inter_intro with vname Nat.eq_dec x0 xs ys in H1;
    ( apply empty_no_elem with (intersect xs ys) x0 in H; contradiction
      || assumption).
  Qed.

Lemma intersect_names_add_intro_r : forall (y : vname) (xs ys : names),
    intersect xs ys = empty -> ~ Elem y xs -> intersect xs (names_add y ys) = empty.
Proof. intros; apply no_elem_empty; unfold not; intros.
  apply set_inter_elim in H1; destruct H1; 
  apply set_add_elim in H2; destruct H2.
  - subst x; contradiction.
  - apply set_inter_intro with vname Nat.eq_dec x xs ys in H1;
    ( apply empty_no_elem with (intersect xs ys) x in H; contradiction
      || assumption).
  Qed.

Lemma intersect_names_add_elim_l : forall (x : vname) (xs ys : names),
    intersect (names_add x xs) ys = empty -> intersect xs ys = empty /\ ~ Elem x ys.
Proof. intros; split. 
  - apply no_elem_empty; unfold not; intros; 
    apply set_inter_elim in H0; destruct H0.
    apply empty_no_elem with (intersect (names_add x xs) ys) x0 in H.
    apply set_add_intro1 with vname Nat.eq_dec x0 x xs in H0.
    apply set_inter_intro with vname Nat.eq_dec x0 (names_add x xs) ys in H1;
    intuition.
  - unfold not; intros.
    apply empty_no_elem with (intersect (names_add x xs) ys) x in H.
    assert (x = x) by reflexivity.
    apply set_add_intro2 with vname Nat.eq_dec x x xs in H1. 
    apply set_inter_intro with vname Nat.eq_dec x (names_add x xs) ys in H0;
    intuition.
  Qed.  

Lemma intersect_names_add_elim_r : forall (y : vname) (xs ys : names),
    intersect xs (names_add y ys) = empty -> intersect xs ys = empty /\ ~ Elem y xs.
Proof. intros; split. 
  - apply no_elem_empty; unfold not; intros; 
    apply set_inter_elim in H0; destruct H0.
    apply empty_no_elem with (intersect xs (names_add y ys)) x in H.
    apply set_add_intro1 with vname Nat.eq_dec x y ys in H1.
    apply set_inter_intro with vname Nat.eq_dec x xs (names_add y ys) in H0;
    intuition.
  - unfold not; intros.
    apply empty_no_elem with (intersect xs (names_add y ys)) y in H.
    assert (y = y) by reflexivity.
    apply set_add_intro2 with vname Nat.eq_dec y y ys in H1.
    apply set_inter_intro with vname Nat.eq_dec y xs (names_add y ys) in H0;
    intuition.
  Qed.
  
Lemma subset_in_intersect : forall (xs ys zs : names),
    intersect xs zs = empty -> Subset ys zs -> intersect xs ys = empty.
Proof. intros; apply no_elem_empty; unfold not; intros. 
  apply set_inter_elim in H1; destruct H1; apply H0 in H2.
  assert (Elem x (intersect xs zs)) by (apply set_inter_intro; assumption);
  rewrite H in H3; intuition. Qed.

Lemma subset_union_diff : forall (xs ys zs : names),
    Subset (union (diff xs zs) (diff ys zs)) (diff (union xs ys) zs) /\
    Subset (diff (union xs ys) zs) (union (diff xs zs) (diff ys zs)).  
Proof. unfold Subset; intros; split; intros.
  - apply set_union_elim in H; destruct H; 
    apply set_diff_iff in H; destruct H; apply set_diff_iff; split;
    try ((apply set_union_intro1; apply H) || (apply set_union_intro2; apply H)); intuition. 
  - apply set_diff_iff in H; destruct H;
    apply set_union_elim in H; destruct H;
    apply (set_diff_intro Nat.eq_dec x xs zs) in H 
      || apply (set_diff_intro Nat.eq_dec x ys zs) in H; try assumption;
    (apply set_union_intro1; apply H) || (apply set_union_intro2; apply H).
  Qed.

  (* II. Name-sets of free variables *)

Fixpoint fv (e0:expr) : names := 
    match e0 with
    | (Bc _)          => empty
    | (Ic _)          => empty
    | (Prim _)        => empty
    | (BV _)          => empty
    | (FV x)          => singleton x
    | (Lambda   e)    => fv e 
    | (App e e')      => union (fv e) (fv e')
    | (LambdaT   k e) => fv e
    | (AppT e t)      => union (fv e) (free t)
    | (Let   ex e)    => union (fv ex) (fv e)
    | (Annot e t)     => union (fv e) (free t) 
    | (If e0 e1 e2)   => union (fv e0) (union (fv e1) (fv e2))
    | Nil t           => (free t) 
    | (Cons t e1 e2)  => union (free t) (union (fv e1) (fv e2))
    | (Switch e eN eC) => union (fv e) (union (fv eN) (fv eC))
    | Error           => empty
    end

with free (t0:type) : names :=
    match t0 with
    | (TRefn b   rs)     => fvP rs
    | (TFunc   t_x t)    => union (free t_x) (free t) 
    | (TExists   t_x t)  => union (free t_x) (free t) 
    | (TPoly   k   t)    => free t
    | (TList    t ps)    => union (free t) (fvP ps)
    end

with fvP (ps0:preds) : names :=
    match ps0 with
    | PEmpty       => empty
    | (PCons p ps) => union (fv p) (fvP ps)
    end. 

Fixpoint ftv (e0:expr) : names := 
    match e0 with
    | (Bc _)          => empty
    | (Ic _)          => empty
    | (Prim _)        => empty
    | (BV _)          => empty
    | (FV x)          => empty
    | (Lambda   e)    => ftv e 
    | (App e e')      => union (ftv e) (ftv e')
    | (LambdaT   k e) => ftv e
    | (AppT e t)      => union (ftv e) (freeTV t)
    | (Let   ex e)    => union (ftv ex) (ftv e) 
    | (Annot e t)     => union (ftv e) (freeTV t) 
    | (If e0 e1 e2)   => union (ftv e0) (union (ftv e1) (ftv e2))
    | Nil t           => freeTV t
    | (Cons t e1 e2)  => union (freeTV t) (union (ftv e1) (ftv e2))
    | (Switch e eN eC) => union (ftv e) (union (ftv eN) (ftv eC)) 
    | Error           => empty
    end

with freeTV (t0:type) : names :=
    match t0 with
    | (TRefn b   r)      => match b with
                            | (FTV a)  => names_add a (ftvP r)
                            | _        => ftvP r
                            end
    | (TFunc   t_x t)    => union (freeTV t_x) (freeTV t) 
    | (TExists   t_x t)  => union (freeTV t_x) (freeTV t) 
    | (TPoly   k   t)    => freeTV t 
    | (TList   t   ps)   => union (freeTV t) (ftvP ps)
    end

with ftvP (ps0:preds) : names :=
    match ps0 with
    | PEmpty       => empty
    | (PCons p ps) => union (ftv p) (ftvP ps) 
    end.


Fixpoint ffreeTV (t0:ftype) : names :=
    match t0 with
    | (FTBasic b)      => match b with
                          | (FTV a)   => singleton a
                          | _         => empty
                          end
    | (FTFunc t_x t)   => union (ffreeTV t_x) (ffreeTV t) 
    | (FTPoly   k t)   => ffreeTV t
    | (FTList     t)   => ffreeTV t
    end.

Lemma lem_erase_freeTV : forall (t:type),
    Subset (ffreeTV (erase t)) (freeTV t).
Proof. induction t; simpl.
  - destruct b; try apply subset_empty_l;
    apply subset_sing_l; apply set_add_intro2;
    reflexivity.
  - apply subset_union_both; assumption.
  - unfold Subset; intros; apply set_union_intro;
    right; apply IHt2; apply H.
  - apply IHt.
  - apply subset_trans with (freeTV t); 
    apply IHt || apply subset_union_intro_r. 
  Qed.
  
    (* III. Free variables under substiution etc *)

Lemma fv_open_at_intro : ( forall (e:expr) (j:index) (y:vname) ,
    Subset (fv e) (fv (open_at j y e))  ) * ((
  forall (t:type) (j:index) (y:vname) ,
    Subset (free t) (free (openT_at j y t)) ) * (
  forall (ps:preds) (j:index) (y:vname) ,
    Subset (fvP ps) (fvP (openP_at j y ps)) )).
Proof. apply ( syntax_mutind
  ( fun e : expr => forall (j:index) (y:vname) ,
    Subset (fv e) (fv (open_at j y e))  )
  ( fun t : type => forall (j:index) (y:vname) ,
    Subset (free t) (free (openT_at j y t)) )
  ( fun ps : preds => forall (j:index) (y:vname) ,
    Subset (fvP ps) (fvP (openP_at j y ps)) ))
  ; simpl; intros
       ; try (apply subset_empty_l)
       ; try (apply subset_refl)
       ; (* one IH *) try ( apply H)
       ; (* two IH *) try ( apply subset_union_both; apply H || apply H0 )
       ; (* 3 IH *) try ( apply subset_union_both; 
                          apply H || apply subset_union_both; trivial).
  Qed.

Lemma fv_unbind_intro : ( forall (e:expr) (y:vname) ,
    Subset (fv e) (fv (unbind y e))  ) * ((
  forall (t:type) (y:vname) ,
    Subset (free t) (free (unbindT y t)) ) * (
  forall (ps:preds) (y:vname) ,
    Subset (fvP ps) (fvP (unbindP y ps)) )).
Proof. repeat split; intros; apply fv_open_at_intro. Qed.

Lemma fv_open_at_elim : ( forall (e:expr) (j:index) (y:vname) ,
    Subset (fv (open_at j y e)) (names_add y (fv e)) ) * ((
  forall (t:type) (j:index) (y:vname) ,
    Subset (free (openT_at j y t)) (names_add y (free t))) * (
  forall (ps:preds) (j:index) (y:vname) ,
    Subset (fvP (openP_at j y ps)) (names_add y (fvP ps)) )).
Proof. apply ( syntax_mutind
  ( fun e : expr => forall (j:index) (y:vname) ,
    Subset (fv (open_at j y e)) (names_add y (fv e)) )
  ( fun t : type => forall (j:index) (y:vname) ,
    Subset (free (openT_at j y t)) (names_add y (free t)) )
  ( fun ps : preds => forall (j:index) (y:vname) ,
    Subset (fvP (openP_at j y ps)) (names_add y (fvP ps))))
  ; simpl; intros
       ; try (apply subset_empty_l)
       ; (* one IH *) try ( apply H )
       ; (* two IH *) try ( apply subset_trans 
              with (union (names_add y (fv e1)) (names_add y (fv e2))) ||
            apply subset_trans  
              with (union (names_add y (fv e)) (names_add y (free t))) ||
            apply subset_trans 
              with (union (names_add y (free tx)) (names_add y (free t))) ||
            apply subset_trans 
              with (union (names_add y (free t)) (names_add y (fvP ps))) ||
            apply subset_trans 
              with (union (names_add y (fv p)) (names_add y (fvP ps)));
          try apply subset_union_both; 
          try apply subset_union_names_add_both; apply H || apply H0).
       - (* BV *) destruct (j =? i); simpl;
          apply subset_empty_l || apply subset_sing_l; simpl; left; reflexivity.
       - (* FV *) destruct (Nat.eq_dec y x); apply subset_sing_l;
          simpl; left; reflexivity.
       - (* If *) apply subset_trans3 
            with (union (names_add y (fv e0)) (union (names_add y (fv e1)) (names_add y (fv e2))))
                 (union (names_add y (fv e0)) (names_add y (union (fv e1) (fv e2))));
          try apply subset_union_both; try apply subset_union_both;
          try apply subset_union_names_add_both; try apply subset_refl;
          apply H || apply H0 || apply H1.
       - (* Cons [t] e1 e2 *) apply subset_trans3 
            with (union (names_add y (free t)) (union (names_add y (fv e1)) (names_add y (fv e2))))
                 (union (names_add y (free t)) (names_add y (union (fv e1) (fv e2))));
          try apply subset_union_both; try apply subset_union_both;
          try apply subset_union_names_add_both; try apply subset_refl;
          apply H || apply H0 || apply H1.
       - (* Switch *) apply subset_trans3 
            with (union (names_add y (fv e)) (union (names_add y (fv eN)) (names_add y (fv eC))))
                 (union (names_add y (fv e)) (names_add y (union (fv eN) (fv eC))));
          try apply subset_union_both; try apply subset_union_both;
          try apply subset_union_names_add_both; try apply subset_refl;
          apply H || apply H0 || apply H1.
  Qed.

Lemma fv_unbind_elim : ( forall (e:expr) (y:vname) ,
    Subset (fv (unbind y e)) (names_add y (fv e)) ) * ((
  forall (t:type) (y:vname) ,
    Subset (free (unbindT y t)) (names_add y (free t))) * (
  forall (ps:preds) (y:vname) ,
    Subset (fvP (unbindP y ps)) (names_add y (fvP ps)) )).
Proof. repeat split; intros; apply fv_open_at_elim. Qed. 

Lemma ftv_open_at_intro : ( forall (e:expr) (j:index) (y:vname) ,
    Subset (ftv e) (ftv (open_at j y e))  ) * ((
  forall (t:type) (j:index) (y:vname) ,
    Subset (freeTV t) (freeTV (openT_at j y t)) ) * (
  forall (ps:preds) (j:index) (y:vname) ,
    Subset (ftvP ps) (ftvP (openP_at j y ps)) )).
Proof. apply ( syntax_mutind
  ( fun e : expr => forall (j:index) (y:vname) ,
    Subset (ftv e) (ftv (open_at j y e))  )
  ( fun t : type => forall (j:index) (y:vname) ,
    Subset (freeTV t) (freeTV (openT_at j y t)) )
  ( fun ps : preds => forall (j:index) (y:vname) ,
    Subset (ftvP ps) (ftvP (openP_at j y ps)) ))
  ; simpl; intros
      ; try (apply subset_empty_l)
      ; try (apply subset_refl)
      ; (* TRefn *)  try destruct b; try (apply subset_add_both_intro)
      ; (* one IH *) try ( apply H )
      ; (* two IH *) try ( apply subset_union_both; apply H || apply H0 )
      ; (* 3 IH *) try ( apply subset_union_both; 
                         apply H || apply subset_union_both; trivial).
  Qed.

Lemma ftv_unbind_intro : ( forall (e:expr) (y:vname) ,
    Subset (ftv e) (ftv (unbind y e))  ) * ((
  forall (t:type) (y:vname) ,
    Subset (freeTV t) (freeTV (unbindT y t)) ) * (
  forall (ps:preds) (y:vname) ,
    Subset (ftvP ps) (ftvP (unbindP y ps)) )).
Proof. repeat split; intros; apply ftv_open_at_intro. Qed. 

Lemma ftv_open_at_elim : ( forall (e:expr) (j:index) (y:vname) ,
    Subset (ftv (open_at j y e)) (ftv e)) * ((
  forall (t:type) (j:index) (y:vname) ,
    Subset (freeTV (openT_at j y t)) (freeTV t)) * (
  forall (ps:preds) (j:index) (y:vname) ,
    Subset (ftvP (openP_at j y ps)) (ftvP ps) )).
Proof. apply ( syntax_mutind
  ( fun e : expr => forall (j:index) (y:vname) ,
    Subset (ftv (open_at j y e)) (ftv e) )
  ( fun t : type => forall (j:index) (y:vname) ,
    Subset (freeTV (openT_at j y t)) (freeTV t))
  ( fun ps : preds => forall (j:index) (y:vname) ,
    Subset (ftvP (openP_at j y ps)) (ftvP ps)))
  ; simpl; intros
       ; try (apply subset_empty_l)
       ; (* one IH *) try ( apply H )
       ; (* two IH *) try ( apply subset_union_both;  
                            apply H || apply H0)
       ; (* 3 IH *) try ( apply subset_union_both; 
                          try apply subset_union_both;
                          apply H || apply H0 || apply H1).
       - (* BV *) destruct (j =? i); simpl;
          apply subset_empty_l || apply subset_sing_l; 
          simpl; left; reflexivity.
       - (* SBase *) destruct b; 
         try apply subset_add_both_intro; apply H.
  Qed.

Lemma ftv_unbind_elim : ( forall (e:expr) (y:vname) ,
    Subset (ftv (unbind y e)) (ftv e) ) * ((
  forall (t:type) (y:vname) ,
    Subset (freeTV (unbindT y t)) (freeTV t)) * (
  forall (ps:preds) (y:vname) ,
    Subset (ftvP (unbindP y ps)) (ftvP ps))).
Proof. repeat split; intros; apply ftv_open_at_elim. Qed. 


Lemma fv_open_tv_at_intro : ( forall (e:expr) (j:index) (a:vname) ,
  Subset (fv e) (fv (open_tv_at j a e))  ) * ((
forall (t:type) (j:index) (a:vname) ,
  Subset (free t) (free (open_tvT_at j a t)) ) * (
forall (ps:preds) (j:index) (a:vname) ,
  Subset (fvP ps) (fvP (open_tvP_at j a ps)) )).
Proof. apply ( syntax_mutind
  ( fun e : expr => forall (j:index) (a:vname) ,
    Subset (fv e) (fv (open_tv_at j a e))  )
  ( fun t : type => forall (j:index) (a:vname) ,
    Subset (free t) (free (open_tvT_at j a t)) )
  ( fun ps : preds => forall (j:index) (a:vname) ,
    Subset (fvP ps) (fvP (open_tvP_at j a ps)) ))
  ; simpl; intros
      ; try (apply subset_empty_l)
      ; try (apply subset_refl)
      ; (* TRefn *)  try destruct b; try destruct (j =? i)
      ; (* one IH *) try ( apply H)
      ; (* two IH *) try ( apply subset_union_both; apply H || apply H0 )
      ; (* 3 IH *) try ( apply subset_union_both; 
                         apply H || apply subset_union_both; trivial).
Qed.

Lemma fv_unbind_tv_intro : ( forall (e:expr) (a:vname) ,
    Subset (fv e) (fv (unbind_tv a e))  ) * ((
  forall (t:type) (a:vname) ,
    Subset (free t) (free (unbind_tvT a t)) ) * (
  forall (ps:preds) (a:vname) ,
    Subset (fvP ps) (fvP (unbind_tvP a ps)) )).
Proof. repeat split; intros; apply fv_open_tv_at_intro. Qed. 

Lemma fv_open_tv_at_elim : ( forall (e:expr) (j:index) (a:vname) ,
    Subset (fv (open_tv_at j a e)) (names_add a (fv e)) ) * ((
  forall (t:type) (j:index) (a:vname) ,
    Subset (free (open_tvT_at j a t)) (names_add a (free t))) * (
  forall (ps:preds) (j:index) (a:vname) ,
    Subset (fvP (open_tvP_at j a ps)) (names_add a (fvP ps)) )).
Proof. apply ( syntax_mutind
  ( fun e : expr => forall (j:index) (a:vname) ,
    Subset (fv (open_tv_at j a e)) (names_add a (fv e)) )
  ( fun t : type => forall (j:index) (a:vname) ,
    Subset (free (open_tvT_at j a t)) (names_add a (free t)))
  ( fun ps : preds => forall (j:index) (a:vname) ,
    Subset (fvP (open_tvP_at j a ps)) (names_add a (fvP ps))))
  ; simpl; intros
       ; try (apply subset_empty_l)
       ; (* one IH *) try ( apply H )
       ; (* two IH *) try ( apply subset_trans 
              with (union (names_add a (fv e1)) (names_add a (fv e2))) ||
            apply subset_trans  
              with (union (names_add a (fv e)) (names_add a (free t))) ||
            apply subset_trans 
              with (union (names_add a (free tx)) (names_add a (free t))) ||
            apply subset_trans 
              with (union (names_add a (free t)) (names_add a (fvP ps))) ||
            apply subset_trans 
              with (union (names_add a (fv p)) (names_add a (fvP ps)));
          try apply subset_union_both; 
          try apply subset_union_names_add_both; apply H || apply H0).
       - (* FV *) destruct (Nat.eq_dec a x); apply subset_sing_l;
          simpl; left; reflexivity.
       - (* If *) apply subset_trans3 
            with (union (names_add a (fv e0)) (union (names_add a (fv e1)) (names_add a (fv e2))))
                 (union (names_add a (fv e0)) (names_add a (union (fv e1) (fv e2))));
          try apply subset_union_both; try apply subset_union_both;
          try apply subset_union_names_add_both; try apply subset_refl;
          apply H || apply H0 || apply H1.
       - (* Cons *) apply subset_trans3 
            with (union (names_add a (free t)) (union (names_add a (fv e1)) (names_add a (fv e2))))
                 (union (names_add a (free t)) (names_add a (union (fv e1) (fv e2))));
          try apply subset_union_both; try apply subset_union_both;
          try apply subset_union_names_add_both; try apply subset_refl;
          apply H || apply H0 || apply H1.  
       - (* Switch *) apply subset_trans3 
            with (union (names_add a (fv e)) (union (names_add a (fv eN)) (names_add a (fv eC))))
                 (union (names_add a (fv e)) (names_add a (union (fv eN) (fv eC))));
          try apply subset_union_both; try apply subset_union_both;
          try apply subset_union_names_add_both; try apply subset_refl;
          apply H || apply H0 || apply H1.          
       - (* TRefn *) destruct b; try destruct (j =? i); simpl; apply H.
  Qed.

Lemma fv_unbind_tv_elim : ( forall (e:expr) (a:vname) ,
    Subset (fv (unbind_tv a e)) (names_add a (fv e)) ) * ((
  forall (t:type) (a:vname) ,
    Subset (free (unbind_tvT a t)) (names_add a (free t))) * (
  forall (ps:preds) (a:vname) ,
    Subset (fvP (unbind_tvP a ps)) (names_add a (fvP ps)) )).
Proof. repeat split; intros; apply fv_open_tv_at_elim. Qed. 

Lemma ftv_open_tv_at_intro : ( forall (e:expr) (j:index) (a:vname) ,
    Subset (ftv e) (ftv (open_tv_at j a e))  ) * ((
  forall (t:type) (j:index) (a:vname) ,
    Subset (freeTV t) (freeTV (open_tvT_at j a t)) ) * (
  forall (ps:preds) (j:index) (a:vname) ,
    Subset (ftvP ps) (ftvP (open_tvP_at j a ps)) )).
Proof. apply ( syntax_mutind
  ( fun e : expr => forall (j:index) (a:vname) ,
    Subset (ftv e) (ftv (open_tv_at j a e))  )
  ( fun t : type => forall (j:index) (a:vname) ,
    Subset (freeTV t) (freeTV (open_tvT_at j a t)) )
  ( fun ps : preds => forall (j:index) (a:vname) ,
    Subset (ftvP ps) (ftvP (open_tvP_at j a ps)) ))
  ; simpl; intros
      ; try (apply subset_empty_l)
      ; try (apply subset_refl)
      ; (* TRefn *)  try destruct b; try destruct (j =? i);
                      try (apply subset_add_both_intro);  try (apply subset_add_intro)
      ; (* one IH *) try ( apply H)
      ; (* two IH *) try ( apply subset_union_both; apply H || apply H0 )
      ; (* 3 IH *) try ( apply subset_union_both; 
                         apply H || apply subset_union_both; trivial).
  Qed.

Lemma ftv_unbind_tv_intro : ( forall (e:expr) (a:vname) ,
    Subset (ftv e) (ftv (unbind_tv a e))  ) * ((
  forall (t:type) (a:vname) ,
    Subset (freeTV t) (freeTV (unbind_tvT a t)) ) * (
  forall (ps:preds) (a:vname) ,
    Subset (ftvP ps) (ftvP (unbind_tvP a ps)) )).
Proof. repeat split; intros; apply ftv_open_tv_at_intro. Qed. 

Lemma ffreeTV_openFT_at_intro : forall (t:ftype) (j:index) (a:vname),
    Subset (ffreeTV t) (ffreeTV (openFT_at j a t)).
Proof. induction t; intros; simpl.
  - destruct b; simpl; try apply subset_refl; try apply subset_empty_l.
  - apply subset_union_both; apply IHt1 || apply IHt2.
  - apply IHt.
  - apply IHt.
  Qed. 



Lemma fv_subFV_elim : ( forall (e:expr) (x:vname) (v:expr),
    Subset (fv (subFV x v e)) (union (diff (fv e) (singleton x)) (fv v))  ) * ((
  forall (t:type) (x:vname) (v:expr),
    Subset (free (tsubFV x v t)) (union (diff (free t) (singleton x)) (fv v)) ) * (
  forall (ps:preds) (x:vname) (v:expr),
    Subset (fvP (psubFV x v ps)) (union (diff (fvP ps) (singleton x)) (fv v)) )).
Proof. apply ( syntax_mutind
  ( fun e : expr => forall (x:vname) (v:expr),
    Subset (fv (subFV x v e)) (union (diff (fv e) (singleton x)) (fv v))  )
  ( fun t : type => forall (x:vname) (v:expr),
    Subset (free (tsubFV x v t)) (union (diff (free t) (singleton x)) (fv v)) )
  ( fun ps : preds => forall (x:vname) (v:expr) ,
    Subset (fvP (psubFV x v ps)) (union (diff (fvP ps) (singleton x)) (fv v)) ))
  ; intros; simpl
  ; try (apply subset_empty_l)
  ; (* one IH *) try ( apply H)
  ; (* two IH *) try ( unfold Subset; intros; 
    apply set_union_elim in H1; destruct H1; 
    apply H in H1 || apply H0 in H1;
    apply set_union_elim in H1; destruct H1; apply set_union_intro; 
    intuition; left; 
    apply set_diff_intro; apply set_diff_iff in H1; destruct H1;
    try assumption; apply set_union_intro; intuition )
  ; (* 3 IH *) try ( unfold Subset; intros; apply set_union_elim in H2; destruct H2;
    try apply set_union_elim in H2; try destruct H2;
    apply H in H2 || apply H0 in H2 || apply H1 in H2;
    apply set_union_elim in H2; destruct H2; apply set_union_intro; 
    intuition; left;
    apply set_diff_intro; apply set_diff_iff in H2; destruct H2;
    try assumption; apply set_union_intro; 
    (left; assumption) || (right; apply set_union_intro); intuition ).
  - destruct (x0 =? x) eqn:E; simpl; 
    apply Nat.eqb_eq in E || apply Nat.eqb_neq in E; 
    symmetry in E || apply Nat.neq_sym in E;
    destruct (Nat.eq_dec x x0) eqn:D; try contradiction.
    * apply union_empty_l. 
    * apply subset_sing_l; apply set_union_intro1; simpl; intuition.
  Qed.

Lemma free_tsubFV_bounded : forall (x:vname) (v_x:expr) (t:type) (ys : names),
    Subset (fv v_x) ys -> Subset (free t) (names_add x ys)
        -> Subset (free (tsubFV x v_x t)) ys.
Proof. intros; apply subset_trans with (union (diff (free t) (singleton x)) (fv v_x));
  try apply fv_subFV_elim; apply subset_union_intro_l; try apply H;
  unfold Subset; intros; apply set_diff_iff in H1; destruct H1;
  apply H0 in H1; apply set_add_elim in H1; destruct H1;
  (apply elem_sing in H1; contradiction) || assumption.
  Qed.

Lemma fv_subFV_intro : ( forall (e:expr) (x:vname) (v:expr),
    Subset (fv e) (names_add x (fv (subFV x v e))) ) * ((  
  forall (t:type) (x:vname) (v:expr),
    Subset (free t) (names_add x (free (tsubFV x v t))) ) * (
  forall (ps:preds) (x:vname) (v:expr),
    Subset (fvP ps) (names_add x (fvP (psubFV x v ps))) )).
Proof. apply ( syntax_mutind
  ( fun e : expr => forall (x:vname) (v:expr),
    Subset (fv e) (names_add x (fv (subFV x v e)))  )
  ( fun t : type => forall (x:vname) (v:expr),
    Subset (free t) (names_add x (free (tsubFV x v t)))  )
  ( fun ps : preds => forall (x:vname) (v:expr) ,
    Subset (fvP ps) (names_add x (fvP (psubFV x v ps)))  ))
  ; intros; simpl
  ; try (apply subset_empty_l) 
  ; (* one IH *) try ( apply H) 
  ; (* two IH *) try ( 
    pose proof (subset_union_both _ _ _ _ (H x v) (H0 x v));
    unfold Subset; intros; apply H1 in H2;
    apply set_union_elim in H2; destruct H2;
    apply set_add_elim in H2;
    apply set_add_intro; intuition; right;
    (apply set_union_intro1; apply H3) || 
        (apply set_union_intro2; apply H3)) .
  - destruct (x0 =? x) eqn:E;
    apply Nat.eqb_eq in E || apply Nat.eqb_neq in E;
    try subst x0; unfold singleton;
    try apply subset_add_both_intro;
    try apply subset_empty_l.
    unfold Subset; intros; apply set_add_elim in H;
    destruct H; try subst x1;
    apply set_add_intro; right; unfold fv; simpl; 
    left; try reflexivity; contradiction.
  - apply subset_trans5 with
      (union (names_add x (fv (subFV x v e0)))
             (union (fv e1) (fv e2)))
      (union (names_add x (fv (subFV x v e0)))
             (union (names_add x (fv (subFV x v e1))) (names_add x (fv (subFV x v e2)))))
      (union (names_add x (fv (subFV x v e0)))
             (union (names_add x (fv (subFV x v e1))) (names_add x (fv (subFV x v e2)))))
      (union (names_add x (fv (subFV x v e0)))
             (names_add x (union (fv (subFV x v e1)) (fv (subFV x v e2)))));
    try apply subset_union_both; 
    try apply subset_union_both;
    try apply subset_union_names_add_both;
    try apply subset_refl; auto. 
  - (* Cons [t] e1 e2 *) apply subset_trans5 with
      (union (names_add x (free (tsubFV x v t)))
             (union (fv e1) (fv e2)))
      (union (names_add x (free (tsubFV x v t)))
             (union (names_add x (fv (subFV x v e1))) (names_add x (fv (subFV x v e2)))))
      (union (names_add x (free (tsubFV x v t)))
             (union (names_add x (fv (subFV x v e1))) (names_add x (fv (subFV x v e2)))))
      (union (names_add x (free (tsubFV x v t)))
             (names_add x (union (fv (subFV x v e1)) (fv (subFV x v e2)))));
    try apply subset_union_both; 
    try apply subset_union_both;
    try apply subset_union_names_add_both;
    try apply subset_refl; auto. 
  - apply subset_trans5 with
      (union (names_add x (fv (subFV x v e)))
             (union (fv eN) (fv eC)))
      (union (names_add x (fv (subFV x v e)))
             (union (names_add x (fv (subFV x v eN))) (names_add x (fv (subFV x v eC)))))
      (union (names_add x (fv (subFV x v e)))
             (union (names_add x (fv (subFV x v eN))) (names_add x (fv (subFV x v eC)))))
      (union (names_add x (fv (subFV x v e)))
             (names_add x (union (fv (subFV x v eN)) (fv (subFV x v eC)))));
    try apply subset_union_both; 
    try apply subset_union_both;
    try apply subset_union_names_add_both;
    try apply subset_refl; auto. 
  Qed.


Lemma ftv_subFV_elim : ( forall (e:expr) (x:vname) (v:expr),
    Subset (ftv (subFV x v e)) (union (ftv e) (ftv v))  ) * ((
  forall (t:type) (x:vname) (v:expr),
    Subset (freeTV (tsubFV x v t)) (union (freeTV t) (ftv v)) ) * (
  forall (ps:preds) (x:vname) (v:expr),
    Subset (ftvP (psubFV x v ps)) (union (ftvP ps) (ftv v)) )).
Proof. apply ( syntax_mutind
  ( fun e : expr => forall (x:vname) (v:expr),
    Subset (ftv (subFV x v e)) (union (ftv e) (ftv v))  )
  ( fun t : type => forall (x:vname) (v:expr),
    Subset (freeTV (tsubFV x v t)) (union (freeTV t) (ftv v)) )
  ( fun ps : preds => forall (x:vname) (v:expr) ,
    Subset (ftvP (psubFV x v ps)) (union (ftvP ps) (ftv v)) ))
  ; intros; simpl
  ; try (apply subset_empty_l)
  ; (* one IH *) try ( apply H)
  ; (* two IH *) try ( unfold Subset; intros; 
    apply set_union_elim in H1; destruct H1;
    apply H in H1 || apply H0 in H1;
    apply set_union_elim in H1; destruct H1; apply set_union_intro;
    intuition; left; apply set_union_intro; intuition )
  ; (* 3 IH *) try ( unfold Subset; intros;
    repeat( apply set_union_elim in H2; destruct H2);
    apply H in H2 || apply H0 in H2 || apply H1 in H2;
    apply set_union_elim in H2; destruct H2; apply set_union_intro;
    intuition; left; apply set_union_intro; 
    intuition; right; apply set_union_intro; intuition  ).
  - (* FV *) destruct (x0 =? x) eqn:E; simpl;
    apply union_empty_l || apply subset_empty_l.
  - (* TRefn *) destruct b; try apply H.
    apply subset_trans with (names_add a (union (ftvP ps) (ftv v))).
    * apply subset_add_both_intro; apply H. 
    * apply subset_union_names_add_l.
  Qed.

Lemma freeTV_tsubFV_bounded : forall (x:vname) (v_x:expr) (t:type) (ys : names),
    Subset (ftv v_x) ys -> Subset (freeTV t) ys
        -> Subset (freeTV (tsubFV x v_x t)) ys.
Proof. intros; apply subset_trans with (union (freeTV t) (ftv v_x));
  try apply ftv_subFV_elim; apply subset_union_intro_l; try apply H; apply H0.
  Qed.
  
Lemma ftv_subFV_intro : ( forall (e:expr) (x:vname) (v:expr),
    Subset (ftv e) (ftv (subFV x v e)) ) * ((
  forall (t:type) (x:vname) (v:expr),
    Subset (freeTV t) (freeTV (tsubFV x v t)) ) * (
  forall (ps:preds) (x:vname) (v:expr),
    Subset (ftvP ps) (ftvP (psubFV x v ps)) )).
Proof. apply ( syntax_mutind
  ( fun e : expr => forall (x:vname) (v:expr),
    Subset (ftv e) (ftv (subFV x v e))  )
  ( fun t : type => forall (x:vname) (v:expr),
    Subset (freeTV t) (freeTV (tsubFV x v t))  )
  ( fun ps : preds => forall (x:vname) (v:expr) ,
    Subset (ftvP ps) (ftvP (psubFV x v ps))  ))
  ; intros; simpl
  ; try (apply subset_empty_l) 
  ; (* one IH *) try ( apply H) 
  ; (* 2+  IH *) try ( repeat apply subset_union_both; trivial ).
  - destruct b; try apply subset_add_both_intro; apply H.
  Qed.


Lemma fv_strengthen_elim : forall (ps qs : preds),
    Subset ( fvP (strengthen ps qs)) (union (fvP ps) (fvP qs)).
Proof. intros; induction ps; simpl.
  - apply subset_union_intro_r; apply subset_refl.
  - apply subset_trans with (union (fv p) (union (fvP ps) (fvP qs))).
    * apply subset_union_both; try apply subset_refl; apply IHps.
    * apply subset_union_assoc.
  Qed.

Lemma fv_strengthen_intro : forall (ps qs : preds),
    Subset (union (fvP ps) (fvP qs)) ( fvP (strengthen ps qs)) .
Proof. intros; induction ps; simpl.
  - apply subset_union_intro_l; try apply subset_empty_l; apply subset_refl.
  - apply subset_trans with (union (fv p) (union (fvP ps) (fvP qs))).
    * apply subset_union_assoc.
    * apply subset_union_both; try apply subset_refl; apply IHps.     
  Qed.

Lemma ftv_strengthen_elim : forall (ps qs : preds),
    Subset ( ftvP (strengthen ps qs)) (union (ftvP ps) (ftvP qs)).
Proof. intros; induction ps; simpl.
  - apply subset_union_intro_r; apply subset_refl.
  - apply subset_trans with (union (ftv p) (union (ftvP ps) (ftvP qs))).
    * apply subset_union_both; try apply subset_refl; apply IHps.
    * apply subset_union_assoc.
  Qed.

Lemma ftv_strengthen_intro : forall (ps qs : preds),
    Subset (union (ftvP ps) (ftvP qs)) ( ftvP (strengthen ps qs)).
Proof. intros; induction ps; simpl.
  - apply subset_union_intro_l; try apply subset_empty_l; apply subset_refl.
  - apply subset_trans with (union (ftv p) (union (ftvP ps) (ftvP qs))).
    * apply subset_union_assoc.
    * apply subset_union_both; try apply subset_refl; apply IHps.
  Qed.

Lemma fv_push_elim : forall (ps : preds) (t_a : type),
    noExists t_a -> Subset (free (push ps t_a)) (union (fvP ps) (free t_a)).
Proof. intros; destruct t_a; simpl in H; try contradiction; unfold push.
  - (* TRefn *) apply fv_strengthen_elim.
  - (* TFunc *) apply subset_union_intro_r.
  - (* TPoly *) apply subset_union_intro_r.
  - (* TList *) apply subset_union_intro_r.
  Qed.

Lemma ftv_push_elim : forall (ps : preds) (t_a : type),
    noExists t_a -> Subset (freeTV (push ps t_a)) (union (ftvP ps) (freeTV t_a)).
Proof. intros; destruct t_a; simpl in H; try contradiction; simpl.
  - (* TRefn *) destruct b; simpl; try apply ftv_strengthen_elim.
    apply subset_trans with (names_add a (union (ftvP ps) (ftvP ps0)));
    try apply subset_union_names_add_r; 
    apply subset_add_both_intro; apply ftv_strengthen_elim.
  - (* TFunc *) apply subset_union_intro_r.
  - (* TPoly *) apply subset_union_intro_r.
  - (* TList*) apply subset_union_intro_r.
  Qed.


  
Lemma fv_subFTV_elim : ( forall (e:expr) (a:vname) (t_a:type),
    noExists t_a -> Subset (fv (subFTV a t_a e)) (union (fv e) (free t_a))  ) * ((
  forall (t:type) (a:vname) (t_a:type),
    noExists t_a -> Subset (free (tsubFTV a t_a t)) (union (free t) (free t_a)) ) * (
  forall (ps:preds) (a:vname) (t_a:type),
    noExists t_a -> Subset (fvP (psubFTV a t_a ps)) (union (fvP ps) (free t_a)) )).
Proof. apply ( syntax_mutind
  ( fun e : expr => forall (a:vname) (t_a:type),
    noExists t_a -> Subset (fv (subFTV a t_a e)) (union (fv e) (free t_a))  )
  ( fun t : type => forall (a:vname) (t_a:type),
    noExists t_a -> Subset (free (tsubFTV a t_a t)) (union (free t) (free t_a)) )
  ( fun ps : preds => forall (a:vname) (t_a:type),
    noExists t_a -> Subset (fvP (psubFTV a t_a ps)) (union (fvP ps) (free t_a)) ))
  ; intros; simpl
  ; try (apply subset_empty_l)
  ; (* one IH *) try ( apply H; apply H0 )
  ; (* two IH *) try ( unfold Subset; intros; 
    apply set_union_elim in H2; destruct H2;
    apply H in H2 || apply H0 in H2; try apply H1;
    apply set_union_elim in H2; destruct H2; apply set_union_intro;
    intuition; left; apply set_union_intro; intuition )
  ; (* 3 IH *) try ( unfold Subset; intros;
    repeat (apply set_union_elim in H3; destruct H3);
    apply H in H3 || apply H0 in H3 || apply H1 in H3; try assumption;
    apply set_union_elim in H3; destruct H3; apply set_union_intro; 
    intuition; left; apply set_union_intro; 
    intuition; right; apply set_union_intro; intuition ) .
  - (* FV *) apply subset_union_intro_r.
  - (* TRefn *) destruct b; try destruct (a =? a0); simpl; 
    try apply H; try apply H0. 
    apply subset_trans with (union (fvP (psubFTV a t_a ps)) (free t_a));
    try apply fv_push_elim; try apply H0.
    apply subset_trans with (union (union (fvP ps) (free t_a)) (free t_a)).
    * apply subset_union_both; try apply subset_refl; apply H; apply H0.
    * apply subset_trans with (union (fvP ps) (union (free t_a) (free t_a)));
      try apply subset_union_assoc; apply subset_union_both;
      try apply subset_union_intro_l; apply subset_refl.
  Qed. 

Lemma free_tsubFTV_bounded : forall (a:vname) (t_a:type) (t:type) (ys : names),
    noExists t_a -> Subset (free t_a) ys -> Subset (free t) ys
        -> Subset (free (tsubFTV a t_a t)) ys.
Proof. intros; apply subset_trans with (union (free t) (free t_a));
  try apply fv_subFTV_elim; try apply H;
  apply subset_union_intro_l; try apply H0; apply H1.
  Qed.

Lemma ftv_subFTV_elim : ( forall (e:expr) (a:vname) (t_a:type),
    noExists t_a 
      -> Subset (ftv (subFTV a t_a e)) (union (diff (ftv e) (singleton a)) (freeTV t_a))  ) * ((
  forall (t:type) (a:vname) (t_a:type),
    noExists t_a 
      -> Subset (freeTV (tsubFTV a t_a t)) (union (diff (freeTV t) (singleton a)) (freeTV t_a)) ) * (
  forall (ps:preds) (a:vname) (t_a:type),
    noExists t_a 
      -> Subset (ftvP (psubFTV a t_a ps)) (union (diff (ftvP ps) (singleton a)) (freeTV t_a)) )).
Proof. apply ( syntax_mutind
  ( fun e : expr => forall (a:vname) (t_a:type),
    noExists t_a 
      -> Subset (ftv (subFTV a t_a e)) (union (diff (ftv e) (singleton a)) (freeTV t_a))  )
  ( fun t : type => forall (a:vname) (t_a:type),
    noExists t_a 
      -> Subset (freeTV (tsubFTV a t_a t)) (union (diff (freeTV t) (singleton a)) (freeTV t_a)) )
  ( fun ps : preds => forall (a:vname) (t_a:type),
    noExists t_a 
      -> Subset (ftvP (psubFTV a t_a ps)) (union (diff (ftvP ps) (singleton a)) (freeTV t_a)) ))
  ; intros; simpl
  ; try (apply subset_empty_l)
  ; (* one IH *) try ( apply H; apply H0 )
  ; (* two IH *) try ( unfold Subset; intros;
    apply set_union_elim in H2; destruct H2; 
    apply H in H2 || apply H0 in H2; try apply H1;
    apply set_union_elim in H2; destruct H2; apply set_union_intro;
    intuition; left; 
    apply set_diff_intro; apply set_diff_iff in H2; destruct H2;
    try assumption; apply set_union_intro; intuition ) 
  ; (* 3 IHs *) try ( unfold Subset; intros;
    repeat (apply set_union_elim in H3; destruct H3);
    apply H in H3 || apply H0 in H3 || apply H1 in H3; try assumption;
    apply set_union_elim in H3; destruct H3; apply set_union_intro; 
    intuition; left; apply set_diff_intro; apply set_diff_iff in H3; destruct H3;
    try apply set_union_intro; intuition; right;
    apply set_union_intro; intuition ).
  + (* TRefn *) destruct b; try destruct (a =? a0) eqn:A; simpl; 
    try apply H; try apply H0.
    - (* FTV a *) apply Nat.eqb_eq in A. subst a0; 
      apply subset_trans with (union (ftvP (psubFTV a t_a ps)) (freeTV t_a));
      try apply ftv_push_elim; try apply H0;
      apply subset_trans 
        with (union (union (diff (ftvP ps) (singleton a)) (freeTV t_a)) (freeTV t_a)).
      * apply subset_union_both; try apply subset_refl; apply H; apply H0.
      * apply subset_trans
          with (union (diff (ftvP ps) (singleton a)) (union (freeTV t_a) (freeTV t_a)));
        try apply subset_union_assoc; apply subset_union_both;
        try apply subset_union_intro_l; try apply subset_refl.
        unfold Subset; intros; apply set_diff_iff in H1; 
        apply set_diff_intro; intuition; apply set_add_intro1; assumption.
    - (* FTV a0 *) unfold Subset; intros; apply set_add_elim in H1;
      apply set_union_intro; destruct H1.
      * left; apply set_diff_intro; try apply set_add_intro2; try apply H1.
        subst x; unfold not; intro; apply elem_sing in H1. 
        apply Nat.eqb_neq in A; intuition.
      * apply H in H1; try apply H0; apply set_union_elim in H1; intuition; left.
        apply set_diff_iff in H2; apply set_diff_intro; 
        try apply set_add_intro; try right; intuition.
  Qed.  

Lemma freeTV_tsubFTV_bounded : forall (a:vname) (t_a:type) (t:type) (ys : names),
    noExists t_a -> Subset (freeTV t_a) ys -> Subset (freeTV t) (names_add a ys)
        -> Subset (freeTV (tsubFTV a t_a t)) ys.
Proof. intros; apply subset_trans with (union (diff (freeTV t) (singleton a)) (freeTV t_a));
  try apply ftv_subFTV_elim; try apply H;
  apply subset_union_intro_l; try apply H0;
  unfold Subset; intros; apply set_diff_iff in H2; destruct H2;
  apply H1 in H2; apply set_add_elim in H2; destruct H2;
  (apply elem_sing in H2; contradiction) || assumption.
  Qed.


(*-------------------------------------------------------------------------
----- | IV. TYPING ENVIRONMENTS
-------------------------------------------------------------------------*)

Inductive env : Set :=  
    | Empty                         (* type env = [(vname, type) or vname] *)
    | ECons  (x : vname) (t : type) (g : env)
    | EConsT (a : vname) (k : kind) (g : env).
    
Fixpoint binds (g : env) : names :=
    match g with
    | Empty         => empty
    | (ECons  x t g) => names_add x (binds g)
    | (EConsT a k g) => names_add a (binds g)
    end.

Fixpoint vbinds (g : env) : names :=
    match g with 
    | Empty         => empty
    | (ECons x t g)  => names_add x (vbinds g)
    | (EConsT a k g) => vbinds g
    end.

Fixpoint tvbinds (g : env) : names :=
    match g with
    | Empty         => empty
    | (ECons x t g)  => tvbinds g
    | (EConsT a k g) => names_add a (tvbinds g) 
    end.

Definition in_env (x : vname) (g : env) : Prop := Elem x (binds g).

Fixpoint unique (g0 : env) : Prop :=
    match g0 with
    | Empty         => True
    | (ECons  x t g) => ~ in_env x g /\ unique g
    | (EConsT a k g) => ~ in_env a g /\ unique g
    end.    

Lemma vbinds_subset : forall (g : env), Subset (vbinds g) (binds g).
Proof. unfold Subset; induction g; simpl.
  - trivial.
  - apply subset_add_both_intro; assumption.
  - apply subset_add_intro; assumption. Qed.
  
Lemma tvbinds_subset : forall (g : env), Subset (tvbinds g) (binds g).
Proof. unfold Subset; induction g; simpl.
  - trivial.
  - apply subset_add_intro; assumption.
  - apply subset_add_both_intro; assumption. Qed. 

Lemma in_env_Cons : forall (x y : vname) (t : type) (g : env),
  ~ in_env x (ECons y t g) -> x <> y /\ ~ in_env x g.
Proof. unfold in_env; simpl; intros; split; unfold not.
  - intro. apply set_add_intro2 with _ Nat.eq_dec x y (binds g) in H0; contradiction.
  - intro. apply set_add_intro1 with _ Nat.eq_dec x y (binds g) in H0; contradiction.
  Qed.

Lemma in_env_ConsT : forall (x a : vname) (k : kind) (g : env),
    ~ in_env x (EConsT a k g) -> x <> a /\ ~ in_env x g.
Proof. unfold in_env; simpl; intros; split; unfold not.
  - intro. apply set_add_intro2 with _ Nat.eq_dec x a (binds g) in H0; contradiction.
  - intro. apply set_add_intro1 with _ Nat.eq_dec x a (binds g) in H0; contradiction.
  Qed.
  
  (* alternative formulations including the assigned type/kind *)

Fixpoint bound_in (x : vname) (t : type) (g0 : env) : Prop := 
    match g0 with
    | Empty          => False
    | (ECons  y t' g) => (x = y /\ t = t') \/ bound_in x t g
    | (EConsT a k  g) => bound_in x t g
    end.

Fixpoint tv_bound_in (a : vname) (k : kind) (g0 : env) : Prop :=
    match g0 with
    | Empty           => False
    | (ECons x t g)    => tv_bound_in a k g
    | (EConsT a' k' g) => (a = a' /\ k = k') \/ tv_bound_in a k g
    end.
 
Lemma lem_boundin_inenv : forall (x:vname) (t:type) (g:env),
    bound_in x t g -> Elem x (vbinds g) (*in_env x g *).
Proof. intros. induction g; simpl in H; simpl; try contradiction;
  try (apply set_add_intro); try (destruct H); try (apply IHg in H); intuition. 
  Qed.

Lemma lem_tvboundin_inenv : forall (a:vname) (k:kind) (g:env),
    tv_bound_in a k g -> Elem a (tvbinds g) (*in_env a g *).
Proof. intros. induction g; simpl in H; simpl; try contradiction;
  try (apply set_add_intro); try (destruct H); try (apply IHg in H); intuition. 
Qed.

  (* --- V. SYSTEM F's TYPING ENVIRONMENTS *)

Inductive fenv := 
    | FEmpty                       (* type fenv = [(vname, ftype) or vname] *)
    | FCons  (x : vname) (t : ftype) (g : fenv)
    | FConsT (a : vname) (k : kind)  (g : fenv).

Fixpoint bindsF (g : fenv) : names :=
    match g with
    | FEmpty         => empty
    | (FCons  x t g) => names_add x (bindsF g)
    | (FConsT a k g) => names_add a (bindsF g)
    end.

Fixpoint vbindsF (g : fenv) : names :=
    match g with 
    | FEmpty         => empty
    | (FCons x t g)  => names_add x (vbindsF g)
    | (FConsT a k g) => vbindsF g
    end.

Fixpoint tvbindsF (g : fenv) : names :=
    match g with
    | FEmpty         => empty
    | (FCons x t g)  => tvbindsF g
    | (FConsT a k g) => names_add a (tvbindsF g) 
    end.

Definition in_envF (x : vname) (g : fenv) : Prop := Elem x (bindsF g).

Fixpoint uniqueF (g0 : fenv) : Prop :=
    match g0 with
    | FEmpty         => True
    | (FCons  x t g) => ~ in_envF x g /\ uniqueF g
    | (FConsT a k g) => ~ in_envF a g /\ uniqueF g
    end.    

Lemma vbindsF_subset : forall (g : fenv), Subset (vbindsF g) (bindsF g).
Proof. unfold Subset; induction g; simpl.
  - trivial.
  - apply subset_add_both_intro; assumption.
  - apply subset_add_intro; assumption. Qed.
  
Lemma tvbindsF_subset : forall (g : fenv), Subset (tvbindsF g) (bindsF g).
Proof. unfold Subset; induction g; simpl.
  - trivial.
  - apply subset_add_intro; assumption.
  - apply subset_add_both_intro; assumption. Qed. 

Lemma in_envF_FCons : forall (x y : vname) (t : ftype) (g : fenv),
  ~ in_envF x (FCons y t g) -> x <> y /\ ~ in_envF x g.
Proof. unfold in_envF; simpl; intros; split; unfold not.
  - intro. apply set_add_intro2 with _ Nat.eq_dec x y (bindsF g) in H0; contradiction.
  - intro. apply set_add_intro1 with _ Nat.eq_dec x y (bindsF g) in H0; contradiction.
  Qed.

Lemma in_envF_FConsT : forall (x a : vname) (k : kind) (g : fenv),
    ~ in_envF x (FConsT a k g) -> x <> a /\ ~ in_envF x g.
Proof. unfold in_envF; simpl; intros; split; unfold not.
  - intro. apply set_add_intro2 with _ Nat.eq_dec x a (bindsF g) in H0; contradiction.
  - intro. apply set_add_intro1 with _ Nat.eq_dec x a (bindsF g) in H0; contradiction.
  Qed.
  
  (* alternative formulations including the assigned ftype/kind *)

Fixpoint bound_inF (x : vname) (t : ftype) (g0 : fenv) : Prop := 
    match g0 with
    | FEmpty          => False
    | (FCons  y t' g) => (x = y /\ t = t') \/ bound_inF x t g
    | (FConsT a k  g) => bound_inF x t g
    end.

Fixpoint tv_bound_inF (a : vname) (k : kind) (g0 : fenv) : Prop :=
    match g0 with
    | FEmpty           => False
    | (FCons x t g)    => tv_bound_inF a k g
    | (FConsT a' k' g) => (a = a' /\ k = k') \/ tv_bound_inF a k g
    end.
 
Lemma lem_boundin_inenvF : forall (x:vname) (t:ftype) (g:fenv),
    bound_inF x t g -> Elem x (vbindsF g) (*in_envF x g *).
Proof. intros. induction g; simpl in H; simpl; try contradiction;
  try (apply set_add_intro); try (destruct H); try (apply IHg in H); intuition. 
  Qed.

Lemma lem_tvboundin_inenvF : forall (a:vname) (k:kind) (g:fenv),
    tv_bound_inF a k g -> Elem a (tvbindsF g) (*in_envF a g *).
Proof. intros. induction g; simpl in H; simpl; try contradiction;
  try (apply set_add_intro); try (destruct H); try (apply IHg in H); intuition. 
Qed.

Fixpoint erase_env (g0 : env) : fenv :=
    match g0 with
    | Empty         => FEmpty
    | (ECons  x t g) => FCons  x (erase t) (erase_env g)
    | (EConsT a k g) => FConsT a k         (erase_env g)
    end.

(*---------------------------------------------------------------------------
----- | VI. NAME SETS and FRESH NAMES
---------------------------------------------------------------------------*)

Definition fresh (xs:names) : vname  :=  1 + List.list_max xs.

Lemma fresh_above_all : forall (x:vname) (xs:names),
    Elem x xs -> x < fresh xs.
Proof. intro x. induction xs as[|y ys IH].
  - simpl; intuition.
  - intro H; simpl in H. 
    destruct H; unfold fresh; simpl; apply Nat.lt_succ_r.
      * subst x.  apply Nat.le_max_l.
      * apply IH in H. unfold fresh in H; simpl in H. 
        apply Nat.le_succ_l in H; apply le_S_n in H.
        transitivity (List.list_max ys); (apply H || apply Nat.le_max_r).
  Qed.

Lemma above_fresh_not_elem : forall (y:vname) (xs : names), 
    fresh xs <= y -> ~ Elem y xs.
Proof. unfold not. intros. apply fresh_above_all in H0. apply Nat.lt_nge in H0.
  contradiction. Qed.

Lemma fresh_not_elem : forall (xs : names), ~ Elem (fresh xs) xs.
Proof. intro xs. apply above_fresh_not_elem; trivial. Qed.
  
Definition fresh_varF (xs : names) (g : fenv) : vname := 
  max (fresh xs) (fresh (bindsF g)).

Lemma above_fresh_varF_not_elem : forall (y:vname) (xs : names) (g : fenv),
    fresh_varF xs g <= y   ->   ~ Elem    y xs /\ ~ in_envF y g.
Proof. split; unfold in_envF; apply above_fresh_not_elem; (*unfold fresh_varF in H. *)
  transitivity (fresh_varF xs g); try assumption;        
  apply Nat.le_max_l || apply Nat.le_max_r. Qed.

Lemma fresh_varF_not_elem : forall (xs : names) (g : fenv),
    ~ Elem (fresh_varF xs g) xs /\ ~ in_envF (fresh_varF xs g) g.
Proof. intros. apply above_fresh_varF_not_elem; trivial. Qed. 
  
Definition fresh_var_excludingF (xs:names) (g:fenv) (y:vname) :=  
    max (fresh_varF xs g) (1+y).

Lemma fresh_var_excludingF_not_elem : forall (xs:names) (g:fenv) (y:vname),
    ~ (fresh_var_excludingF xs g y) = y        /\
    ~ Elem    (fresh_var_excludingF xs g y) xs /\ 
    ~ in_envF (fresh_var_excludingF xs g y) g.
Proof. split; unfold fresh_var_excludingF.
  - unfold not. intro. assert (1 + y <= max (fresh_varF xs g) (1 + y) ).
    apply Nat.le_max_r. rewrite H in H0. apply Nat.lt_nge in H0. intuition.
  - apply above_fresh_varF_not_elem; unfold fresh_varF;
    apply Nat.le_max_l || apply Nat.le_max_r. Qed.

Definition fresh_varFE (xs : names) (g : fenv) (e : expr) : vname :=
  max (fresh_varF xs g) (max (fresh (fv e)) (fresh (ftv e))).

Lemma above_fresh_varFE_not_elem : forall (y:vname) (xs:names) (g:fenv) (e:expr),
  fresh_varFE xs g e <= y ->  ~ Elem    y (fv e)  /\
                              ~ Elem    y (ftv e) /\
                              ~ Elem    y xs      /\ 
                              ~ in_envF y g       .
Proof. split; try split; try
  ( apply above_fresh_not_elem; 
    transitivity (max (fresh (fv e)) (fresh (ftv e))); try (apply Nat.le_max_l || apply Nat.le_max_r);
    transitivity (fresh_varFE xs g e); unfold fresh_varFE; try (apply Nat.le_max_r); assumption );
  apply above_fresh_varF_not_elem; 
  transitivity (fresh_varFE xs g e); unfold fresh_varFE; try (apply Nat.le_max_l); assumption.
  Qed.

Lemma fresh_varFE_not_elem : forall (xs:names) (g:fenv) (e:expr),
    ~ Elem    (fresh_varFE xs g e) (fv e)  /\
    ~ Elem    (fresh_varFE xs g e) (ftv e) /\
    ~ Elem    (fresh_varFE xs g e) xs      /\ 
    ~ in_envF (fresh_varFE xs g e) g       .
Proof. intros; apply  above_fresh_varFE_not_elem; trivial. Qed.
  
Definition fresh_var (xs : names) (g : env) : vname := 
  max (fresh xs) (fresh (binds g)).

Lemma above_fresh_var_not_elem : forall (y:vname) (xs : names) (g : env),
    fresh_var xs g <= y   ->   ~ Elem    y xs /\ ~ in_env y g.
Proof. split; unfold in_env; apply above_fresh_not_elem; 
  transitivity (fresh_var xs g); try assumption;        
  apply Nat.le_max_l || apply Nat.le_max_r. Qed.

Lemma fresh_var_not_elem : forall (xs : names) (g : env),
    ~ Elem (fresh_var xs g) xs /\ ~ in_env (fresh_var xs g) g.
Proof. intros. apply above_fresh_var_not_elem; trivial. Qed. 
  
Definition fresh_var_excluding (xs:names) (g:env) (y:vname) :=  
    max (fresh_var xs g) (1+y).

Lemma fresh_var_excluding_not_elem : forall (xs:names) (g:env) (y:vname),
    ~ (fresh_var_excluding xs g y) = y        /\
    ~ Elem    (fresh_var_excluding xs g y) xs /\ 
    ~ in_env  (fresh_var_excluding xs g y) g.
Proof. split; unfold fresh_var_excluding.
  - unfold not. intro. assert (1 + y <= max (fresh_var xs g) (1 + y) ).
    apply Nat.le_max_r. rewrite H in H0. apply Nat.lt_nge in H0. intuition.
  - apply above_fresh_var_not_elem; unfold fresh_var;
    apply Nat.le_max_l || apply Nat.le_max_r. Qed.

Definition fresh_varE (xs : names) (g : env) (e : expr) : vname :=
  max (fresh_var xs g) (max (fresh (fv e)) (fresh (ftv e))).

Lemma above_fresh_varE_not_elem : forall (y:vname) (xs:names) (g:env) (e:expr),
  fresh_varE xs g e <= y ->  ~ Elem   y (fv e)  /\
                             ~ Elem   y (ftv e) /\
                             ~ Elem   y xs      /\ 
                             ~ in_env y g       .
Proof. split; try split; try
  ( apply above_fresh_not_elem; 
    transitivity (max (fresh (fv e)) (fresh (ftv e))); try (apply Nat.le_max_l || apply Nat.le_max_r);
    transitivity (fresh_varE xs g e); unfold fresh_varE; try (apply Nat.le_max_r); assumption );
  apply above_fresh_var_not_elem; 
  transitivity (fresh_varE xs g e); unfold fresh_varE; try (apply Nat.le_max_l); assumption.
  Qed.

Lemma fresh_varE_not_elem : forall (xs:names) (g:env) (e:expr),
    ~ Elem   (fresh_varE xs g e) (fv e)  /\
    ~ Elem   (fresh_varE xs g e) (ftv e) /\
    ~ Elem   (fresh_varE xs g e) xs      /\ 
    ~ in_env (fresh_varE xs g e) g       .
Proof. intros; apply  above_fresh_varE_not_elem; trivial. Qed.

Definition fresh_varT (xs : names) (g : env) (t : type) : vname :=
  max (fresh_var xs g) (max (fresh (free t)) (fresh (freeTV t))).

Lemma above_fresh_varT_not_elem : forall (y:vname) (xs:names) (g:env) (t:type),
  fresh_varT xs g t <= y ->  ~ Elem   y (free   t) /\
                             ~ Elem   y (freeTV t) /\
                             ~ Elem   y xs      /\ 
                             ~ in_env y g       .
Proof. split; try split; try
  ( apply above_fresh_not_elem; 
    transitivity (max (fresh (free t)) (fresh (freeTV t))); 
    try (apply Nat.le_max_l || apply Nat.le_max_r);
    transitivity (fresh_varT xs g t); unfold fresh_varT; try (apply Nat.le_max_r); assumption );
  apply above_fresh_var_not_elem; 
  transitivity (fresh_varT xs g t); unfold fresh_varT; try (apply Nat.le_max_l); assumption.
  Qed.

Lemma fresh_varT_not_elem : forall (xs:names) (g:env) (t:type),
    ~ Elem   (fresh_varT xs g t) (free   t) /\
    ~ Elem   (fresh_varT xs g t) (freeTV t) /\
    ~ Elem   (fresh_varT xs g t) xs      /\ 
    ~ in_env (fresh_varT xs g t) g       .
Proof. intros; apply  above_fresh_varT_not_elem; trivial. Qed.

Definition fresh_varFTs (xs : names) (g : env) (t1 : ftype) (t2 : ftype): vname :=
  max (fresh_var xs g) (max (fresh (ffreeTV t1)) (fresh (ffreeTV t2))).

Lemma above_fresh_varFTs_not_elem : forall (y:vname) (xs:names) (g:env) (t1:ftype) (t2:ftype),
  fresh_varFTs xs g t1 t2 <= y ->  ~ Elem   y (ffreeTV t1) /\
                                   ~ Elem   y (ffreeTV t2) /\
                                   ~ Elem   y xs      /\ 
                                   ~ in_env y g       .
Proof. split; try split; try
  ( apply above_fresh_not_elem; 
    transitivity (max (fresh (ffreeTV t1)) (fresh (ffreeTV t2))); 
    try (apply Nat.le_max_l || apply Nat.le_max_r);
    transitivity (fresh_varFTs xs g t1 t2); 
    unfold fresh_varFTs; try (apply Nat.le_max_r); assumption );
  apply above_fresh_var_not_elem; 
  transitivity (fresh_varFTs xs g t1 t2); unfold fresh_varFTs; try (apply Nat.le_max_l); assumption.
  Qed.

Lemma fresh_varFTs_not_elem : forall (xs:names) (g:env) (t1:ftype) (t2:ftype),
    ~ Elem   (fresh_varFTs xs g t1 t2) (ffreeTV t1) /\
    ~ Elem   (fresh_varFTs xs g t1 t2) (ffreeTV t2) /\
    ~ Elem   (fresh_varFTs xs g t1 t2) xs      /\ 
    ~ in_env (fresh_varFTs xs g t1 t2) g       .
Proof. intros; apply  above_fresh_varFTs_not_elem; trivial. Qed.