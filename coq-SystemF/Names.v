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


Lemma no_elem_empty : forall (ys : names),
    (forall (x:vname), ~ Elem x ys) -> ys = empty.
Proof. intros. destruct ys.
  - reflexivity.
  - assert (List.In v (v :: ys)) by intuition.
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

Lemma subset_union_assoc : forall (xs ys zs : names),
    Subset (union (union xs ys) zs) (union xs (union ys zs)) /\
    Subset (union xs (union ys zs)) (union (union xs ys) zs).
Proof. unfold Subset; split; intros; apply set_union_elim in H;
  destruct H; try (apply set_union_elim in H; destruct H);
  apply set_union_intro;
  ( left;  apply H || apply set_union_intro; (left; apply H) || (right; apply H) ) || 
  ( right; apply H || apply set_union_intro; (left; apply H) || (right; apply H) ).
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

Lemma intersect_empty_r : forall (xs : names), intersect xs empty = empty.
Proof. intro xs; apply no_elem_empty; unfold not; intros; 
  apply set_inter_elim in H; intuition. Qed.

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
    end

with free (t0:type) : names :=
    match t0 with
    | (TRefn b   rs)     => fvP rs
    | (TFunc   t_x t)    => union (free t_x) (free t) 
    | (TExists   t_x t)  => union (free t_x) (free t) 
    | (TPoly   k   t)    => free t
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
    end.

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
       ; (* two IH *) try ( apply subset_union_both; apply H || apply H0 ).
  Qed.

Lemma fv_unbind_intro : ( forall (e:expr) (y:vname) ,
    Subset (fv e) (fv (unbind y e))  ) * ((
  forall (t:type) (y:vname) ,
    Subset (free t) (free (unbindT y t)) ) * (
  forall (ps:preds) (y:vname) ,
    Subset (fvP ps) (fvP (unbindP y ps)) )).
Proof. unfold unbind; unfold unbindT; unfold unbindP; repeat split; 
  intros; apply fv_open_at_intro. Qed. 

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
      ; (* two IH *) try ( apply subset_union_both; apply H || apply H0 ).
  Qed.

Lemma ftv_unbind_intro : ( forall (e:expr) (y:vname) ,
    Subset (ftv e) (ftv (unbind y e))  ) * ((
  forall (t:type) (y:vname) ,
    Subset (freeTV t) (freeTV (unbindT y t)) ) * (
  forall (ps:preds) (y:vname) ,
    Subset (ftvP ps) (ftvP (unbindP y ps)) )).
Proof. unfold unbind; unfold unbindT; unfold unbindP; repeat split; 
  intros; apply ftv_open_at_intro. Qed. 


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
      ; (* two IH *) try ( apply subset_union_both; apply H || apply H0 ).
Qed.

Lemma fv_unbind_tv_intro : ( forall (e:expr) (a:vname) ,
    Subset (fv e) (fv (unbind_tv a e))  ) * ((
  forall (t:type) (a:vname) ,
    Subset (free t) (free (unbind_tvT a t)) ) * (
  forall (ps:preds) (a:vname) ,
    Subset (fvP ps) (fvP (unbind_tvP a ps)) )).
Proof. unfold unbind_tv; unfold unbind_tvT; unfold unbind_tvP; repeat split; 
  intros; apply fv_open_tv_at_intro. Qed. 

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
      ; (* two IH *) try ( apply subset_union_both; apply H || apply H0 ).
  Qed.

Lemma ftv_unbind_tv_intro : ( forall (e:expr) (a:vname) ,
    Subset (ftv e) (ftv (unbind_tv a e))  ) * ((
  forall (t:type) (a:vname) ,
    Subset (freeTV t) (freeTV (unbind_tvT a t)) ) * (
  forall (ps:preds) (a:vname) ,
    Subset (ftvP ps) (ftvP (unbind_tvP a ps)) )).
Proof. unfold unbind_tv; unfold unbind_tvT; unfold unbind_tvP; repeat split; 
  intros; apply ftv_open_tv_at_intro. Qed. 

Lemma ffreeTV_openFT_at_intro : forall (t:ftype) (j:index) (a:vname),
    Subset (ffreeTV t) (ffreeTV (openFT_at j a t)).
Proof. induction t; intros; simpl.
  - destruct b; simpl; try apply subset_refl; try apply subset_empty_l.
  - apply subset_union_both; apply IHt1 || apply IHt2.
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
    try assumption; apply set_union_intro; intuition ).
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
    intuition; left; apply set_union_intro; intuition ).
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

Lemma fv_strengthen_elim : forall (ps qs : preds),
    Subset ( fvP (strengthen ps qs)) (union (fvP ps) (fvP qs)).
Proof. intros; induction ps; simpl.
  - apply subset_union_intro_r; apply subset_refl.
  - apply subset_trans with (union (fv p) (union (fvP ps) (fvP qs))).
    * apply subset_union_both; try apply subset_refl; apply IHps.
    * apply subset_union_assoc.
  Qed.

Lemma ftv_strengthen_elim : forall (ps qs : preds),
    Subset ( ftvP (strengthen ps qs)) (union (ftvP ps) (ftvP qs)).
Proof. intros; induction ps; simpl.
  - apply subset_union_intro_r; apply subset_refl.
  - apply subset_trans with (union (ftv p) (union (ftvP ps) (ftvP qs))).
    * apply subset_union_both; try apply subset_refl; apply IHps.
    * apply subset_union_assoc.
  Qed.

Lemma fv_push_elim : forall (ps : preds) (t_a : type),
    noExists t_a -> Subset (free (push ps t_a)) (union (fvP ps) (free t_a)).
Proof. intros; destruct t_a; simpl in H; try contradiction; unfold push.
  - (* TRefn *) apply fv_strengthen_elim.
  - (* TFunc *) apply subset_union_intro_r.
  - (* TPoly *) apply subset_union_intro_r.
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
    intuition; left; apply set_union_intro; intuition ).
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
  . (* TRefn *) destruct b; try destruct (a =? a0) eqn:A; simpl; 
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
    | Cons  (x : vname) (t : type) (g : env)
    | ConsT (a : vname) (k : kind) (g : env).
    
Fixpoint binds (g : env) : names :=
    match g with
    | Empty         => empty
    | (Cons  x t g) => names_add x (binds g)
    | (ConsT a k g) => names_add a (binds g)
    end.

Fixpoint vbinds (g : env) : names :=
    match g with 
    | Empty         => empty
    | (Cons x t g)  => names_add x (vbinds g)
    | (ConsT a k g) => vbinds g
    end.

Fixpoint tvbinds (g : env) : names :=
    match g with
    | Empty         => empty
    | (Cons x t g)  => tvbinds g
    | (ConsT a k g) => names_add a (tvbinds g) 
    end.

Definition in_env (x : vname) (g : env) : Prop := Elem x (binds g).

Fixpoint unique (g0 : env) : Prop :=
    match g0 with
    | Empty         => True
    | (Cons  x t g) => ~ in_env x g /\ unique g
    | (ConsT a k g) => ~ in_env a g /\ unique g
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
  ~ in_env x (Cons y t g) -> x <> y /\ ~ in_env x g.
Proof. unfold in_env; simpl; intros; split; unfold not.
  - intro. apply set_add_intro2 with _ Nat.eq_dec x y (binds g) in H0; contradiction.
  - intro. apply set_add_intro1 with _ Nat.eq_dec x y (binds g) in H0; contradiction.
  Qed.

Lemma in_env_ConsT : forall (x a : vname) (k : kind) (g : env),
    ~ in_env x (ConsT a k g) -> x <> a /\ ~ in_env x g.
Proof. unfold in_env; simpl; intros; split; unfold not.
  - intro. apply set_add_intro2 with _ Nat.eq_dec x a (binds g) in H0; contradiction.
  - intro. apply set_add_intro1 with _ Nat.eq_dec x a (binds g) in H0; contradiction.
  Qed.
  
  (* alternative formulations including the assigned type/kind *)

Fixpoint bound_in (x : vname) (t : type) (g0 : env) : Prop := 
    match g0 with
    | Empty          => False
    | (Cons  y t' g) => (x = y /\ t = t') \/ bound_in x t g
    | (ConsT a k  g) => bound_in x t g
    end.

Fixpoint tv_bound_in (a : vname) (k : kind) (g0 : env) : Prop :=
    match g0 with
    | Empty           => False
    | (Cons x t g)    => tv_bound_in a k g
    | (ConsT a' k' g) => (a = a' /\ k = k') \/ tv_bound_in a k g
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
    | (Cons  x t g) => FCons  x (erase t) (erase_env g)
    | (ConsT a k g) => FConsT a k         (erase_env g)
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
    destruct H; unfold fresh; simpl; apply le_lt_n_Sm.
      * subst x.  apply Nat.le_max_l.
      * apply IH in H. unfold fresh in H; simpl in H. 
        apply lt_le_S in H; apply le_S_n in H.
        transitivity (List.list_max ys); (apply H || apply Nat.le_max_r).
  Qed.

Lemma above_fresh_not_elem : forall (y:vname) (xs : names), 
    fresh xs <= y -> ~ Elem y xs.
Proof. unfold not. intros. apply fresh_above_all in H0. apply lt_not_le in H0.
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
    apply Nat.le_max_r. rewrite H in H0. apply lt_not_le in H0. intuition.
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
  
    
(*
{-@ fresh_var :: xs:names -> g:env -> { x:vname | not (in_env x g) && NotElem x xs } @-}
fresh_var :: names -> env -> vname
fresh_var xs g = n `withProof` lem_above_max_nms_env n xs g
  where
    n    = 1 + max_nms_env xs g

{-@ fresh_var_excluding :: xs:names -> g:env -> x:vname 
                -> { y:vname | not (in_env y g) && y != x && NotElem y xs } @-}
fresh_var_excluding :: names -> env -> vname -> vname
fresh_var_excluding xs g x = if in_env x g then fresh_var xs g
                                 else fresh_var xs (Cons x (TRefn TBool PEmpty) g)

{-@ reflect max_nms_env @-}
{-@ max_nms_env :: names -> env -> { x:vname | x >= 0 } @-}
max_nms_env :: names -> env -> vname 
max_nms_env ([])   Empty         = 0
max_nms_env ([])   (Cons  x t g) = if (x > max_nms_env [] g) then x else (max_nms_env [] g)
max_nms_env ([])   (ConsT a k g) = if (a > max_nms_env [] g) then a else (max_nms_env [] g)
max_nms_env (x:xs) g             = if (x > max_nms_env xs g) then x else (max_nms_env xs g)

{-@ lem_above_max_nms_env :: x:vname -> xs:names -> { g:env | x > max_nms_env xs g } 
                                      -> { pf:_ | NotElem x xs && not (in_env x g) } @-}
lem_above_max_nms_env :: vname -> names -> env -> Proof
lem_above_max_nms_env _ []     Empty         = ()
lem_above_max_nms_env x []     (Cons  y t g) = lem_above_max_nms_env x [] g
lem_above_max_nms_env x []     (ConsT a k g) = lem_above_max_nms_env x [] g
lem_above_max_nms_env x (_:ys) g             = lem_above_max_nms_env x ys g


{-@ fresh_varT :: xs:names -> g:env -> t:type 
        -> { x:vname | not (Set_mem x (free t)) && not (in_env x g) && NotElem x xs } @-}
fresh_varT :: names -> env -> type -> vname
fresh_varT xs g t
  = n `withProof` lem_above_max_nms_type n xs (freeList t) g
      where
        n    = 1 + max_nms_type xs (freeList t) g

{-@ reflect max_nms_type @-}
{-@ max_nms_type :: names -> names -> env -> { x:vname | x >= 0 } @-}
max_nms_type :: names -> names -> env -> vname 
max_nms_type ([])   ([])   Empty         = 0
max_nms_type ([])   ([])   (Cons  x t g) 
  = if (x > max_nms_type [] [] g) then x else (max_nms_type [] [] g)
max_nms_type ([])   ([])   (ConsT a k g)
  = if (a > max_nms_type [] [] g) then a else (max_nms_type [] [] g)
max_nms_type ([])   (y:ys) g 
  = if (y > max_nms_type [] ys g) then y else (max_nms_type [] ys g)
max_nms_type (x:xs) ys     g 
  = if (x > max_nms_type xs ys g) then x else (max_nms_type xs ys g)

{-@ lem_above_max_nms_type :: x:vname -> xs:names -> ys:names
        -> { g:env | x > max_nms_type xs ys g } 
        -> { pf:_ | NotElem x xs && NotElem x ys && not (in_env x g) } @-}
lem_above_max_nms_type :: vname -> names -> names -> env -> Proof
lem_above_max_nms_type _ []     []     Empty         = ()
lem_above_max_nms_type x []     []     (Cons  y t g) = lem_above_max_nms_type x [] [] g
lem_above_max_nms_type x []     []     (ConsT a k g) = lem_above_max_nms_type x [] [] g
lem_above_max_nms_type x []     (_:ys) g             = lem_above_max_nms_type x [] ys g
lem_above_max_nms_type x (_:xs) ys     g             = lem_above_max_nms_type x xs ys g

{-@ fresh_varFTs :: xs:names -> g:env -> t1:ftype -> t2:ftype 
        -> { x:vname | not (Set_mem x (ffreeTV t1)) && not (Set_mem x (ffreeTV t2)) && 
                       not (in_env x g)             && NotElem x xs } @-}
fresh_varFTs :: names -> env -> ftype -> ftype -> vname
fresh_varFTs xs g t1 t2 
  = n `withProof` lem_above_max_nms_ftypes n xs (ffreeTVList t1) (ffreeTVList t2) g
      where
        n    = 1 + max_nms_ftypes xs (ffreeTVList t1) (ffreeTVList t2) g

{-@ reflect max_nms_ftypes @-}
{-@ max_nms_ftypes :: names -> names -> names -> env -> { x:vname | x >= 0 } @-}
max_nms_ftypes :: names -> names -> names -> env -> vname 
max_nms_ftypes ([])   ([])   ([])   Empty         = 0
max_nms_ftypes ([])   ([])   ([])   (Cons  x t g) 
  = if (x > max_nms_ftypes [] [] [] g) then x else (max_nms_ftypes [] [] [] g)
max_nms_ftypes ([])   ([])   ([])   (ConsT a k g)
  = if (a > max_nms_ftypes [] [] [] g) then a else (max_nms_ftypes [] [] [] g)
max_nms_ftypes ([])   ([])   (z:zs) g 
  = if (z > max_nms_ftypes [] [] zs g) then z else (max_nms_ftypes [] [] zs g)
max_nms_ftypes ([])   (y:ys) zs     g 
  = if (y > max_nms_ftypes [] ys zs g) then y else (max_nms_ftypes [] ys zs g)
max_nms_ftypes (x:xs) ys     zs     g 
  = if (x > max_nms_ftypes xs ys zs g) then x else (max_nms_ftypes xs ys zs g)

{-@ lem_above_max_nms_ftypes :: x:vname -> xs:names -> ys:names -> zs:names
        -> { g:env | x > max_nms_ftypes xs ys zs g } 
        -> { pf:_ | NotElem x xs && NotElem x ys && NotElem x zs && not (in_env x g) } @-}
lem_above_max_nms_ftypes :: vname -> names -> names -> names -> env -> Proof
lem_above_max_nms_ftypes _ []     []     []     Empty         = ()
lem_above_max_nms_ftypes x []     []     []     (Cons  y t g) 
  = lem_above_max_nms_ftypes x [] [] [] g
lem_above_max_nms_ftypes x []     []     []     (ConsT a k g) 
  = lem_above_max_nms_ftypes x [] [] [] g
lem_above_max_nms_ftypes x []     []     (_:zs) g = lem_above_max_nms_ftypes x [] [] zs g
lem_above_max_nms_ftypes x []     (_:ys) zs     g = lem_above_max_nms_ftypes x [] ys zs g
lem_above_max_nms_ftypes x (_:xs) ys     zs     g = lem_above_max_nms_ftypes x xs ys zs g
*) 


(* erase_env :: g:env -> { g':fenv | binds g == bindsF g' && vbinds g == vbindsF g' 
                                                           && tvbinds g == tvbindsF g'} *)

(*) lem_erase_freeTV :: t:type -> { pf:_ | Set_sub (ffreeTV (erase t)) (freeTV t) } @-}
lem_erase_freeTV :: type -> Proof
lem_erase_freeTV (TRefn   b   p) = ()
lem_erase_freeTV (TFunc   t_z t) = () ? lem_erase_freeTV t_z
                                      ? lem_erase_freeTV t
lem_erase_freeTV (TExists t_z t) = () ? lem_erase_freeTV t
lem_erase_freeTV (TPoly    k' t) = () ? lem_erase_freeTV t *)

(*
(* open_at :: j:index -> y:vname -> e:expr
                 -> { e':expr | Set_sub (fv e') (Set_cup (Set_sng y) (fv e)) &&
                                Set_sub (ftv e') (ftv e) *)
Fixpoint open_at (j : index) (y : vname) (e : expr) : expr := 
    match e with
    | (Bc b)             => Bc b
    | (Ic n)             => Ic n
    | (Prim c)           => Prim c
    | (BV i)             => if i =? j then FV y else BV i (* TODO: or i =? j *)
    | (FV x)             => FV x
    | (Lambda e')        => Lambda (open_at (j+1) y e')
    | (App e1 e2)        => App   (open_at j y e1)  (open_at j y e2)
    | (LambdaT k e')     => LambdaT k (open_at j y e')  
    | (AppT e' t)        => AppT  (open_at j y e')  (openT_at j y t)
    | (Let ex e')        => Let   (open_at j y ex) (open_at (j+1) y e')
    | (Annot e' t)       => Annot (open_at j y e')  (openT_at j y t)
    end

(* openT_at :: j:index -> y:vname -> t:type 
                 -> { t':type | Set_sub (free t') (Set_cup (Set_sng y) (free t)) &&
                                Set_sub (freeTV t') (freeTV t) 
                                (noExists t => noExists t') && erase t == erase t' } / [tsize t] *)
with openT_at (j : index) (y : vname) (t0 : type) : type :=
    match t0 with
    | (TRefn b ps)    => TRefn b (openP_at (j+1) y ps)
    | (TFunc   t_z t) => TFunc   (openT_at j y t_z) (openT_at (j+1) y t)
    | (TExists t_z t) => TExists (openT_at j y t_z) (openT_at (j+1) y t)
    | (TPoly   k   t) => TPoly k (openT_at j y t) 
    end

(* openP_at :: j:index -> y:vname -> ps:preds
  -> { ps':preds | Set_sub (fvP ps') (Set_cup (Set_sng y) (fvP ps)) &&
                 Set_sub (fvP ps) (fvP ps') &&
                 Set_sub (ftvP ps') (ftvP ps) && Set_sub (ftvP ps) (ftvP ps') &&
                 predsize ps == predsize ps' } / [predsize ps] *)
with openP_at (j : index) (y : vname) (ps0 : preds) : preds  :=
    match ps0 with
    | PEmpty       => PEmpty
    | (PCons p ps) => PCons (open_at j y p) (openP_at j y ps)
    end.

(* unbind :: y:vname -> e:expr     -- unbind opens to (FV y) in e 
                -> { e':expr | Set_sub (fv e') (Set_cup (Set_sng y) (fv e)) &&
                               Set_sub (ftv e') (ftv e) &&
                               esize e == esize e' } / [esize e] *)
(* unbindT :: y:vname -> t:type 
                      -> { t':type | Set_sub (free t') (Set_cup (Set_sng y) (free t)) &&
                                     Set_sub (freeTV t') (freeTV t) &&
                                     (noExists t => noExists t') && erase t == erase t' } / [tsize t] *)
(* unbindP :: y:vname -> ps:preds
                 -> { ps':preds | Set_sub (fvP ps') (Set_cup (Set_sng y) (fvP ps)) &&
                                  Set_sub (ftvP ps') (ftvP ps) && 
                                  predsize ps == predsize ps' } / [predsize ps] *)


(* open_tv_at :: j:index -> a':vname -> e:expr
                    -> { e':expr | Set_sub (ftv e') (Set_cup (Set_sng a') (ftv e)) &&
                                   Set_sub (fv e') (fv e)  &&  esize e == esize e' } / [esize e] *)
Fixpoint open_tv_at (j : index) (a' : vname) (e0 : expr) : expr :=
    match e0 with
    | (Bc b)                       => Bc b
    | (Ic n)                       => Ic n
    | (Prim p)                     => Prim p
    | (BV i)                       => BV i    (* looking for type vars *)
    | (FV y)                       => FV y
    | (Lambda e)                   => Lambda    (open_tv_at j a' e)  
    | (App e e')                   => App       (open_tv_at j a' e)  (open_tv_at j a' e')
    | (LambdaT k e)                => LambdaT k (open_tv_at (j+1) a' e)
    | (AppT e t)                   => AppT      (open_tv_at j a' e)  (open_tvT_at j a' t)
    | (Let e1 e2  )                => Let       (open_tv_at j a' e1) (open_tv_at  j a' e2) 
    | (Annot e t)                  => Annot     (open_tv_at j a' e)  (open_tvT_at j a' t)
    end

(* open_tvT_at :: j:index -> a':vname -> t:type 
                    -> { t':type | Set_sub (freeTV t') (Set_cup (Set_sng a') (freeTV t)) &&
                                  Set_sub (free t') (free t) && (noExists t => noExists t') *) 
with open_tvT_at (j : index) (a' : vname) (t0 : type) : type  :=
    match t0 with
    | (TRefn b  ps)     => match b with 
          | (BTV i)  => if i =? j then TRefn (FTV a') (open_tvP_at j a' ps) 
                                else TRefn b        (open_tvP_at j a' ps)
          | _        =>                TRefn b        (open_tvP_at j a' ps) 
          end
    | (TFunc   t_z t)   => TFunc    (open_tvT_at j a' t_z) (open_tvT_at j a' t)
    | (TExists t_z t)   => TExists  (open_tvT_at j a' t_z) (open_tvT_at j a' t)
    | (TPoly   k  t)    => TPoly k  (open_tvT_at (j+1) a' t)
    end

(* open_tvP_at :: j:index -> a':vname -> ps:preds
                    -> { ps':preds | Set_sub (ftvP ps') (Set_cup (Set_sng a') (ftvP ps)) &&
                    Set_sub (ftvP ps) (ftvP ps') *)
with open_tvP_at (j : index) (a' : vname) (ps0 : preds) : preds  :=
    match ps0 with
    | PEmpty       => PEmpty
    | (PCons p ps) => PCons (open_tv_at j a' p) (open_tvP_at j a' ps)
    end.

(* unbind_tv :: a':vname -> e:expr 
                    -> { e':expr | Set_sub (ftv e') (Set_cup (Set_sng a') (ftv e)) &&
                                   Set_sub (fv e') (fv e)  &&  esize e == esize e' &&
                                   ( e == Bc True => e' == Bc True ) } / [esize e] *)
Definition unbind_tv  (a' : vname) (e : expr) : expr  :=  open_tv_at 0 a' e.

(* unbind_tvT :: a':vname -> t:type 
                       -> { t':type | Set_sub (freeTV t') (Set_cup (Set_sng a') (freeTV t)) &&
                                      Set_sub (free t') (free t) &&
                                      (noExists t => noExists t') }*) 
Definition unbind_tvT (a' : vname) (t : type) : type  :=  open_tvT_at 0 a' t.

(* unbind_tvP :: a':vname -> ps:preds
                     -> { ps':preds | Set_sub (ftvP ps') (Set_cup (Set_sng a') (ftvP ps)) &&
                                      Set_sub (fvP ps') (fvP ps)  &&  
Definition unbind_tvP (a' : vname) (ps : preds) : preds := open_tvP_at 0 a' ps.


(* subBV_at :: j:index -> v:Value -> e:expr
                 -> { e':expr | Set_sub (fv e') (Set_cup (fv e) (fv v)) &&
                                Set_sub (ftv e') (Set_cup (ftv e) (ftv v)) &&
                              ( esize v != 1 || esize e == esize e') } / [esize e] *)
Fixpoint subBV_at (j : index) (v : expr) (e0 : expr) : expr :=
    match e0 with
    | (Bc b)             => Bc b
    | (Ic n)             => Ic n
    | (Prim c)           => Prim c
    | (BV i)             => if i =? j then (*toExpr*) v else BV i
    | (FV x)             => FV x
    | (Lambda e)         => Lambda (subBV_at (j+1) v e)
    | (App e e')         => App   (subBV_at j v e)  (subBV_at j v e')
    | (LambdaT k e)      => LambdaT k (subBV_at j v e) 
    | (AppT e t)         => AppT  (subBV_at j v e)  (tsubBV_at j v t)
    | (Let ex e)         => Let   (subBV_at j v ex) (subBV_at (j+1) v e)
    | (Annot e t)        => Annot (subBV_at j v e)  (tsubBV_at j v t)
    end

(*{ tsubBV_at :: j:index -> v_x:Value -> t:type  
    -> { t':type | Set_sub (free t') (Set_cup (fv v_x) (free t)) &&
                   Set_sub (freeTV t') (Set_cup (ftv v_x) (freeTV t)) &&
                   erase t == erase t' &&
                   ( esize v_x != 1 || tsize t == tsize t' ) } / [tsize t] *)
with tsubBV_at (j : index) (v_x : expr) (t0 : type) : type :=
    match t0 with
    | (TRefn b ps)    => TRefn b (psubBV_at (j+1) v_x ps)  
    | (TFunc   t_z t) => TFunc   (tsubBV_at j v_x t_z) (tsubBV_at (j+1) v_x t)
    | (TExists t_z t) => TExists (tsubBV_at j v_x t_z) (tsubBV_at (j+1) v_x t)
    | (TPoly   k  t)  => TPoly k (tsubBV_at j v_x t)  
    end

(* psubBV_at :: j:index -> v:Value -> ps:preds
                 -> { ps':preds | Set_sub (fvP ps') (Set_cup (fvP ps) (fv v)) &&
                                  Set_sub (ftvP ps') (Set_cup (ftvP ps) (ftv v)) &&
                                ( esize v != 1 || predsize ps == predsize ps') } *)
with psubBV_at (j : index) (v_x : expr) (ps0 : preds) : preds  := 
    match ps0 with
    | PEmpty       => PEmpty
    | (PCons p ps) => PCons (subBV_at j v_x p) (psubBV_at j v_x ps)
    end.

(* subBV :: v:Value -> e:expr 
                -> { e':expr | Set_sub (fv e') (Set_cup (fv e) (fv v)) &&
                               Set_sub (ftv e') (Set_cup (ftv e) (ftv v)) &&
                             ( esize v != 1 || esize e == esize e') } / [esize e] *)
Definition subBV  (v : expr) (e : expr) : expr  :=  subBV_at 0 v e.

(* tsubBV :: v_x:Value -> t:type  
                -> { t':type | Set_sub (free t') (Set_cup (fv v_x) (free t)) &&
                               Set_sub (freeTV t') (Set_cup (ftv v_x) (freeTV t)) &&
                               erase t == erase t' && 
                               ( esize v_x != 1 || tsize t == tsize t' ) } / [tsize t] *)
Definition tsubBV  (v_x : expr) (t : type) : type  :=  tsubBV_at 0 v_x t.

(* psubBV :: v:Value -> ps:preds
              -> { ps':preds | Set_sub (fvP ps') (Set_cup (fvP ps) (fv v)) &&
                              Set_sub (ftvP ps') (Set_cup (ftvP ps) (ftv v)) &&
                            ( esize v != 1 || predsize ps == predsize ps') } *)
Definition psubBV (v : expr) (ps : preds) : preds := psubBV_at 0 v ps.

(* subBTV_at :: j:index -> t:Usertype -> e:expr
                     -> { e':expr | Set_sub (fv e') (Set_cup (fv e) (free t)) &&
                                    Set_sub (ftv e') (Set_cup (ftv e) (freeTV t)) &&
                                    ( e == Bc True => e' == Bc True ) } / [esize e] *)
Fixpoint subBTV_at (j : index) (t_a : type) (e0 : expr) : expr :=
    match e0 with
    | (Bc b)                       => Bc b
    | (Ic n)                       => Ic n
    | (Prim p)                     => Prim p
    | (BV y)                       => BV y 
    | (FV y)                       => FV y
    | (Lambda   e)                 => Lambda    (subBTV_at j t_a e)  
    | (App e e')                   => App       (subBTV_at j t_a e)  (subBTV_at j t_a e')
    | (LambdaT  k e)               => LambdaT k (subBTV_at (j+1) t_a e)
    | (AppT e t)                   => AppT      (subBTV_at j t_a e) (tsubBTV_at j t_a t)
    | (Let   e1 e2)                => Let       (subBTV_at j t_a e1) (subBTV_at j t_a e2) 
    | (Annot e t)                  => Annot     (subBTV_at j t_a e) (tsubBTV_at j t_a t)
    end

(* tsubBTV_at :: j:index -> t_a:Usertype -> t:type
    -> { t':type | Set_sub (free t') (Set_cup (free t_a) (free t)) &&
                   tdepth t' <= tdepth t_a + tdepth t && tdepth t' >= tdepth t &&
                   Set_sub (freeTV t') (Set_cup (freeTV t_a) (freeTV t)) } / [tsize t] *)
with tsubBTV_at (j : index) (t_a : type) (t0 : type) : type :=
    match t0 with
    | (TRefn b   ps)     => match b with
          | (BTV i) => if i =? j then push (psubBTV_at j t_a ps) t_a 
                                 else TRefn b (psubBTV_at j t_a ps) (* TExists y t_y (push x r[t_a/a] t')  *)
          | _       =>                TRefn b (psubBTV_at j t_a ps)    
          end
    | (TFunc   t_z t)    => TFunc    (tsubBTV_at j t_a t_z) (tsubBTV_at j t_a t)  
    | (TExists t_z t)    => TExists  (tsubBTV_at j t_a t_z) (tsubBTV_at j t_a t)  
    | (TPoly   k  t)     => TPoly k  (tsubBTV_at (j+1) t_a t)
    end

(* psubBTV_at :: j:index -> t:Usertype -> ps:preds
                       -> { ps':preds | Set_sub (fvP ps') (Set_cup (fvP ps) (free t)) &&
                                        Set_sub (ftvP ps') (Set_cup (ftvP ps) (freeTV t)) } / [predsize ps] *)
with psubBTV_at (j : index) (t_a : type) (ps0 : preds) : preds :=
    match ps0 with
    | PEmpty       => PEmpty
    | (PCons p ps) => PCons (subBTV_at j t_a p) (psubBTV_at j t_a ps)
    end.

(* subBTV :: t:Usertype -> e:expr
                     -> { e':expr | Set_sub (fv e') (Set_cup (fv e) (free t)) &&
                                    Set_sub (ftv e') (Set_cup (ftv e) (freeTV t)) &&
                                    ( e == Bc True => e' == Bc True ) } / [esize e] *)
Definition subBTV (t : type) (e : expr) : expr  :=  subBTV_at 0 t e.
(* tsubBTV :: t_a:Usertype -> t:type
                -> { t':type | Set_sub (free t') (Set_cup (free t_a) (free t)) &&
                               tdepth t' <= tdepth t_a + tdepth t && tdepth t' >= tdepth t &&
                               Set_sub (freeTV t') (Set_cup (freeTV t_a) (freeTV t)) } / [tsize t] *)
Definition tsubBTV (t_a : type) (t : type) : type  :=  tsubBTV_at 0 t_a t.
(* psubBTV :: t:Usertype -> ps:preds
                       -> { ps':preds | Set_sub (fvP ps') (Set_cup (fvP ps) (free t)) &&
                                        Set_sub (ftvP ps') (Set_cup (ftvP ps) (freeTV t)) } / [predsize ps] *)
Definition psubBTV (t_a : type) (ps : preds) : preds  :=  psubBTV_at 0 t_a ps.
*) *)

(* BARE TYPES: i.e. System F types. These still contain type polymorphism and type variables, 
     but all the refinements, dependent arrow binders, and existentials have been erased. *)

(* openFT_at :: j:index -> a':vname -> t:ftype
                       -> { t':ftype | Set_sub (ffreeTV t') (Set_cup (Set_sng a') (ffreeTV t)) &&
                                       Set_sub (ffreeTV t) (ffreeTV t') * )
Fixpoint openFT_at (j : index) (a' : vname) (t0 : ftype) : ftype :=
    match t0 with
    | (FTBasic b)    => match b with
                        | (BTV i) => if i =? j then FTBasic (FTV a') else FTBasic b
                        | _       => FTBasic b
                        end
    | (FTFunc t_x t) => FTFunc (openFT_at j a' t_x) (openFT_at j a' t)
    | (FTPoly k   t) => FTPoly k (openFT_at (j+1) a' t)
    end.

(* unbindFT :: a':vname -> t:ftype 
                       -> { t':ftype | Set_sub (ffreeTV t') (Set_cup (Set_sng a') (ffreeTV t)) &&
                                       Set_sub (ffreeTV t) (ffreeTV t') *) 
Definition unbindFT (a' : vname) (t : ftype) : ftype := openFT_at 0 a' t.

(* ftsubFV :: a:vname -> t_a:ftype -> t:ftype  
         -> { t':ftype | ( Set_mem a (ffreeTV t) || t == t' ) && 
                ( Set_sub (ffreeTV t') (Set_cup (ffreeTV t_a) (Set_dif (ffreeTV t) (Set_sng a))) ) &&
                ( (not (Set_mem a (ffreeTV t_a))) => not (Set_mem a (ffreeTV t')) ) } *)
Fixpoint ftsubFV (a : vname) (t_a : ftype) (t0 : ftype) : ftype :=
    match t0 with
    | (FTBasic b)     => match b with
                         | (FTV a')  => if a =? a' then t_a else FTBasic b
                         | _         => FTBasic b
                         end
    | (FTFunc t_z t)  => FTFunc (ftsubFV a t_a t_z) (ftsubFV a t_a t)
    | (FTPoly   k t)  => FTPoly k (ftsubFV a t_a t)
    end.

(* ftsubBV_at :: index -> t_a:ftype -> t:ftype  
        -> { t':ftype | Set_sub (ffreeTV t') (Set_cup (ffreeTV t_a) (ffreeTV t)) *)
Fixpoint ftsubBV_at (j : index) (t_a : ftype) (t0 : ftype) : ftype :=
    match t0 with
    | (FTBasic   b)   =>  match b with
                          | (BTV i) => if i =? j then t_a else FTBasic b
                          | _       => FTBasic b
                          end
    | (FTFunc t_z t)  => FTFunc (ftsubBV_at j t_a t_z) (ftsubBV_at j t_a t)
    | (FTPoly  k  t)  => FTPoly k (ftsubBV_at (j+1) t_a t)
    end.
 
(*) ftsubBV :: t_a:ftype -> t:ftype  
        -> { t':ftype | Set_sub (ffreeTV t') (Set_cup (ffreeTV t_a) (ffreeTV t)) *)
Definition ftsubBV (t_a : ftype) (t : ftype) : ftype  :=  ftsubBV_at 0 t_a t.
*)