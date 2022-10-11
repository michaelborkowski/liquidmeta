Require Import Arith.
Require Import Lists.ListSet.

Require Import SystemF.BasicDefinitions.

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

Lemma subset_union_names_add_both : forall (xs ys : names) (z : vname),
    Subset (union (names_add z xs) (names_add z ys)) (names_add z (union xs ys)).
Proof. unfold Subset; intros.
  apply set_union_elim in H; destruct H; apply set_add_elim in H;
  apply set_add_intro; intuition; right; 
  (apply set_union_intro1; assumption) || (apply set_union_intro2; assumption). Qed.

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
    | (AppT e t)      => fv e
    | (Let   ex e)    => union (fv ex) (fv e)
    | (Annot e t)     => fv e
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
    | (AppT e t)      => union (ftv e) (ffreeTV t)
    | (Let   ex e)    => union (ftv ex) (ftv e) 
    | (Annot e t)     => union (ftv e) (ffreeTV t) 
    end.

    (* III. Free variables under substiution etc *)

Lemma fv_open_at_intro : forall (e:expr) (j:index) (y:vname) ,
    Subset (fv e) (fv (open_at j y e)).
Proof. induction e; simpl; intros
       ; try (apply subset_empty_l)
       ; try (apply subset_refl)
       ; (* one IH *) try ( apply IHe)
       ; (* two IH *) try ( apply subset_union_both; apply IHe1 || apply IHe2 ).
  Qed.

Lemma fv_unbind_intro : forall (e:expr) (y:vname) ,
    Subset (fv e) (fv (unbind y e)).
Proof. unfold unbind; intros; apply fv_open_at_intro. Qed.

Lemma ftv_open_at_intro : forall (e:expr) (j:index) (y:vname) ,
    Subset (ftv e) (ftv (open_at j y e)).
Proof. induction e; simpl; intros
      ; try (apply subset_empty_l)
      ; try (apply subset_refl)
      ; (* one IH *) try ( apply IHe )
      ; (* one IH *) try ( apply subset_union_both; apply IHe || apply subset_refl )
      ; (* two IH *) try ( apply subset_union_both; apply IHe1 || apply IHe2 ).
  Qed.

Lemma ftv_unbind_intro : forall (e:expr) (y:vname) ,
    Subset (ftv e) (ftv (unbind y e)).
Proof. unfold unbind; intros; apply ftv_open_at_intro. Qed. 

Lemma fv_open_tv_at_intro : forall (e:expr) (j:index) (a:vname) ,
  Subset (fv e) (fv (open_tv_at j a e)).
Proof. induction e; simpl; intros
      ; try (apply subset_empty_l)
      ; try (apply subset_refl)
      ; (* one IH *) try ( apply IHe )
      ; (* two IH *) try ( apply subset_union_both; apply IHe1 || apply IHe2 ).
Qed.

Lemma fv_unbind_tv_intro : forall (e:expr) (a:vname) ,
    Subset (fv e) (fv (unbind_tv a e)).
Proof. unfold unbind_tv; intros; apply fv_open_tv_at_intro. Qed. 

Lemma ffreeTV_openFT_at_intro : forall (t:ftype) (j:index) (a:vname),
    Subset (ffreeTV t) (ffreeTV (openFT_at j a t)).
Proof. induction t; intros; simpl.
  - destruct b; simpl; try apply subset_refl; try apply subset_empty_l.
  - apply subset_union_both; apply IHt1 || apply IHt2.
  - apply IHt.
  Qed. 

Lemma ftv_open_tv_at_intro : forall (e:expr) (j:index) (a:vname) ,
    Subset (ftv e) (ftv (open_tv_at j a e)).
Proof. induction e; simpl; intros
      ; try (apply subset_empty_l)
      ; try (apply subset_refl)
      ; (* one IH *) try ( apply IHe )
      ; try ( apply subset_union_both; apply IHe || apply ffreeTV_openFT_at_intro )
      ; (* two IH *) try ( apply subset_union_both; apply IHe1 || apply IHe2 ).
  Qed.

Lemma ftv_unbind_tv_intro : forall (e:expr) (a:vname) ,
    Subset (ftv e) (ftv (unbind_tv a e)).
Proof. unfold unbind_tv; intros; apply ftv_open_tv_at_intro. Qed. 


Lemma fv_subFV_elim : forall (e:expr) (x:vname) (v:expr),
    Subset (fv (subFV x v e)) (union (diff (fv e) (singleton x)) (fv v)).
Proof. induction e; intros; simpl
  ; try (apply subset_empty_l)
  ; (* one IH *) try ( apply IHe )
  ; (* two IH *) try ( unfold Subset; intros; 
    apply set_union_elim in H; destruct H; 
    apply IHe1 in H || apply IHe2 in H;
    apply set_union_elim in H; destruct H; apply set_union_intro; 
    intuition; left; 
    apply set_diff_intro; apply set_diff_iff in H; destruct H;
    try assumption; apply set_union_intro; intuition ).
  - destruct (x0 =? x) eqn:E; simpl; 
    apply Nat.eqb_eq in E || apply Nat.eqb_neq in E; 
    symmetry in E || apply Nat.neq_sym in E;
    destruct (Nat.eq_dec x x0) eqn:D; try contradiction.
    * apply union_empty_l. 
    * apply subset_sing_l; apply set_union_intro1; simpl; intuition.
  Qed.

Lemma ftv_subFV_elim : forall (e:expr) (x:vname) (v:expr),
    Subset (ftv (subFV x v e)) (union (ftv e) (ftv v)).
Proof. induction e; intros; simpl
  ; try (apply subset_empty_l)
  ; (* one IH *) try ( apply IHe )
  ; (* two IH *) try ( unfold Subset; intros; 
    apply set_union_elim in H; destruct H;
    apply IHe1 in H || apply IHe2 in H || (try apply IHe in H);
    try apply set_union_elim in H; try destruct H; apply set_union_intro;
    intuition; left; apply set_union_intro; intuition ).
  - (* FV *) destruct (x0 =? x) eqn:E; simpl;
    apply union_empty_l || apply subset_empty_l.
  Qed.

Lemma fv_subFTV_elim : forall (e:expr) (a:vname) (t_a:ftype),
    Subset (fv (subFTV a t_a e)) (union (fv e) (ffreeTV t_a)).
Proof. induction e; intros; simpl
  ; try (apply subset_empty_l)
  ; (* one IH *) try apply IHe 
  ; (* two IH *) try ( unfold Subset; intros; 
    apply set_union_elim in H; destruct H;
    apply IHe1 in H || apply IHe2 in H; 
    apply set_union_elim in H; destruct H; apply set_union_intro;
    intuition; left; apply set_union_intro; intuition ).
  - (* FV *) apply subset_union_intro_r.
  Qed. 

Lemma ffreeTV_ftsubFV_elim : forall (t:ftype) (a:vname) (t_a:ftype),
    Subset (ffreeTV (ftsubFV a t_a t)) (union (diff (ffreeTV t) (singleton a)) (ffreeTV t_a)).
Proof. induction t; intros; simpl
  ; (* one IH *) try apply IHt
  ; (* two IH *) try ( unfold Subset; intros;
    apply set_union_elim in H; destruct H; 
    apply IHt1 in H || apply IHt2 in H ; 
    apply set_union_elim in H; destruct H; apply set_union_intro;
    intuition; left; 
    apply set_diff_intro; apply set_diff_iff in H; destruct H;
    try assumption; apply set_union_intro; intuition ).
  - (* FTBasic *) destruct b eqn:B; simpl; try apply subset_empty_l;
    destruct (Nat.eqb a a0) eqn:A; destruct (Nat.eq_dec a0 a) eqn:D; 
    simpl; try apply subset_union_intro_r.
    apply Nat.eqb_neq in A; rewrite e in A; contradiction.
  Qed.

Lemma ftv_subFTV_elim : forall (e:expr) (a:vname) (t_a:ftype),
    Subset (ftv (subFTV a t_a e)) (union (diff (ftv e) (singleton a)) (ffreeTV t_a)).
Proof. induction e; intros; simpl
  ; try (apply subset_empty_l)
  ; (* one IH *) try apply IHe
  ; (* two IH *) try ( unfold Subset; intros;
    apply set_union_elim in H; destruct H; 
    apply IHe1 in H || apply IHe2 in H 
      || (try apply IHe in H) || (try apply ffreeTV_ftsubFV_elim in H); 
    try apply set_union_elim in H; try destruct H; apply set_union_intro;
    intuition; left; 
    apply set_diff_intro; apply set_diff_iff in H; destruct H;
    try assumption; apply set_union_intro; intuition ).
  Qed.  

(*-------------------------------------------------------------------------
----- | IV. TYPING ENVIRONMENTS
-------------------------------------------------------------------------*)

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
  
  (* V. alternative formulations including the assigned ftype/kind *)

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
Proof. split; unfold in_envF; apply above_fresh_not_elem; 
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