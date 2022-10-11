Require Import Arith.

Require Import SystemRF.BasicDefinitions.

(*------------------------------------------------------------------------------
 *---- | Local Closure of Locally Nameless Terms
 *----------------------------------------------------------------------------*)

Lemma lem_islc_at_weaken : (forall  (e : expr) (j k j' k' : index),
    j <= j' -> k <= k' -> isLC_at j k e -> isLC_at j' k' e ) * ((
  forall (t : type) (j k j' k' : index),
    j <= j' -> k <= k' -> isLCT_at j k t -> isLCT_at j' k' t ) * (
  forall (ps : preds) (j k j' k' : index),
    j <= j' -> k <= k' -> isLCP_at j k ps -> isLCP_at j' k' ps ))%type.
Proof. apply (syntax_mutind
  (fun e : expr => forall (j k j' k' : index),
       j <= j' -> k <= k' -> isLC_at j k e -> isLC_at j' k' e)
  (fun t : type => forall (j k j' k' : index),
       j <= j' -> k <= k' -> isLCT_at j k t -> isLCT_at j' k' t)   
  (fun ps : preds => forall (j k j' k' : index),
       j <= j' -> k <= k' -> isLCP_at j k ps -> isLCP_at j' k' ps)).
   
  all : simpl.
  - (* Bc b *) reflexivity.
  - (* Ic n *) reflexivity.
  - (* Prim p *) reflexivity. 
  - (* BV i *) simpl. intros i j k j' k' j_le k_le Hjk. apply lt_le_trans with j. all : assumption.
  - (* FV x *) reflexivity.
  - (* Lambda e *) intros e IHe j k j' k' j_le k_le. apply IHe. 
      { apply plus_le_compat_r. apply j_le. } 
      { apply k_le. }
  - (* App e e' *) intros e1 IHe1 e2 IHe2 j k j' k' j_le k_le Hjk. 
      destruct Hjk as [H1 H2]. split.
      { apply IHe1 with j k. apply j_le. apply k_le. apply H1. } 
      { apply IHe2 with j k. apply j_le. apply k_le. apply H2. }
  - (* LambdaT k e *) intros k e IHe j k0 j' k' j_le k_le Hjk. 
      apply IHe with j (k0+1). 
      apply j_le. apply plus_le_compat_r. apply k_le. apply Hjk.
  - (* AppT e t *) intros e IHe t IHt j k j' k' j_le k_le Hjk. 
      destruct Hjk as [He Ht]. split.
      { apply IHe with j k. all : assumption. }
      { apply IHt with j k. all : assumption. }
  - (* Let e1 e2 *) intros.
      destruct H3 as [He1 He2]. split.
      { apply H  with j     k. all : assumption. }
      { apply H0 with (j+1) k. apply plus_le_compat_r. all : assumption. }
  - (* Annot e t *) intros. destruct H3 as [He Ht]. split.
      { apply H  with j k. all : assumption. }
      { apply H0 with j k. all : assumption. }

  - (* TRefn b ps *) intros. destruct b.
      { apply H with (j+1) k. apply plus_le_compat_r. all : assumption.  }
      { apply H with (j+1) k. apply plus_le_compat_r. all : assumption.  }
      { destruct H2. split. 
        { apply lt_le_trans with k. all : assumption. }
        { apply H with (j+1) k. apply plus_le_compat_r. all : assumption. }}
      { apply H with (j+1) k. apply plus_le_compat_r. all : assumption.  }
  - (* TFunc tx t *) intros. destruct H3 as [Htx Ht]. split.
      { apply H  with j     k. all : assumption. } 
      { apply H0 with (j+1) k. apply plus_le_compat_r. all : assumption. }
  - (* TExists tx t *) intros. destruct H3 as [Htx Ht]. split.
      { apply H  with j     k. all : assumption. } 
      { apply H0 with (j+1) k. apply plus_le_compat_r. all : assumption. }
  - (* TPoly k t *) intros. apply H with j (k0+1). 
      assumption. apply plus_le_compat_r. all: assumption.

  - (* PEmpty *) reflexivity.
  - (* PCons p ps *) intros. destruct H3 as [Hp Hps]. split.
      { apply H  with j k. all : assumption. }
      { apply H0 with j k. all : assumption. }
  Qed.

Lemma lem_islc_at_subFV : (forall  (e : expr) (j k : index) (x : vname) (v_x : expr),
    isLC v_x -> isLC_at j k e -> isLC_at j k (subFV x v_x e )) * ((
  forall (t : type) (j k : index) (x : vname) (v_x : expr),
    isLC v_x -> isLCT_at j k t -> isLCT_at j k (tsubFV x v_x t ) ) * (
  forall (ps : preds) (j k : index) (x : vname) (v_x : expr),
    isLC v_x -> isLCP_at j k ps -> isLCP_at j k (psubFV x v_x ps ) ))%type.
Proof. apply (syntax_mutind
  (fun e : expr => forall (j k : index) (x : vname) (v_x : expr),
    isLC v_x -> isLC_at j k e -> isLC_at j k (subFV x v_x e ))
  (fun t : type => forall (j k : index) (x : vname) (v_x : expr),
    isLC v_x -> isLCT_at j k t -> isLCT_at j k (tsubFV x v_x t ))   
  (fun ps : preds => forall (j k : index) (x : vname) (v_x : expr),
    isLC v_x -> isLCP_at j k ps -> isLCP_at j k (psubFV x v_x ps ))).

  all : simpl.
  - (* Bc b *) reflexivity.
  - (* Ic n *) reflexivity.
  - (* Prim p *) reflexivity. 
  - (* BV i *) intros. assumption.
  - (* FV x *) intros. destruct (x0 =? x). 
      { apply lem_islc_at_weaken with 0 0. apply le_0_n. apply le_0_n. assumption. }
      { reflexivity. }
  - (* Lambda e *) intros. apply H. all : assumption.
  - (* App e e' *) intros. 
      destruct H2 as [He1 He2]. split.
      { apply H.  all : assumption. } 
      { apply H0. all : assumption. }
  - (* LambdaT k e *) intros. apply H. all : assumption.
  - (* AppT e t *) intros. 
      destruct H2 as [He Ht]. split.
      { apply H . all : assumption. }
      { apply H0. all : assumption. }
  - (* Let e1 e2 *) intros.
      destruct H2 as [He1 He2]. split.
      { apply H . all : assumption. }
      { apply H0. all : assumption. }
  - (* Annot e t *) intros. destruct H2 as [He Ht]. split.
      { apply H . all : assumption. }
      { apply H0. all : assumption. }

  - (* TRefn b ps *) intros. destruct b.
      { apply H. all : assumption.  }
      { apply H. all : assumption.  }
      { destruct H1. split. { assumption. } 
        { apply H. all : assumption. }}
      { apply H. all : assumption.  }
  - (* TFunc tx t *) intros. destruct H2 as [Htx Ht]. split.
      { apply H . all : assumption. } 
      { apply H0. all : assumption. }
  - (* TExists tx t *) intros. destruct H2 as [Htx Ht]. split.
      { apply H . all : assumption. } 
      { apply H0. all : assumption. }
  - (* TPoly k t *) intros. apply H. all: assumption.

  - (* PEmpty *) reflexivity.
  - (* PCons p ps *) intros. destruct H2 as [Hp Hps]. split.
      { apply H . all : assumption. }
      { apply H0. all : assumption. }
  Qed.   

Lemma lem_islcp_at_strengthen : forall (j k : index) (ps : preds) (ts : preds),
    j >= 1 -> isLCP_at j k ps -> isLCP_at 1 0 ts -> isLCP_at j k (strengthen ps ts ).
Proof. intros j k. induction ps. all : simpl.
  - (* PEmpty *) intros. apply lem_islc_at_weaken with 1 0. 
      { assumption. } { apply le_0_n. } { assumption. }
  - (* PCons p ps *) intros. destruct H0 as [Hp Hps]. split.
      { assumption. } { apply IHps. all : assumption. }
  Qed.

Lemma lem_islcp_at_push : forall (j k:index) (ps:preds) (t_a:type),
    j >= 1 -> noExists t_a -> isLCP_at j k ps -> isLCT t_a -> isLCT_at (j-1) k (push ps t_a).
Proof. intros j k ps t_a H_j1 H_ut H_ps. (*destruct t_a as [t] eqn:E. simpl. *)
  destruct t_a; unfold isLCT.
  - (* TRefn b ps0 *) simpl. assert ((j - 1) + 1 = j) as Hj. 
      { rewrite plus_comm. rewrite minus_Sn_m. 
          - symmetry. apply plus_minus. reflexivity. 
          - assumption. }
      destruct b eqn:Eb; rewrite Hj. 
      (* b = TBool *) { apply lem_islcp_at_strengthen; assumption. }
      (* b = TInt  *) { apply lem_islcp_at_strengthen; assumption. }
      (* b = BTV i *) { intro H1. destruct H1. split.
          * apply lt_le_trans with 0. assumption. apply le_0_n.
          * apply lem_islcp_at_strengthen; assumption. }
      (* b = FTV x *) { apply lem_islcp_at_strengthen; assumption. }
  - (* TFunc t1 t2 *) apply lem_islc_at_weaken; apply le_0_n.
  - (* TExists t1 t2 *) contradiction.
  - (* TPoly k1 k2 *) apply lem_islc_at_weaken; apply le_0_n.
  Qed.

Lemma lem_islc_at_subFTV : (
  forall (e: expr) (j k : index) (a : vname) (t_a : type),
    noExists t_a -> isLCT t_a -> isLC_at j k e -> isLC_at j k (subFTV a t_a e)  ) * ((
  forall (t:type) (j k : index) (a : vname) (t_a : type),
    noExists t_a -> isLCT t_a -> isLCT_at j k t -> isLCT_at j k (tsubFTV a t_a t)  ) * (
  forall (ps : preds) (j k : index) (a : vname) (t_a : type),
    noExists t_a -> isLCT t_a -> isLCP_at j k ps -> isLCP_at j k (psubFTV a t_a ps)  )).
Proof. apply (syntax_mutind
  (fun e : expr => forall (j k : index) (a : vname) (t_a : type),
    noExists t_a -> isLCT t_a -> isLC_at j k e -> isLC_at j k (subFTV a t_a e))
  (fun t : type => forall (j k : index) (a : vname) (t_a : type),
    noExists t_a -> isLCT t_a -> isLCT_at j k t -> isLCT_at j k (tsubFTV a t_a t))   
  (fun ps : preds => forall (j k : index) (a : vname) (t_a : type),
    noExists t_a -> isLCT t_a -> isLCP_at j k ps -> isLCP_at j k (psubFTV a t_a ps))).

  all : simpl.
  - (* Bc b *) reflexivity.
  - (* Ic n *) reflexivity.
  - (* Prim p *) reflexivity. 
  - (* BV i *) intros. assumption. 
  - (* FV x *) reflexivity.
  - (* Lambda e *) intros e IH j. apply IH.
  - (* App e e' *) intros. destruct H3. 
      split; (apply H || apply H0); assumption.
  - (* LambdaT k e *) intros k e IH j k0. apply IH.
  - (* AppT e t *) intros. destruct H3.
      split; (apply H || apply H0); assumption.
  - (* Let e1 e2 *) intros. destruct H3.
      split; (apply H || apply H0); assumption.
  - (* Annot e t *) intros. destruct H3.
      split; (apply H || apply H0); assumption.

  - (* TRefn b ps *) intros. destruct b as [ | |i|a']; simpl.
      (* TBool *) { apply H; assumption. }
      (* TInt  *) { apply H; assumption. }
      (* BTV i *) { destruct H2. split. assumption. 
          apply H; assumption. }
      (* FTV a' *) { destruct (a =? a').
          * rewrite <- (minus_plus 1 j). rewrite plus_comm. 
            apply lem_islcp_at_push; try assumption. 
              - apply le_plus_r. 
              - apply H; assumption.
          * apply H; assumption.  }
  - (* TFunc tx t *) intros. destruct H3.
      split; (apply H || apply H0); assumption.
  - (* TExists tx t *) intros. destruct H3.
      split; (apply H || apply H0); assumption.
  - (* TPoly k t *) intros. apply H; assumption.

  - (* PEmpty *) reflexivity.
  - (* PCons p ps *) intros. destruct H3.
      split; (apply H || apply H0); assumption. 
  Qed.   

(*-------------------------------------------------------------------------------
  -- | Behavior of isLC, isLC_at etc under unbind, open_at etc
-------------------------------------------------------------------------------*)

Lemma lt_S : forall (j : index), j < j + 1.
Proof. intro j. rewrite <- plus_0_r at 1. apply plus_lt_compat_l. unfold lt. trivial. Qed.

Lemma tighten_lt : forall (i j : index),
    i < j + 1  ->  j <> i  ->  i < j.
Proof. intros i j Hlt Hneq. rewrite plus_comm in Hlt. simpl in Hlt.  
  unfold lt in Hlt. unfold lt.
  apply not_eq_S in Hneq. apply Nat.le_succ_r in Hlt. 
  destruct Hlt. { assumption. } 
                { symmetry in H; contradiction. } 
  Qed.

Lemma loosen_lt : forall (i j : index),
    i < j -> i < j + 1. 
Proof. intros i j Hlt. assert (j < j + 1). apply lt_S. 
  apply lt_trans with j; assumption. Qed. 

Lemma beq_lt_S : forall ( i j : index ),
  (j =? i) = true  ->  i < j + 1.
Proof. intros. apply beq_nat_true in H. rewrite H. apply lt_S. Qed.


Lemma lem_islc_at_before_open_at : (forall (e : expr) (j k : index) (y : vname),
    isLC_at (j+1) k e -> isLC_at j k (open_at j y e) ) * ((
  forall (t : type) (j k : index) (y : vname),
    isLCT_at (j+1) k t -> isLCT_at j k (openT_at j y t)  ) * (
  forall (ps : preds) (j k : index) (y : vname),
    isLCP_at (j+1) k ps -> isLCP_at j k (openP_at j y ps))).
Proof. apply (syntax_mutind
  (fun e : expr => forall (j k : index) (y : vname),
    isLC_at (j+1) k e -> isLC_at j k (open_at j y e))
  (fun t : type => forall (j k : index) (y : vname),
    isLCT_at (j+1) k t -> isLCT_at j k (openT_at j y t))   
  (fun ps : preds => forall  (j k : index) (y : vname),
    isLCP_at (j+1) k ps -> isLCP_at j k (openP_at j y ps))); 
  simpl.
  - (* Bc b *) reflexivity.
  - (* Ic n *) reflexivity.
  - (* Prim p *) reflexivity.
  - (* BV i *) intros i j k y H_ij1. destruct (j =? i) eqn:E; simpl.
        { reflexivity. } 
        { apply beq_nat_false in E. apply tighten_lt; assumption. }
  - (* FV x *) reflexivity.
  - (* Lambda e *) intros e H j k y. apply H. 
  - (* App e e' *) intros. destruct H1.
      split; (apply H || apply H0); assumption. 
  - (* LambdaT k e *) intros k e H j k0 y. apply H.
  - (* AppT e t *) intros. destruct H1.
      split; (apply H || apply H0); assumption. 
  - (* Let e1 e2 *) intros. destruct H1.
      split; (apply H || apply H0); assumption. 
  - (* Annot e t *) intros. destruct H1.
      split; (apply H || apply H0); assumption. 

  - (* TRefn b ps *) intros. destruct b as [ | |i|a']; 
      try (apply H; assumption).
      (* BTV i *) { destruct H0. split. assumption. apply H. assumption. }
  - (* TFunc tx t *) intros. destruct H1.
      split; (apply H || apply H0); assumption. 
  - (* TExists tx t *) intros. destruct H1.
      split; (apply H || apply H0); assumption. 
  - (* TPoly k t *) intros k t IH j k0 y. apply IH.

  - (* PEmpty *) reflexivity.
  - (* PCons p ps *) intros. destruct H1.
      split; (apply H || apply H0); assumption.  
  Qed.  

(* -- In particular, isLC (unbind y e) => isLC_at 1 0 e *)
Lemma lem_islc_at_after_open_at : (forall (e : expr) (j k : index) (y : vname),
  isLC_at j k (open_at j y e) -> isLC_at (j+1) k e ) * ((
forall (t : type) (j k : index) (y : vname),
  isLCT_at j k (openT_at j y t) -> isLCT_at (j+1) k t ) * (
forall (ps : preds) (j k : index) (y : vname),
  isLCP_at j k (openP_at j y ps) -> isLCP_at (j+1) k ps )).
Proof. apply (syntax_mutind
  (fun e : expr => forall (j k : index) (y : vname),
    isLC_at j k (open_at j y e) -> isLC_at (j+1) k e)
  (fun t : type => forall (j k : index) (y : vname),
    isLCT_at j k (openT_at j y t) -> isLCT_at (j+1) k t)   
  (fun ps : preds => forall  (j k : index) (y : vname),
    isLCP_at j k (openP_at j y ps) -> isLCP_at (j+1) k ps)); 
  simpl.
  - (* Bc b *) reflexivity.
  - (* Ic n *) reflexivity.
  - (* Prim p *) reflexivity.
  - (* BV i *) intros. destruct (j =? i) eqn:E.
      { apply beq_lt_S. assumption. }
      { simpl in H. apply loosen_lt. assumption. }
  - (* FV x *) reflexivity.
  - (* Lambda e *) intros e H j k y. apply H. 
  - (* App e e' *) intros. destruct H1. 
      split; (apply H with y || apply H0 with y ); assumption. 
  - (* LambdaT k e *) intros k e H j k0 y. apply H.
  - (* AppT e t *) intros. destruct H1.
      split; (apply H with y || apply H0 with y ); assumption. 
  - (* Let e1 e2 *) intros. destruct H1.
      split; (apply H with y || apply H0 with y ); assumption. 
  - (* Annot e t *) intros. destruct H1.
      split; (apply H with y || apply H0 with y ); assumption. 

  - (* TRefn b ps *) intros. destruct b as [ | |i|a']; 
      try (apply H with y; assumption).
      (* BTV i *) { destruct H0. split. assumption. apply H with y. assumption. }
  - (* TFunc tx t *) intros. destruct H1.
      split; (apply H with y || apply H0 with y ); assumption. 
  - (* TExists tx t *) intros. destruct H1.
      split; (apply H with y || apply H0 with y ); assumption. 
  - (* TPoly k t *) intros k t IH j k0 y. apply IH.

  - (* PEmpty *) reflexivity.
  - (* PCons p ps *) intros. destruct H1.
      split; (apply H with y || apply H0 with y ); assumption.  
  Qed.  


Lemma lem_islc_at_after_open_tv_at : (forall (e : expr) (j k : index) (a : vname), 
    isLC_at j k (open_tv_at k a e) -> isLC_at j (k+1) e  ) * ((
  forall (t : type) (j k : index) (a : vname), 
    isLCT_at j k (open_tvT_at k a t) -> isLCT_at j (k+1) t ) * (
  forall (ps : preds) (j k : index) (a : vname), 
    isLCP_at j k (open_tvP_at k a ps) -> isLCP_at j (k+1) ps )).
Proof. apply (syntax_mutind
  (fun e : expr => forall (j k : index) (a : vname),
    isLC_at j k (open_tv_at k a e) -> isLC_at j (k+1) e)
  (fun t : type => forall (j k : index) (a : vname),
    isLCT_at j k (open_tvT_at k a t) -> isLCT_at j (k+1) t )   
  (fun ps : preds => forall (j k : index) (a : vname),
    isLCP_at j k (open_tvP_at k a ps) -> isLCP_at j (k+1) ps )); simpl.

  - (* Bc b *) reflexivity.
  - (* Ic n *) reflexivity.
  - (* Prim p *) reflexivity. 
  - (* BV i *) intros. assumption.
  - (* FV x *) reflexivity.
  - (* Lambda e *) intros e IH j k. apply IH. 
  - (* App e e' *) intros. destruct H1.
      split; (apply H with a || apply H0 with a ); assumption.
  - (* LambdaT k e *) intros k e IH j k0. apply IH.
  - (* AppT e t *) intros. destruct H1.
      split; (apply H with a || apply H0 with a ); assumption.
  - (* Let e1 e2 *) intros. destruct H1.
      split; (apply H with a || apply H0 with a ); assumption.
  - (* Annot e t *) intros. destruct H1.
      split; (apply H with a || apply H0 with a ); assumption. 

  - (* TRefn b ps *) intros b ps IH j k. destruct b;
      try (apply IH).
      (* BTV i *) { intros. destruct (k =? i) eqn:E. simpl in H.
        * split. apply beq_lt_S in E. assumption. apply IH with a. assumption.
        * simpl in H. split; destruct H. 
            { apply loosen_lt. assumption. } 
            { apply IH with a. assumption. }}
  - (* TFunc tx t *) intros. destruct H1.
      split; (apply H with a || apply H0 with a ); assumption.
  - (* TExists tx t *) intros. destruct H1.
      split; (apply H with a || apply H0 with a ); assumption. 
  - (* TPoly k t *) intros k t IH j k0. apply IH.

  - (* PEmpty *) reflexivity.
  - (* PCons p ps *) intros. destruct H1.
      split; (apply H with a || apply H0 with a ); assumption.
  Qed.  

(*  -- | System F Version  *)
Lemma lem_islcft_at_after_openFT_at : forall (t : ftype) (j : index) (a : vname),
    isLCFT_at j (openFT_at j a t) -> isLCFT_at (j+1) t.
Proof. induction t; simpl.
  - (* FTBasic b *) intros j a. destruct b; try reflexivity.
        (* BTV i *) destruct (j =? i) eqn:Eij; simpl. 
            * (* i =? j *) intro. apply beq_lt_S. assumption. 
            * (* i /= j *) apply loosen_lt.
  - (* FTFunc tx t *) intros j a H. destruct H as [Ht1 Ht2].
      split; (apply IHt1 with a || apply IHt2 with a); assumption.
  - (* FTPoly k t *) intros j a. apply IHt.
  Qed. 