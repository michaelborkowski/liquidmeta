Require Import Arith.

Require Import SystemF.BasicDefinitions.

(*------------------------------------------------------------------------------
 *---- | Local Closure of Locally Nameless Terms
 *----------------------------------------------------------------------------*)

Lemma lem_islcft_at_weaken: forall (t:ftype) (k k' : index),
    k <= k' -> isLCFT_at k t -> isLCFT_at k' t.
Proof. induction t. 
  - (* FTBasic b *) intros. destruct b; simpl; trivial.
      { simpl in H0. apply lt_le_trans with k; assumption. }
  - (* TFunc tx t *) intros. destruct H0 as [Htx Ht]. split.
      { apply IHt1 with k. all : assumption. } 
      { apply IHt2 with k. all : assumption. }
  - (* TPoly k t *) intros. apply IHt with (k0+1). 
      apply plus_le_compat_r. all: assumption.
  Qed.

Lemma lem_islc_at_weaken : forall  (e : expr) (j k j' k' : index),
    j <= j' -> k <= k' -> isLC_at j k e -> isLC_at j' k' e.
Proof. induction e.
   
  all : simpl.
  - (* Bc b *) reflexivity.
  - (* Ic n *) reflexivity.
  - (* Prim p *) reflexivity. 
  - (* BV i *) simpl. intros j k j' k' j_le k_le Hjk. apply lt_le_trans with j. all : assumption.
  - (* FV x *) reflexivity.
  - (* Lambda e *) intros j k j' k' j_le k_le. apply IHe. 
      { apply plus_le_compat_r. apply j_le. } 
      { apply k_le. }
  - (* App e e' *) intros j k j' k' j_le k_le Hjk. 
      destruct Hjk as [H1 H2]. split.
      { apply IHe1 with j k. apply j_le. apply k_le. apply H1. } 
      { apply IHe2 with j k. apply j_le. apply k_le. apply H2. }
  - (* LambdaT k e *) intros j k0 j' k' j_le k_le Hjk. 
      apply IHe with j (k0+1). 
      apply j_le. apply plus_le_compat_r. apply k_le. apply Hjk.
  - (* AppT e t *) intros j k j' k' j_le k_le Hjk. 
      destruct Hjk as [He Ht]. split.
      { apply IHe with j k. all : assumption. }
      { apply lem_islcft_at_weaken with k. all : assumption. }
  - (* Let e1 e2 *) intros.
      destruct H1 as [He1 He2]. split.
      { apply IHe1 with j     k. all : assumption. }
      { apply IHe2 with (j+1) k. apply plus_le_compat_r. all : assumption. }
  - (* Annot e t *) intros. destruct H1 as [He Ht]. split.
      { apply IHe with j k. all : assumption. }
      { apply lem_islcft_at_weaken with k. all : assumption. }
  Qed.

Lemma lem_islc_at_subFV : forall  (e : expr) (j k : index) (x : vname) (v_x : expr),
    isLC v_x -> isLC_at j k e -> isLC_at j k (subFV x v_x e ).
Proof. induction e.

  all : simpl.
  - (* Bc b *) reflexivity.
  - (* Ic n *) reflexivity.
  - (* Prim p *) reflexivity. 
  - (* BV i *) intros. assumption.
  - (* FV x *) intros. destruct (x0 =? x). 
      { apply lem_islc_at_weaken with 0 0. apply le_0_n. apply le_0_n. assumption. }
      { reflexivity. }
  - (* Lambda e *) intros. apply IHe. all : assumption.
  - (* App e e' *) intros. 
      destruct H0 as [He1 He2]. split.
      { apply IHe1. all : assumption. } 
      { apply IHe2. all : assumption. }
  - (* LambdaT k e *) intros. apply IHe. all : assumption.
  - (* AppT e t *) intros. 
      destruct H0 as [He Ht]. split.
      apply IHe. all : assumption. 
  - (* Let e1 e2 *) intros.
      destruct H0 as [He1 He2]. split.
      { apply IHe1. all : assumption. }
      { apply IHe2. all : assumption. }
  - (* Annot e t *) intros. destruct H0 as [He Ht]. split.
      apply IHe. all : assumption.
  Qed.   

Lemma lem_islcft_at_ftsubFV : forall (t:ftype) (k:index) (a:vname) (t_a:ftype),
  isLCFT t_a -> isLCFT_at k t -> isLCFT_at k (ftsubFV a t_a t).
Proof. induction t. all : simpl.
  - (* FTBasic b *) intros. destruct b as [ | |i|a']; simpl.
      (* TBool *) trivial.
      (* TInt  *) trivial.
      (* BTV i *) assumption. 
      (* FTV a' *) destruct (a =? a'); simpl.
        apply lem_islcft_at_weaken with 0. 
        all : intuition.
  - (* FTFunc tx t *) intros. destruct H0.
      split; (apply IHt1 || apply IHt2); assumption.
  - (* FTPoly k t *) intros. apply IHt; assumption.
  Qed.

Lemma lem_islc_at_subFTV : forall (e:expr) (j k:index) (a:vname) (t_a:ftype),
    isLCFT t_a -> isLC_at j k e -> isLC_at j k (subFTV a t_a e).
Proof. induction e.

  all : simpl.
  - (* Bc b *) reflexivity.
  - (* Ic n *) reflexivity.
  - (* Prim p *) reflexivity. 
  - (* BV i *) intros. assumption. 
  - (* FV x *) reflexivity.
  - (* Lambda e *) intros j. apply IHe. 
  - (* App e e' *) intros. destruct H0. 
      split; (apply IHe1 || apply IHe2); assumption.
  - (* LambdaT k e *) intros j k0. apply IHe.
  - (* AppT e t *) intros. destruct H0.
      split; (apply IHe || apply lem_islcft_at_ftsubFV); assumption.
  - (* Let e1 e2 *) intros. destruct H0. 
      split; (apply IHe1 || apply IHe2); assumption.
  - (* Annot e t *) intros. destruct H0.
      split; (apply IHe || apply lem_islcft_at_ftsubFV); assumption.
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


Lemma lem_islc_at_before_open_at : forall (e : expr) (j k : index) (y : vname),
    isLC_at (j+1) k e -> isLC_at j k (open_at j y e).
Proof. induction e; simpl.
  - (* Bc b *) reflexivity.
  - (* Ic n *) reflexivity.
  - (* Prim p *) reflexivity.
  - (* BV i *) intros j k y H_ij1. destruct (j =? i) eqn:E; simpl.
        { reflexivity. } 
        { apply beq_nat_false in E. apply tighten_lt; assumption. }
  - (* FV x *) reflexivity.
  - (* Lambda e *) intros j k y. apply IHe. 
  - (* App e e' *) intros. destruct H.
      split; (apply IHe1 || apply IHe2); assumption. 
  - (* LambdaT k e *) intros j k0 y. apply IHe.
  - (* AppT e t *) intros. destruct H;
      split; apply IHe || assumption; assumption. 
  - (* Let e1 e2 *) intros. destruct H.
      split; (apply IHe1 || apply IHe2); assumption. 
  - (* Annot e t *) intros. destruct H;
      split; apply IHe || assumption; assumption.
  Qed. 

(* -- In particular, isLC (unbind y e) => isLC_at 1 0 e *)
Lemma lem_islc_at_after_open_at : forall (e : expr) (j k : index) (y : vname),
  isLC_at j k (open_at j y e) -> isLC_at (j+1) k e.
Proof. induction e; simpl.
  - (* Bc b *) reflexivity.
  - (* Ic n *) reflexivity.
  - (* Prim p *) reflexivity.
  - (* BV i *) intros. destruct (j =? i) eqn:E.
      { apply beq_lt_S. assumption. }
      { simpl in H. apply loosen_lt. assumption. }
  - (* FV x *) reflexivity.
  - (* Lambda e *) intros j k y. apply IHe. 
  - (* App e e' *) intros. destruct H. 
      split; (apply IHe1 with y || apply IHe2 with y ); assumption. 
  - (* LambdaT k e *) intros j k0 y. apply IHe.
  - (* AppT e t *) intros. destruct H.
      split; (apply IHe with y || assumption ); assumption. 
  - (* Let e1 e2 *) intros. destruct H. 
      split; (apply IHe1 with y || apply IHe2 with y ); assumption. 
  - (* Annot e t *) intros. destruct H.
      split; (apply IHe with y || assumption ); assumption. 
  Qed.  

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

Lemma lem_islc_at_after_open_tv_at : forall (e : expr) (j k : index) (a : vname), 
    isLC_at j k (open_tv_at k a e) -> isLC_at j (k+1) e.
Proof. induction e; simpl.

  - (* Bc b *) reflexivity.
  - (* Ic n *) reflexivity.
  - (* Prim p *) reflexivity. 
  - (* BV i *) intros. assumption.
  - (* FV x *) reflexivity.
  - (* Lambda e *) intros j k. apply IHe. 
  - (* App e e' *) intros. destruct H.
      split; (apply IHe1 with a || apply IHe2 with a ); assumption.
  - (* LambdaT k e *) intros j k0. apply IHe.
  - (* AppT e t *) intros. destruct H.
      split; (apply IHe with a || apply lem_islcft_at_after_openFT_at with a); 
      assumption.
  - (* Let e1 e2 *) intros. destruct H.
      split; (apply IHe1 with a || apply IHe2 with a ); assumption.
  - (* Annot e t *) intros. destruct H.
      split; (apply IHe with a || apply lem_islcft_at_after_openFT_at with a); 
      assumption.
  Qed.  