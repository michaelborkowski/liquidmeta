Require Import SystemRF.BasicDefinitions. 
Require Import SystemRF.Names.
Require Import SystemRF.SystemFWellFormedness.
Require Import Denotations.Denotations.

From Equations Require Import Equations.

Require Import ZArith.

Fixpoint fdepth (t : ftype) : nat :=
    match t with
    | (FTBasic b)    => 0
    | (FTFunc tx t') => 1 + max (fdepth tx) (fdepth t')
    | (FTPoly k t')  => 1 + fdepth t'
    | (FTList t')    => 1 + fdepth t'
    end.

Lemma fdepth_openFT_at : forall (j:index) (a:vname) (t:ftype),
    fdepth (openFT_at j a t) = fdepth t.
Proof. intros j a t; revert j; induction t; intros;
  simpl; try destruct b; try destruct (Nat.eqb j i); 
  reflexivity || f_equal; apply IHt || f_equal;
  try apply IHt1; try apply IHt2; apply H. Qed.

Lemma fdepth_unbindFT : forall (a:vname) (t:ftype),
    fdepth (unbindFT a t) = fdepth t.
Proof. intros; apply fdepth_openFT_at; assumption. Qed.

(*** we need a stack env for BTV deBruijn's and their kinds ***)

(*----------------------------------------------------------------------------
  --- | AUTOMATED INFERENCE of SYSTEM F WELL-FORMEDNESS JUDGMENTS
  --------------------------------------------------------------------------*)

Equations isWFFT (g:fenv) (t:ftype) (k:kind) : Prop 
  by wf (fdepth t) :=
isWFFT g (FTBasic b) k := 
    match b with
    | TBool    => True
    | TInt     => True
    | (BTV a)  => False
    | (FTV a)  => (tv_bound_inF a Base g) \/ 
                    (tv_bound_inF a Star g /\ k = Star)
    end;
isWFFT g (FTFunc t_x t) k := 
    k = Star /\ isWFFT g t_x Star  /\ isWFFT g t   Star;
isWFFT g (FTPoly k'  t) k := 
    let a' := fresh_varF nil g
    in  k = Star /\ isWFFT (FConsT a' k' g) (unbindFT a' t) Star;
isWFFT g (FTList t) k     := 
    k = Star /\ isWFFT g t   Star.
  Obligation 1. (* fdepth t_x "<" fdepth t *)
    pose proof Nat.le_max_l (fdepth  t_x) (fdepth  t) as Hd.
    apply Nat.lt_succ_r; apply Hd.
  Defined.
  Obligation 2. (* fdepth t' "<" fdepth t *)
    pose proof Nat.le_max_r (fdepth  t_x) (fdepth  t) as Hd.
    apply Nat.lt_succ_r; apply Hd.
  Defined.
  Obligation 3.
    rewrite fdepth_unbindFT; apply Nat.lt_succ_r; trivial.
  Defined.

Example isWFFT_one : isWFFT FEmpty (FTList (FTBasic TInt)) Star.
Proof. funelim (isWFFT FEmpty (FTList (FTBasic TInt)) Star);
  (*unfold not;*) split; intros;
  (discriminate || contradiction || constructor). Qed.

Example isWFFT_two : isWFFT FEmpty (FTPoly Base (FTBasic (BTV 0))) Star.
Proof. funelim (isWFFT FEmpty (FTPoly Base (FTBasic (BTV 0))) Star);
  (*unfold not;*) split; intros;
  (discriminate || contradiction || constructor);
  simpl; auto. Qed.  

Lemma makeWFFT : forall (n:nat) (g:fenv) (t:ftype) (k:kind),
    fdepth t <= n   -> isWFFT g t k -> WFFT g t k.
Proof. intros n; induction n.
  - (* Base *) intros;
    assert (fdepth t = 0) by auto with *.
    destruct t; simpl in H1; try discriminate.
    destruct b; rewrite isWFFT_equation_1 in H0;
    try contradiction; destruct k;
    try destruct H0; 
    try destruct H0; try discriminate;
    try (apply WFFTFV; apply H0);
    try apply WFFTKind;
    try apply WFFTFV; try apply WFFTBasic;
    simpl; trivial.
  - (* Inductive *) intros.
    destruct t eqn:T;
    (* avoid proving base case again *)
    try (assert (fdepth t <= n) as Hbase
          by (rewrite T; simpl; auto with *);
         apply IHn; subst t; trivial);
    simpl in H; apply Nat.succ_le_mono in H.
    * (* FTFunc t1 t2 *)
      rewrite isWFFT_equation_2 in H0;
      destruct H0; destruct H1; subst k.
      apply WFFTFunc with Star Star; 
      apply IHn; try apply Nat.le_trans 
        with (Init.Nat.max (fdepth f1) (fdepth f2));
      try apply Nat.le_max_l;
      try apply Nat.le_max_r; trivial.
    * (* FTPoly k0 f *)
      rewrite isWFFT_equation_3 in H0;
      destruct H0; subst k;
      apply WFFTPoly with Star (bindsF g);
      intros; apply IHn;
      
      try rewrite fdepth_unbindFT; trivial. 
    * (* FTList f *) 
      rewrite isWFFT_equation_4 in H0; destruct H0; subst k.
      apply WFFTList with Star; 
      apply IHn; trivial.
    

Theorem checkWFFT : forall (g:fenv) (t:ftype) (k:kind),
    isWFFT g t k -> WFFT g t k.
Proof. intros. apply makeWFFT with (fdepth t); trivial. Qed.