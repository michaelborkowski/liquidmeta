Require Import SystemRF.BasicDefinitions. 
Require Import SystemRF.Names.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.SystemFWellFormedness.

From Equations Require Import Equations.

Require Import Arith.
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

Inductive deBruijnTVs : Set := 
    | DTEmpty 
    | DTBind  (k : kind) (d : deBruijnTVs).

Fixpoint btv_bound_in (i : index) (k : kind) (d : deBruijnTVs) : Prop :=
    match i, d with 
    | _,     DTEmpty         => False
    | 0,     (DTBind k' d')  => k = k'
    | (S j), (DTBind k' d')  => btv_bound_in j k d'
    end.

Fixpoint dtlen (d : deBruijnTVs) : nat :=
    match d with
    | DTEmpty       => 0
    | (DTBind k d') => dtlen d' + 1
    end.    

Lemma lem_btvboundin_upper_bound : forall (i:index) (k:kind) (d:deBruijnTVs),
    btv_bound_in i k d -> i < dtlen d.
Proof. induction i; intros; destruct d; try contradiction.
  - (* Base *) simpl; auto with *.
  - (* Ind *) simpl. rewrite <- plus_n_Sm; rewrite <- plus_n_O; auto with *.
  Qed.

Fixpoint concatD (d d'0 : deBruijnTVs) : deBruijnTVs :=
    match d'0 with
    | DTEmpty       => d
    | (DTBind k d') => DTBind k (concatD d d')
    end.    

Lemma lem_empty_concatD : forall (d : deBruijnTVs),
    concatD DTEmpty d = d.
Proof. induction d; simpl; try rewrite IHd; reflexivity. Qed.    

Lemma lem_btvboundin_append : forall (d : deBruijnTVs) (i:index) (k k':kind),
    btv_bound_in i k (concatD (DTBind k' DTEmpty) d) 
          ->   i < dtlen d /\ btv_bound_in i k d
            \/ i = dtlen d /\ k = k'.
Proof. induction d; intros.
  - (* Base *) destruct i; simpl in H; right; intuition;
    destruct i; try contradiction.
  - (* Ind *) destruct i; simpl in H. 
      * (* 0 *) subst k0; simpl; left; auto with *.
      * (* S i *) apply IHd in H; destruct H; [left|right].
          + (* in d *) destruct H; split; simpl; auto with *.
          + (* at end *) simpl; rewrite <- plus_n_Sm; rewrite <- plus_n_O;
            destruct H; split; auto.
  Qed.

(*----------------------------------------------------------------------------
  --- | AUTOMATED INFERENCE of SYSTEM F WELL-FORMEDNESS JUDGMENTS
  --------------------------------------------------------------------------*)

Fixpoint isWFFT' (g:fenv) (d:deBruijnTVs) (t:ftype) (k:kind) : Prop :=
    match t with 
    | (FTBasic b)    => match b with
                        | TBool    => True
                        | TInt     => True
                        | (BTV i)  => btv_bound_in i Base d  \/
                                        (btv_bound_in i Star d /\ k = Star)
                        | (FTV a)  => (tv_bound_inF a Base g) \/ 
                                        (tv_bound_inF a Star g /\ k = Star)
                        end
    | (FTFunc t_x t) => k = Star /\ isWFFT' g d t_x Star  /\ isWFFT' g d t Star
    | (FTPoly k'  t) => k = Star /\ isWFFT' g (DTBind k' d) t Star
    | (FTList     t) => k = Star /\ isWFFT' g d t   Star
    end.

Definition isWFFT (g:fenv) (t:ftype) (k:kind) : Prop := isWFFT' g DTEmpty t k.

Lemma lem_isWFFT_openFT_at : 
  forall (g:fenv) (t:ftype) (k:kind) (k':kind) (d:deBruijnTVs) (a:vname),
           isWFFT' g (concatD (DTBind k' DTEmpty) d) t k
        -> ~ in_envF a g 
        -> isWFFT' (FConsT a k' g) d (openFT_at (dtlen d) a t) k.
Proof. intros g; induction t.
  - (* FTBasic *) intros. destruct b; simpl in H; simpl; try apply I.
    * (* BTV *) 
      destruct H; simpl in H; try destruct H;
      apply lem_btvboundin_append in H; destruct H; destruct H;
      try assert (dtlen d =? i = true)
         by (apply Nat.eqb_eq; symmetry; apply H);
      try assert (dtlen d =? i = false)
         by (apply Nat.eqb_neq; auto with *); 
      rewrite H3 || rewrite H2; simpl; intuition.
    * (* FTV *) destruct H; [left|right]; try destruct H;
      try split; try right; trivial.
  - (* FTFunc *) intros; simpl; simpl in H; destruct H; destruct H1;
    split; try split; try apply IHt1; try apply IHt2; trivial.
  - (* FTPoly *) intros; simpl; simpl in H; destruct H; split;
    try apply IHt; trivial.
  - (* FTList *) intros; simpl; simpl in H; destruct H; split;
    try apply IHt; trivial.
  Qed.

Lemma lem_isWFFT_unbindFT : 
  forall (g:fenv) (t:ftype) (k:kind) (k':kind) (a:vname),
           isWFFT' g (DTBind k' DTEmpty) t k-> ~ in_envF a g 
        -> isWFFT (FConsT a k' g) (unbindFT a t) k.
Proof. intros; apply lem_isWFFT_openFT_at; simpl; trivial. Qed.

Example isWFFT_one : isWFFT FEmpty (FTList (FTBasic TInt)) Star.
Proof. unfold isWFFT; simpl; auto. Qed.

Example isWFFT_two : isWFFT FEmpty (FTPoly Base (FTBasic (BTV 0))) Star.
Proof. unfold isWFFT; simpl; auto. Qed.
  

Lemma makeWFFT' : forall (n:nat) (g:fenv) (t:ftype) (k:kind),
    fdepth t <= n   -> isWFFT g t k -> WFFT g t k.
Proof. intros n; induction n.
  - (* Base *) intros;
    assert (fdepth t = 0) by auto with *.
    destruct t; simpl in H1; try discriminate.
    destruct b; unfold isWFFT in H0; simpl in H0;
    destruct k; try destruct H0;
    try destruct H0; try discriminate;
    try (destruct i; contradiction);
    try (apply WFFTFV; apply H0);
    try apply WFFTKind; try apply WFFTFV; 
    try apply WFFTBasic; simpl; trivial.
  - (* Inductive *) intros.
    destruct t eqn:T;
    (* avoid proving base case again *)
    try (assert (fdepth t <= n) as Hbase
          by (rewrite T; simpl; auto with *);
         apply IHn; subst t; trivial);
    simpl in H; apply Nat.succ_le_mono in H.
    * (* FTFunc t1 t2 *)
      unfold isWFFT in H0; 
      destruct H0; destruct H1; subst k.
      apply WFFTFunc with Star Star; 
      apply IHn; try apply Nat.le_trans 
        with (Init.Nat.max (fdepth f1) (fdepth f2));
      try apply Nat.le_max_l;
      try apply Nat.le_max_r; trivial.
    * (* FTPoly k0 f *)
      unfold isWFFT in H0; destruct H0; subst k.
      apply WFFTPoly with Star (bindsF g);
      intros; apply IHn; try rewrite fdepth_unbindFT;
      try apply lem_isWFFT_unbindFT; trivial.
    * (* FTList f *) 
      unfold isWFFT in H0; destruct H0; subst k.
      apply WFFTList with Star; apply IHn; trivial.
  Qed.

Theorem makeWFFT : forall (g:fenv) (t:ftype) (k:kind),
    isWFFT g t k -> WFFT g t k.
Proof. intros. apply makeWFFT' with (fdepth t); trivial. Qed.