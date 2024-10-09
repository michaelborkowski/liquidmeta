Require Import SystemRF.BasicDefinitions. 
Require Import SystemRF.Names.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.SystemFWellFormedness.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.LemmasTransitive. (* importing depth *)
Require Import Bidirectional.Decidable.
Require Import Bidirectional.SynthWFFT.
Require Import Bidirectional.SynthFType.

From Equations Require Import Equations.

Require Import Arith.
Require Import ZArith.

(*** we need a stack env for BV deBruijn's and their ftypes ***)

Inductive deBruijns : Set := 
    | DVEmpty 
    | DVBind  (t : type) (d : deBruijns).

Fixpoint bv_bound_in (i : index) (t : type) (d : deBruijns) : Prop :=
    match d with 
    | DVEmpty      => False
    | DVBind t' d' => match i with
                      | 0     => t = t'
                      | (S j) => bv_bound_in j t d'
                      end
    end.      

Fixpoint lookupD (i : index) (d : deBruijns) : option type :=
    match d with 
    | DVEmpty      => None
    | DVBind t' d' => match i with
                      | 0     => Some t'
                      | (S j) => lookupD j d'
                      end
    end.

Fixpoint dlen (d : deBruijnsF) : nat :=
    match d with
    | DFEmpty       => 0
    | (DFBind t d') => dflen d' + 1
    end.    

Lemma lem_bvboundinF_upper_bound : forall (i:index) (t:ftype) (d:deBruijnsF),
    bv_bound_inF i t d -> i < dflen d.
Proof. induction i; intros; destruct d; try contradiction.
  - (* Base *) simpl; auto with *.
  - (* Ind *) simpl. rewrite <- plus_n_Sm; rewrite <- plus_n_O; auto with *.
  Qed.

Fixpoint concatDF (d d'0 : deBruijnsF) : deBruijnsF :=
    match d'0 with
    | DFEmpty       => d
    | (DFBind t d') => DFBind t (concatDF d d')
    end.    

Lemma lem_empty_concatDF : forall (d : deBruijnsF),
    concatDF DFEmpty d = d.
Proof. induction d; simpl; try rewrite IHd; reflexivity. Qed.    

Lemma lem_bvboundinF_append : forall (d : deBruijnsF) (i:index) (t t':ftype),
    bv_bound_inF i t (concatDF (DFBind t' DFEmpty) d) 
          ->   i < dflen d /\ bv_bound_inF i t d
            \/ i = dflen d /\ t = t'.
Proof. induction d; intros.
  - (* Base *) destruct i; simpl in H; right; intuition;
    destruct i; try contradiction.
  - (* Ind *) destruct i; simpl in H. 
      * (* 0 *) subst t0; simpl; left; auto with *.
      * (* S i *) apply IHd in H; destruct H; [left|right].
          + (* in d *) destruct H; split; simpl; auto with *.
          + (* at end *) simpl; rewrite <- plus_n_Sm; rewrite <- plus_n_O;
            destruct H; split; auto.
  Qed.


Fixpoint lookupF (x : vname) (g : fenv) : option ftype :=
    match g with 
    | FEmpty          => None
    | FCons x' t' g'  => if (x =? x') then Some t' else lookupF x g'
    | FConsT a' k' g' => lookupF x g'
    end.


(*----------------------------------------------------------------------------
  --- | AUTOMATED INFERENCE of SYSTEM F WELL-FORMEDNESS JUDGMENTS
  --------------------------------------------------------------------------*)

Fixpoint isWFtype' (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (t:type) (k:kind) : Prop :=
    match t with 
    | (TRefn b ps)    => checkP' g (DFBind (FTBasic b) (erase_db dv)) dtv ps /\ (
                          match b with
                          | TBool    => True
                          | TInt     => True
                          | (BTV i)  => btv_bound_in i Base d  \/
                                          (btv_bound_in i Star d /\ k = Star)
                          | (FTV a)  => (tv_bound_inF a Base g) \/ 
                                          (tv_bound_inF a Star g /\ k = Star)
                          end)
    | (TFunc t_x t)   => k = Star /\ isWFFT' g d t_x Star  /\ isWFFT' g d t Star
    | (TExists t_x t) => k = Star /\ isWFFT' g d t_x Star  /\ isWFFT' g d t Star
    | (TPoly k'  t)   => k = Star /\ isWFFT' g (DTBind k' d) t Star
    | (TList  t ps)   => k = Star /\ isWFFT' g d t   Star
    end.

Definition isWFFT (g:fenv) (t:ftype) (k:kind) : Prop := isWFFT' g DTEmpty t k.

Lemma lem_isWFFT_openFT_at : 
  forall (g:fenv) (t:ftype) (k:kind) (k':kind) (d:deBruijnTVs) (a:vname),
           isWFFT' g (concatDT (DTBind k' DTEmpty) d) t k
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

(* But to make this an effective algorithm,
    isWFFT' needs to be *decidable* *)

Lemma btv_bound_in_dec : forall (i:index) (k:kind) (d:deBruijnTVs),
    { btv_bound_in i k d } + { ~ btv_bound_in i k d }.
Proof. intros i k d; revert i k; induction d; intros; simpl. 
  - right; destruct i; simpl; auto.
  - destruct i; simpl;
    try apply kind_eq_dec; apply IHd.
Qed.

Definition btv_bound_inb (i:index) (k:kind) (d:deBruijnTVs) : bool :=
    match (btv_bound_in_dec i k d) with
    | left A    => true
    | right B   => false
    end.

Lemma isWFFT'_dec : forall (g:fenv) (d:deBruijnTVs) (t:ftype) (k:kind),
    { isWFFT' g d t k } + { ~ isWFFT' g d t k }.
Proof. intros g d t; revert g d; induction t.
  - intros; destruct b; simpl; auto.
    * destruct (btv_bound_in_dec i Base d);
      destruct (btv_bound_in_dec i Star d);
      destruct (kind_eq_dec k Star); intuition.
    * destruct (tv_bound_inF_dec a Base g);
      destruct (tv_bound_inF_dec a Star g);
      destruct (kind_eq_dec k Star); intuition.
  - intros; simpl; destruct (IHt1 g d Star); 
    destruct (IHt2 g d Star);
    destruct (kind_eq_dec k Star); intuition.
  - intros; simpl; destruct (IHt g (DTBind k d) Star);
    destruct (kind_eq_dec k0 Star); intuition.
  - intros; simpl; destruct (IHt g d Star);
    destruct (kind_eq_dec k Star); intuition.
Qed.

Lemma isWFFT_dec : forall (g:fenv) (t:ftype) (k:kind),
    { isWFFT g t k } + { ~ isWFFT g t k }.
Proof. intros; unfold isWFFT; apply isWFFT'_dec. Qed.

Definition isWFFTb (g:fenv) (t:ftype) (k:kind) : bool :=
    match (isWFFT_dec g t k) with
    | left A    => true
    | right B   => false
    end.
