Require Import SystemRF.BasicDefinitions. 
Require Import SystemRF.Names.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.SystemFWellFormedness.

From Equations Require Import Equations.

Require Import Arith.
Require Import ZArith.
Require Import Lists.List.
Require Import Lists.ListSet.
Require Import Logic.Decidable.

Lemma basic_eq_dec : forall (b b' : basic),
    { b = b' } + { b <> b' }.
Proof. intros; destruct b; destruct b';
  try (left; reflexivity);
  try (right; discriminate);
  try destruct (eq_dec i i0); 
  try destruct (eq_dec a a0);
  try (left; subst i0 || subst a0; reflexivity);
  right; unfold not; intros; injection H as H; contradiction.
Qed.

Definition basic_eq (b b' : basic) : bool :=
  match (basic_eq_dec b b') with
  | left _  => true
  | right _ => false
  end.

Lemma kind_eq_dec : forall (k k' : kind),
    { k = k' } + { k <> k' }.
Proof. intros; destruct k; destruct k';
  try (left; reflexivity);
  right; discriminate.
Qed.

Definition kind_eq (k k' : kind) : bool :=
  match (kind_eq_dec k k') with
  | left _  => true
  | right _ => false
  end.

Lemma prim_eq_dec : forall (p p' : prim),
    { p = p' } + { p <> p' }.
Proof. intros; destruct p; destruct p';
  try destruct (Z.eq_dec n n0) as [Heq|Hneq];
  try rewrite Heq;
  try (left; reflexivity);
  right; try discriminate; 
  unfold not; intros Hyp;
  injection Hyp as Hyp; contradiction.
Qed.


Lemma syntax_mut_eq_dec : (forall (e e': expr),
    { e = e' } + { e <> e' }) * ((
  forall (t t': type),
    { t = t' } + { t <> t' } ) * (
  forall (ps qs: preds),
    { ps = qs } + { ps <> qs } ))%type.
Proof. apply (syntax_mutind
  (fun e : expr => forall (e' : expr), 
      { e = e' } + { e <> e' } )
  (fun t : type => forall (t' : type),
      { t = t' } + { t <> t' } )
  (fun ps : preds => forall (qs : preds), 
      { ps = qs } + { ps <> qs } )); 
  simpl; intros; (* case split on the RHS *)
  try destruct e'; try destruct t';
  try destruct qs; try (right; discriminate);
  (* are the subterms equal? *)
  try (destruct b; destruct b0);
  try destruct (Z.eq_dec n n0) as [Heq|Hneq];
  try destruct (prim_eq_dec p p0) as [Heq|Hneq];
  try destruct (eq_dec i i0) as [Heq|Hneq];
  try destruct (eq_dec x x0) as [Heq|Hneq];
  try destruct (eq_dec a a0) as [Heq|Hneq];
  try destruct (kind_eq_dec k k0) as [Heq|Hneq];
  try ( destruct (H t0) as [H3|H3]; (* special case *)
        destruct (H0 e'1) as [H4|H4]; (* for Cons *)
        destruct (H1 e'2) as [H5|H5]  );
  try destruct (H e') as [H3|H3];
  try destruct (H e'1) as [H3|H3];
  try destruct (H t0) as [H3|H3];
  try destruct (H t') as [H3|H3];
  try destruct (H t'1) as [H3|H3];
  try destruct (H p0) as [H3|H3];
  try destruct (H ps0) as [H3|H3];
  try destruct (H0 e'2) as [H4|H4];
  try destruct (H0 t0) as [H4|H4];
  try destruct (H0 t'2) as [H4|H4];
  try destruct (H0 ps0) as [H4|H4];
  try destruct (H0 qs) as [H4|H4];
  try destruct (H1 e'3) as [H5|H5];
  (* either they all are ... *)
  try rewrite Heq; try rewrite H3; try rewrite H4; try rewrite H5;
  try (left; reflexivity);
  (* ... or at least one is not *)
  try (right; discriminate);
  try ( right; unfold not; intros Hyp;
        injection Hyp as Hyp; contradiction).
Qed.

Lemma expr_eq_dec : forall (e e': expr),
    { e = e' } + { e <> e' }.
Proof. apply syntax_mut_eq_dec. Qed.   
 
Lemma type_eq_dec : forall (t t' : type),
      { t = t' } + { t <> t' }.
Proof. apply syntax_mut_eq_dec. Qed.

Lemma preds_eq_dec : forall (ps qs : preds), 
      { ps = qs } + { ps <> qs }.
Proof. apply syntax_mut_eq_dec. Qed.

Lemma ftype_eq_dec : forall (t t': ftype),
    { t = t' } + { t <> t' }.
Proof. induction t; simpl; intros;
  try destruct t'; try (right; discriminate);
  (* are the subterms equal? *)
  try (destruct b; destruct b0);
  try destruct (Z.eq_dec n n0) as [Heq|Hneq];
  try destruct (prim_eq_dec p p0) as [Heq|Hneq];
  try destruct (eq_dec i i0) as [Heq|Hneq];
  try destruct (eq_dec a a0) as [Heq|Hneq];
  try destruct (kind_eq_dec k k0) as [Heq|Hneq];
  try destruct (IHt t') as [H|H];
  try destruct (IHt1 t'1) as [H|H];
  try destruct (IHt2 t'2) as [H0|H0];
  (* either they all are ... *)
  try rewrite Heq; try rewrite H; try rewrite H0;
  try (left; reflexivity);
  (* ... or at least one is not *)
  try (right; discriminate);
  try ( right; unfold not; intros Hyp;
        injection Hyp as Hyp; contradiction).
Qed.

Definition expr_eq (e e' : expr) : bool :=
  match (expr_eq_dec e e') with
  | left _  => true
  | right _ => false
  end.

Definition type_eq (t t' : type) : bool :=
  match (type_eq_dec t t') with
  | left _  => true
  | right _ => false
  end.

Definition preds_eq (ps qs : preds) : bool :=
  match (preds_eq_dec ps qs) with
  | left _  => true
  | right _ => false
  end.

Definition ftype_eq (t t' : ftype) : bool :=
  match (ftype_eq_dec t t') with
  | left _  => true
  | right _ => false
  end.

Lemma noExists_dec : forall (t:type),
    { noExists t } + { ~ noExists t }.
Proof. induction t; simpl; intros;
  try destruct IHt1; try destruct IHt2; try destruct IHt;
  try (left; intuition; reflexivity);
  right; intuition.
Qed.

Definition noExistsb (t:type) : bool :=
    match noExists_dec t with
    | left A    => true
    | right b   => false
    end.

Lemma isMono_dec : forall (t:type),
    { isMono t } + { ~ isMono t }.
Proof. induction t; simpl; intros;
  try destruct IHt1; try destruct IHt2; try destruct IHt;
  try (left; intuition; reflexivity);
  right; intuition.
Qed.

Definition isMonob (t:type) : bool :=
    match isMono_dec t with
    | left A    => true
    | right b   => false
    end.

Lemma bound_inF_dec : forall (x:vname) (t:ftype) (g:fenv),
    { bound_inF x t g } + { ~ bound_inF x t g }.
Proof. intros x t; induction g; simpl. 
  - right; auto.
  - destruct IHg; try (left; right; apply b).
    destruct (eq_dec x x0);
    destruct (ftype_eq_dec t t0);
    try (left; left; split; assumption);
    right; intuition.
  - apply IHg.
Qed.

Definition bound_inFb (x:vname) (t:ftype) (g:fenv) : bool :=
    match (bound_inF_dec x t g) with
    | left A    => true
    | right B   => false
    end.

Lemma tv_bound_inF_dec : forall (a:vname) (k:kind) (g:fenv),
    { tv_bound_inF a k g } + { ~ tv_bound_inF a k g }.
Proof. intros a k; induction g; simpl. 
  - right; auto.
  - apply IHg.
  - destruct IHg; try (left; right; apply t).
    destruct (eq_dec a a0);
    destruct (kind_eq_dec k k0);
    try (left; left; split; assumption);
    right; intuition.
Qed.

Definition tv_bound_inFb (a:vname) (k:kind) (g:fenv) : bool :=
    match (tv_bound_inF_dec a k g) with
    | left A    => true
    | right B   => false
    end.

Lemma and_dec : forall (A B:Prop),
    {A} + {~A} -> {B} + {~B} -> {A /\ B} + {~ (A /\ B)}.
Proof. intros; destruct H; destruct H0;
  try (left; split; assumption);
  right; unfold not; intros; destruct H; contradiction. Qed.

Lemma isLC_at_dec' : (forall (e: expr) (j_x j_a:index),
    { isLC_at j_x j_a e } + { ~ isLC_at j_x j_a e }) * ((
  forall (t: type) (j_x j_a:index) ,
    { isLCT_at j_x j_a t } + { ~ isLCT_at j_x j_a t } ) * (
  forall (ps: preds) (j_x j_a:index) ,
    { isLCP_at j_x j_a ps } + { ~ isLCP_at j_x j_a ps } ))%type.
Proof. apply (syntax_mutind
  (fun e : expr => forall (j_x j_a:index) , 
      { isLC_at j_x j_a e } + { ~ isLC_at j_x j_a e } )
  (fun t : type => forall (j_x j_a:index) ,
      { isLCT_at j_x j_a t } + { ~ isLCT_at j_x j_a t } )
  (fun ps : preds => forall (j_x j_a:index) , 
      { isLCP_at j_x j_a ps } + { ~ isLCP_at j_x j_a ps } ));
  simpl; intros;
  try destruct b;
  try apply and_dec; try apply and_dec;
  try apply lt_dec;
  try apply H; try apply H0; try apply H1;
  try (left; reflexivity).
Qed.

Lemma isLCT_at_dec : forall (j_x j_a:index) (t: type) ,
    { isLCT_at j_x j_a t } + { ~ isLCT_at j_x j_a t }.
Proof. intros; apply isLC_at_dec'; trivial. Qed.

Definition isLCT_atb (j_x j_a:index) (t: type) : bool :=
    match isLCT_at_dec j_x j_a t with
    | left _  => true
    | right _ => false
    end.

Lemma Subset_dec : forall (xs ys : names),
    { Subset xs ys } + { ~ Subset xs ys }.
Proof. induction xs; intros.
  - left. apply subset_empty_l.
  - destruct (IHxs ys) as [IH|IH];
    destruct (set_In_dec eq_dec a ys);
    try ( left; unfold Subset; intros; destruct H;
          try subst x; apply s || (apply IH; apply H) );
    right; unfold not; intros;
    apply n || apply IH;
    try (apply H; unfold Elem; apply in_eq).
    apply subset_trans with (a :: xs); try apply H;
    unfold Subset; intros; unfold Elem; unfold set_In;
    apply in_cons; apply H0.
Qed.

Definition Subsetb (xs ys : names) : bool := 
    match Subset_dec xs ys with
    | left _  => true
    | right _ => false
    end.  
  