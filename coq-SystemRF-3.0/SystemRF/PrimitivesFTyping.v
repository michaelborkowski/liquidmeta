Require Import ZArith.

Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFWellFormedness.
Require Import SystemRF.SystemFTyping.           

(* -- | Well Formedness of System F PRIMITIVES *)

Lemma lem_wfft_erase_ty : forall (g:fenv) (c:prim),  WFFT g (erase_ty c) Star.
Proof. intros. destruct c; try (apply WFFTPoly with Star (bindsF g))
                ; intros; unfold unbindFT; simpl
                ; ( match goal with 
                    | [ |- WFFT (FConsT _ Base _) _ _] => apply WFFTFunc with Base Star
                    | [ |- WFFT (FConsT _ Star _) _ _] => apply WFFTFunc with Star Star
                    | [ |- _ ]                         => apply WFFTFunc with Base Star
                    end ) 
                ; try apply WFFTFunc with Base Base
                ; try apply WFFTList with Star
                ; try apply WFFTFV
                ; try apply WFFTKind
                ; try apply WFFTBasic
                ; simpl; intuition. Qed.

(*-----------------------------------------------------------------------------
-- | (System F) TYPES of DELTA (of Applications of primitives)
-----------------------------------------------------------------------------*)

Definition isBool (e:expr) : Prop :=
    match e with
    | (Bc _ ) => True
    | _       => False
    end.

Lemma lem_bool_values : forall (v:expr), 
    isValue v -> HasFtype FEmpty v (FTBasic TBool) ->  isBool v.
Proof. intros v val p_v_bl. inversion p_v_bl; subst v;
    try inversion val; try contradiction.
    - (* v = Bc *) simpl; trivial.
    - (* v = Prim *) destruct c; simpl in H2; discriminate.
    - (* v = Length [t] *) subst e; inversion H0; subst t';
      unfold ftsubBV in H; simpl in H; discriminate.
    Qed. 

Definition isInt (e:expr) : Prop :=
    match e with
    | (Ic _ ) => True
    | _       => False
    end.

Lemma lem_int_values : forall (v:expr),
    isValue v -> HasFtype FEmpty v (FTBasic TInt) -> isInt v.
Proof. intros v val p_v_Z. inversion p_v_Z; subst v; 
    try inversion val; try contradiction.
    - (* v = Ic *) simpl; apply I. 
    - (* v = Prim *) destruct c; simpl in H2; discriminate.
    - (* v = Length [t] *) subst e; inversion H0; subst t';
      unfold ftsubBV in H; simpl in H; discriminate.
    Qed. 

Definition isLambdaOrPrim (e:expr) : Prop :=
    match e with
    | (Prim _)               => True
    | (Lambda _)             => True
    | (AppT (Prim Length) _) => True (* sad but true! *)
    | _                      => False
    end.

Definition isLambdaTOrPrim (e:expr) : Prop :=
    match e with
    | (Prim _)               => True
    | (LambdaT _ _)          => True
    | _                      => False
    end.

Definition isPoly (c:prim) : Prop :=
    match c with
    | Eql     => True
    | Leql    => True
    | _       => False
    end.

Definition isMeasure (c:prim) : Prop :=
    match c with
    | Length  => True
    | _       => False
    end.

Lemma lemma_function_values : forall (v:expr) (t:ftype) (t':ftype),
    isValue v -> HasFtype FEmpty v (FTFunc t t') -> isLambdaOrPrim v.
Proof.  intros v t t' val p_v_tt'; inversion p_v_tt'; subst v;
  inversion val; simpl; try contradiction; auto. Qed.    

Lemma lemma_tfunction_values : forall (v:expr) (k:kind) (t:ftype),
    isValue v -> HasFtype FEmpty v (FTPoly k t) -> isLambdaTOrPrim v.
Proof. intros v k t val p_v_kt; inversion p_v_kt; subst v;
  inversion val; try subst e; try inversion H0; try subst t';
  try unfold ftsubBV in H; simpl in H; try discriminate;
  simpl; try contradiction; auto. Qed.

(* New for 2024: Lemmas for List values *)

Fixpoint isList (e:expr) : Prop :=
    match e with
    | Nil         => True
    | (Cons _ es) => isList es
    | _           => False
    end.

Lemma lemma_list_values : forall (v:expr) (t:ftype),
    isValue v -> HasFtype FEmpty v (FTList t) -> isList v.
Proof. induction v; intros; inversion H; inversion H0; 
  try simpl in H4; try contradiction;
  try destruct p; try simpl in H5; try discriminate;
  try subst v; try inversion H6; try subst t';
  try unfold ftsubBV in H5; try simpl in H5; try discriminate.
  - (* v = Nil *) simpl; apply I.
  - (* v = Cons v1 v2 *) simpl; apply IHv2 with t; assumption.
  Qed.

Lemma lem_prim_compat_in_ftapp : forall (p:prim) (v:expr) (t:ftype),
    isValue v -> HasFtype FEmpty (App (Prim p) v) t -> isCompat' p v.
Proof. intros p v t val p_pv_t. 
  destruct p; inversion p_pv_t; inversion H2; subst b;
  (apply lem_bool_values || apply lem_int_values); assumption. Qed.

Lemma lem_delta_ftyp : forall (c:prim) (v:expr) (t_x:ftype) (t':ftype),
    isValue v -> HasFtype FEmpty (Prim c) (FTFunc t_x t') -> HasFtype FEmpty v t_x
              -> exists e, Some e = delta' c v /\ HasFtype FEmpty e t'.
Proof. intros c v t_x t' val p_c_txt' p_v_tx. 
  destruct c; inversion p_c_txt'; subst t_x;
  try (apply (lem_bool_values v val) in p_v_tx as Hv);
  try (apply (lem_int_values v val) in p_v_tx as Hv);
  destruct v; try contradiction;
  try (destruct b); simpl;
  ( match goal with
    | [ |- exists _, Some _ = Some ?term /\ _ ] => exists term
    end )
         ; split    
         ; try apply FTAbs with Base empty
         ; intros; unfold unbind; simpl
         ; try apply FTApp with (FTBasic TBool)
         ; try apply WFFTBasic
         ; try apply FTVar
         ; try apply FTPrm
         ; try apply FTBC
         ; try apply FTIC
         ; simpl; auto.
  Qed.

Lemma lem_base_types : forall (t:ftype),
    WFFT FEmpty t Base -> isClosedBaseF t.
Proof. intros t p_t_b; inversion p_t_b; subst t;
  try (destruct b); simpl; simpl in H;
  (trivial || contradiction). Qed.

Lemma lem_prim_compatT_in_ftappt : forall (c:prim) (rt:type) (t:ftype),
    ~ isMeasure c -> HasFtype FEmpty (AppT (Prim c) rt) t  
        ->  isCompatT' c rt.
Proof. intros c rt t Hnmeas p_crt_t. destruct c; 
  simpl in Hnmeas; try contradiction; inversion p_crt_t; inversion H1;
  subst k; apply lem_base_types in H9; 
  destruct (erase rt) eqn:Hrt; simpl in H9; try contradiction; 
  simpl; rewrite Hrt; trivial. Qed.
  
Lemma lem_deltaT_ftyp : forall (c:prim) (k:kind) (s:ftype) (t:type),
  ~ isMeasure c
    -> HasFtype FEmpty (Prim c) (FTPoly k s) -> WFFT FEmpty (erase t) k
        -> exists e, Some e = deltaT' c t /\ HasFtype FEmpty e (ftsubBV (erase t) s).
Proof. intros c k s t Hnmeas p_c_aks p_emp_t; 
  destruct c; simpl in Hnmeas; try contradiction; 
  inversion p_c_aks; subst k;
  apply lem_base_types in p_emp_t as Ht;
  destruct (erase t) eqn:E; try contradiction;
  destruct b; try contradiction;
  unfold deltaT'; rewrite E;
  ( match goal with
    | [ |- exists _, Some _ = Some ?term /\ _ ] => exists term
    end )
         ; split
         ; try (apply FTPrm)
         ; auto.
  Qed. 

Lemma lem_prim_compatM_in_ftappappt : 
  forall (c:prim) (rt:type) (v:expr) (t:ftype),
    isMeasure c -> isValue v -> HasFtype FEmpty (App (AppT (Prim c) rt) v) t  
        ->  isCompatM' c v.
Proof. intros c rt v t Hmeas Hval. induction Hval; intros;
  destruct c; simpl in Hmeas; try contradiction;
  inversion H; inversion H3; inversion H9; subst t';
  unfold ftsubBV in H8; simpl in H8; inversion H8; subst b0 || subst b;
  apply lemma_list_values in H5 as H5'; 
  try constructor; try apply Hval1; try apply Hval2;
  simpl in H5'; try contradiction. simpl.
  apply IHHval2. apply FTApp with (FTList (erase rt));
  inversion H5; apply H3 || apply H26. Qed.

Lemma lem_deltaM_ftyp : forall (c:prim) (k:kind) (s:ftype) (v:expr) (t:ftype),
  isMeasure c -> isValue v -> 
    HasFtype FEmpty (Prim c) (FTPoly k s) -> HasFtype FEmpty v (FTList t) 
        -> exists e, Some e = deltaM' c v /\ HasFtype FEmpty e (FTBasic TInt).
Proof. intros c k s v t Hmeas Hval. induction Hval; intros;
  destruct c; simpl in Hmeas; try contradiction;
  inversion H0;
  (* v = Prim? *) try destruct c0; try simpl in H4; try discriminate;
  (* v = len [t]? *) try inversion H4; try subst t';
    unfold ftsubBV in H3; simpl in H3; try discriminate;
  (* v = FV x? *) try contradiction.
  - (* v = Nil *) exists (Ic 0); intuition; apply FTIC.
  - (* v = Cons v1 v2*) apply IHHval2 in H; try apply H6.
    destruct H as [e_n [Hen p_en_int]].
    exists (App (Prim Succ) e_n). simpl; rewrite <- Hen; intuition.
    apply FTApp with (FTBasic TInt); apply FTPrm || apply p_en_int.
  Qed.
      