Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFWellFormedness.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.PrimitivesFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.BasicPropsWellFormedness.
Require Import SystemRF.Typing.
Require Import Denotations.ClosingSubstitutions.
Require Import Denotations.Denotations.
Require Import Denotations.PrimitivesSemantics.

Require Import Arith.

(*------------------------------------------------------------------------
  -- | Inverting Denotations of the Basic Types
  ------------------------------------------------------------------------*)
  
Lemma lem_den_bools : forall (t:type) (v:expr),
    isValue v -> erase t = FTBasic TBool -> Denotes t v -> isBool v.
Proof. intros; apply lem_den_hasftype in H1;
  apply lem_bool_values; try rewrite <- H0; assumption. Qed.

Lemma lem_den_ints : forall (t:type) (v:expr),
    isValue v -> erase t = FTBasic TInt -> Denotes t v -> isInt v.
Proof. intros; apply lem_den_hasftype in H1;
  apply lem_int_values; try rewrite <- H0; assumption. Qed.

  (* -- Lemmata. Denotations of Primitive/Constant Types *)

Lemma lem_den_tybc : forall (b:bool), Denotes (tybc b) (Bc b).
Proof. intro b; unfold tybc; rewrite Denotes_equation_1;
  repeat split; unfold psubBV; simpl; trivial; try apply FTBC. 
  apply PECons; try apply PEEmp.
  assert (true = Bool.eqb b b) by (destruct b; reflexivity);
  rewrite H; apply lemma_eql_bool_semantics; apply Refl. Qed.

Lemma lem_den_tyic : forall (n:nat), Denotes (tyic n) (Ic n).
Proof. intro n; unfold tyic; rewrite Denotes_equation_1;
  repeat split; unfold psubBV; simpl; trivial; try apply FTIC. 
  apply PECons; try apply PEEmp.
  assert ((n =? n) = true) by (apply Nat.eqb_eq; reflexivity).
  rewrite <- H; apply lemma_eql_int_semantics; apply Refl. Qed. 

Lemma lem_den_and : Denotes (ty And) (Prim And).
Proof. unfold ty; rewrite Denotes_equation_2;
  repeat split; unfold tsubBV; simpl; try apply FTPrm; intros.
  assert (isBool v_x)
    by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial).
  destruct v_x eqn:E; simpl in H1; try contradiction.
  destruct b eqn:B.
  - (* Bc true *) exists (Lambda (BV 0)); split; try split;
    try apply lem_step_evals; try apply lem_step_and_tt.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTVar; unfold bound_inF; auto;
    assert (isBool v_x0)
      by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bc b0); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply EAppAbs;
    try apply FTBC; try apply PECons; try apply PEEmp; 
    try apply lemma_evals_trans with (Bc (Bool.eqb (andb true b0) b0)); 
    try apply lemma_semantics_refn_and; destruct b0; simpl; 
    try apply Refl; auto.
  - (* Bc false *) exists (Lambda (Bc false)); split; try split;
    try apply lem_step_evals; try apply lem_step_and_ff.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTBC; trivial. 
    assert (isBool v_x0)
      by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bc false); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply EAppAbs; try apply H2;
    try apply FTBC; apply PECons; try apply PEEmp.
    apply lemma_evals_trans with (Bc (Bool.eqb (andb false b0) false)); 
    try apply lemma_semantics_refn_and; destruct b0; simpl; apply Refl.
  Qed.

Lemma lem_den_or : Denotes (ty Or) (Prim Or).
Proof. unfold ty; rewrite Denotes_equation_2.
  repeat split; unfold tsubBV; simpl; try apply FTPrm; intros.
  assert (isBool v_x)
    by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial).
  destruct v_x eqn:E; simpl in H1; try contradiction.
  destruct b eqn:B.
  - (* Bc true *) exists (Lambda (Bc true)); split; try split;
    try apply lem_step_evals; try apply lem_step_or_tt.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTBC; trivial. 
    assert (isBool v_x0)
      by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bc true); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply EAppAbs; try apply H2;
    try apply FTBC; apply PECons; try apply PEEmp.
    apply lemma_evals_trans with (Bc (Bool.eqb (andb false b0) false)); 
    try apply lemma_semantics_refn_or; destruct b0; simpl; apply Refl.  
  - (* Bc false *) exists (Lambda (BV 0)); split; try split;
    try apply lem_step_evals; try apply lem_step_or_ff.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTVar; unfold bound_inF; auto;
    assert (isBool v_x0)
      by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bc b0); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply EAppAbs;
    try apply FTBC; try apply PECons; try apply PEEmp; 
    try apply lemma_evals_trans with (Bc (Bool.eqb (andb true b0) b0)); 
    try apply lemma_semantics_refn_or; destruct b0; simpl; 
    try apply Refl; auto.
  Qed.

Lemma lem_den_not : Denotes (ty Not) (Prim Not).
Proof. unfold ty; rewrite Denotes_equation_2;
  repeat split; unfold tsubBV; simpl; try apply FTPrm; intros.
  assert (isBool v_x)
    by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial).
  destruct v_x eqn:E; simpl in H1; try contradiction.
  exists (Bc (negb b)); repeat split; unfold psubBV; simpl;
  try apply lem_step_evals; try apply lem_step_not;
  try apply FTBC; apply PECons; try apply PEEmp;
  apply lemma_evals_trans with (Bc (Bool.eqb (negb b) (negb b)));
  try apply lemma_semantics_refn_not; destruct b; simpl; apply Refl.
  Qed.  

Lemma lem_den_eqv : Denotes (ty Eqv) (Prim Eqv).
Proof. unfold ty; rewrite Denotes_equation_2;
  repeat split; unfold tsubBV; simpl; try apply FTPrm; intros.
  assert (isBool v_x)
    by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial).
  destruct v_x eqn:E; simpl in H1; try contradiction.
  destruct b eqn:B.
  - (* Bc true *) exists (Lambda (BV 0)); split; try split;
    try apply lem_step_evals; try apply lem_step_eqv_tt.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTVar; unfold bound_inF; auto;
    assert (isBool v_x0)
      by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bc b0); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply EAppAbs;
    try apply FTBC; try apply PECons; try apply PEEmp; 
    try apply lemma_evals_trans with (Bc (Bool.eqb (Bool.eqb true b0) b0)); 
    try apply lemma_semantics_refn_eqv; destruct b0; simpl; 
    try apply Refl; auto.
  - (* Bc false *) exists (Prim Not); split; try split;
    try apply lem_step_evals; try apply lem_step_eqv_ff.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTPrm; trivial. 
    assert (isBool v_x0)
      by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bc (negb b0)); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply lem_step_not;
    try apply FTBC; apply PECons; try apply PEEmp.
    apply lemma_evals_trans with (Bc (Bool.eqb (Bool.eqb false b0) (negb b0)));
    try apply lemma_semantics_refn_eqv; destruct b0; simpl; apply Refl.
  Qed.  

Lemma lem_den_imp : Denotes (ty Imp) (Prim Imp).
Proof. unfold ty; rewrite Denotes_equation_2;
  repeat split; unfold tsubBV; simpl; try apply FTPrm; intros.
  assert (isBool v_x)
    by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial).
  destruct v_x eqn:E; simpl in H1; try contradiction.
  destruct b eqn:B.
  - (* Bc true *) exists (Lambda (BV 0)); split; try split;
    try apply lem_step_evals; try apply lem_step_imp_tt.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTVar; unfold bound_inF; auto;
    assert (isBool v_x0)
      by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bc b0); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply EAppAbs;
    try apply FTBC; try apply PECons; try apply PEEmp;
    try apply lemma_evals_trans with (Bc (Bool.eqb (implb true b0) b0)); 
    try apply lemma_semantics_refn_imp; destruct b0; simpl; 
    try apply Refl; auto.
  - (* Bc false *) exists (Lambda (Bc true)); split; try split;
    try apply lem_step_evals; try apply lem_step_imp_ff.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTBC; trivial. 
    assert (isBool v_x0)
      by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bc true); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply EAppAbs; try apply H2;
    try apply FTBC; apply PECons; try apply PEEmp.
    apply lemma_evals_trans with (Bc (Bool.eqb (implb false b0) true)); 
    try apply lemma_semantics_refn_imp; destruct b0; simpl; apply Refl.  
  Qed.  

Lemma lem_den_leqn : forall (n:nat), Denotes (ty (Leqn n)) (Prim (Leqn n)).
Proof. intro n; unfold ty; rewrite Denotes_equation_2;
  simpl; repeat split; try apply FTPrm; try apply WFFTBasic;
  unfold tsubBV; simpl; intros.
  assert (isInt v_x)
    by (apply lem_den_ints with (TRefn TInt PEmpty); simpl; trivial);
  destruct v_x eqn:E0; try contradiction.
  exists (Bc (n <=? n0)); repeat split; unfold psubBV; simpl;
  try apply lem_step_evals; try apply lem_step_leqn;
  try apply FTBC; try apply PECons; try apply PEEmp; 
  apply lemma_evals_trans with (Bc (Bool.eqb (n <=? n0) (n <=? n0)));
  try apply lemma_semantics_refn_leq;  
  set (b := n <=? n0); assert (Bool.eqb b b = true)
    by (pose proof (Bool.eqb_refl b); destruct (Bool.eqb b b); 
        try contradiction; reflexivity);
  rewrite H2; apply Refl. Qed.

Lemma lem_den_leq : Denotes (ty Leq) (Prim Leq).
Proof. unfold ty; rewrite Denotes_equation_2;
  repeat split; unfold tsubBV; simpl; try apply FTPrm; intros.
  assert (isInt v_x)
    by (apply lem_den_ints with (TRefn TInt PEmpty); simpl; trivial).
  destruct v_x eqn:E; simpl in H1; try contradiction.
  exists (Prim (Leqn n)); split; try split;
  try apply lem_step_evals; try apply lem_step_leq;
  apply lem_den_leqn. Qed. 

Lemma lem_den_eqn : forall (n:nat), Denotes (ty (Eqn n)) (Prim (Eqn n)).
Proof. intro n; unfold ty; rewrite Denotes_equation_2;
  simpl; repeat split; try apply FTPrm; try apply WFFTBasic;
  unfold tsubBV; simpl; intros.
  assert (isInt v_x)
    by (apply lem_den_ints with (TRefn TInt PEmpty); simpl; trivial);
  destruct v_x eqn:E0; try contradiction.
  exists (Bc (n =? n0)); repeat split; unfold psubBV; simpl;
  try apply lem_step_evals; try apply lem_step_eqn;
  try apply FTBC; try apply PECons; try apply PEEmp; 
  apply lemma_evals_trans with (Bc (Bool.eqb (n =? n0) (n =? n0)));
  try apply lemma_semantics_refn_eq;  
  set (b := n =? n0); assert (Bool.eqb b b = true)
    by (pose proof (Bool.eqb_refl b); destruct (Bool.eqb b b); 
        try contradiction; reflexivity);
  rewrite H2; apply Refl. Qed.

Lemma lem_den_eq : Denotes (ty Eq) (Prim Eq).
Proof. unfold ty; rewrite Denotes_equation_2;
  repeat split; unfold tsubBV; simpl; try apply FTPrm; intros.
  assert (isInt v_x)
    by (apply lem_den_ints with (TRefn TInt PEmpty); simpl; trivial).
  destruct v_x eqn:E; simpl in H1; try contradiction.
  exists (Prim (Eqn n)); split; try split;
  try apply lem_step_evals; try apply lem_step_eq;
  apply lem_den_eqn. Qed. 
  
Lemma lem_den_leql : Denotes (ty Leql) (Prim Leql).
Proof. unfold ty; rewrite Denotes_equation_4;
  repeat split; unfold tsubBTV; simpl; try apply FTPrm; intros.
  destruct (erase t_a) eqn:Heta; apply lem_erase_wftype in H0;
  rewrite Heta in H0; simpl in H0; inversion H0;
  try (simpl in H3; contradiction);
  destruct b eqn:B; simpl in H3; try contradiction;
  destruct t_a eqn:Hta; simpl in Heta; try discriminate;
  simpl in H; try contradiction; injection Heta as Heta;
  subst b1; subst t_a.
  - (* TBool *) exists (Prim Imp); split; simpl;
    try apply lem_step_evals; try apply lem_step_leql_tbool.
    
    pose proof lem_den_imp; simpl in H5; apply H5.

  - (* TInt *)

  destruct t_a eqn:TA; simpl in H; try contradiction;
  inversion H0; try (simpl in H5; contradiction). Focus 2.


{-@ lem_den_ty :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th)
        -> c:Prim -> ProofOf(Denotes (ctsubst th (ty c)) (Prim c)) @-}
lem_den_ty :: Env -> CSub -> DenotesEnv -> Prim -> Denotes
lem_den_ty g th den_g_th And      = lem_den_and    ? lem_ctsubst_nofree th (ty And)
lem_den_ty g th den_g_th Or       = lem_den_or     ? lem_ctsubst_nofree th (ty Or)
lem_den_ty g th den_g_th Not      = lem_den_not () ? lem_ctsubst_nofree th (ty Not)
lem_den_ty g th den_g_th Eqv      = lem_den_eqv    ? lem_ctsubst_nofree th (ty Eqv)
lem_den_ty g th den_g_th Leq      = lem_den_leq    ? lem_ctsubst_nofree th (ty Leq)
lem_den_ty g th den_g_th (Leqn n) = lem_den_leqn n ? lem_ctsubst_nofree th (ty (Leqn n))
lem_den_ty g th den_g_th Eq       = lem_den_eq     ? lem_ctsubst_nofree th (ty Eq)
lem_den_ty g th den_g_th (Eqn n)  = lem_den_eqn  n ? lem_ctsubst_nofree th (ty (Eqn n))
lem_den_ty g th den_g_th Eql      = lem_den_eql () ? lem_ctsubst_nofree th (ty Eql)


{-@ lem_denote_sound_typ_tprim :: g:Env -> c:Prim 
        ->  th:CSub  -> ProofOf(DenotesEnv g th)
        -> ProofOf(ValueDenoted (csubst th (Prim c)) (ctsubst th (ty c))) @-}
lem_denote_sound_typ_tprim :: Env -> Prim -> CSub -> DenotesEnv -> ValueDenoted
lem_denote_sound_typ_tprim g c th den_g_th 
  = ValDen (Prim c ? lem_csubst_prim th c) (ctsubst th (ty c)) (Prim c ? val_pf ? term_pf) 
           (Refl (Prim c)) den_tyc_c
      where
        den_tyc_c = lem_den_ty g th den_g_th c
        val_pf    = toProof ( isValue (Prim c) === True )
        term_pf   = toProof ( isTerm (Prim c) === True )
