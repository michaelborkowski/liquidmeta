Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFWellFormedness.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.PrimitivesFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.BasicPropsWellFormedness.
Require Import SystemRF.Typing.
Require Import SystemRF.LemmasWellFormedness.
Require Import Denotations.ClosingSubstitutions.
Require Import Denotations.Denotations.
Require Import Denotations.BasicPropsCSubst.
Require Import Denotations.BasicPropsDenotes.
Require Import Denotations.PrimitivesSemantics.
Require Import Denotations.BasicPropsSemantics.
Require Import Denotations.EnvironmentSubstitutions.

Require Import ZArith.
Require Import BinInt.

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

Lemma lem_den_lists : forall (t t':type) (v:expr),
    isValue v -> erase t = FTList (erase t') 
        -> Denotes t v -> isList v.
Proof. intros; apply lem_den_hasftype in H1; rewrite H0 in H1;
  apply lemma_list_values with (erase t'); assumption. Qed.  

Lemma lem_denotes_list_pempty : forall (t:type) (ps:preds) (v:expr),
    isValue v -> isList v -> Denotes (TList t ps) v
        -> Denotes (TList t PEmpty) v.
Proof. intros t ps; induction v; intros; simpl in H0; try contradiction.
  - rewrite Denotes_equation_17 in *; unfold psubBV; simpl in *; 
    intuition; apply PEEmp.
  - rewrite Denotes_equation_18 in *; repeat split; simpl in *;
    destruct H1 as [p_v1v2 [val1 [val2 [den_t_v1 [den_ts_v2 ev_psv1v2]]]]];
    unfold psubBV; simpl; try apply PEEmp; trivial.
  Qed.

  (* -- Lemmata. Denotations of Primitive/Constant Types *)

Lemma lem_den_tybc : forall (b:bool), Denotes (tybc b) (Bc b).
Proof. intro b; unfold tybc; rewrite Denotes_equation_1;
  repeat split; unfold psubBV; constructor || trivial; simpl;
  try apply FTBC; try apply PEEmp.
  assert (true = Bool.eqb b b) by (destruct b; reflexivity);
  rewrite H; apply lemma_eql_bool_semantics; apply Refl. Qed.

Lemma lem_den_tyic : forall (n:Z), Denotes (tyic n) (Ic n).
Proof. intro n; unfold tyic; rewrite Denotes_equation_1;
  repeat split; unfold psubBV; simpl; trivial; try apply val_Ic;
  try apply FTIC. apply PECons; try apply PEEmp.
  assert ((Z.eqb n n) = true) by (apply Z.eqb_eq; reflexivity).
  rewrite <- H; apply lemma_eql_int_semantics; apply Refl. Qed. 

Lemma lem_den_and : Denotes (ty And) (Prim And).
Proof. unfold ty; rewrite Denotes_equation_2;
  repeat split; unfold tsubBV; simpl; try apply FTPrm; 
  try apply val_Prm; intros.
  assert (isBool v_x)
    by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial).
  destruct v_x eqn:E; simpl in H1; try contradiction.
  destruct b eqn:B.
  - (* Bc true *) exists (Lambda (BV 0)); split; try split;
    try apply lem_step_evals; try apply lem_step_and_tt; try apply val_Lam.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTVar; unfold bound_inF; auto; try apply val_Lam.
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
    try apply lem_step_evals; try apply lem_step_and_ff; try apply val_Lam.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTBC; trivial; try apply val_Lam. 
    assert (isBool v_x0)
      by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bc false); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply EAppAbs; try apply H2; trivial;
    try apply FTBC; apply PECons; try apply PEEmp.
    apply lemma_evals_trans with (Bc (Bool.eqb (andb false b0) false)); 
    try apply lemma_semantics_refn_and; destruct b0; simpl; apply Refl.
  Qed.

Lemma lem_den_or : Denotes (ty Or) (Prim Or).
Proof. unfold ty; rewrite Denotes_equation_2.
  repeat split; unfold tsubBV; try constructor; try apply FTPrm; intros.
  assert (isBool v_x)
    by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial).
  destruct v_x eqn:E; simpl in H1; try contradiction.
  destruct b eqn:B.
  - (* Bc true *) exists (Lambda (Bc true)); split; try split; simpl;
    try apply lem_step_evals; try apply lem_step_or_tt; try apply val_Lam.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTBC; trivial; try apply val_Lam. 
    assert (isBool v_x0)
      by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bc true); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply EAppAbs; try apply H2; trivial;
    try apply FTBC; apply PECons; try apply PEEmp.
    apply lemma_evals_trans with (Bc (Bool.eqb (andb false b0) false)); 
    try apply lemma_semantics_refn_or; destruct b0; simpl; apply Refl.  
  - (* Bc false *) exists (Lambda (BV 0)); split; try split; simpl;
    try apply lem_step_evals; try apply lem_step_or_ff; try apply val_Lam.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTVar; unfold bound_inF; auto; try apply val_Lam;
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
  repeat split; unfold tsubBV; simpl; try apply FTPrm; try apply val_Prm; intros.
  assert (isBool v_x)
    by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial).
  destruct v_x eqn:E; simpl in H1; try contradiction.
  exists (Bc (negb b)); repeat split; unfold psubBV; simpl;
  try apply lem_step_evals; try apply lem_step_not; try apply val_Bc;
  try apply FTBC; apply PECons; try apply PEEmp;
  apply lemma_evals_trans with (Bc (Bool.eqb (negb b) (negb b)));
  try apply lemma_semantics_refn_not; destruct b; simpl; apply Refl.
  Qed.  

Lemma lem_den_eqv : Denotes (ty Eqv) (Prim Eqv).
Proof. unfold ty; rewrite Denotes_equation_2;
  repeat split; unfold tsubBV; simpl; try apply FTPrm; try apply val_Prm; intros.
  assert (isBool v_x)
    by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial).
  destruct v_x eqn:E; simpl in H1; try contradiction.
  destruct b eqn:B.
  - (* Bc true *) exists (Lambda (BV 0)); split; try split;
    try apply lem_step_evals; try apply lem_step_eqv_tt; try apply val_Lam.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTVar; unfold bound_inF; auto; try apply val_Lam;
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
    try apply lem_step_evals; try apply lem_step_eqv_ff; try apply val_Prm.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTPrm; try apply val_Prm; trivial. 
    assert (isBool v_x0)
      by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bc (negb b0)); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply lem_step_not; try apply val_Bc;
    try apply FTBC; apply PECons; try apply PEEmp.
    apply lemma_evals_trans with (Bc (Bool.eqb (Bool.eqb false b0) (negb b0)));
    try apply lemma_semantics_refn_eqv; destruct b0; simpl; apply Refl.
  Qed.  

Lemma lem_den_imp : Denotes (ty Imp) (Prim Imp).
Proof. unfold ty; simpl; rewrite Denotes_equation_2;
  repeat split; unfold tsubBV; simpl; try apply FTPrm; try apply val_Prm; intros.
  assert (isBool v_x)
    by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial).
  destruct v_x eqn:E; simpl in H1; try contradiction.
  destruct b eqn:B.
  - (* Bc true *) exists (Lambda (BV 0)); split; try split;
    try apply lem_step_evals; try apply lem_step_imp_tt; try apply val_Lam.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTVar; unfold bound_inF; auto; try apply val_Lam;
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
    try apply lem_step_evals; try apply lem_step_imp_ff; try apply val_Lam.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTBC; trivial; try apply val_Lam. 
    assert (isBool v_x0)
      by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bc true); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply EAppAbs; try apply H2; try apply val_Bc;
    try apply FTBC; apply PECons; try apply PEEmp.
    apply lemma_evals_trans with (Bc (Bool.eqb (implb false b0) true)); 
    try apply lemma_semantics_refn_imp; destruct b0; simpl; apply Refl.  
  Qed.  

Lemma lem_den_leqn : forall (n:Z), Denotes (ty (Leqn n)) (Prim (Leqn n)).
Proof. intro n; unfold ty; rewrite Denotes_equation_2;
  simpl; repeat split; try apply FTPrm; try apply WFFTBasic;
  unfold tsubBV; try apply val_Prm; simpl; intros.
  assert (isInt v_x)
    by (apply lem_den_ints with (TRefn TInt PEmpty); simpl; trivial);
  destruct v_x eqn:E0; try contradiction.
  exists (Bc (Z.leb n n0)); repeat split; unfold psubBV; simpl;
  try apply lem_step_evals; try apply lem_step_leqn; try apply val_Bc;
  try apply FTBC; try apply PECons; try apply PEEmp; 
  apply lemma_evals_trans with (Bc (Bool.eqb (Z.leb n n0) (Z.leb n n0)));
  try apply lemma_semantics_refn_leq;  
  set (b := Z.leb n n0); assert (Bool.eqb b b = true)
    by (pose proof (Bool.eqb_refl b); destruct (Bool.eqb b b); 
        try contradiction; reflexivity);
  rewrite H2; apply Refl. Qed.

Lemma lem_den_leq : Denotes (ty Leq) (Prim Leq).
Proof. unfold ty; rewrite Denotes_equation_2;
  repeat split; unfold tsubBV; simpl; try apply FTPrm; try apply val_Prm; intros.
  assert (isInt v_x)
    by (apply lem_den_ints with (TRefn TInt PEmpty); simpl; trivial).
  destruct v_x eqn:E; simpl in H1; try contradiction.
  exists (Prim (Leqn n)); split; try split;
  try apply lem_step_evals; try apply lem_step_leq;
  apply lem_den_leqn. Qed. 

Lemma lem_den_eqn : forall (n:Z), Denotes (ty (Eqn n)) (Prim (Eqn n)).
Proof. intro n; unfold ty; rewrite Denotes_equation_2;
  simpl; repeat split; try apply FTPrm; try apply WFFTBasic;
  unfold tsubBV; simpl; try apply val_Prm; intros.
  assert (isInt v_x)
    by (apply lem_den_ints with (TRefn TInt PEmpty); simpl; trivial);
  destruct v_x eqn:E0; try contradiction.
  exists (Bc (Z.eqb n n0)); repeat split; unfold psubBV; simpl;
  try apply lem_step_evals; try apply lem_step_eqn; try apply val_Bc;
  try apply FTBC; try apply PECons; try apply PEEmp; 
  apply lemma_evals_trans with (Bc (Bool.eqb (Z.eqb n n0) (Z.eqb n n0)));
  try apply lemma_semantics_refn_eq;  
  set (b := Z.eqb n n0); assert (Bool.eqb b b = true)
    by (pose proof (Bool.eqb_refl b); destruct (Bool.eqb b b); 
        try contradiction; reflexivity);
  rewrite H2; apply Refl. Qed.

Lemma lem_den_eq : Denotes (ty Eq) (Prim Eq).
Proof. unfold ty; rewrite Denotes_equation_2;
  repeat split; unfold tsubBV; simpl; try apply FTPrm; try apply val_Prm; intros.
  assert (isInt v_x)
    by (apply lem_den_ints with (TRefn TInt PEmpty); simpl; trivial).
  destruct v_x eqn:E; simpl in H1; try contradiction.
  exists (Prim (Eqn n)); split; try split;
  try apply lem_step_evals; try apply lem_step_eq;
  apply lem_den_eqn. Qed. 

Lemma lem_den_succ : Denotes (ty Succ) (Prim Succ).
Proof. unfold ty; rewrite Denotes_equation_2; repeat split;
  unfold tsubBV; simpl; try apply FTPrm; try apply val_Prm; intros. 
  assert (isInt v_x)
    by (apply lem_den_ints with (TRefn TInt PEmpty); simpl; trivial).
  destruct v_x eqn:E; simpl in H1; try contradiction.
  exists (Ic (1+n)); split; try split; try apply val_Ic;
  try apply lem_step_evals; try apply lem_step_succ.
  rewrite Denotes_equation_1; repeat split; try apply val_Ic;
  set (n' := Zplus 1 n);  unfold psubBV; simpl; try apply FTIC;
  apply PECons; try apply PEEmp.
  apply lemma_evals_trans with (Bc (Z.eqb (1+n) n'));
  try apply lemma_semantics_refn_succ.
  assert(1 + n =? n' = true)%Z by (apply Z.eqb_eq; auto). 
  rewrite H2; apply Refl. Qed.

Lemma lem_den_leql : Denotes (ty Leql) (Prim Leql).
Proof. unfold ty; rewrite Denotes_equation_4;
  repeat split; unfold tsubBTV; simpl; 
  try apply val_Prm; try apply FTPrm; intros.
  destruct (erase t_a) eqn:Heta; apply lem_erase_wftype in H0;
  rewrite Heta in H0; simpl in H0; inversion H0;
  try (simpl in H3; contradiction);
  destruct b eqn:B; simpl in H3; try contradiction;
  destruct t_a eqn:Hta; simpl in Heta; try discriminate;
  simpl in H; try contradiction; injection Heta as Heta;
  subst b1; subst t_a.
  - (* TBool *) exists (Prim Imp); split; try split; simpl; try apply val_Prm;
    try apply lem_step_evals; try apply lem_step_leql_tbool;
    rewrite Denotes_equation_2; 
    repeat split; unfold tsubBV; simpl; 
    try apply val_Prm; try apply FTPrm; intros.
    assert (isBool v_x)
        by (apply lem_den_bools with (TRefn TBool ps); simpl; trivial).
    destruct v_x eqn:E; simpl in H1; try contradiction.
    destruct b1 eqn:B1.
    * (* Bc true *) exists (Lambda (BV 0)); split; try split;
      try apply lem_step_evals; try apply lem_step_imp_tt; try apply val_Lam.
      rewrite Denotes_equation_2; simpl; repeat split;
      try apply FTAbs with Base empty; try apply WFFTBasic;
      unfold unbind; unfold tsubBV; simpl; intros;
      try apply FTVar; unfold bound_inF; auto; try apply val_Lam.
      assert (isBool v_x0)
        by (apply lem_den_bools with (TRefn TBool (psubBV_at 1 (Bc true) ps)); 
            simpl; trivial);
      destruct v_x0 eqn:E0; try contradiction.
      exists (Bc b2); repeat split; unfold psubBV; simpl;
      try apply lem_step_evals; try apply EAppAbs;
      try apply FTBC; try apply PECons; try apply PEEmp;
      try apply AddStep with  
        (App (App (Prim Eqv) (App (App (Prim Imp) (Bc true)) (Bc b2))) (Bc b2));
      try apply EApp1; try apply EApp2; try apply EApp1; try apply EApp1;
      try apply lem_step_leql_tbool;
      try apply lemma_evals_trans with (Bc (Bool.eqb (implb true b2) b2)); 
      try apply lemma_semantics_refn_imp; destruct b2; simpl; 
      try apply Refl; try apply val_Prm; auto.
    * (* Bc false *) exists (Lambda (Bc true)); split; try split;
      try apply lem_step_evals; try apply lem_step_imp_ff; try apply val_Lam.
      rewrite Denotes_equation_2; simpl; repeat split;
      try apply FTAbs with Base empty; try apply WFFTBasic;
      unfold unbind; unfold tsubBV; simpl; intros;
      try apply FTBC; trivial; try apply val_Lam. 
      assert (isBool v_x0)
        by (apply lem_den_bools with (TRefn TBool (psubBV_at 1 (Bc false) ps)); 
            simpl; trivial);
      destruct v_x0 eqn:E0; try contradiction.
      exists (Bc true); repeat split; unfold psubBV; simpl; try apply val_Bc;
      try apply lem_step_evals; try apply EAppAbs; try apply H8;
      try apply FTBC; apply PECons; try apply PEEmp.
      apply AddStep with  
        (App (App (Prim Eqv) (App (App (Prim Imp) (Bc false)) (Bc b2))) (Bc true));
      try apply EApp1; try apply EApp2; try apply EApp1; try apply EApp1;
      try apply lem_step_leql_tbool;  try apply val_Prm;
      try apply lemma_evals_trans with (Bc (Bool.eqb (implb false b2) true)); 
      try apply lemma_semantics_refn_imp; destruct b2; try apply Refl; simpl; exact I.  
  - (* TInt *) exists (Prim Leq); split; try split; simpl; try apply val_Prm;
    try apply lem_step_evals; try apply lem_step_leql_tint.
    rewrite Denotes_equation_2; 
    repeat split; unfold tsubBV; simpl; 
    try apply val_Prm; try apply FTPrm; intros.
    assert (isInt v_x)
        by (apply lem_den_ints with (TRefn TInt ps); simpl; trivial).
    destruct v_x eqn:E; simpl in H1; try contradiction.
    exists (Prim (Leqn n)); split; try split;
    try apply lem_step_evals; try apply lem_step_leq; try apply val_Prm.
    rewrite Denotes_equation_2; simpl; repeat split; 
    try apply val_Prm; try apply FTPrm; unfold tsubBV; simpl; intros.
    assert (isInt v_x0)
      by (apply lem_den_ints with (TRefn TInt (psubBV_at 1 (Ic n) ps)); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bc (Z.leb n n0)); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply lem_step_leqn; try apply val_Bc;
    try apply FTBC; try apply PECons; try apply PEEmp.
    apply AddStep with  
        (App (App (Prim Eqv) (App (App (Prim Leq) (Ic n)) (Ic n0))) (Bc (Z.leb n n0)));
    try apply EApp1; try apply EApp2; try apply EApp1; try apply EApp1;
    try apply lem_step_leql_tint;    
    try apply lemma_evals_trans with (Bc (Bool.eqb (Z.leb n n0) (Z.leb n n0)));
    try apply lemma_semantics_refn_leq;  
    set (b' := Z.leb n n0); assert (Bool.eqb b' b' = true)
      by (pose proof (Bool.eqb_refl b'); destruct (Bool.eqb b' b'); 
          try contradiction; reflexivity);
    try rewrite H10; try apply Refl; try apply val_Prm; auto. 
  Qed.

Lemma lem_den_eql : Denotes (ty Eql) (Prim Eql).
Proof. unfold ty; rewrite Denotes_equation_4;
  repeat split; unfold tsubBTV; simpl; 
  try apply val_Prm; try apply FTPrm; intros.
  destruct (erase t_a) eqn:Heta; apply lem_erase_wftype in H0;
  rewrite Heta in H0; simpl in H0; inversion H0;
  try (simpl in H3; contradiction);
  destruct b eqn:B; simpl in H3; try contradiction;
  destruct t_a eqn:Hta; simpl in Heta; try discriminate;
  simpl in H; try contradiction; injection Heta as Heta;
  subst b1; subst t_a.
  - (* TBool *) exists (Prim Eqv); split; try split; simpl;
    try apply lem_step_evals; try apply lem_step_eql_tbool;
    try rewrite Denotes_equation_2; 
    repeat split; unfold tsubBV; simpl; 
    try apply val_Prm; try apply FTPrm; intros.
    assert (isBool v_x)
        by (apply lem_den_bools with (TRefn TBool ps); simpl; trivial).
    destruct v_x eqn:E; simpl in H1; try contradiction.
    destruct b1 eqn:B1.
    * (* Bc true *) exists (Lambda (BV 0)); split; try split;
      try apply lem_step_evals; try apply lem_step_eqv_tt; try apply val_Lam.
      rewrite Denotes_equation_2; simpl; repeat split;
      try apply FTAbs with Base empty; try apply WFFTBasic;
      unfold unbind; unfold tsubBV; simpl; intros;
      try apply FTVar; unfold bound_inF; auto; try apply val_Lam;
      assert (isBool v_x0)
        by (apply lem_den_bools with (TRefn TBool (psubBV_at 1 (Bc true) ps)); 
            simpl; trivial);
      destruct v_x0 eqn:E0; try contradiction.
      exists (Bc b2); repeat split; unfold psubBV; simpl;
      try apply lem_step_evals; try apply EAppAbs;
      try apply FTBC; try apply PECons; try apply PEEmp;
      try apply AddStep with  
        (App (App (Prim Eqv) (App (App (Prim Eqv) (Bc true)) (Bc b2))) (Bc b2));
      try apply EApp1; try apply EApp2; try apply EApp1; try apply EApp1;
      try apply lem_step_eql_tbool;
      try apply lemma_evals_trans with (Bc (Bool.eqb (Bool.eqb true b2) b2)); 
      try apply lemma_semantics_refn_eqv; destruct b2; simpl; 
      try apply Refl; try apply val_Prm; auto.
    * (* Bc false *) exists (Prim Not); split; try split;
      try apply lem_step_evals; try apply lem_step_eqv_ff;
      try rewrite Denotes_equation_2; simpl; repeat split;
      try apply val_Prm; try apply FTPrm; unfold tsubBV; simpl; intros.
      assert (isBool v_x0)
        by (apply lem_den_bools with (TRefn TBool (psubBV_at 1 (Bc false) ps)); 
            simpl; trivial);
      destruct v_x0 eqn:E0; try contradiction.
      exists (Bc (negb b2)); repeat split; unfold psubBV; simpl;
      try apply lem_step_evals; try apply lem_step_not; try apply val_Bc;
      try apply FTBC; apply PECons; try apply PEEmp.
      apply AddStep with  
        (App (App (Prim Eqv) (App (App (Prim Eqv) (Bc false)) (Bc b2))) (Bc (negb b2)));
      try apply EApp1; try apply EApp2; try apply EApp1; try apply EApp1;
      try apply lem_step_eql_tbool;
      try apply lemma_evals_trans with (Bc (Bool.eqb (Bool.eqb false b2) (negb b2)));
      try apply lemma_semantics_refn_eqv; destruct b2; 
      try apply val_Prm; try apply Refl; simpl; exact I. 
  - (* TInt *) exists (Prim Eq); split; try split; simpl;
    try apply lem_step_evals; try apply lem_step_eql_tint;
    try rewrite Denotes_equation_2; 
    repeat split; unfold tsubBV; simpl; 
    try apply val_Prm; try apply FTPrm; intros.
    assert (isInt v_x)
        by (apply lem_den_ints with (TRefn TInt ps); simpl; trivial).
    destruct v_x eqn:E; simpl in H1; try contradiction.
    exists (Prim (Eqn n)); split; try split; try apply val_Prm;
    try apply lem_step_evals; try apply lem_step_eq.
    rewrite Denotes_equation_2; simpl; repeat split; 
    try apply val_Prm; try apply FTPrm; unfold tsubBV; simpl; intros.
    assert (isInt v_x0)
      by (apply lem_den_ints with (TRefn TInt (psubBV_at 1 (Ic n) ps)); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bc (Z.eqb n n0)); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply lem_step_eqn; try apply val_Bc;
    try apply FTBC; try apply PECons; try apply PEEmp.
    apply AddStep with  
        (App (App (Prim Eqv) (App (App (Prim Eq) (Ic n)) (Ic n0))) (Bc (Z.eqb n n0)));
    try apply EApp1; try apply EApp2; try apply EApp1; try apply EApp1;
    try apply lem_step_eql_tint;    
    try apply lemma_evals_trans with (Bc (Bool.eqb (Z.eqb n n0) (Z.eqb n n0)));
    try apply lemma_semantics_refn_eq;  
    set (b' := Z.eqb n n0); assert (Bool.eqb b' b' = true)
      by (pose proof (Bool.eqb_refl b'); destruct (Bool.eqb b' b'); 
          try contradiction; reflexivity);
    try rewrite H10; try apply Refl; try apply val_Prm; auto. 
  Qed.

Lemma lem_den_length : Denotes (ty Length) (Prim Length).
Proof. unfold ty; rewrite Denotes_equation_4;
  repeat split; unfold tsubBTV; simpl; 
  try apply val_Prm; try apply FTPrm; intros;
  rewrite lem_push_empty; trivial.

  exists (AppT (Prim Length) t_a);  split; try split;
  try apply val_Len; try apply Refl; 
  try rewrite Denotes_equation_2;
  repeat split; unfold tsubBV; simpl; try apply val_Len;
  assert (FTFunc (FTList (erase t_a)) (FTBasic TInt)
    = ftsubBV (erase t_a) (FTFunc (FTList (FTBasic (BTV 0))) (FTBasic TInt)))
    by reflexivity; try rewrite H1; try apply FTAppT with Star;
  try apply lem_wftype_islct in H0 as Hlct;
  pose proof lem_subBV_at_lc_at as [Hsub [Hsubt _]];
  apply lem_free_subset_binds in H0 as Hfr; destruct Hfr;
  try apply FTPrm; try apply lem_erase_wftype in H0 as p_emp_erta;
  simpl; trivial; intros; 
  try apply lem_den_hasftype in H5 as p_vx_ta;
  try apply lem_ftyp_islc in p_vx_ta as Hlce.

  apply lem_den_lists with (TList t_a PEmpty) t_a v_x in H5 as Hlist;
  try apply lemma_length_list_semantics with t_a v_x in Hlist as Hn; trivial.
  destruct Hn as [n Hn]; exists (Ic n); repeat split;
  try apply val_Ic; unfold psubBV; simpl; try apply FTIC;
  try rewrite Hsubt with t_a 1 v_x 0 0;
  try rewrite Hsub  with v_x 0 (Ic n) 0 0; 
  try rewrite Hsubt with t_a 0 (Ic n) 0 0; 
  try apply PECons; try apply PEEmp; auto.

  assert (n =? n = true)%Z by (apply Z.eqb_eq; reflexivity);
  apply lemma_evals_trans with (Bc (Z.eqb n n));
  try apply lemma_eq_semantics; try rewrite H6; 
  try apply Refl; trivial.
Qed.

Lemma lem_den_ty : forall (g:env) (th:csub) (c:prim),
    DenotesEnv g th -> Denotes (ctsubst th (ty c)) (Prim c).
Proof. intros; rewrite lem_ctsubst_nofree; destruct c; 
  simpl; try reflexivity.
  - apply lem_den_and.
  - apply lem_den_or.
  - apply lem_den_not.
  - apply lem_den_eqv.
  - apply lem_den_imp.
  - apply lem_den_leq.
  - apply lem_den_leqn.
  - apply lem_den_eq.
  - apply lem_den_eqn.
  - apply lem_den_succ.
  - apply lem_den_leql.
  - apply lem_den_eql.
  - apply lem_den_length.
  Qed.

Lemma lem_den_len_zero_nil : forall (th:csub) (t t0:type) (ps:preds),
  loc_closed th -> substitutable th
    -> Denotes (TList (ctsubst th t) (cpsubst th ps)) (Nil t0)
    -> Denotes (TList (ctsubst th t) 
                      (cpsubst th (PCons (eq (Ic 0) (length t (BV 0))) ps))) (Nil t0).
Proof. intros th t t0 ps Hlc Hsub; intros; 
  rewrite Denotes_equation_17 in H; destruct H.
  rewrite Denotes_equation_17; split; simpl; simpl in H; try apply H.
  shelve. (*
  rewrite lem_cpsubst_pcons;
  unfold psubBV; try apply PECons;
  fold subBV_at; fold psubBV_at; try apply H0.
  rewrite <- lem_csubst_nil with th t0.
  try rewrite <- lem_csubst_subBV; unfold subBV; simpl;
  try rewrite <- lem_csubst_bc with th true;
  try apply lem_csubst_evals;
  try apply lemma_semantics_refn_length_nil; trivial.
  *) Admitted. (*
  Qed.*)

Lemma lem_den_len_succ_cons : 
  forall (y:vname) (v1 v2:expr) (th:csub) (t t0:type) (ps:preds),
    loc_closed th -> substitutable th -> closed th 
      -> ~ in_csubst y th -> free t0 = empty -> freeTV t0 = empty
      -> fv v1 = empty -> ftv v1 = empty 
      -> fv v2 = empty -> ftv v2 = empty -> isLC v2
      -> free (ctsubst th t) = empty -> fvP (cpsubst th ps) = empty
      -> Denotes (TList (ctsubst th t) (cpsubst th ps)) (Cons t0 v1 v2)
      -> Denotes (TList (ctsubst (CCons y v2 th) t) 
                        (cpsubst (CCons y v2 th) 
                                 (PCons (eq (App (Prim Succ) (length t (FV y))) 
                                            (length t (BV 0))) ps))) (Cons t0 v1 v2).
Proof. intros y v1 v2 th t t0 ps Hlc Hsub Hc Hy Ht0 Ht0' Hfv1 Hftv1 Hfv Hftv Hlc2 Hfr Hfrv H.
  apply lem_den_lists with (TList (ctsubst th t) (cpsubst th ps)) 
                           (ctsubst th t) (Cons t0 v1 v2)
    in H as Hlis;
  rewrite Denotes_equation_18 in H; destruct H
    as [p_v1v2 [val1 [val2 [den_tht_v1 [den_thts_v2 ev_psv1v2_tt]]]]];
  try apply val_Cons; trivial.
  rewrite Denotes_equation_18; repeat split; unfold erase; fold erase;
  simpl in p_v1v2; try rewrite lem_unroll_ctsubst_left;
  try rewrite lem_erase_tsubFV; 
  try rewrite lem_tsubFV_notin;
  try (apply empty_no_elem; apply Hfr);
  try split; trivial.   
  rewrite lem_cpsubst_pcons;
  unfold psubBV; try apply PECons;
  fold subBV_at; fold psubBV_at;
  try rewrite lem_unroll_cpsubst_left;
  try rewrite lem_psubFV_notin; 
  try (apply empty_no_elem; apply Hfrv);
  try split; trivial.
  assert (y =? y = true) by (apply Nat.eqb_eq; reflexivity);
  simpl; rewrite H. 
  rewrite <- (lem_csubst_nofv th (Cons t0 v1 v2));
  try rewrite <- lem_csubst_subBV; unfold subBV; simpl;
  try rewrite <- lem_csubst_bc with th true;
  try apply lem_csubst_evals;
  pose proof (lem_subBV_lc (Cons t0 v1 v2) v2); 
  unfold subBV in H0; try rewrite H0;
  try apply lemma_semantics_refn_length_cons; 
  try apply no_elem_empty; try intro x;
  try apply not_elem_union_intro;
  try apply not_elem_union_intro; try apply empty_no_elem;
  try apply val_Cons; trivial.
  Qed.

Lemma lem_den_eqlLenPred : forall (v:expr) (th:csub) (t:type),
    loc_closed th -> substitutable th -> isList v -> isLC v
      -> Denotes (TList (ctsubst th t) PEmpty) v
      -> Denotes (TList (ctsubst th t) 
                    (cpsubst th (PCons (App (App (Prim Eq) (App (AppT (Prim Length) t) v)) 
                                            (App (AppT (Prim Length) t) (BV 0))) PEmpty))) v.
Proof. intros v th t Hlc Hsub Hlis Hlcv; intros; destruct v eqn:V;
  simpl in Hlis; try contradiction.
  shelve. shelve. (*
  - rewrite Denotes_equation_17 in H; destruct H.
    rewrite Denotes_equation_17; split; simpl; simpl in H; try apply H.
    rewrite <- (lem_csubst_nil th) at 1;
    try rewrite <- lem_cpsubst_psubBV; unfold psubBV; simpl;
    try rewrite lem_cpsubst_pcons; try apply PECons;
    try rewrite lem_cpsubst_pempty; 
    try rewrite <- lem_csubst_bc with th true;
    try apply lem_csubst_evals;
    assert ((Z.eqb 0 0) = true) by (apply Z.eqb_eq; reflexivity);
    try rewrite <- H1; try apply lemma_eq_semantics;
    try apply lem_step_evals; try apply lem_step_length_nil; trivial.
  - rewrite Denotes_equation_18 in H; destruct H
      as [p_v1v2 [val1 [val2 [den_tht_v1 [den_thts_v2 ev_psv1v2_tt]]]]];
    rewrite Denotes_equation_18; repeat split; 
    unfold erase; fold erase; trivial.
    apply lemma_length_list_semantics with (tsubBV_at 0 (Cons e1 e2) t) e2
      in Hlis as exists_n; try apply val2;
    destruct exists_n as [n ev_lenv2_n].
    apply lem_fv_subset_bindsF in p_v1v2 as Hfv; simpl in Hfv;
    destruct Hfv as [Hfv Hftv];
    rewrite <- (lem_csubst_nofv th (Cons e1 e2)) at 1;
    try apply no_elem_empty; try apply not_elem_subset with empty;
    try rewrite <- lem_cpsubst_psubBV; unfold psubBV; simpl;
    try rewrite lem_cpsubst_pcons; try rewrite lem_cpsubst_pempty;
    try apply PECons; try rewrite <- lem_csubst_bc with th true;
    try apply lem_csubst_evals; 
    unfold isLC  in Hlcv; simpl in Hlcv; destruct Hlcv;
    try repeat rewrite lem_subBV_lc;
    assert ((Z.eqb (1+n) (1+n)) = true) by (apply Z.eqb_eq; reflexivity);
    try rewrite <- H1; try apply lemma_eq_semantics;
    try apply lemma_length_cons_semantics with e1 e2;
    try apply Refl;    trivial.  *)
    Admitted. (*
  Qed.      *)
