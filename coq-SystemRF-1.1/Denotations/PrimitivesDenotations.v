Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFWellFormedness.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.PrimitivesFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.Typing.
Require Import Denotations.ClosingSubstitutions.
Require Import Denotations.Denotations.

Lemma lem_step_and_tt : Step (App (Prim And) (Bc true)) (Lambda (BV 0)).
Proof. assert (isCompat And (Bc true)) as pfB by apply isCpt_And;
  assert (delta And (Bc true) pfB = Lambda (BV 0))
      by (pose proof (delta_delta' And (Bc true) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.

Lemma lem_step_and_ff : Step (App (Prim And) (Bc false)) (Lambda (Bc false)).
Proof. assert (isCompat And (Bc false)) as pfB by apply isCpt_And;
  assert (delta And (Bc false) pfB = Lambda (Bc false))
      by (pose proof (delta_delta' And (Bc false) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.

Lemma lem_step_or_tt : Step (App (Prim Or) (Bc true)) (Lambda (Bc true)).
Proof. assert (isCompat Or (Bc true)) as pfB by apply isCpt_Or;
  assert (delta Or (Bc true) pfB = Lambda (Bc true))
      by (pose proof (delta_delta' Or (Bc true) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.
  
Lemma lem_step_or_ff : Step (App (Prim Or) (Bc false)) (Lambda (BV 0)).
Proof. assert (isCompat Or (Bc false)) as pfB by apply isCpt_Or;
  assert (delta Or (Bc false) pfB = Lambda (BV 0))
      by (pose proof (delta_delta' Or (Bc false) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.

Lemma lem_step_not : forall (b:bool), 
    Step (App (Prim Not) (Bc b)) (Bc (negb b)).
Proof. intro b. assert (isCompat Not (Bc b)) as pfB by apply isCpt_Not.
  assert (delta Not (Bc b) pfB = Bc (negb b))
      by (pose proof (delta_delta' Not (Bc b) pfB) as D;
          destruct b; simpl in D; injection D; trivial ). 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.

Lemma lem_step_eqv_tt : Step (App (Prim Eqv) (Bc true)) (Lambda (BV 0)).
Proof. assert (isCompat Eqv (Bc true)) as pfB by apply isCpt_Eqv.
  assert (delta Eqv (Bc true) pfB = Lambda (BV 0))
      by (pose proof (delta_delta' Eqv (Bc true) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.

Lemma lem_step_eqv_ff : Step (App (Prim Eqv) (Bc false)) (Prim Not).
Proof. assert (isCompat Eqv (Bc false)) as pfB by apply isCpt_Eqv.
  assert (delta Eqv (Bc false) pfB = Prim Not)
      by (pose proof (delta_delta' Eqv (Bc false) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.  

Lemma lem_step_eql_tbool : forall (ps:preds), 
    Step (AppT (Prim Eql) (TRefn TBool ps)) (Prim Eqv).
Proof. intro ps;
  assert (isCompatT Eql (TRefn TBool ps)) as pfB
      by (apply isCptT_EqlB; auto);
  assert (Prim Eqv = deltaT Eql (TRefn TBool ps) pfB)
      by (pose proof (deltaT_deltaT' Eql (TRefn TBool ps) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite H; apply EPrimT; simpl; exact I. Qed.

Lemma lem_step_eql_tint : forall (ps:preds), 
    Step (AppT (Prim Eql) (TRefn TInt ps)) (Prim Eq).
Proof. intro ps;
  assert (isCompatT Eql (TRefn TInt ps)) as pfZ
      by (apply isCptT_EqlZ; auto);
  assert (Prim Eq = deltaT Eql (TRefn TInt ps) pfZ)
      by (pose proof (deltaT_deltaT' Eql (TRefn TInt ps) pfZ) as D;
          simpl in D; injection D; trivial ); 
  rewrite H; apply EPrimT; simpl; exact I. Qed.


{-@ lemma_and_semantics :: p:Expr -> b:Bool  -> ProofOf(EvalsTo p (Bc b))
                        -> q:Expr -> b':Bool -> ProofOf(EvalsTo q (Bc b'))
                        -> ProofOf(EvalsTo (App (App (Prim And) p) q) (Bc (blAnd b b'))) @-}
lemma_and_semantics :: Expr -> Bool -> EvalsTo -> Expr -> Bool -> EvalsTo -> EvalsTo
lemma_and_semantics p b ev_p_b q b' ev_q_b' = ev_andpq
  where
    ev_andp    = lemma_reduce_to_delta And p (Bc b) ev_p_b
    ev_andpq_1 = lemma_app_both_many (App (Prim And) p) (delta And (Bc b)) ev_andp q (Bc b') ev_q_b'
    {-@ st_andpq_2 :: ProofOf(Step (App (delta And (Bc b)) (Bc b')) (Bc (blAnd b b'))) @-}
    st_andpq_2 = if b then ( EAppAbs 1 (BV 1)     (Bc b') )
                      else ( EAppAbs 1 (Bc False) (Bc b') )
    ev_andpq   = lemma_add_step_after (App (App (Prim And) p) q) (App (delta And (Bc b)) (Bc b'))
                                      ev_andpq_1 (Bc (b && b')) st_andpq_2

Lemma lemma_eqv_semantics : forall (p q:expr) (b b':bool),
    EvalsTo p (Bc b) -> EvalsTo q (Bc b') 
        -> EvalsTo (App (App (Prim Eqv) p) q) (Bc (Bool.eqb b b')).
Proof. intros; apply lemma_evals_trans with (App (App (Prim Eqv) (Bc b)) q).
  - apply lemma_app_many; apply lemma_app_many2; simpl; trivial.
  - destruct b.
    * apply lemma_evals_trans with (App (Lambda (BV 0)) (Bc b'));
      try apply lemma_app_both_many; destruct b'; simpl; trivial;
      apply lem_step_evals; apply lem_step_eqv_tt || apply EAppAbs; 
      simpl; trivial.
    * apply lemma_evals_trans with (App (Prim Not) (Bc b'));
      try apply lemma_app_both_many; destruct b'; simpl; trivial;
      apply lem_step_evals; apply lem_step_eqv_ff || apply lem_step_not. 
  Qed.
  
Lemma lemma_eql_bool_semantics : forall (p q:expr) (b b':bool),
    EvalsTo p (Bc b) -> EvalsTo q (Bc b')  
        -> EvalsTo (App (App (AppT (Prim Eql) (TRefn TBool PEmpty)) p) q) (Bc (Bool.eqb b b')).
Proof. intros. apply lemma_evals_trans with (App (App (Prim Eqv) p) q).
  - apply lem_step_evals; apply EApp1; apply EApp1;
    apply lem_step_eql_tbool.
  - apply lemma_eqv_semantics; trivial.
  Qed.


Lemma lemma_semantics_refn_and : forall (b b' b'' : bool), 
    EvalsTo (App (App (Prim Eqv) (Bc b'')) (App (App (Prim And) (Bc b)) (Bc b'))) 
            (Bc (Bool.eqb b'' (andb b b'))).
Proof. intros. apply lemma_eqv_semantics; apply lemma_and_semantics.
lemma_semantics_refn_and :: Bool -> Bool -> Bool -> EvalsTo
lemma_semantics_refn_and b b' b'' = reduce_eqv
  where
    reduce_and = lemma_and_semantics (Bc b) b (Refl (Bc b)) (Bc b') b' (Refl (Bc b'))
    reduce_eqv = lemma_eqv_semantics (Bc b'') b'' (Refl (Bc b'')) 
                                     (App (App (Prim And) (Bc b)) (Bc b')) (blAnd b b') reduce_and

{-@ reduce_and_tt :: b:Bool -> b':Bool -> { pf:_ | propOf pf == 
      EvalsTo (subBV 0 (Bc (blAnd b b')) (subBV 2 (Bc b') (subBV 1 (Bc b) (refn_pred And)))) (Bc True) } @-}
reduce_and_tt :: Bool -> Bool -> EvalsTo
reduce_and_tt b b' = lemma_semantics_refn_and b b' (b && b') -- (Bc b) b (Refl (Bc b)) (Bc b') b' (Refl (Bc b'))
                                             -- (Bc (blAnd b b')) (b && b') (Refl (Bc (b && b'))) 

{-@ lemma_semantics_refn_or :: b:Bool -> b':Bool -> b'':Bool 
                -> ProofOf(EvalsTo (App (App (Prim Eqv) (Bc b'')) (App (App (Prim Or) (Bc b)) (Bc b'))) 
                                   (Bc (blIff b'' (blOr b b'))) ) @-}
lemma_semantics_refn_or :: Bool -> Bool -> Bool -> EvalsTo
lemma_semantics_refn_or b b' b'' = reduce_eqv
  where
    reduce_or  = lemma_or_semantics (Bc b) b (Refl (Bc b)) (Bc b') b' (Refl (Bc b'))
    reduce_eqv = lemma_eqv_semantics (Bc b'') b'' (Refl (Bc b'')) 
                                     (App (App (Prim Or) (Bc b)) (Bc b')) (blOr b b') reduce_or

{-@ reduce_or_tt :: b:Bool -> b':Bool -> { pf:_ | propOf pf == 
      EvalsTo (subBV 0 (Bc (blOr b b')) (subBV 2 (Bc b') (subBV 1 (Bc b) (refn_pred Or)))) (Bc True) } @-}
reduce_or_tt :: Bool -> Bool -> EvalsTo
reduce_or_tt b b' = lemma_semantics_refn_or b b' (b || b')

{-@ reduce_or_tt' :: b:Bool -> b':Bool -> { pf:_ | propOf pf == 
      EvalsTo (subBV 0 (Bc (blOr b b')) (subBV 2 (Bc b') (subBV 1 (Bc b) 
                (App (App (Prim Eqv) (BV 0)) (App (App (Prim Or) (BV 1)) (BV 2)))))) (Bc True) } @-}
reduce_or_tt' :: Bool -> Bool -> EvalsTo
reduce_or_tt' b b' = lemma_semantics_refn_or b b' (b || b')

{-@ lemma_semantics_refn_not :: b:Bool -> b':Bool
                -> ProofOf(EvalsTo (App (App (Prim Eqv) (Bc b')) (App (Prim Not) (Bc b))) 
                                   (Bc (blIff b' (blNot b)))) @-}
lemma_semantics_refn_not :: Bool -> Bool -> EvalsTo
lemma_semantics_refn_not b b' = reduce_eqv
  where
    reduce_not = lemma_not_semantics (Bc b) b (Refl (Bc b))
    reduce_eqv = lemma_eqv_semantics (Bc b') b' (Refl (Bc b')) (App (Prim Not) (Bc b)) (blNot b) reduce_not

{-@ reduce_not_tt :: b:Bool -> { pf:_ | propOf pf ==
      EvalsTo (subBV 0 (Bc (blNot b)) (subBV 2 (Bc b) (refn_pred Not))) (Bc True) } @-}
reduce_not_tt :: Bool -> EvalsTo
reduce_not_tt b = lemma_semantics_refn_not b (blNot b)  

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

Lemma lem_den_and : Denotes (ty And) (Prim And).
Proof. unfold ty; rewrite Denotes_equation_2;
  repeat split; unfold psubBV; unfold tsubBV; simpl; trivial;
  try apply FTPrm; try apply PEEmp; intros.
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

    auto.
    

    destruct b0 eqn:B0.
    * (* Bc true *) exists (V)

    (*
    {-@ val_den_func_and :: v_x:Value -> ProofOf(Denotes (TRefn TBool Z (Bc True)) v_x) 
    -> ProofOf(ValueDenoted (App (Prim And) v_x) (tsubBV 1 v_x (ty' And))) @-}
val_den_func_and :: Expr -> Denotes -> ValueDenoted
val_den_func_and v_x den_tx_vx = case v_x of 
(Bc True)  -> ValDen (App (Prim And) (Bc True)) (tsubBV 1 (Bc True) (ty' And)) (Lambda 1 (BV 1) ? val_id) 
(lem_step_evals (App (Prim And) (Bc True)) (Lambda 1 (BV 1)) 
        (EPrim And (Bc True ? comp_t) ? del_t )) den_t'andt_id
(Bc False) -> ValDen (App (Prim And) (Bc False)) (tsubBV 1 (Bc False) (ty' And)) (Lambda 1 (Bc False) ? val_ff) 
(lem_step_evals (App (Prim And) (Bc False)) (Lambda 1 (Bc False)) 
        (EPrim And (Bc False ? comp_f) ? del_f )) den_t'andf_lamff
_     -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool Z (Bc True) ? er_bool ) den_tx_vx)
where
comp_f    = isCompat And (Bc False)
comp_t    = isCompat And (Bc True)
del_f     = delta And (Bc False ? comp_f ? val_f)
del_t     = delta And (Bc True  ? comp_t ? val_t)
val_f     = isValue (Bc False)  ? isTerm (Bc False)
val_t     = isValue (Bc True)   ? isTerm (Bc True)
val_ff    = isValue (Lambda 1 (Bc False)) ? isTerm (Lambda 1 (Bc False))
val_id    = isValue (Lambda 1 (BV 1))     ? isTerm (Lambda 1 (BV 1))
er_bool   = erase (TRefn TBool Z (Bc True)) 

{-@ ple den_t'andt_id @-}
{-@ den_t'andt_id :: ProofOf(Denotes (tsubBV 1 (Bc True) (ty' And)) (Lambda 1 (BV 1))) @-}
den_t'andt_id :: Denotes
den_t'andt_id = DFunc 2 (TRefn TBool Z (Bc True)) t'and_t (Lambda 1 (BV 1) ? val_id) 
(FTAbs FEmpty 1 (FTBasic TBool) Base (WFFTBasic FEmpty TBool) (BV 1) 
(FTBasic TBool) (1 ? ftv1 ? femp) (FTVar1 FEmpty 1 (FTBasic TBool) ? un1) ? er_func) 
val_den_func_and2
? ( tsubBV 1 (Bc True ? val_t) (ty' And) ? lem_tsubBV_notin 1 (Bc True ? val_t) (TRefn TBool Z (Bc True))
=== TFunc 2 (TRefn TBool Z (Bc True)) (tsubBV 1 (Bc True) (TRefn TBool Z (refn_pred And))) )
where
t'and_t   = tsubBV 1 (Bc True ? val_t) (TRefn TBool Z (refn_pred And))
femp      = not (in_envF 1 FEmpty) === not (S.member 1 (bindsF FEmpty))
ftv1      = fv (BV 1) ? ftv (BV 1)
un1       = unbind 1 1 (BV 1) === subBV 1 (FV 1 ? val1) (BV 1) ? lem_subBV_id 1 (FV 1 ? val1)
val_id    = isValue (Lambda 1 (BV 1))    ? (isTerm (Lambda 1 (BV 1)) === isTerm (BV 1))
val_t     = isValue (Bc True) ? isTerm (Bc True)
val1      = isValue (FV 1) ? isTerm (FV 1)
er_func   = ( erase (TFunc 2 (TRefn TBool Z (Bc True)) 
   (tsubBV 1 (Bc True ? val_t) (TRefn TBool Z (refn_pred And))))
=== FTFunc (erase (TRefn TBool Z (Bc True)))
(erase (tsubBV 1 (Bc True ? val_t) (TRefn TBool Z (refn_pred And))))
? lem_erase_tsubBV 1 (Bc True ? val_t) (TRefn TBool Z (refn_pred And))
=== FTFunc (FTBasic TBool) (erase (TRefn TBool Z (refn_pred And))) )

{-@ ple val_den_func_and2 @-}
{-@ val_den_func_and2 :: v_x:Value -> ProofOf(Denotes (TRefn TBool Z (Bc True)) v_x)
-> ProofOf(ValueDenoted (App (Lambda 1 (BV 1)) v_x) 
(tsubBV 2 v_x (tsubBV 1 (Bc True) (TRefn TBool Z (refn_pred And))))) @-}
val_den_func_and2 :: Expr -> Denotes -> ValueDenoted
val_den_func_and2 v_x den_tx_vx = case v_x of 
(Bc True)  -> ValDen (App (Lambda 1 (BV 1)) (Bc True)) (tsubBV 2 (Bc True) (t'and_t)) (Bc True ? val_t)
(lem_step_evals (App (Lambda 1 (BV 1)) (Bc True)) (Bc True ? subtt) 
        (EAppAbs 1 (BV 1) (Bc True)  {-? subtt-} )) den_t''t_tt 
(Bc False) -> ValDen (App (Lambda 1 (BV 1)) (Bc False)) (tsubBV 2 (Bc False) (t'and_t)) (Bc False )
(lem_step_evals (App (Lambda 1 (BV 1)) (Bc False)) (Bc False ? subft) 
        (EAppAbs 1 (BV 1) (Bc False) {-? subft-} )) den_t''f_ff 
_          -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool Z (Bc True) ? er_bool) den_tx_vx)
where
t'and_t     = tsubBV 1 (Bc True) (TRefn TBool Z (refn_pred And))
den_t''t_tt = DRefn TBool Z p''t (Bc True) (FTBC FEmpty True) ev_prt''t_tt
p''t        = subBV 2 (Bc True ? val_t)  (subBV 1 (Bc True ? val_t) (refn_pred And))
den_t''f_ff = DRefn TBool Z p''f (Bc False) (FTBC FEmpty False) ev_prt''f_ff
p''f        = subBV 2 (Bc False ? val_f) (subBV 1 (Bc True ? val_t) (refn_pred And))
subtt       = subBV 1 (Bc True) (BV 1)  ?  lem_subBV_id 1 (Bc True)  
             === Bc True  ? lem_value_pred (Bc True)
subft       = subBV 1 (Bc False) (BV 1) ?  lem_subBV_id 1 (Bc False) 
             === Bc False ? lem_value_pred (Bc False)
val1        = isValue (BV 1) ? isTerm (BV 1)
val_f       = isValue (Bc False)  ? isTerm (Bc False)
val_t       = isValue (Bc True)   ? isTerm (Bc True)
er_bool     = erase (TRefn TBool Z (Bc True)) 

{-@ ev_prt''t_tt :: ProofOf(EvalsTo (subBV 0 (Bc True) (subBV 2 (Bc True)  (subBV 1 (Bc True) (refn_pred And)))) 
      (Bc True)) @-}
ev_prt''t_tt :: EvalsTo
ev_prt''t_tt = reduce_and_tt True True ? blAnd True True

{-@ ev_prt''f_ff :: ProofOf(EvalsTo (subBV 0 (Bc False) (subBV 2 (Bc False) (subBV 1 (Bc True) (refn_pred And)))) 
      (Bc True)) @-}
ev_prt''f_ff :: EvalsTo
ev_prt''f_ff = reduce_and_tt True False ? blAnd True False

{-@ den_t'andf_lamff :: ProofOf(Denotes (tsubBV 1 (Bc False) (ty' And)) (Lambda 1 (Bc False))) @-}
den_t'andf_lamff :: Denotes
den_t'andf_lamff = DFunc 2 (TRefn TBool Z (Bc True)) t'and_f (Lambda 1 (Bc False) ? val_ff)
(FTAbs FEmpty 1 (FTBasic TBool) Base (WFFTBasic FEmpty TBool) (Bc False) 
(FTBasic TBool) (1 ? ftv1) (FTBC (FCons 1 (FTBasic TBool) (FEmpty ? femp)) False ? un1)
? er_func ) val_den_func_and3
? ( tsubBV 1 (Bc False ? val_f) (ty' And) 
? lem_tsubBV_notin 1 (Bc False ? val_f) (TRefn TBool Z (Bc True))
=== TFunc 2 (TRefn TBool Z (Bc True)) (tsubBV 1 (Bc False) (TRefn TBool Z (refn_pred And))) )
where
t'and_f   = tsubBV 1 (Bc False ? val_f) (TRefn TBool Z (refn_pred And))
femp      = not (in_envF 1 FEmpty) === not (S.member 1 (bindsF FEmpty))
ftv1      = fv (Bc False) ? ftv (Bc False)
un1       = unbind 1 1 (Bc False) === subBV 1 (FV 1 ? val1) (Bc False)
val1      = isValue (FV 1) ? isTerm (FV 1)
val_f     = isValue (Bc False)  ? isTerm (Bc False)
val_t     = isValue (Bc True)   ? isTerm (Bc True)
val_ff    = isValue (Lambda 1 (Bc False))   ? (isTerm (Lambda 1 (Bc False)) === isTerm (Bc False))
er_func   = ( erase (TFunc 2 (TRefn TBool Z (Bc True)) 
   (tsubBV 1 (Bc False ? val_f) (TRefn TBool Z (refn_pred And))))
=== FTFunc (erase (TRefn TBool Z (Bc True)))
(erase (tsubBV 1 (Bc False ? val_f) (TRefn TBool Z (refn_pred And))))
? lem_erase_tsubBV 1 (Bc False ? val_f) (TRefn TBool Z (refn_pred And))
=== FTFunc (FTBasic TBool) (erase (TRefn TBool Z (refn_pred And))) )

{-@ val_den_func_and3 :: v_x:Value -> ProofOf(Denotes (TRefn TBool Z (Bc True)) v_x)
-> ProofOf(ValueDenoted (App (Lambda 1 (Bc False)) v_x) 
     (tsubBV 2 v_x (tsubBV 1 (Bc False) (TRefn TBool Z (refn_pred And))))) @-}
val_den_func_and3 :: Expr -> Denotes -> ValueDenoted
val_den_func_and3 v_x den_tx_vx = case v_x of
(Bc True)  -> ValDen (App (Lambda 1 (Bc False)) (Bc True)) (tsubBV 2 (Bc True) t'and_f) (Bc False ? val_f)
(lem_step_evals (App (Lambda 1 (Bc False)) (Bc True)) (Bc False ? val_f) 
        (EAppAbs 1 (Bc False) (Bc True) ? subtf)) den_t'''t_ff
(Bc False) -> ValDen (App (Lambda 1 (Bc False)) (Bc False)) (tsubBV 2 (Bc False) t'and_f) (Bc False ? val_f)
(lem_step_evals (App (Lambda 1 (Bc False)) (Bc False)) (Bc False ? val_f) 
        (EAppAbs 1 (Bc False) (Bc False) ? subff)) den_t'''f_ff
_          -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool Z (Bc True) ? er_bool) den_tx_vx)
where
t'and_f   = tsubBV 1 (Bc False) (TRefn TBool Z (refn_pred And))
den_t'''t_ff = DRefn TBool Z p'''t (Bc False) (FTBC FEmpty False) ev_prt'''t_ff
p'''t = subBV 2 (Bc True ? val_t)  (subBV 1 (Bc False ? val_f) (refn_pred And))
den_t'''f_ff = DRefn TBool Z p'''f (Bc False) (FTBC FEmpty False) ev_prt'''f_ff
p'''f = subBV 2 (Bc False ? val_f) (subBV 1 (Bc False ? val_t) (refn_pred And))
subtf       = subBV 1 (Bc True  ? val_t) (Bc False)
subff       = subBV 1 (Bc False ? val_f) (Bc False)
val_f       = isValue (Bc False)  ? isTerm (Bc False)
val_t       = isValue (Bc True)   ? isTerm (Bc True)
er_bool     = erase (TRefn TBool Z (Bc True)) 

{-@ ev_prt'''t_ff :: ProofOf(EvalsTo (subBV 0 (Bc False) (subBV 2 (Bc True)  (subBV 1 (Bc False) (refn_pred And))))
       (Bc True)) @-}
ev_prt'''t_ff :: EvalsTo
ev_prt'''t_ff = reduce_and_tt False True ? blAnd False True

{-@ ev_prt'''f_ff :: ProofOf(EvalsTo (subBV 0 (Bc False) (subBV 2 (Bc False) (subBV 1 (Bc False) (refn_pred And))))
       (Bc True)) @-}
ev_prt'''f_ff :: EvalsTo
ev_prt'''f_ff = reduce_and_tt False False ? blAnd False False


(*
Lemma lemma_reduce_to_deltaT :: c:Prim -> p:Expr -> { v:Value | isCompat c v } -> ProofOf(EvalsTo p v)
                          -> ProofOf(EvalsTo (App (Prim c) p) (delta c v)) @-}
lemma_reduce_to_delta :: Prim -> Expr -> Expr -> EvalsTo -> EvalsTo
lemma_reduce_to_delta c p v ev_p_v = ev_appcp
  where
    ev_appcp_1 = lemma_app_many2 (Prim c) p v ev_p_v
    st_appcp_2 = EPrim c v
    ev_appcp   = lemma_add_step_after (App (Prim c) p) (App (Prim c) v) ev_appcp_1 (delta c v) st_appcp_2
*)

(*
Lemma lemma_not_semantics : forall (p:expr) (b:bool),
    EvalsTo p (Bc b)      -> ProofOf(EvalsTo (App (Prim Not) p) (Bc (blNot b))) @-}
lemma_not_semantics :: Expr -> Bool -> EvalsTo -> EvalsTo
lemma_not_semantics p b ev_p_b = lemma_reduce_to_delta Not p (Bc b) ev_p_b
*)

(*
{-@ ple reduce_pred_tyic @-}
{-@ reduce_pred_tyic :: n:Int -> ProofOf(EvalsTo (subBV 0 (Ic n) (App (App (Prim Eq) (BV 0)) (Ic n))) (Bc True)) @-}
reduce_pred_tyic :: Int -> EvalsTo
reduce_pred_tyic n = lemma_eq_semantics (Ic n) n (Refl (Ic n)) (Ic n) n (Refl (Ic n))

{-@ lem_den_tyic :: n:Int -> ProofOf(Denotes (tyic n) (Ic n)) @-}
lem_den_tyic :: Int -> Denotes
lem_den_tyic n = DRefn TInt Z (App (App (Prim Eq) (BV 0)) (Ic n) ? pred_pf) 
                       (Ic n ? val_pf) (FTIC FEmpty n) (reduce_pred_tyic n)
                       ? toProof ( tyic n === TRefn TInt Z (App (App (Prim Eq) (BV 0)) (Ic n)) )
  where
    val_pf    = toProof ( isValue (Ic n) === True )
    pred_pf   = toProof ( isPred (App (App (Prim Eq) (BV 0)) (Ic n))
                    === ( isTerm (App (Prim Eq) (BV 0)) && isTerm (Ic n) )
                    === ( isTerm (Prim Eq) && isTerm (BV 0) && isTerm (Ic n) )
                    ===    True )

                    




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

-- these are used in lem_exact_type in the (self (ty(b/i)c (b/n)) e k) cases
{-@ ple lem_csub_unbind_refn_bc @-}
{-@ lem_csub_unbind_refn_bc :: g:Env -> th:CSub -> { y:Vname | not (in_csubst y th) } 
        -> { v:Value | Set_emp (fv v) && Set_emp (ftv v) } -> b:Bool
        -> { pf:_ | csubst (CCons y v th) (unbind 0 y (App (App (Prim Eqv) (BV 0)) (Bc b)))
                 == App (App (Prim Eqv) v) (Bc b) } @-}
lem_csub_unbind_refn_bc :: Env -> CSub -> Vname -> Expr -> Bool -> Proof
lem_csub_unbind_refn_bc g th y v b = () ? lem_subBV_notin 0 (FV y) (Bc b)
                                        ? lem_subFV_notin y v      (Bc b)
                                        ? lem_csubst_app  th (App (Prim Eqv) v) (Bc b)
                                        ? lem_csubst_app  th (Prim Eqv) v
                                        ? lem_csubst_prim th Eqv
                                        ? lem_csubst_nofv th v
                                        ? lem_csubst_bc   th b  

{-@ ple lem_csub_unbind_refn'_bc @-}
{-@ lem_csub_unbind_refn'_bc :: g:Env -> th:CSub -> { y:Vname | not (in_csubst y th) }
        -> { v:Value | Set_emp (fv v) && Set_emp (ftv v) } -> b:Bool
        -> { pf:_ | csubst (CCons y v th) (unbind 0 y (App (App (AppT (Prim Eql) (tybc b)) (BV 0)) (Bc b))) 
                 == App (App (AppT (Prim Eql) (tsubBV 0 v (tybc b))) v) (Bc b) } @-}
lem_csub_unbind_refn'_bc :: Env -> CSub -> Vname -> Expr -> Bool -> Proof 
lem_csub_unbind_refn'_bc g th y v b = () ? lem_subBV_notin  0 (FV y) (Bc b)
                                         ? lem_subFV_notin  y v      (Bc b)
                                         ? lem_tsubFV_unbindT 0 y v (tybc b)
                                         ? lem_csubst_app  th (App (AppT (Prim Eql) (tybc b)) v) (Bc b)
                                         ? lem_csubst_app  th (AppT (Prim Eql) (tybc b)) v
                                         ? lem_csubst_appT th (Prim Eql) (tybc b)
                                         ? lem_csubst_prim th Eql
                                         ? lem_ctsubst_nofree th (tybc b)
                                         ? lem_csubst_nofv th v
                                         ? lem_csubst_bc   th b  

{-@ ple lem_csub_unbind_refn_ic @-}
{-@ lem_csub_unbind_refn_ic :: g:Env -> th:CSub -> { y:Vname | not (in_csubst y th) } 
        -> { v:Value | Set_emp (fv v) && Set_emp (ftv v) } -> n:Int
        -> { pf:_ | csubst (CCons y v th) (unbind 0 y (App (App (Prim Eq) (BV 0)) (Ic n)))
                 == App (App (Prim Eq) v) (Ic n) } @-}
lem_csub_unbind_refn_ic :: Env -> CSub -> Vname -> Expr -> Int -> Proof
lem_csub_unbind_refn_ic g th y v n = () ? lem_subBV_notin 0 (FV y) (Ic n)
                                        ? lem_subFV_notin y v      (Ic n)
                                        ? lem_csubst_app  th (App (Prim Eq) v) (Ic n)
                                        ? lem_csubst_app  th (Prim Eq) v
                                        ? lem_csubst_prim th Eq
                                        ? lem_csubst_nofv th v
                                        ? lem_csubst_ic   th n 

{-@ ple lem_csub_unbind_refn'_ic @-}
{-@ lem_csub_unbind_refn'_ic :: g:Env -> th:CSub -> { y:Vname | not (in_csubst y th) }
        -> { v:Value | Set_emp (fv v) && Set_emp (ftv v) } -> n:Int
        -> { pf:_ | csubst (CCons y v th) (unbind 0 y (App (App (AppT (Prim Eql) (tyic n)) (BV 0)) (Ic n))) 
                 == App (App (AppT (Prim Eql) (tsubBV 0 v (tyic n))) v) (Ic n) } @-}
lem_csub_unbind_refn'_ic :: Env -> CSub -> Vname -> Expr -> Int -> Proof 
lem_csub_unbind_refn'_ic g th y v n = () ? lem_subBV_notin  0 (FV y) (Ic n)
                                         ? lem_subFV_notin  y v      (Ic n)
                                         ? lem_tsubFV_unbindT 0 y v (tyic n)
                                         ? lem_csubst_app  th (App (AppT (Prim Eql) (tyic n)) v) (Ic n)
                                         ? lem_csubst_app  th (AppT (Prim Eql) (tyic n)) v
                                         ? lem_csubst_appT th (Prim Eql) (tyic n)
                                         ? lem_csubst_prim th Eql
                                         ? lem_ctsubst_nofree th (tyic n)
                                         ? lem_csubst_nofv th v
                                         ? lem_csubst_ic   th n  

{-@ ple lem_exact_type_tbc @-}
{-@ lem_exact_type_tbc :: g:Env -> v:Value -> t:Type 
        -> { p_v_t:HasType | (propOf p_v_t == HasType g v t) && isTBC p_v_t } -> k:Kind
        -> ProofOf(WFType g t k) -> ProofOf(WFEnv g) -> ProofOf(HasType g v (self t v k)) @-}
lem_exact_type_tbc :: Env -> Expr -> Type -> HasType -> Kind -> WFType -> WFEnv -> HasType
lem_exact_type_tbc g e t (TBC _ b)   Base p_g_t p_g_wf 
  = TSub g (Bc b) (tybc b) (TBC g b) (self (tybc b) (Bc b) Base) Base p_g_self_tybc tybc_self_tybc
      where
        p_er_g_wf      = lem_erase_env_wfenv g p_g_wf
        p_g_tybc       = lem_wf_tybc g b
        p_g_self_tybc  = lem_selfify_wf' g (tybc b) Base p_g_tybc p_g_wf (Bc b) (TBC g b)
        {-@ ev_transf :: th':CSub -> ProofOf(DenotesEnv (Cons (fresh_var g) (TRefn TBool Z refn) g) th')
                           -> ProofOf(EvalsTo (csubst th' (unbind 0 (fresh_var g) refn))  (Bc True))
                           -> ProofOf(EvalsTo (csubst th' (unbind 0 (fresh_var g) refn')) (Bc True)) @-}
        ev_transf :: CSub -> DenotesEnv -> EvalsTo -> EvalsTo
        ev_transf th' den_g'_th' ev_th'ref_tt = case den_g'_th' of
          (DExt _g th den_g_th y _tybc v den_thtybc_v)
            -> AddStep (App (App (AppT (Prim Eql) (tsubBV 0 v (tybc b))) v) (Bc b))
                       (App (App (Prim Eqv) v) (Bc b)) step1'' (Bc True) (ev_th'ref_tt
                   ? lem_csub_unbind_refn_bc  g th (y ? lem_binds_env_th g th den_g_th) v b)
                   ? lem_csub_unbind_refn'_bc g th (y ? lem_binds_env_th g th den_g_th) v b
                 where
                   step1   = EPrimT Eql (tsubBV 0 v (tybc b) ? lem_erase_tsubBV 0 v (tybc b))
                   step1'  = EApp1 (AppT (Prim Eql) (tsubBV 0 v (tybc b))) (Prim Eqv) step1 v
                   step1'' = EApp1 (App (AppT (Prim Eql) (tsubBV 0 v (tybc b))) v) (App (Prim Eqv) v) step1' (Bc b)
        refn           = App (App (Prim Eqv) (BV 0)) (Bc b)
        refn'          = App (App (AppT (Prim Eql) (tybc b)) (BV 0)) (Bc b)
        tybc_self_tybc = lem_subtype_repetition g p_er_g_wf TBool Z refn p_g_tybc refn' ev_transf
lem_exact_type_tbc g e t p_e_t       Star p_g_t p_g_wf = p_e_t ? ( self t e Star === t )

{-@ ple lem_exact_type_tic @-}
{-@ lem_exact_type_tic :: g:Env -> v:Value -> t:Type 
        -> { p_v_t:HasType | (propOf p_v_t == HasType g v t) && isTIC p_v_t } -> k:Kind
        -> ProofOf(WFType g t k) -> ProofOf(WFEnv g) -> ProofOf(HasType g v (self t v k)) @-}
lem_exact_type_tic :: Env -> Expr -> Type -> HasType -> Kind -> WFType -> WFEnv -> HasType
lem_exact_type_tic g e t (TIC _ n)   Base p_g_t p_g_wf 
  = TSub g (Ic n) (tyic n) (TIC g n) (self (tyic n) (Ic n) Base) Base p_g_self_tyic tyic_self_tyic
      where
        p_er_g_wf      = lem_erase_env_wfenv g p_g_wf
        p_g_tyic       = lem_wf_tyic g n
        p_g_self_tyic  = lem_selfify_wf' g (tyic n) Base p_g_tyic p_g_wf (Ic n) (TIC g n)
        {-@ ev_transf :: th':CSub -> ProofOf(DenotesEnv (Cons (fresh_var g) (TRefn TInt Z refn) g) th')
                           -> ProofOf(EvalsTo (csubst th' (unbind 0 (fresh_var g) refn))  (Bc True))
                           -> ProofOf(EvalsTo (csubst th' (unbind 0 (fresh_var g) refn')) (Bc True)) @-}
        ev_transf :: CSub -> DenotesEnv -> EvalsTo -> EvalsTo
        ev_transf th' den_g'_th' ev_th'ref_tt = case den_g'_th' of
          (DExt _g th den_g_th y _tybc v den_thtybc_v)
            -> AddStep (App (App (AppT (Prim Eql) (tsubBV 0 v (tyic n))) v) (Ic n))
                       (App (App (Prim Eq) v) (Ic n)) step1'' (Bc True) (ev_th'ref_tt
                   ? lem_csub_unbind_refn_ic  g th (y ? lem_binds_env_th g th den_g_th) v n)
                   ? lem_csub_unbind_refn'_ic g th (y ? lem_binds_env_th g th den_g_th) v n
                 where
                   step1   = EPrimT Eql (tsubBV 0 v (tyic n) ? lem_erase_tsubBV 0 v (tyic n))
                   step1'  = EApp1 (AppT (Prim Eql) (tsubBV 0 v (tyic n))) (Prim Eq) step1 v
                   step1'' = EApp1 (App (AppT (Prim Eql) (tsubBV 0 v (tyic n))) v) (App (Prim Eq) v) step1' (Ic n)
        refn           = App (App (Prim Eq) (BV 0)) (Ic n)
        refn'          = App (App (AppT (Prim Eql) (tyic n)) (BV 0)) (Ic n)
        tyic_self_tyic = lem_subtype_repetition g p_er_g_wf TInt Z refn p_g_tyic refn' ev_transf
lem_exact_type_tic g e t p_e_t       Star p_g_t p_g_wf = p_e_t ? ( self t e Star === t )
*)





(* PrimitiveSemantics.hs *)

(*
{-@ reflect intLeq @-}
intLeq :: Int -> Int -> Bool
intLeq n m = n <= m

{-@ reflect intEq @-}
intEq :: Int -> Int -> Bool
intEq n m = n == m

{-@ lemma_strengthen_semantics :: p:Pred -> b:Bool  -> ProofOf(EvalsTo p (Bc b))
                               -> q:Pred -> b':Bool -> ProofOf(EvalsTo q (Bc b'))
                               -> ProofOf(HasFType FEmpty p (FTBasic TBool))
                               -> ProofOf(EvalsTo (strengthen p q) (Bc (blAnd b b'))) / [esize p] @-}
lemma_strengthen_semantics :: Expr -> Bool -> EvalsTo -> Expr -> Bool -> EvalsTo 
                                   -> HasFType -> EvalsTo
lemma_strengthen_semantics (Conj p1 p2) b ev_p_b q b' ev_q_b' pf_p_bl = ev_pq_bb'
                           ? lem_evals_val_det (Conj p1 p2) (Bc b) ev_p_b (Bc (blAnd b1 b2)) ev_p_b1b2
                           ? lem_blAnd_assoc b1 b2 b'
  where
    (ConjRed _p1 v1 ev_p1_v1 _p2 v2 ev_p2_v2)
                = lemma_evals_conj_value p1 p2 (Bc b) ev_p_b
    (FTConj _ _ pf_p1_bl _ pf_p2_bl) = pf_p_bl
    pf_v1_bl    = lemma_many_preservation p1 (v1  ? lem_evals_pred p1 v1 ev_p1_v1)
                                  ev_p1_v1 (FTBasic TBool) pf_p1_bl
    pf_v2_bl    = lemma_many_preservation p2 (v2  ? lem_evals_pred p2 v2 ev_p2_v2)
                                  ev_p2_v2 (FTBasic TBool) pf_p2_bl
    (Bc b1)     = v1 ? lem_bool_values v1  pf_v1_bl
    (Bc b2)     = v2 ? lem_bool_values v2  pf_v2_bl
    ev_p_b1b2   = lemma_conj_semantics p1 b1 ev_p1_v1 p2 b2 ev_p2_v2 
    ev_p2q_b2b' = lemma_strengthen_semantics p2 b2 ev_p2_v2 q b' ev_q_b' pf_p2_bl
    ev_pq_bb'   = lemma_strengthen_semantics p1 b1 ev_p1_v1 (strengthen p2 q) (blAnd b2 b') 
                                             ev_p2q_b2b' pf_p1_bl
lemma_strengthen_semantics p            b ev_p_b q b' ev_q_b' pf_p_bl = ev_andpq
  where
    ev_andpq_1 = lemma_conj_both_many p (Bc b) ev_p_b q (Bc b') ev_q_b'
    ev_andpq   = lemma_add_step_after (Conj p q) (Conj (Bc b) (Bc b'))
                                      ev_andpq_1 (Bc (b && b')) (EConjV (Bc b) (Bc b'))

{-@ lemma_reduce_to_delta :: c:Prim -> p:Expr -> { v:Value | isCompat c v } -> ProofOf(EvalsTo p v)
                          -> ProofOf(EvalsTo (App (Prim c) p) (delta c v)) @-}
lemma_reduce_to_delta :: Prim -> Expr -> Expr -> EvalsTo -> EvalsTo
lemma_reduce_to_delta c p v ev_p_v = ev_appcp
  where
    ev_appcp_1 = lemma_app_many2 (Prim c) p v ev_p_v
    st_appcp_2 = EPrim c v
    ev_appcp   = lemma_add_step_after (App (Prim c) p) (App (Prim c) v) ev_appcp_1 (delta c v) st_appcp_2
  
{-@ lemma_or_semantics :: p:Expr -> b:Bool  -> ProofOf(EvalsTo p (Bc b))
                       -> q:Expr -> b':Bool -> ProofOf(EvalsTo q (Bc b'))
                       -> ProofOf(EvalsTo (App (App (Prim Or) p) q) (Bc (blOr b b'))) @-}
lemma_or_semantics :: Expr -> Bool -> EvalsTo -> Expr -> Bool -> EvalsTo -> EvalsTo
lemma_or_semantics p b ev_p_b q b' ev_q_b' = ev_orpq
  where
    ev_orp    = lemma_reduce_to_delta Or p (Bc b) ev_p_b
    ev_orpq_1 = lemma_app_both_many (App (Prim Or) p) (delta Or (Bc b)) ev_orp q (Bc b') ev_q_b'
    {-@ st_orpq_2 :: ProofOf(Step (App (delta Or (Bc b)) (Bc b')) (Bc (blOr b b'))) @-}
    st_orpq_2 = if b then ( EAppAbs 1 (Bc True) (Bc b') )
                     else ( EAppAbs 1 (BV 1)    (Bc b') )
    ev_orpq   = lemma_add_step_after (App (App (Prim Or) p) q) (App (delta Or (Bc b)) (Bc b'))
                                     ev_orpq_1 (Bc (b || b')) st_orpq_2


{-@ lemma_leq_semantics :: p:Expr -> n:Int -> ProofOf(EvalsTo p (Ic n))
                        -> q:Expr -> m:Int -> ProofOf(EvalsTo q (Ic m))
                        -> ProofOf(EvalsTo (App (App (Prim Leq) p) q) (Bc (intLeq n m))) @-}
lemma_leq_semantics :: Expr -> Int -> EvalsTo -> Expr -> Int -> EvalsTo -> EvalsTo
lemma_leq_semantics p n ev_p_n q m ev_q_m = ev_leqpq
  where
    ev_leqp    = lemma_reduce_to_delta Leq p (Ic n) ev_p_n
    ev_leqpq_1 = lemma_app_both_many (App (Prim Leq) p) (delta Leq (Ic n)) ev_leqp q (Ic m) ev_q_m
    ev_leqpq_2 = lemma_leqn_semantics n (Ic m) m (Refl (Ic m))
    ev_leqpq   = lemma_evals_trans (App (App (Prim Leq) p) q) (App (Prim (Leqn n)) (Ic m)) 
                                   (Bc (n <= m)) ev_leqpq_1 ev_leqpq_2

{-@ lemma_leqn_semantics :: n:Int -> q:Expr -> m:Int -> ProofOf(EvalsTo q (Ic m))
                         -> ProofOf(EvalsTo (App (Prim (Leqn n)) q) (Bc (intLeq n m))) @-}
lemma_leqn_semantics :: Int -> Expr -> Int -> EvalsTo -> EvalsTo
lemma_leqn_semantics n q m ev_q_m = lemma_reduce_to_delta (Leqn n) q (Ic m) ev_q_m
   
{-@ lemma_eq_semantics :: p:Expr -> n:Int -> ProofOf(EvalsTo p (Ic n))
                       -> q:Expr -> m:Int -> ProofOf(EvalsTo q (Ic m))
                       -> ProofOf(EvalsTo (App (App (Prim Eq) p) q) (Bc (intEq n m))) @-}
lemma_eq_semantics :: Expr -> Int -> EvalsTo -> Expr -> Int -> EvalsTo -> EvalsTo
lemma_eq_semantics p n ev_p_n q m ev_q_m = ev_eqpq
  where
    ev_eqp    = lemma_reduce_to_delta Eq p (Ic n) ev_p_n
    ev_eqpq_1 = lemma_app_both_many (App (Prim Eq) p) (delta Eq (Ic n)) ev_eqp q (Ic m) ev_q_m
    ev_eqpq_2 = lemma_eqn_semantics n (Ic m) m (Refl (Ic m))
    ev_eqpq   = lemma_evals_trans (App (App (Prim Eq) p) q) (App (Prim (Eqn n)) (Ic m)) 
                                   (Bc (n == m)) ev_eqpq_1 ev_eqpq_2

{-@ lemma_eqn_semantics :: n:Int -> q:Expr -> m:Int -> ProofOf(EvalsTo q (Ic m))
                        -> ProofOf(EvalsTo (App (Prim (Eqn n)) q) (Bc (intEq n m))) @-}
lemma_eqn_semantics :: Int -> Expr -> Int -> EvalsTo -> EvalsTo
lemma_eqn_semantics n q m ev_q_m = lemma_reduce_to_delta (Eqn n) q (Ic m) ev_q_m
   
--replace `reduce_eqv b b'` by `lemma_eqv_semantics (Bc b) b (Refl (Bc b)) (Bc b') ....
--replace `reduce_eq  n m`  by `lemma_eq_semantics (Ic n) ....

---------------------------------------------------------------------------
-- | BUILT-IN PRIMITIVES : Big-Step-style SEMANTICS for ty(c)'s refinement 
---------------------------------------------------------------------------


{-@ lemma_semantics_refn_eqv :: b:Bool -> b':Bool -> b'':Bool
                -> ProofOf(EvalsTo (App (App (Prim Eqv) (Bc b'')) (App (App (Prim Or) 
                                        (App (App (Prim And) (Bc b)) (Bc b')))
                                        (App (App (Prim And) (App (Prim Not) (Bc b))) (App (Prim Not) (Bc b')))))
                                   (Bc (blIff b'' (blIff b b'))) ) @-}
lemma_semantics_refn_eqv :: Bool -> Bool -> Bool -> EvalsTo
lemma_semantics_refn_eqv b b' b'' = reduce_eqv
  where
    reduce_left_and  = lemma_and_semantics (Bc b) b (Refl (Bc b)) (Bc b') b' (Refl (Bc b'))
    reduce_right_and = lemma_and_semantics (App (Prim Not) (Bc b)) (blNot b) 
                                           (lemma_not_semantics (Bc b) b (Refl (Bc b)))
                                           (App (Prim Not) (Bc b')) (blNot b')
                                           (lemma_not_semantics (Bc b') b' (Refl (Bc b')))
    reduce_or        = lemma_or_semantics (App (App (Prim And) (Bc b)) (Bc b')) (blAnd b b') reduce_left_and
                           (App (App (Prim And) (App (Prim Not) (Bc b))) (App (Prim Not) (Bc b'))) 
                           (blAnd (blNot b) (blNot b')) reduce_right_and
    reduce_eqv       = lemma_eqv_semantics (Bc b'') b'' (Refl (Bc b'')) 
                           (App (App (Prim Or) (App (App (Prim And) (Bc b)) (Bc b')))
                                 (App (App (Prim And) (App (Prim Not) (Bc b))) (App (Prim Not) (Bc b'))))
                           (blIff b b') reduce_or

{-@ reduce_eqv_tt :: b:Bool -> b':Bool -> { pf:_ | propOf pf ==
      EvalsTo (subBV 0 (Bc (blIff b b')) (subBV 2 (Bc b') (subBV 1 (Bc b) (refn_pred Eqv)))) (Bc True) } @-}
reduce_eqv_tt :: Bool -> Bool -> EvalsTo
reduce_eqv_tt b b' = lemma_semantics_refn_eqv b b' (blIff b b')

{-@ lemma_semantics_refn_leq :: n:Int -> m:Int -> b'':Bool
                -> ProofOf(EvalsTo (App (App (Prim Eqv) (Bc b'')) (App (App (Prim Leq) (Ic n)) (Ic m))) 
                                   (Bc (blIff b'' (intLeq n m)))) @-}
lemma_semantics_refn_leq :: Int -> Int -> Bool -> EvalsTo
lemma_semantics_refn_leq n m b'' = reduce_eqv
  where
    reduce_leq = lemma_leq_semantics (Ic n) n (Refl (Ic n)) (Ic m) m (Refl (Ic m))
    reduce_eqv = lemma_eqv_semantics (Bc b'') b'' (Refl (Bc b''))
                                     (App (App (Prim Leq) (Ic n)) (Ic m)) (intLeq n m) reduce_leq
  
{-@ reduce_leq_tt :: n:Int -> m:Int -> { pf:_ | propOf pf == 
      EvalsTo (subBV 0 (Bc (intLeq n m)) (subBV 2 (Ic m) (subBV 1 (Ic n) (refn_pred Leq)))) (Bc True) } @-}
reduce_leq_tt :: Int -> Int -> EvalsTo
reduce_leq_tt n m = lemma_semantics_refn_leq n m (intLeq n m)

{-@ reduce_leqn_tt :: n:Int -> m:Int -> { pf:_ | propOf pf ==
      EvalsTo (subBV 0 (Bc (intLeq n m)) (subBV 2 (Ic m) (refn_pred (Leqn n)))) (Bc True) } @-}
reduce_leqn_tt :: Int -> Int -> EvalsTo
reduce_leqn_tt n m = reduce_leq_tt n m

{-@ lemma_semantics_refn_eq :: n:Int -> m:Int -> b'':Bool
                -> ProofOf(EvalsTo (App (App (Prim Eqv) (Bc b'')) (App (App (Prim Eq) (Ic n)) (Ic m))) 
                                   (Bc (blIff b'' (intEq n m)))) @-}
lemma_semantics_refn_eq :: Int -> Int -> Bool -> EvalsTo
lemma_semantics_refn_eq n m b'' = reduce_eqv
  where
    reduce_eq  = lemma_eq_semantics (Ic n) n (Refl (Ic n)) (Ic m) m (Refl (Ic m))
    reduce_eqv = lemma_eqv_semantics (Bc b'') b'' (Refl (Bc b''))
                                     (App (App (Prim Eq) (Ic n)) (Ic m)) (intEq n m) reduce_eq
  
{-@ reduce_eq_tt :: n:Int -> m:Int -> { pf:_ | propOf pf == 
      EvalsTo (subBV 0 (Bc (intEq n m)) (subBV 2 (Ic m) (subBV 1 (Ic n) (refn_pred Eq)))) (Bc True) } @-}
reduce_eq_tt :: Int -> Int -> EvalsTo
reduce_eq_tt n m = lemma_semantics_refn_eq n m (intEq n m)

{-@ reduce_eqn_tt :: n:Int -> m:Int -> { pf:_ | propOf pf ==
      EvalsTo (subBV 0 (Bc (intEq n m)) (subBV 2 (Ic m) (refn_pred (Eqn n)))) (Bc True) } @-}
reduce_eqn_tt :: Int -> Int -> EvalsTo
reduce_eqn_tt n m = reduce_eq_tt n m

*)*) 