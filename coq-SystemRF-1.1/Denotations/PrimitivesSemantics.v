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

Require Import Nat.

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

Lemma lem_step_imp_tt : Step (App (Prim Imp) (Bc true)) (Lambda (BV 0)).
Proof. assert (isCompat Imp (Bc true)) as pfB by apply isCpt_Imp.
  assert (delta Imp (Bc true) pfB = Lambda (BV 0))
      by (pose proof (delta_delta' Imp (Bc true) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.

Lemma lem_step_imp_ff : Step (App (Prim Imp) (Bc false)) (Lambda (Bc true)).
Proof. assert (isCompat Imp (Bc false)) as pfB by apply isCpt_Imp.
  assert (delta Imp (Bc false) pfB = Lambda (Bc true))
      by (pose proof (delta_delta' Imp (Bc false) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.  

Lemma lem_step_leq : forall (n:nat), 
    Step (App (Prim Leq) (Ic n)) (Prim (Leqn n)).
Proof. intro n. assert (isCompat Leq (Ic n)) as pfB by apply isCpt_Leq.
  assert (delta Leq (Ic n) pfB = Prim (Leqn n))
      by (pose proof (delta_delta' Leq (Ic n) pfB) as D;
          simpl in D; injection D; trivial ). 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.  

Lemma lem_step_leqn : forall (n m:nat), 
    Step (App (Prim (Leqn n)) (Ic m)) (Bc (n <=? m)).
Proof. intros n m. assert (isCompat (Leqn n) (Ic m)) as pfB by apply isCpt_Leqn.
  assert (delta (Leqn n) (Ic m) pfB = (Bc (n <=? m)))
      by (pose proof (delta_delta' (Leqn n) (Ic m) pfB) as D;
          simpl in D; injection D; trivial ). 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.  
  
Lemma lem_step_eq : forall (n:nat), 
    Step (App (Prim Eq) (Ic n)) (Prim (Eqn n)).
Proof. intro n. assert (isCompat Eq (Ic n)) as pfB by apply isCpt_Eq.
  assert (delta Eq (Ic n) pfB = Prim (Eqn n))
      by (pose proof (delta_delta' Eq (Ic n) pfB) as D;
          simpl in D; injection D; trivial ). 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.    

Lemma lem_step_eqn : forall (n m:nat), 
    Step (App (Prim (Eqn n)) (Ic m)) (Bc (n =? m)).
Proof. intros n m. assert (isCompat (Eqn n) (Ic m)) as pfB by apply isCpt_Eqn.
  assert (delta (Eqn n) (Ic m) pfB = (Bc (n =? m)))
      by (pose proof (delta_delta' (Eqn n) (Ic m) pfB) as D;
          simpl in D; injection D; trivial ). 
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

Lemma lemma_and_semantics : forall (p q:expr) (b b':bool),
    EvalsTo p (Bc b) -> EvalsTo q (Bc b')
        -> EvalsTo (App (App (Prim And) p) q) (Bc (b && b')).
Proof. intros; apply lemma_evals_trans with (App (App (Prim And) (Bc b)) q).
  - apply lemma_app_many; apply lemma_app_many2; simpl; trivial.
  - destruct b.
    * apply lemma_evals_trans with (App (Lambda (BV 0)) (Bc b'));
      try apply lemma_app_both_many; destruct b'; simpl; trivial;
      apply lem_step_evals; apply lem_step_and_tt || apply EAppAbs; 
      simpl; trivial.
    * apply lemma_evals_trans with (App (Lambda (Bc false)) (Bc b'));
      try apply lemma_app_both_many; try apply H0;
      try apply lem_step_evals; try apply lem_step_and_ff;
      try apply EAppAbs; simpl; trivial. 
  Qed.

Lemma lemma_or_semantics : forall (p q:expr) (b b':bool),
    EvalsTo p (Bc b) -> EvalsTo q (Bc b')
        -> EvalsTo (App (App (Prim Or) p) q) (Bc (b || b')).
Proof. intros; apply lemma_evals_trans with (App (App (Prim Or) (Bc b)) q).
  - apply lemma_app_many; apply lemma_app_many2; simpl; trivial.
  - destruct b.
    * apply lemma_evals_trans with (App (Lambda (Bc true)) (Bc b'));
      try apply lemma_app_both_many; try apply H0;
      try apply lem_step_evals; try apply lem_step_or_tt;
      try apply EAppAbs; simpl; trivial. 
    * apply lemma_evals_trans with (App (Lambda (BV 0)) (Bc b'));
      try apply lemma_app_both_many; destruct b'; simpl; trivial;
      apply lem_step_evals; apply lem_step_or_ff || apply EAppAbs; 
      simpl; trivial.
  Qed.




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
    EvalsTo (App (App (Prim Eqv) (App (App (Prim And) (Bc b)) (Bc b'))) (Bc b'')) 
            (Bc (Bool.eqb (andb b b') b'')).
Proof. intros. apply lemma_eqv_semantics; try apply lemma_and_semantics;
  apply Refl. Qed.

Lemma lemma_semantics_refn_or : forall (b b' b'' : bool), 
    EvalsTo (App (App (Prim Eqv) (App (App (Prim Or) (Bc b)) (Bc b'))) (Bc b''))
            (Bc (Bool.eqb (orb b b') b'')).
Proof. intros. apply lemma_eqv_semantics; try apply lemma_or_semantics;
  apply Refl. Qed.

(*
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
*)

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

(* PrimitiveSemantics.hs *)
(*
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

*)