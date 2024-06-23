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

Require Import ZArith.

Lemma lem_step_and_tt : Step (App (Prim And) (Bc true)) (Lambda (BV 0)).
Proof. assert (isCompat And (Bc true)) as pfB by apply isCpt_And;
  assert (delta And (Bc true) pfB = Lambda (BV 0))
      by (pose proof (delta_delta' And (Bc true) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; constructor. Qed.

Lemma lem_step_and_ff : Step (App (Prim And) (Bc false)) (Lambda (Bc false)).
Proof. assert (isCompat And (Bc false)) as pfB by apply isCpt_And;
  assert (delta And (Bc false) pfB = Lambda (Bc false))
      by (pose proof (delta_delta' And (Bc false) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; constructor. Qed.

Lemma lem_step_or_tt : Step (App (Prim Or) (Bc true)) (Lambda (Bc true)).
Proof. assert (isCompat Or (Bc true)) as pfB by apply isCpt_Or;
  assert (delta Or (Bc true) pfB = Lambda (Bc true))
      by (pose proof (delta_delta' Or (Bc true) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; constructor. Qed.
  
Lemma lem_step_or_ff : Step (App (Prim Or) (Bc false)) (Lambda (BV 0)).
Proof. assert (isCompat Or (Bc false)) as pfB by apply isCpt_Or;
  assert (delta Or (Bc false) pfB = Lambda (BV 0))
      by (pose proof (delta_delta' Or (Bc false) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; constructor. Qed.

Lemma lem_step_not : forall (b:bool), 
    Step (App (Prim Not) (Bc b)) (Bc (negb b)).
Proof. intro b. assert (isCompat Not (Bc b)) as pfB by apply isCpt_Not.
  assert (delta Not (Bc b) pfB = Bc (negb b))
      by (pose proof (delta_delta' Not (Bc b) pfB) as D;
          destruct b; simpl in D; injection D; trivial ). 
  rewrite <- H; apply EPrim; simpl; constructor. Qed.

Lemma lem_step_eqv_tt : Step (App (Prim Eqv) (Bc true)) (Lambda (BV 0)).
Proof. assert (isCompat Eqv (Bc true)) as pfB by apply isCpt_Eqv.
  assert (delta Eqv (Bc true) pfB = Lambda (BV 0))
      by (pose proof (delta_delta' Eqv (Bc true) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; constructor. Qed.

Lemma lem_step_eqv_ff : Step (App (Prim Eqv) (Bc false)) (Prim Not).
Proof. assert (isCompat Eqv (Bc false)) as pfB by apply isCpt_Eqv.
  assert (delta Eqv (Bc false) pfB = Prim Not)
      by (pose proof (delta_delta' Eqv (Bc false) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; constructor. Qed.  

Lemma lem_step_imp_tt : Step (App (Prim Imp) (Bc true)) (Lambda (BV 0)).
Proof. assert (isCompat Imp (Bc true)) as pfB by apply isCpt_Imp.
  assert (delta Imp (Bc true) pfB = Lambda (BV 0))
      by (pose proof (delta_delta' Imp (Bc true) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; constructor. Qed.

Lemma lem_step_imp_ff : Step (App (Prim Imp) (Bc false)) (Lambda (Bc true)).
Proof. assert (isCompat Imp (Bc false)) as pfB by apply isCpt_Imp.
  assert (delta Imp (Bc false) pfB = Lambda (Bc true))
      by (pose proof (delta_delta' Imp (Bc false) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; constructor. Qed.  

Lemma lem_step_leq : forall (n:Z), 
    Step (App (Prim Leq) (Ic n)) (Prim (Leqn n)).
Proof. intro n. assert (isCompat Leq (Ic n)) as pfB by apply isCpt_Leq.
  assert (delta Leq (Ic n) pfB = Prim (Leqn n))
      by (pose proof (delta_delta' Leq (Ic n) pfB) as D;
          simpl in D; injection D; trivial ). 
  rewrite <- H; apply EPrim; simpl; constructor. Qed.  

Lemma lem_step_leqn : forall (n m:Z), 
    Step (App (Prim (Leqn n)) (Ic m)) (Bc (Z.leb n m)).
Proof. intros n m. assert (isCompat (Leqn n) (Ic m)) as pfB by apply isCpt_Leqn.
  assert (delta (Leqn n) (Ic m) pfB = (Bc (Z.leb n m)))
      by (pose proof (delta_delta' (Leqn n) (Ic m) pfB) as D;
          simpl in D; injection D; trivial ). 
  rewrite <- H; apply EPrim; simpl; constructor. Qed.  
  
Lemma lem_step_eq : forall (n:Z), 
    Step (App (Prim Eq) (Ic n)) (Prim (Eqn n)).
Proof. intro n. assert (isCompat Eq (Ic n)) as pfB by apply isCpt_Eq.
  assert (delta Eq (Ic n) pfB = Prim (Eqn n))
      by (pose proof (delta_delta' Eq (Ic n) pfB) as D;
          simpl in D; injection D; trivial ). 
  rewrite <- H; apply EPrim; simpl; constructor. Qed.    

Lemma lem_step_eqn : forall (n m:Z), 
    Step (App (Prim (Eqn n)) (Ic m)) (Bc (Z.eqb n m)).
Proof. intros n m. assert (isCompat (Eqn n) (Ic m)) as pfB by apply isCpt_Eqn.
  assert (delta (Eqn n) (Ic m) pfB = (Bc (Z.eqb n m)))
      by (pose proof (delta_delta' (Eqn n) (Ic m) pfB) as D;
          simpl in D; injection D; trivial ). 
  rewrite <- H; apply EPrim; simpl; constructor. Qed.  

Lemma lem_step_succ : forall (n:Z), 
    Step (App (Prim Succ) (Ic n)) (Ic (1+n)).
Proof. intro n. assert (isCompat Succ (Ic n)) as pfB by apply isCpt_Succ.
  assert (delta Succ (Ic n) pfB = (Ic (1+n)))
      by (pose proof (delta_delta' Succ (Ic n) pfB) as D;
          simpl in D; injection D; trivial ). 
  rewrite <- H; apply EPrim; simpl; constructor. Qed.  


Lemma lem_step_leql_tbool : forall (ps:preds), 
    Step (AppT (Prim Leql) (TRefn TBool ps)) (Prim Imp).
Proof. intro ps;
  assert (isCompatT Leql (TRefn TBool ps)) as pfB
      by (apply isCptT_LeqlB; auto);
  assert (Prim Imp = deltaT Leql (TRefn TBool ps) pfB)
      by (pose proof (deltaT_deltaT' Leql (TRefn TBool ps) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite H; apply EPrimT; simpl; exact I. Qed.

Lemma lem_step_leql_tint : forall (ps:preds), 
    Step (AppT (Prim Leql) (TRefn TInt ps)) (Prim Leq).
Proof. intro ps;
  assert (isCompatT Leql (TRefn TInt ps)) as pfZ
      by (apply isCptT_LeqlZ; auto);
  assert (Prim Leq = deltaT Leql (TRefn TInt ps) pfZ)
      by (pose proof (deltaT_deltaT' Leql (TRefn TInt ps) pfZ) as D;
          simpl in D; injection D; trivial ); 
  rewrite H; apply EPrimT; simpl; exact I. Qed.

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

Lemma lem_step_length_nil : forall (t:type), 
    Step (App (AppT (Prim Length) t) Nil) (Ic 0).
Proof. intro t;
  assert (isCompatM Length Nil) as pfL
      by (apply isCptM_LNil).
  assert (Some (Ic 0) = Some (deltaM Length Nil pfL))
      by (rewrite deltaM_deltaM'; simpl; reflexivity);
  injection H as H; rewrite H; apply EPrimM; apply val_Nil. Qed. 
    
Lemma lem_step_length_cons : forall (t:type) (vH vT n': expr), 
  isValue vH -> isValue vT -> Step (App (AppT (Prim Length) t) vT) n' 
        -> Step (App (AppT (Prim Length) t) (Cons vH vT)) 
                (App (Prim Succ) n').
Proof. intros; inversion H1;
  try apply lem_value_stuck in H5; try apply val_Len; try contradiction;
  try apply lem_value_stuck in H6; try apply H0; try contradiction;    
  assert (isCompatM Length (Cons vH vT)) as pfL
      by (apply isCptM_LCons; trivial).
  assert (Some (App (Prim Succ) n') = Some (deltaM Length (Cons vH vT) pfL))
      by (rewrite deltaM_deltaM'; simpl; rewrite <- deltaM_deltaM' with Length vT pf;
          rewrite H3; reflexivity).
  injection H7 as H7; rewrite H3; rewrite H7; apply EPrimM; 
  apply val_Cons; trivial. Qed. 


Lemma lemma_and_semantics : forall (p q:expr) (b b':bool),
    EvalsTo p (Bc b) -> EvalsTo q (Bc b')
        -> EvalsTo (App (App (Prim And) p) q) (Bc (b && b')).
Proof. intros; apply lemma_evals_trans with (App (App (Prim And) (Bc b)) q).
  - apply lemma_app_many; apply lemma_app_many2; constructor || trivial.
  - destruct b.
    * apply lemma_evals_trans with (App (Lambda (BV 0)) (Bc b'));
      try apply lemma_app_both_many; destruct b'; try constructor; trivial;
      apply lem_step_evals; apply lem_step_and_tt || apply EAppAbs; constructor.
    * apply lemma_evals_trans with (App (Lambda (Bc false)) (Bc b'));
      try apply lemma_app_both_many; try apply H0;
      try apply lem_step_evals; try apply lem_step_and_ff;
      try apply EAppAbs; simpl; trivial || constructor. 
  Qed.

Lemma lemma_or_semantics : forall (p q:expr) (b b':bool),
    EvalsTo p (Bc b) -> EvalsTo q (Bc b')
        -> EvalsTo (App (App (Prim Or) p) q) (Bc (b || b')).
Proof. intros; apply lemma_evals_trans with (App (App (Prim Or) (Bc b)) q).
  - apply lemma_app_many; apply lemma_app_many2; constructor || trivial.
  - destruct b.
    * apply lemma_evals_trans with (App (Lambda (Bc true)) (Bc b'));
      try apply lemma_app_both_many; try apply H0;
      try apply lem_step_evals; try apply lem_step_or_tt;
      try apply EAppAbs; simpl; trivial || constructor.  
    * apply lemma_evals_trans with (App (Lambda (BV 0)) (Bc b'));
      try apply lemma_app_both_many; destruct b'; try constructor; trivial;
      apply lem_step_evals; apply lem_step_or_ff || apply EAppAbs;
      trivial || constructor. 
  Qed.

Lemma lemma_not_semantics : forall (p:expr) (b:bool),
    EvalsTo p (Bc b) -> EvalsTo (App (Prim Not) p) (Bc (negb b)).
Proof. intros; apply lemma_evals_trans with (App (Prim Not) (Bc b));
  try apply lemma_app_many2;
  try (apply lem_step_evals; apply lem_step_not); trivial || constructor.  
  Qed.

Lemma lemma_eqv_semantics : forall (p q:expr) (b b':bool),
    EvalsTo p (Bc b) -> EvalsTo q (Bc b') 
        -> EvalsTo (App (App (Prim Eqv) p) q) (Bc (Bool.eqb b b')).
Proof. intros; apply lemma_evals_trans with (App (App (Prim Eqv) (Bc b)) q).
  - apply lemma_app_many; apply lemma_app_many2; constructor || trivial.
  - destruct b.
    * apply lemma_evals_trans with (App (Lambda (BV 0)) (Bc b'));
      try apply lemma_app_both_many; destruct b'; try constructor; trivial;
      apply lem_step_evals; apply lem_step_eqv_tt || apply EAppAbs; 
      trivial || constructor. 
    * apply lemma_evals_trans with (App (Prim Not) (Bc b'));
      try apply lemma_app_both_many; destruct b'; try constructor; trivial;
      apply lem_step_evals; apply lem_step_eqv_ff || apply lem_step_not. 
  Qed.
  
Lemma lemma_imp_semantics : forall (p q:expr) (b b':bool),
    EvalsTo p (Bc b) -> EvalsTo q (Bc b') 
        -> EvalsTo (App (App (Prim Imp) p) q) (Bc (implb b b')).
Proof. intros; apply lemma_evals_trans with (App (App (Prim Imp) (Bc b)) q).
  - apply lemma_app_many; apply lemma_app_many2; constructor || trivial.
  - destruct b.
    * apply lemma_evals_trans with (App (Lambda (BV 0)) (Bc b'));
      try apply lemma_app_both_many; destruct b'; try constructor; trivial;
      apply lem_step_evals; apply lem_step_imp_tt || apply EAppAbs; 
      trivial || constructor.  
    * apply lemma_evals_trans with (App (Lambda (Bc true)) (Bc b'));
      try apply lemma_app_both_many; destruct b'; try constructor; trivial;
      apply lem_step_evals; apply lem_step_imp_ff || apply EAppAbs;
      trivial || constructor.  
  Qed.

Lemma lemma_leq_semantics : forall (p q:expr) (n m:Z),
    EvalsTo p (Ic n) -> EvalsTo q (Ic m)
        -> EvalsTo (App (App (Prim Leq) p) q) (Bc (Z.leb n m)).
Proof. intros; apply lemma_evals_trans with (App (App (Prim Leq) (Ic n)) q).
  - apply lemma_app_many; apply lemma_app_many2; constructor || trivial.
  - apply lemma_evals_trans with (App (Prim (Leqn n)) (Ic m));
    try apply lemma_app_both_many; try constructor; trivial;
    apply lem_step_evals; apply lem_step_leq || apply lem_step_leqn.
  Qed.
  
Lemma lemma_leqn_semantics : forall (q:expr) (n m:Z),
    EvalsTo q (Ic m) -> EvalsTo (App (Prim (Leqn n)) q) (Bc (Z.leb n m)).
Proof. intros; apply lemma_evals_trans with (App (Prim (Leqn n)) (Ic m));
  try apply lemma_app_many2; trivial; try constructor;
  apply lem_step_evals; apply lem_step_leqn. Qed.
  
Lemma lemma_eq_semantics : forall (p q:expr) (n m:Z),
    EvalsTo p (Ic n) -> EvalsTo q (Ic m)
        -> EvalsTo (App (App (Prim Eq) p) q) (Bc (Z.eqb n m)).
Proof. intros; apply lemma_evals_trans with (App (App (Prim Eq) (Ic n)) q).
  - apply lemma_app_many; apply lemma_app_many2; constructor || trivial.
  - apply lemma_evals_trans with (App (Prim (Eqn n)) (Ic m));
    try apply lemma_app_both_many; try constructor; trivial;
    apply lem_step_evals; apply lem_step_eq || apply lem_step_eqn.
  Qed.
    
Lemma lemma_eqn_semantics : forall (q:expr) (n m:Z),
    EvalsTo q (Ic m) -> EvalsTo (App (Prim (Eqn n)) q) (Bc (Z.eqb n m)).
Proof. intros; apply lemma_evals_trans with (App (Prim (Eqn n)) (Ic m));
  try apply lemma_app_many2; trivial; try constructor;
  apply lem_step_evals; apply lem_step_eqn. Qed.

Lemma lemma_succ_semantics : forall (p:expr) (n:Z),
    EvalsTo p (Ic n) -> EvalsTo (App (Prim Succ) p) (Ic (1+n)).
Proof. intros; apply lemma_evals_trans with (App (Prim Succ) (Ic n));
  try apply lemma_app_many2; trivial; try constructor;
  apply lem_step_evals; apply lem_step_succ. Qed.

Lemma lemma_leql_bool_semantics : forall (p q:expr) (b b':bool),
    EvalsTo p (Bc b) -> EvalsTo q (Bc b')  
        -> EvalsTo (App (App (AppT (Prim Leql) (TRefn TBool PEmpty)) p) q) (Bc (implb b b')).
Proof. intros. apply lemma_evals_trans with (App (App (Prim Imp) p) q).
  - apply lem_step_evals; apply EApp1; apply EApp1;
    apply lem_step_leql_tbool.
  - apply lemma_imp_semantics; trivial.
  Qed.

Lemma lemma_leql_int_semantics : forall (p q:expr) (n m:Z),
    EvalsTo p (Ic n) -> EvalsTo q (Ic m)  
        -> EvalsTo (App (App (AppT (Prim Leql) (TRefn TInt PEmpty)) p) q) (Bc (Z.leb n m)).
Proof. intros. apply lemma_evals_trans with (App (App (Prim Leq) p) q).
  - apply lem_step_evals; apply EApp1; apply EApp1;
    apply lem_step_leql_tint.
  - apply lemma_leq_semantics; trivial.
  Qed.

Lemma lemma_eql_bool_semantics : forall (p q:expr) (b b':bool),
    EvalsTo p (Bc b) -> EvalsTo q (Bc b')  
        -> EvalsTo (App (App (AppT (Prim Eql) (TRefn TBool PEmpty)) p) q) (Bc (Bool.eqb b b')).
Proof. intros. apply lemma_evals_trans with (App (App (Prim Eqv) p) q).
  - apply lem_step_evals; apply EApp1; apply EApp1;
    apply lem_step_eql_tbool.
  - apply lemma_eqv_semantics; trivial.
  Qed.

Lemma lemma_eql_int_semantics : forall (p q:expr) (n m:Z),
    EvalsTo p (Ic n) -> EvalsTo q (Ic m)  
        -> EvalsTo (App (App (AppT (Prim Eql) (TRefn TInt PEmpty)) p) q) (Bc (Z.eqb n m)).
Proof. intros. apply lemma_evals_trans with (App (App (Prim Eq) p) q).
  - apply lem_step_evals; apply EApp1; apply EApp1;
    apply lem_step_eql_tint.
  - apply lemma_eq_semantics; trivial.
  Qed.

Lemma lemma_length_nil_semantics : forall (t:type) (p:expr),
    EvalsTo p Nil -> EvalsTo (App (AppT (Prim Length) t) p) (Ic 0).
Proof. intros; apply lemma_evals_trans with (App (AppT (Prim Length) t) Nil).
  - apply lemma_app_many2; constructor || trivial.
  - apply lem_step_evals; apply lem_step_length_nil.
  Qed.

Lemma lemma_length_cons_semantics : forall (t:type) (p vH vT:expr) (n:Z),
    isValue vH -> isValue vT 
        -> EvalsTo p (Cons vH vT) -> EvalsTo (App (AppT (Prim Length) t) vT) (Ic n)
        -> EvalsTo (App (AppT (Prim Length) t) p) (Ic (1+n)).
Proof. intros; apply lemma_evals_trans with (App (AppT (Prim Length) t) (Cons vH vT)).
  - apply lemma_app_many2; constructor || trivial.
  - apply lemma_evals_trans with (App (Prim Succ) (Ic n));
    try (apply lem_step_evals; apply lem_step_succ).
    inversion H2; apply lemma_evals_trans with (App (Prim Succ) e2);
    try (apply lem_step_evals; apply lem_step_length_cons);
    try apply lemma_app_many2; try apply val_Prm; trivial.
  Qed.

Lemma lemma_length_list_semantics : forall (t:type) (v:expr),
    isValue v -> isList v -> 
        exists n, EvalsTo (App (AppT (Prim Length) t) v) (Ic n).
Proof. intro t; induction v; intros val lst; simpl in lst; try contradiction.
  - exists 0%Z; apply lemma_length_nil_semantics; apply Refl.
  - inversion val; destruct IHv2 as [n lenv2]; trivial.
    exists (1+n)%Z; apply lemma_length_cons_semantics with v1 v2;
    try apply Refl; trivial.
  Qed.

(* ---------------------------------------------------------------------------
   -- | BUILT-IN PRIMITIVES : Big-Step-style SEMANTICS for ty(c)'s refinement 
   --------------------------------------------------------------------------- *)

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

Lemma lemma_semantics_refn_not : forall (b b' : bool), 
    EvalsTo (App (App (Prim Eqv) (App (Prim Not) (Bc b))) (Bc b'))
            (Bc (Bool.eqb (negb b) b')).
Proof. intros; apply lemma_eqv_semantics; try apply lemma_not_semantics;
  apply Refl. Qed.
  
Lemma lemma_semantics_refn_eqv  : forall (b b' b'' : bool), 
    EvalsTo (App (App (Prim Eqv) (App (App (Prim Eqv) (Bc b)) (Bc b'))) (Bc b''))
            (Bc (Bool.eqb (Bool.eqb b b') b'')).
Proof. intros; repeat apply lemma_eqv_semantics; apply Refl. Qed.

Lemma lemma_semantics_refn_imp  : forall (b b' b'' : bool), 
    EvalsTo (App (App (Prim Eqv) (App (App (Prim Imp) (Bc b)) (Bc b'))) (Bc b''))
            (Bc (Bool.eqb (implb b b') b'')).
Proof. intros. apply lemma_eqv_semantics; try apply lemma_imp_semantics;
  apply Refl. Qed.      

Lemma lemma_semantics_refn_leq : forall (n m : Z) (b'':bool),
    EvalsTo (App (App (Prim Eqv) (App (App (Prim Leq) (Ic n)) (Ic m))) (Bc b''))
            (Bc (Bool.eqb (Z.leb n m) b'')).
Proof. intros. apply lemma_eqv_semantics; try apply lemma_leq_semantics;
  apply Refl. Qed.

Lemma lemma_semantics_refn_leqn : forall (n m : Z) (b'':bool),
    EvalsTo (App (App (Prim Eqv) (App (Prim (Leqn n)) (Ic m))) (Bc b''))
            (Bc (Bool.eqb (Z.leb n m) b'')).
Proof. intros. apply lemma_eqv_semantics; try apply lemma_leqn_semantics;
  apply Refl. Qed.

Lemma lemma_semantics_refn_eq : forall (n m : Z) (b'':bool),
    EvalsTo (App (App (Prim Eqv) (App (App (Prim Eq) (Ic n)) (Ic m))) (Bc b''))
            (Bc (Bool.eqb (Z.eqb n m) b'')).
Proof. intros. apply lemma_eqv_semantics; try apply lemma_eq_semantics;
  apply Refl. Qed.

Lemma lemma_semantics_refn_eqn : forall (n m : Z) (b'':bool),
    EvalsTo (App (App (Prim Eqv) (App (Prim (Eqn n)) (Ic m))) (Bc b''))
            (Bc (Bool.eqb (Z.eqb n m) b'')).
Proof. intros. apply lemma_eqv_semantics; try apply lemma_eqn_semantics;
  apply Refl. Qed.

Lemma lemma_semantics_refn_succ : forall (n n': Z) ,
    EvalsTo (App (App (Prim Eq) (App (Prim Succ) (Ic n'))) (Ic n))
            (Bc (Z.eqb (1+n') n)).
Proof. intros; apply lemma_eq_semantics;
  try apply lemma_succ_semantics; apply Refl. Qed.

Lemma lemma_semantics_refn_length_nil : forall (t:type),
    EvalsTo (App (App (Prim Eq) (Ic BinNums.Z0)) 
                 (App (AppT (Prim Length) t) Nil)) 
            (Bc true).
Proof. intros; apply lemma_evals_trans with (Bc (Z.eqb 0 0));
  try apply lemma_eq_semantics; try apply lemma_length_nil_semantics;
  apply Refl. Qed.

Lemma lemma_semantics_refn_length_cons : forall (t:type) (vH vT:expr),
    isValue (Cons vH vT) -> isList (Cons vH vT)
      -> EvalsTo (App (App (Prim Eq) (App (Prim Succ) (App (AppT (Prim Length) t) vT))) 
                      (App (AppT (Prim Length) t) (Cons vH vT))) 
                 (Bc true) .
Proof. intros; inversion H; simpl in H0;
  apply lemma_length_list_semantics with t vT in H0 as ev_lenvT; try apply H4;
  destruct ev_lenvT as [n ev_lenvT_n];
  apply lemma_evals_trans with (Bc (Z.eqb (1+n) (1+n)));
  try apply lemma_eq_semantics; try apply lemma_succ_semantics;
  try apply lemma_length_cons_semantics with vH vT;
  assert (1+n =? 1+n = true)%Z by (apply Z.eqb_eq; reflexivity); 
  try rewrite H5; try apply Refl; trivial.
  Qed.