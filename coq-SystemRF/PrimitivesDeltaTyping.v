Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.Semantics.
(*import SystemFWellFormedness*)
Require Import SystemRF.SystemFTyping.
(*import BasicPropsSubstitution*)
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.PrimitivesFTyping.
Require Import SystemRF.PrimitivesWFType.
(*import BasicPropsWellFormedness         --(lem_wffunc_for_wf_tfunc,lem_wfpoly_for_wf_tpoly)*)
Require Import SystemRF.Typing.
Require Import SystemRF.LemmasWellFormedness.
(*import SubstitutionLemmaWF*)
(*import SubstitutionLemmaWFTV*)
Require Import SystemRF.LemmasTyping.
Require Import SystemRF.LemmasSubtyping.
Require Import SystemRF.LemmasExactness. (* poss remove *)
Require Import SystemRF.SubstitutionLemmaTyp.
Require Import SystemRF.SubstitutionLemmaTypTV.
Require Import SystemRF.LemmasTransitive.
(*import LemmasInversion*)

(* -- Lemma. Typing of \delta(c,v) and \delta_T(c,t) *)
Lemma lem_delta_ty'c : forall (c:prim) (v:expr),
    ~ isPoly c -> isValue v -> Hastype Empty v (intype c)
               -> exists e, Some e = delta' c v /\ Hastype Empty e (tsubBV v (ty' c)).
Proof. intros c v np val p_v_inc; destruct c eqn:C;
  simpl in np; try contradiction;
  apply lem_typing_hasftype in p_v_inc as Hv; try apply WFEEmpty;
  simpl in Hv; 
  try apply (lem_bool_values v val) in Hv;
  try apply (lem_int_values v val) in Hv;
  destruct v eqn:V; simpl in Hv; try contradiction;
  assert (isCompat c v) as pf by (rewrite C; rewrite V; constructor);
    rewrite C in pf; rewrite V in pf;
(*  assert (isCompat And (Bc true))  as pfAT by constructor;
  assert (isCompat And (Bc false)) as pfAF by constructor;
  assert (isCompat Or  (Bc true))  as pfOT by constructor;
  assert (isCompat Or  (Bc false)) as pfOF by constructor;
  assert (isCompat Not (Bc true))  as pfNT by constructor;
  assert (isCompat Not (Bc false)) as pfNF by constructor; *)
  assert (forall m:nat, isCompat Leq (Ic m)) as pfL by constructor;
  assert (forall m:nat, isCompat Eq  (Ic m)) as pfE by constructor;
  assert (isCompatT Eql (TRefn TBool PEmpty)) as pfB by (apply isCptT_EqlB; trivial);
  assert (isCompatT Eql (TRefn TInt  PEmpty)) as pfZ by (apply isCptT_EqlZ; trivial);
  assert (forall m:nat, delta Leq (Ic m) (pfL m) = Prim (Leqn m)) as delL
      by (intro m; pose proof (delta_delta' Leq (Ic m) (pfL m)) as D; 
          simpl in D; injection D; trivial);
  assert (forall m:nat, delta Eq  (Ic m) (pfE m) = Prim (Eqn m))  as delE
      by (intro m; pose proof (delta_delta' Eq  (Ic m) (pfE m)) as D; 
          simpl in D; injection D; trivial);
  assert ( Prim Eqv = deltaT Eql (TRefn TBool PEmpty) pfB ) as delTB
    by (pose proof (deltaT_deltaT' Eql (TRefn TBool PEmpty) pfB) as D;
        simpl in D; injection D; trivial );
  assert ( Prim Eq  = deltaT Eql (TRefn TInt PEmpty) pfZ ) as delTZ
    by (pose proof (deltaT_deltaT' Eql (TRefn TInt PEmpty) pfZ) as D;
        simpl in D; injection D; trivial );        
  (*assert (delta And (Bc true)  pfAT = Lambda (BV 0)) as delAT
      by (pose proof (delta_delta' And (Bc true)  pfAT) as D; simpl in D; injection D; trivial);
  assert (delta And (Bc false) pfAF = Lambda (Bc false)) as delAF
      by (pose proof (delta_delta' And (Bc false) pfAF) as D; simpl in D; injection D; trivial);
  assert (delta Or  (Bc true)  pfOT = Lambda (Bc true)) as delOT
      by (pose proof (delta_delta' Or  (Bc true)  pfOT) as D; simpl in D; injection D; trivial);
  assert (delta Or  (Bc false) pfOF = Lambda (BV 0)) as delOF
      by (pose proof (delta_delta' Or  (Bc false) pfOF) as D; simpl in D; injection D; trivial);
  assert (delta Not (Bc true)  pfNT = (Bc false)) as delNT
      by (pose proof (delta_delta' Not (Bc true)  pfNT) as D; simpl in D; injection D; trivial);
  assert (delta Not (Bc false) pfNF = (Bc true)) as delNF
      by (pose proof (delta_delta' Not (Bc false) pfNF) as D; simpl in D; injection D; trivial); *)
  try destruct b; unfold tsubBV;  simpl;
  ( match goal with
    | [ |- exists _, Some _ = Some ?term /\ _ ] => exists term
    end )
          ; split ; try reflexivity.
  - (* And true *) 
    assert (delta And (Bc true) pf = Lambda (BV 0)) as del
      by (pose proof (delta_delta' And (Bc true) pf) as D; simpl in D; injection D; trivial);
    apply TAbs with Base empty;
    try apply WFBase; trivial; intros; 
    unfold unbind; unfold unbindT; simpl;
    apply TSub 
      with (self (TRefn TBool PEmpty) (App (App (Prim And) (Bc true)) (FV y)) Base) Base;
    try apply TSub with (self (TRefn TBool PEmpty) (FV y)  Base) Base;
    try apply SBase with (singleton y); intros; unfold unbindP;
    try ( apply IEvals2;
          apply AddStep with (App (delta And (Bc true) pf) (FV y)); 
          try apply EApp1; try apply EPrim; try rewrite del; 
          try apply lem_step_evals; try apply EAppAbs; intuition ) ;
    try ( apply IEvals; rewrite delTB; apply lem_step_evals; 
          apply EApp1; apply EApp1; apply EPrimT; trivial ) ;
    try apply TVar; 
    try apply lem_selfify_wf; try apply WFBase;
    try apply WFRefn with (singleton y);
    try apply WFBase; intros; unfold unbindP; simpl;
    try apply PFTCons; try apply PFTEmp;
    try apply FTApp with (FTBasic TBool); try apply FTApp with (FTBasic TBool);
    try apply FTApp with (FTBasic TBool);
    try apply FTPrm; try apply FTVar; try apply FTBC;
    try discriminate; simpl; intuition.
  - (* And false *)
    assert (delta And (Bc false) pf = Lambda (Bc false)) as del
      by (pose proof (delta_delta' And (Bc false) pf) as D; simpl in D; injection D; trivial);
    apply TAbs with Base empty;
    try apply WFBase; trivial; intros; 
    unfold unbind; unfold unbindT; simpl;
    apply TSub 
      with (self (TRefn TBool PEmpty) (App (App (Prim And) (Bc false)) (FV y)) Base) Base;
    try apply TSub with (self (TRefn TBool PEmpty)    (Bc false)     Base) Base;
    try apply SBase with (singleton y); intros; unfold unbindP; 
    try ( apply IEvals2;
          apply AddStep with (App (delta And (Bc false) pf) (FV y)); 
          try apply EApp1; try apply EPrim; try rewrite del; 
          try apply lem_step_evals; try apply EAppAbs; intuition ) ;
    try ( apply IEvals; rewrite delTB; apply lem_step_evals; 
          apply EApp1; apply EApp1; apply EPrimT; trivial ) ;
    try apply TVar; try apply TBC;
    try apply lem_selfify_wf; try apply WFBase;
    try apply WFRefn with (singleton y);
    try apply WFBase; intros; unfold unbindP; simpl;
    try apply PFTCons; try apply PFTEmp;
    try apply FTApp with (FTBasic TBool); try apply FTApp with (FTBasic TBool);
    try apply FTApp with (FTBasic TBool);
    try apply FTPrm; try apply FTVar; try apply FTBC;
    try discriminate; simpl; intuition.
  - (* Or true *)
    assert (delta Or (Bc true) pf = Lambda (Bc true)) as del
      by (pose proof (delta_delta' Or (Bc true) pf) as D; simpl in D; injection D; trivial);
    apply TAbs with Base empty;
    try apply WFBase; trivial; intros; 
    unfold unbind; unfold unbindT; simpl;
    apply TSub 
      with (self (TRefn TBool PEmpty) (App (App (Prim Or) (Bc true)) (FV y)) Base) Base;
    try apply TSub with (self (TRefn TBool PEmpty)    (Bc true)     Base) Base;
    try apply SBase with (singleton y); intros; unfold unbindP; 
    try ( apply IEvals2;
          apply AddStep with (App (delta Or (Bc true) pf) (FV y)); 
          try apply EApp1; try apply EPrim; try rewrite del; 
          try apply lem_step_evals; try apply EAppAbs; intuition ) ;
    try ( apply IEvals; rewrite delTB; apply lem_step_evals; 
          apply EApp1; apply EApp1; apply EPrimT; trivial ) ;
    try apply TVar; try apply TBC;
    try apply lem_selfify_wf; try apply WFBase;
    try apply WFRefn with (singleton y);
    try apply WFBase; intros; unfold unbindP; simpl;
    try apply PFTCons; try apply PFTEmp;
    try apply FTApp with (FTBasic TBool); try apply FTApp with (FTBasic TBool);
    try apply FTApp with (FTBasic TBool);
    try apply FTPrm; try apply FTVar; try apply FTBC;
    try discriminate; simpl; intuition.
  - (* Or false *)
    assert (delta Or (Bc false) pf = Lambda (BV 0)) as del
      by (pose proof (delta_delta' Or (Bc false) pf) as D; simpl in D; injection D; trivial);
    apply TAbs with Base empty;
    try apply WFBase; trivial; intros; 
    unfold unbind; unfold unbindT; simpl;
    apply TSub 
      with (self (TRefn TBool PEmpty) (App (App (Prim Or) (Bc false)) (FV y)) Base) Base;
    try apply TSub with (self (TRefn TBool PEmpty)    (FV y)     Base) Base;
    try apply SBase with (singleton y); intros; unfold unbindP; 
    try ( apply IEvals2;
          apply AddStep with (App (delta Or (Bc false) pf) (FV y)); 
          try apply EApp1; try apply EPrim; try rewrite del; 
          try apply lem_step_evals; try apply EAppAbs; intuition ) ;
    try ( apply IEvals; rewrite delTB; apply lem_step_evals; 
          apply EApp1; apply EApp1; apply EPrimT; trivial ) ;
    try apply TVar; try apply TBC;
    try apply lem_selfify_wf; try apply WFBase;
    try apply WFRefn with (singleton y);
    try apply WFBase; intros; unfold unbindP; simpl;
    try apply PFTCons; try apply PFTEmp;
    try apply FTApp with (FTBasic TBool); try apply FTApp with (FTBasic TBool);
    try apply FTApp with (FTBasic TBool);
    try apply FTPrm; try apply FTVar; try apply FTBC;
    try discriminate; simpl; intuition.
  - (* Not true *)
    assert (delta Not (Bc true) pf = Bc false) as del
      by (pose proof (delta_delta' Not (Bc true) pf) as D; simpl in D; injection D; trivial);
    apply TSub 
      with (self (TRefn TBool PEmpty) (App (Prim Not) (Bc true))  Base) Base;
    try apply TSub with (self (TRefn TBool PEmpty)    (Bc false)     Base) Base;
    try apply SBase with empty; intros; unfold unbindP;
    try ( apply IEvals2; rewrite <- del; 
          apply lem_step_evals; apply EPrim; intuition ) ;
    try ( apply IEvals; rewrite delTB; apply lem_step_evals; 
          apply EApp1; apply EApp1; apply EPrimT; trivial ) ;
    try apply TVar; try apply TBC;
    try apply lem_selfify_wf; try apply WFBase;
    try apply WFRefn with empty;
    try apply WFBase; intros; unfold unbindP; simpl;
    try apply PFTCons; try apply PFTEmp;
    try apply FTApp with (FTBasic TBool); try apply FTApp with (FTBasic TBool);
    try apply FTApp with (FTBasic TBool);
    try apply FTPrm; try apply FTVar; try apply FTBC;
    try discriminate; simpl; intuition.        
  - (* Not false *)
    assert (delta Not (Bc false) pf = Bc true) as del
      by (pose proof (delta_delta' Not (Bc false) pf) as D; simpl in D; injection D; trivial);
    apply TSub 
      with (self (TRefn TBool PEmpty) (App (Prim Not) (Bc false))  Base) Base;
    try apply TSub with (self (TRefn TBool PEmpty)    (Bc true)     Base) Base;
    try apply SBase with empty; intros; unfold unbindP;
    try ( apply IEvals2; rewrite <- del; 
          apply lem_step_evals; apply EPrim; intuition ) ;
    try ( apply IEvals; rewrite delTB; apply lem_step_evals; 
          apply EApp1; apply EApp1; apply EPrimT; trivial ) ;
    try apply TVar; try apply TBC;
    try apply lem_selfify_wf; try apply WFBase;
    try apply WFRefn with empty;
    try apply WFBase; intros; unfold unbindP; simpl;
    try apply PFTCons; try apply PFTEmp;
    try apply FTApp with (FTBasic TBool); try apply FTApp with (FTBasic TBool);
    try apply FTApp with (FTBasic TBool);
    try apply FTPrm; try apply FTVar; try apply FTBC;
    try discriminate; simpl; intuition.
  - (* Eqv True *)    
    assert (delta Eqv (Bc true) pf = Lambda (BV 0)) as del
      by (pose proof (delta_delta' Eqv (Bc true) pf) as D; simpl in D; injection D; trivial);
    apply TAbs with Base empty;
    try apply WFBase; trivial; intros; 
    unfold unbind; unfold unbindT; simpl;
    apply TSub 
      with (self (TRefn TBool PEmpty) (App (App (Prim Eqv) (Bc true)) (FV y)) Base) Base;
    try apply TSub with (self (TRefn TBool PEmpty) (FV y)  Base) Base;
    try apply SBase with (singleton y); intros; unfold unbindP;
    try ( apply IEvals2;
          apply AddStep with (App (delta Eqv (Bc true) pf) (FV y)); 
          try apply EApp1; try apply EPrim; try rewrite del; 
          try apply lem_step_evals; try apply EAppAbs; intuition ) ;
    try ( apply IEvals; rewrite delTB at 2; apply lem_step_evals; 
          apply EApp1; apply EApp1; apply EPrimT; trivial ) ;
    try apply TVar; 
    try apply lem_selfify_wf; try apply WFBase;
    try apply WFRefn with (singleton y);
    try apply WFBase; intros; unfold unbindP; simpl;
    try apply PFTCons; try apply PFTEmp;
    try apply FTApp with (FTBasic TBool); try apply FTApp with (FTBasic TBool);
    try apply FTApp with (FTBasic TBool);
    try apply FTPrm; try apply FTVar; try apply FTBC;
    try discriminate; simpl; intuition.
  - (* Eqv False *)
    assert (delta Eqv (Bc false) pf = Prim Not) as del
      by (pose proof (delta_delta' Eqv (Bc false) pf) as D; simpl in D; injection D; trivial);
    apply TSub with (ty Not) Star; try apply SFunc with empty; unfold intype;
    try apply lem_sub_refl with Base; intros;
    try apply SBase with (singleton y); intros; unfold unbindP;
    try ( apply IEvals2;
          apply AddStep with (App (delta Eqv (Bc false) pf) (FV y));
          try apply EApp1; try apply EPrim; try rewrite del; 
          try apply Refl; intuition );
    try apply TPrm; 
    try apply WFFunc with Base Base empty; intros;
    try apply WFRefn with (singleton y);
    try apply WFBase; intros; unfold unbindP; simpl;
    try apply PFTCons; try apply PFTEmp;
    try apply FTApp with (FTBasic TBool); try apply FTApp with (FTBasic TBool);
    try apply FTApp with (FTBasic TBool);
    try apply FTPrm; try apply FTVar; try apply FTBC;
    try discriminate; simpl; intuition.
  - (* Imp True *)
    assert (delta Imp (Bc true) pf = Lambda (BV 0)) as del
      by (pose proof (delta_delta' Imp (Bc true) pf) as D; simpl in D; injection D; trivial);
    apply TAbs with Base empty;
    try apply WFBase; trivial; intros; 
    unfold unbind; unfold unbindT; simpl;
    apply TSub 
      with (self (TRefn TBool PEmpty) (App (App (Prim Imp) (Bc true)) (FV y)) Base) Base;
    try apply TSub with (self (TRefn TBool PEmpty) (FV y)  Base) Base;
    try apply SBase with (singleton y); intros; unfold unbindP;
    try ( apply IEvals2;
          apply AddStep with (App (delta Imp (Bc true) pf) (FV y)); 
          try apply EApp1; try apply EPrim; try rewrite del; 
          try apply lem_step_evals; try apply EAppAbs; intuition ) ;
    try ( apply IEvals; rewrite delTB; apply lem_step_evals; 
          apply EApp1; apply EApp1; apply EPrimT; trivial ) ;
    try apply TVar; 
    try apply lem_selfify_wf; try apply WFBase;
    try apply WFRefn with (singleton y);
    try apply WFBase; intros; unfold unbindP; simpl;
    try apply PFTCons; try apply PFTEmp;
    try apply FTApp with (FTBasic TBool); try apply FTApp with (FTBasic TBool);
    try apply FTApp with (FTBasic TBool);
    try apply FTPrm; try apply FTVar; try apply FTBC;
    try discriminate; simpl; intuition.
  - (* Imp False *)
    assert (delta Imp (Bc false) pf = Lambda (Bc true)) as del
      by (pose proof (delta_delta' Imp (Bc false) pf) as D; simpl in D; injection D; trivial);
    apply TAbs with Base empty;
    try apply WFBase; trivial; intros; 
    unfold unbind; unfold unbindT; simpl;
    apply TSub 
      with (self (TRefn TBool PEmpty) (App (App (Prim Imp) (Bc false)) (FV y)) Base) Base;
    try apply TSub with (self (TRefn TBool PEmpty)  (Bc true)  Base) Base;
    try apply SBase with (singleton y); intros; unfold unbindP;
    try ( apply IEvals2;
          apply AddStep with (App (delta Imp (Bc false) pf) (FV y)); 
          try apply EApp1; try apply EPrim; try rewrite del; 
          try apply lem_step_evals; try apply EAppAbs; intuition ) ;
    try ( apply IEvals; rewrite delTB; apply lem_step_evals; 
          apply EApp1; apply EApp1; apply EPrimT; trivial ) ;
    try apply TVar; try apply TBC;
    try apply lem_selfify_wf; try apply WFBase;
    try apply WFRefn with (singleton y);
    try apply WFBase; intros; unfold unbindP; simpl;
    try apply PFTCons; try apply PFTEmp;
    try apply FTApp with (FTBasic TBool); try apply FTApp with (FTBasic TBool);
    try apply FTApp with (FTBasic TBool);
    try apply FTPrm; try apply FTVar; try apply FTBC;
    try discriminate; simpl; intuition.
  - (* Leq *)
    assert (delta Leq (Ic n) pf = Prim (Leqn n) ) as del
      by (pose proof (delta_delta' Leq (Ic n) pf) as D; simpl in D; injection D; trivial);
    apply TSub with (ty (Leqn n)) Star; try apply SFunc with empty; unfold intype;
    try apply lem_sub_refl with Base; intros;
    try apply SBase with (singleton y); intros; unfold unbindP;  
    try apply IRefl;
    try apply TPrm;
    try apply WFFunc with Base Base empty; intros;
    try apply WFRefn with (singleton y);
    try apply WFBase; intros; unfold unbindP; simpl;
    try apply PFTCons; try apply PFTEmp;
    try apply FTApp with (FTBasic TBool);
    try ( apply FTApp with (FTBasic TBool); 
          apply FTPrm || apply FTVar; simpl; intuition );
    try apply FTApp with (FTBasic TInt);
    try apply FTApp with (FTBasic TInt);
    try apply FTPrm; try apply FTVar; try apply FTIC;
    try discriminate; simpl; intuition.
  - (* Leqn *)
    assert (delta (Leqn n) (Ic n0) pf = Bc (Nat.leb n n0) ) as del
      by (pose proof (delta_delta' (Leqn n) (Ic n0) pf) as D; simpl in D; injection D; trivial).
    apply TSub 
      with (self (TRefn TBool PEmpty)  (App (App (Prim Leq) (Ic n)) (Ic n0))  Base) Base;
    try apply TSub with (self (TRefn TBool PEmpty)    (Bc (Nat.leb n n0))    Base) Base;
    try apply SBase with empty; intros; unfold unbindP ;
    try ( apply IEvals2; rewrite <- del; 
          apply AddStep with (App (Prim (Leqn n)) (Ic n0));
          try (rewrite <- delL; apply EApp1; apply EPrim);
          try apply lem_step_evals; try apply EPrim; intuition ) ;
    try ( apply IEvals; rewrite delTB; apply lem_step_evals; 
          apply EApp1; apply EApp1; apply EPrimT; trivial ) ;
    try apply TBC;
    try apply lem_selfify_wf; try apply WFBase;
    try apply WFRefn with empty;
    try apply WFBase; intros; unfold unbindP; simpl;
    try apply PFTCons; try apply PFTEmp;
    try ( apply FTApp with (FTBasic TInt); 
          try apply FTApp with (FTBasic TInt); 
          apply FTPrm || apply FTIC );
    try apply FTApp with (FTBasic TBool);
    try ( apply FTApp with (FTBasic TInt); 
          try apply FTApp with (FTBasic TInt); 
          apply FTPrm || apply FTIC );
    try apply FTApp with (FTBasic TBool);
    try apply FTPrm; try apply FTVar; 
    try discriminate; simpl; intuition.
  - (* Eq *)
    assert (delta Eq (Ic n) pf = Prim (Eqn n) ) as del
      by (pose proof (delta_delta' Eq (Ic n) pf) as D; simpl in D; injection D; trivial);
    apply TSub with (ty (Eqn n)) Star; try apply SFunc with empty; unfold intype;
    try apply lem_sub_refl with Base; intros;
    try apply SBase with (singleton y); intros; unfold unbindP;  
    try apply IRefl;
    try apply TPrm;
    try apply WFFunc with Base Base empty; intros;
    try apply WFRefn with (singleton y);
    try apply WFBase; intros; unfold unbindP; simpl;
    try apply PFTCons; try apply PFTEmp;
    try apply FTApp with (FTBasic TBool);
    try ( apply FTApp with (FTBasic TBool); 
          apply FTPrm || apply FTVar; simpl; intuition );
    try apply FTApp with (FTBasic TInt);
    try apply FTApp with (FTBasic TInt);
    try apply FTPrm; try apply FTVar; try apply FTIC;
    try discriminate; simpl; intuition.
  - (* Leqn *)
    assert (delta (Eqn n) (Ic n0) pf = Bc (Nat.eqb n n0) ) as del
      by (pose proof (delta_delta' (Eqn n) (Ic n0) pf) as D; simpl in D; injection D; trivial).
    apply TSub 
      with (self (TRefn TBool PEmpty)  (App (App (Prim Eq) (Ic n)) (Ic n0))  Base) Base;
    try apply TSub with (self (TRefn TBool PEmpty)    (Bc (Nat.eqb n n0))    Base) Base;
    try apply SBase with empty; intros; unfold unbindP ;
    try ( apply IEvals2; rewrite <- del; 
          apply AddStep with (App (Prim (Eqn n)) (Ic n0));
          try (rewrite <- delE; apply EApp1; apply EPrim);
          try apply lem_step_evals; try apply EPrim; intuition ) ;
    try ( apply IEvals; rewrite delTB; apply lem_step_evals; 
          apply EApp1; apply EApp1; apply EPrimT; trivial ) ;
    try apply TBC;
    try apply lem_selfify_wf; try apply WFBase;
    try apply WFRefn with empty;
    try apply WFBase; intros; unfold unbindP; simpl;
    try apply PFTCons; try apply PFTEmp;
    try ( apply FTApp with (FTBasic TInt); 
          try apply FTApp with (FTBasic TInt); 
          apply FTPrm || apply FTIC );
    try apply FTApp with (FTBasic TBool);
    try ( apply FTApp with (FTBasic TInt); 
          try apply FTApp with (FTBasic TInt); 
          apply FTPrm || apply FTIC );
    try apply FTApp with (FTBasic TBool);
    try apply FTPrm; try apply FTVar; try discriminate; simpl; intuition.
  Qed.

Lemma lem_deltaT_ty'c : forall (c:prim) (t:type),
    isPoly c -> noExists t -> WFtype Empty t Base
               -> exists e, Some e = deltaT' c t /\ 
                            Hastype Empty e (tsubBTV t (TFunc (intype c) (ty' c))).
Proof.
   
{-@ lem_deltaT_ty'c :: { c:Prim | isPoly c } -> t:UserType -> ProofOf()
        -> ProofOf(HasType Empty (deltaT c t)
                           ) @-}
lem_deltaT_ty'c :: Prim -> Type -> WFType -> HasType
lem_deltaT_ty'c c t p_emp_t = undefined -- this part we leave as an assumption

{-@ lem_prim_compat_in_tapp :: p:Prim -> v:Value -> t:type
        -> ProofOf(Hastype Empty (App (Prim p) v) t)
        -> { pf:_ | isCompat p v } @-}
lem_prim_compat_in_tapp :: Prim -> expr -> type -> Hastype -> Proof
lem_prim_compat_in_tapp c v t p_cv_t
    = lem_prim_compat_in_ftapp c v (erase t) (p_cv_er_t)
        where
          p_cv_er_t    = lem_typing_hasftype Empty (App (Prim c) v) t p_cv_t WFEEmpty

{-@ lem_prim_compatT_in_tappT :: c:Prim -> t_a:Usertype -> t:type
        -> ProofOf(Hastype Empty (AppT (Prim c) t_a) t) -> { pf:_ | isCompatT c t_a } @-}
lem_prim_compatT_in_tappT :: Prim -> type -> type -> Hastype -> Proof
lem_prim_compatT_in_tappT c t_a t p_cta_t 
  = lem_prim_compatT_in_ftappt c t_a (erase t) p_er_cta_t
      where
        p_er_cta_t = lem_typing_hasftype Empty (AppT (Prim c) t_a) t p_cta_t WFEEmpty

{-@ lem_delta_typ ::  c:Prim  -> v:Value  -> t_x:type -> t':type
        -> ProofOf(Hastype Empty (Prim c) (TFunc t_x t')) -> ProofOf(Hastype Empty v t_x)
        -> { pf:_ | propOf pf == Hastype Empty (delta c v) (TExists t_x t') } @-} 
lem_delta_typ :: Prim -> expr ->  type -> type -> Hastype -> Hastype -> Hastype
lem_delta_typ c v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (TPrm _ _) -> TSub n Empty (delta c v ? compat) (tsubBV v (ty' c)) p_cv_ty'cv
                     (TExists (intype c) (ty' c)) Star p_emp_exty' p_ty'cv_exty'
    where
      p_cv_ty'cv    = lem_delta_ty'c c v p_v_tx
      p_emp_exty'   = WFExis Empty t_x Base (lem_wf_intype c) (ty' c) Star [] (lem_wf_ty' c)
      p_ty'cv_exty' = lem_witness_sub Empty v t_x p_v_tx (ty' c) Star p_emp_exty' WFEEmpty
      n             = max (typSize p_cv_ty'cv) (subtypSize  p_ty'cv_exty')
  (TSub {})  
    -> let (TSub _ _ _ s p_c_s _ k_t p_g_txt' p_s_t) 
               = lem_collapse_sub Empty (Prim c) (TFunc t_x t') WFEEmpty p_c_txt'
         in case p_s_t of
              (SFunc n _ _ _ p_tx_in _ _ nms mk_p_ty'c_t') -> case p_c_s of
                (TPrm Empty _c) 
                      -> TSub n''' Empty (delta c (v ? compat)) ty'cv p_cv_ty'cv
                              (TExists t_x t') Star p_emp_extxt' p_ty'cv_extxt'
                    where
                      {-@ mk_wf_ty' :: y:vname  
                            -> ProofOf(WFtype (Cons y t_x Empty) (unbindT y (ty' c)) Star) @-}
                      mk_wf_ty' y = lem_narrow_wf Empty Empty y t_x (intype c) p_tx_in
                                                  (unbindT y (ty' c)) Star (lem_wf_ty' c y)                
                      p_g_tx         = lem_typing_wf Empty v t_x p_v_tx WFEEmpty
                      ty'cv          = tsubBV v (ty' c)
                      p_v_in         = TSub n'' Empty v t_x p_v_tx (intype c) Base (lem_wf_intype c) p_tx_in
                      p_cv_ty'cv     = lem_delta_ty'c c v p_v_in
                      p_emp_extxt'   = lem_typing_wf Empty (App (Prim c) v) (TExists t_x t')
                                                     p_cv_extxt' WFEEmpty
                      p_emp_exty'    = WFExis Empty t_x Star p_g_tx (ty' c) Star [] mk_wf_ty' --(lem_wf_ty' c)
                      p_ty'cv_txty'  = lem_witness_sub Empty v t_x p_v_tx (ty' c) Star p_emp_exty'
                                                       WFEEmpty
                      p_txty'_extxt' = lem_subtype_in_exists n Empty t_x (ty' c) 
                                                     (t' ? lem_wftype_islct Empty (TExists t_x t') 
                                                                            Star p_emp_extxt')
                                                     Star p_g_tx nms mk_p_ty'c_t'
                      p_emp_ty'cv    = lem_typing_wf Empty (delta c v ? compat) (tsubBV v (ty' c)) 
                                                     p_cv_ty'cv WFEEmpty
                      p_ty'cv_extxt' = lem_sub_trans Empty WFEEmpty (tsubBV v (ty' c)) Star p_emp_ty'cv
                                                     (TExists t_x (ty' c)) (TExists t_x t') Star
                                                     p_emp_extxt' p_ty'cv_txty' p_txty'_extxt' 
                      n''         = max (typSize p_v_tx)     (subtypSize p_tx_in)
                      n'''        = max (typSize p_cv_ty'cv) (subtypSize p_ty'cv_extxt')     
              (SBind {}) -> case p_c_s of
                (TPrm {}) -> impossible "s == tyc must be TFunc"
 where
     p_cv_extxt'    = TApp n' Empty (Prim c) t_x t' p_c_txt' v p_v_tx
     compat         = lem_prim_compat_in_tapp c v (TExists t_x t') p_cv_extxt'
     n'          = max (typSize p_c_txt')   (typSize p_v_tx)

{-@ lem_tyeql_forallbase :: c:Prim  -> k:kind -> s:type 
        -> ProofOf(Subtype Empty (ty c) (TPoly k s)) -> { pf:_ | k == Base } @-}
lem_tyeql_forallbase :: Prim -> kind -> type -> Subtype -> Proof
lem_tyeql_forallbase c k s p_ty_aks = case p_ty_aks of
  (SPoly {}) -> ()

{-@ lem_deltaT_typ ::  c:Prim  -> k:kind -> s:type
        -> ProofOf(Hastype Empty (Prim c) (TPoly k s)) -> t:Usertype -> ProofOf(WFtype Empty t k)
        -> ProofOf(Hastype Empty (deltaT c t) (tsubBTV t s)) @-}
lem_deltaT_typ :: Prim -> kind -> type -> Hastype -> type -> WFtype -> Hastype
lem_deltaT_typ c k u' p_c_ku' t p_emp_t  = case p_c_ku' of
  (TPrm _ _) -> lem_deltaT_ty'c c t p_emp_t 
  (TSub {})
    -> let (TSub _ _ _ tyc p_c_tyc _ k_u p_emp_ku' p_tyc_u)
               = lem_collapse_sub Empty (Prim c) (TPoly k u') WFEEmpty p_c_ku'
         in case p_tyc_u of
              (SPoly n _ _ tyc' _ nms mk_p_tyc'_u') -> case p_c_tyc of 
                (TPrm Empty _c) 
                      -> TSub n'' Empty deltaT_c_t tyct p_ct_tyct (tsubBTV t u') Star
                              p_emp_u't p_tyct_u't
                    where
                      p_ct_u't    = TAppT n' Empty (Prim c) k u' p_c_ku' t p_emp_t
                      deltaT_c_t  = deltaT c (t ? lem_prim_compatT_in_tappT c t (tsubBTV t u') p_ct_u't)
                      tyct        = tsubBTV t (TFunc  (intype c) (ty' c))
                      p_ct_tyct   = lem_deltaT_ty'c c t (p_emp_t ? lem_tyeql_forallbase c k u' p_tyc_u)
                      a           = fresh nms --_var {-(union-} nms {-nms')-} Empty
                      p_emp_u't   = lem_typing_wf Empty (AppT (Prim c) t) (tsubBTV t u') p_ct_u't 
                                                  WFEEmpty
                      p_tyct_u't  = lem_subst_tv_sub Empty Empty a t k p_emp_t WFEEmpty
                                      (unbind_tvT a (TFunc (intype c) (ty' c)))
                                      (unbind_tvT a u') (mk_p_tyc'_u' a)
                                  ? toProof ( esubFTV a t Empty === Empty )
                                  ? lem_empty_concatE Empty
                                  ? lem_tsubFTV_unbind_tvT a t (TFunc (intype c) (ty' c)
                                          ? lem_free_bound_in_env Empty (ty c) Star (lem_wf_ty c) a)
                                  ? lem_tsubFTV_unbind_tvT a t 
                                          (u' ? lem_free_bound_in_env Empty (TPoly k u') k_u p_emp_ku' a)
                      n'          = typSize p_c_ku'
                      n''         = max (typSize p_ct_tyct) (subtypSize p_tyct_u't)
              (SBind {}) -> case p_c_tyc of
                (TAbsT {}) -> impossible "ty(c) must be TPoly"
