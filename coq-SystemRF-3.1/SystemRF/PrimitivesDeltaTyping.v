Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.LocalClosure.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFWellFormedness.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.PrimitivesFTyping.
Require Import SystemRF.SystemFLemmasWeaken.
Require Import SystemRF.PrimitivesWFType.
Require Import SystemRF.BasicPropsWellFormedness.
Require Import SystemRF.SystemFLemmasWellFormedness.
Require Import SystemRF.Typing.
Require Import SystemRF.LemmasWeakenWF.
Require Import SystemRF.LemmasWellFormedness.
Require Import SystemRF.SubstitutionLemmaWF.
Require Import SystemRF.SubstitutionLemmaWFTV.
Require Import SystemRF.LemmasTyping.
Require Import SystemRF.LemmasSubtyping.
Require Import SystemRF.LemmasExactness. 
Require Import SystemRF.SubstitutionLemmaTyp.
Require Import SystemRF.SubstitutionLemmaTypTV.
Require Import SystemRF.LemmasTransitive.
Require Import SystemRF.LemmasInversion.
Require Import SystemRF.LemmasLists.

Require Import ZArith.

Lemma lem_prim_compat_in_tapp : forall (p:prim) (v:expr) (t:type),
    isValue v -> Hastype Empty (App (Prim p) v) t -> isCompat' p v.
Proof. intros p v t val p_pv_t; apply lem_prim_compat_in_ftapp with (erase t);
  assert (erase_env Empty = FEmpty) by reflexivity; try rewrite <- H;
  try apply lem_typing_hasftype; try apply WFEEmpty; assumption. Qed.
  
Lemma lem_prim_compatT_in_tappT : forall (c:prim) (t_a t:type),
    ~ isMeasure c -> noExists t_a 
        -> Hastype Empty (AppT (Prim c) t_a) t -> isCompatT' c t_a.
Proof. intros c t_a t nomeas noex p_cta_t; apply lem_prim_compatT_in_ftappt with (erase t);
  assert (erase_env Empty = FEmpty) by reflexivity; try rewrite <- H;
  try apply lem_typing_hasftype; try apply WFEEmpty; assumption. Qed.

Lemma lem_prim_compatM_in_tappappT : forall (c:prim) (t t':type) (v:expr),
    isMeasure c -> isValue v -> Hastype Empty (App (AppT (Prim c) t) v) t'  
        ->  isCompatM' c v.
Proof. intros c t t' v Hmeas Hval; intro H. 
  apply lem_prim_compatM_in_ftappappt with t (erase t');
  assert (erase_env Empty = FEmpty) by reflexivity;
  try rewrite <- H0;
  try apply lem_typing_hasftype; try apply WFEEmpty;
  trivial. Qed.

(* -- Lemma. Typing of \delta(c,v) and \delta_T(c,t) *)
Lemma lem_delta_ty'c : forall (c:prim) (v:expr),
    ~ isPoly c -> ~ isMeasure c -> isValue v -> Hastype Empty v (intype c)
               -> exists e, Some e = delta' c v /\ Hastype Empty e (tsubBV v (ty' c)).
Proof. intros c v np nm val p_v_inc; destruct c eqn:C;
  simpl in np; simpl in nm; try contradiction;
  apply lem_typing_hasftype in p_v_inc as Hv; try apply WFEEmpty;
  simpl in Hv;
  try apply (lem_bool_values v val) in Hv;
  try apply (lem_int_values v val) in Hv;
  destruct v eqn:V; simpl in Hv; try contradiction;
  assert (isCompat c v) as pf by (rewrite C; rewrite V; constructor);
  assert (forall m:Z, isCompat Leq (Ic m)) as pfL by constructor;
  assert (forall m:Z, isCompat Eq  (Ic m)) as pfE by constructor;
  assert (isCompatT Eql (TRefn TBool PEmpty)) as pfB by (apply isCptT_EqlB; trivial);
  assert (isCompatT Eql (TRefn TInt  PEmpty)) as pfZ by (apply isCptT_EqlZ; trivial);
  assert (forall m:Z, delta Leq (Ic m) (pfL m) = Prim (Leqn m)) as delL
      by (intro m; pose proof (delta_delta' Leq (Ic m) (pfL m)) as D; 
          simpl in D; injection D; trivial);
  assert (forall m:Z, delta Eq  (Ic m) (pfE m) = Prim (Eqn m))  as delE
      by (intro m; pose proof (delta_delta' Eq  (Ic m) (pfE m)) as D; 
          simpl in D; injection D; trivial);
  assert ( Prim Eqv = deltaT Eql (TRefn TBool PEmpty) pfB ) as delTB
    by (pose proof (deltaT_deltaT' Eql (TRefn TBool PEmpty) pfB) as D;
        simpl in D; injection D; trivial );
  assert ( Prim Eq  = deltaT Eql (TRefn TInt PEmpty) pfZ ) as delTZ
    by (pose proof (deltaT_deltaT' Eql (TRefn TInt PEmpty) pfZ) as D;
        simpl in D; injection D; trivial );        
  try destruct b; unfold tsubBV; simpl;
  ( match goal with
    | [ |- exists _, Some _ = Some ?term /\ _ ] 
           => assert (delta c v pf = term) as del
                by ( pose proof (delta_delta' c v pf) as D; 
                     subst c; subst v; simpl in D; injection D; trivial ) ; 
              exists term
    end )
          ; split ; try reflexivity 
          ; try apply TAbs with Base empty 
          ; try apply WFBase; trivial; intros       (* remove? *)
          ; unfold unbind; unfold unbindT; simpl ;  (* remove? *) 
  ( try match goal with
    | [ |- Hastype _ (FV ?yy) _ ] =>
            apply TSub 
              with (TRefn TBool (PCons (App (App (Prim Eqv) (FV yy)) (BV 0)) 
                                       PEmpty)) Base
          ; try apply TSub with (self (TRefn TBool PEmpty) (FV yy)  Base) Base
          ; try apply SBase with (singleton y); intros; unfold unbindP ;
          try ( apply IEvals; rewrite delTB; apply lem_step_evals; 
                apply EApp1; apply EApp1; apply EPrimT; trivial ) ;
          try ( apply IEvals2;
                apply AddStep 
                  with (App (App (Prim Eqv) (App (delta c v pf) (FV y))) (FV y0));
                subst c; subst v;
                try apply EApp1; try apply EApp2; 
                  try apply EApp1; try apply EPrim; try rewrite del; 
                try apply lem_step_evals; try apply EApp1; 
                  try apply EApp2; try apply EAppAbs; intuition ) ;
          try apply TVar
    | [ |- Hastype (ECons _ _ _) (Bc ?bb) _ ] =>
            apply TSub 
              with (TRefn TBool (PCons (App (App (Prim Eqv) (Bc bb)) (BV 0)) 
                                       PEmpty)) Base
          ; try apply TSub with (self (TRefn TBool PEmpty)    (Bc bb)     Base) Base 
          ; try apply SBase with (singleton y); intros; unfold unbindP; 
          try ( apply IEvals; rewrite delTB; apply lem_step_evals; 
                apply EApp1; apply EApp1; apply EPrimT; trivial ) ;
          try ( apply IEvals2;
                apply AddStep 
                  with (App (App (Prim Eqv) (App (delta c v pf) (FV y))) (FV y0));
                subst c; subst v;
                try apply EApp1; try apply EApp2; 
                  try apply EApp1; try apply EPrim; try rewrite del; 
                try apply lem_step_evals; try apply EApp1; 
                  try apply EApp2; try apply EAppAbs; intuition ) ;
          try apply TBC
    | [ |- Hastype Empty (Bc ?bb) _ ] =>
            apply TSub 
              with (TRefn TBool (PCons (App (App (Prim Eqv) (Bc bb)) (BV 0)) 
                                       PEmpty)) Base
          ; try apply TSub with (self (TRefn TBool PEmpty)    (Bc bb)     Base) Base
          ; try apply SBase with empty; intros; unfold unbindP
          ; try ( apply IEvals; rewrite delTB; apply lem_step_evals; 
                  apply EApp1; apply EApp1; apply EPrimT; trivial ) 
          ; try ( apply IEvals2; rewrite <- del; 
                  ( match goal with
                    | [ |- EvalsTo (App (App _ (App _ (Ic _))) _) _] 
                            => try apply AddStep with (App (App (Prim Eqv) (App (Prim c) v)) (FV y))
                    | [ |- _ ] => trivial
                    end
                  ) ; subst c; subst v;
                  try apply lem_step_evals; apply EApp1; apply EApp2; try apply EApp1; 
                  try (apply EPrim || (rewrite <- delL; try apply EPrim)
                                   || (rewrite <- delE; try apply EPrim)); 
                  intuition ) 
          ; try apply TBC
    | [ |- Hastype _ (Prim ?c') _ ] =>
            apply TSub with (ty c') Star; try apply SFunc with empty; unfold intype;
          try apply lem_sub_refl with Base; intros;
          try apply SBase with (singleton y); intros; unfold unbindP; 
          try apply IRefl;
          try ( apply IEvals2; apply lem_step_evals; apply EApp1; apply EApp2;
                try apply EApp1; try rewrite <- del; subst c; subst v; 
                try apply EPrim; intuition );
          try apply TPrm; 
          try apply WFFunc with Base Base empty; intros
    | [ |- Hastype Empty (Ic ?nn) _ ] =>
          apply TSub 
              with (TRefn TInt (PCons (App (App (Prim Eq) (Ic nn)) (BV 0)) 
                                       PEmpty)) Base
          ; try apply TSub with (self (TRefn TInt PEmpty)    (Ic nn)     Base) Base
          ; try apply SBase with empty; intros; unfold unbindP
          ; try ( apply IEvals; rewrite delTZ; apply lem_step_evals; 
                  apply EApp1; apply EApp1; apply EPrimT; trivial ) 
          ; try ( apply IEvals2; rewrite <- del; simpl;
                  apply lem_step_evals; apply EApp1; apply EApp2;
                  subst c; subst v; try apply EPrim; constructor )
          ; try apply TIC
    end )  
          ; try constructor ; intuition
          ; try (apply WFRefn with (singleton y); try apply WFBase) 
          ; try apply WFRefn with empty
          ; try apply WFBase; intros; unfold unbindP; simpl
          ; try apply PFTCons; try apply PFTEmp
          ; try match goal with
            | [ |- HasFtype (FCons _ (FTBasic TBool) _) _ _ ]
                => try apply FTApp with (FTBasic TBool)
            | [ |- HasFtype (FCons _ (FTBasic TInt) _) _ _ ]
                => try apply FTApp with (FTBasic TInt)
            end
          ; try match goal with
            | [ |- HasFtype (FCons _ (FTBasic TBool) _) _ _ ]
                => try apply FTApp with (FTBasic TBool)
            | [ |- HasFtype (FCons _ (FTBasic TInt) _) _ _ ]
                => try apply FTApp with (FTBasic TInt)
            end
          ; try ( apply FTApp with (FTBasic TInt); 
                  try apply FTApp with (FTBasic TInt); 
                  apply FTPrm || apply FTIC || apply FTVar) 
          ; try apply FTApp with (FTBasic TBool) 
          ; try apply FTApp with (FTBasic TBool)
          ; try apply FTPrm; try apply FTVar
          ; try apply FTBC ; try apply FTIC
          ; try discriminate ; simpl ; intuition.
  Qed.

Lemma lem_deltaT_ty'c : forall (c:prim) (t:type),
    isPoly c -> noExists t -> WFtype Empty t Base
               -> exists e, Some e = deltaT' c t /\ 
                            Hastype Empty e (tsubBTV t (TFunc (intype c) (ty' c))).
Proof. intros c t ispo noex p_emp_t; destruct c eqn:C;
  simpl in ispo; try contradiction;
  apply lem_erase_wftype in p_emp_t as Ht;
  apply lem_base_types in Ht; destruct t eqn:T; try destruct b eqn:B;
  simpl in Ht; try contradiction;
  unfold deltaT'; unfold erase;
  ( match goal with
    | [ |- exists _, Some _ = Some ?term /\ _ ] => exists term
    end ) 
          ; split ; unfold tsubBTV; simpl
          ; try ( match goal with 
                  | [ |- Hastype _ (Prim ?c) _ ] => apply TSub with (ty c) Star
                  end ) 
          ; try apply TPrm
          ; try apply WFFunc with Base Star empty; intros
          ; try apply WFFunc with Base Base (singleton y) ; intros ; fold openP_at 
          ; try assert (openP_at (0 + 1) y ps = ps) as Hps
              by ( apply lem_wftype_islct in p_emp_t as lct;  
                   unfold isLCT in lct; simpl in lct;         
                   apply lem_open_at_lc_at with 0; assumption )
          ; try assert (openP_at (0 + 1 + 1 + 1) y ps = ps) as Hps3
              by ( apply lem_wftype_islct in p_emp_t as lct;  
                   unfold isLCT in lct; simpl in lct;         
                   apply lem_open_at_lc_at with 0; 
                   apply lem_islc_at_weaken with 1 0; auto with * )              
          ; try rewrite Hps ; try rewrite Hps3; try reflexivity 

          ; try apply WFRefn with (names_add y0 (singleton y))
          ; try apply WFBase; fold openP_at; fold open_at 
          ; try apply lem_weaken_wf_top; intros
          ; destruct (Nat.eqb (0 + 1 + 1) 0) eqn:E0
          ; destruct (Nat.eqb (0 + 1 + 1) 1) eqn:E1
          ; destruct (Nat.eqb (0 + 1 + 1) 2) eqn:E2
          ; try (simpl in E0; discriminate E0)
          ; try (simpl in E1; discriminate E1)
          ; try (simpl in E2; discriminate E2)
          ; unfold unbindP; simpl; try assumption 
          ; try assert (openP_at 2 y0 ps = ps) as Hps2
              by ( apply lem_wftype_islct in p_emp_t as lct;  
                   unfold isLCT in lct; simpl in lct;         
                   apply lem_open_at_lc_at with 0; 
                   apply lem_islc_at_weaken with 1 0; auto with *  )
          ; try assert (openP_at 1 y1 ps = ps) as Hps1
              by ( apply lem_wftype_islct in p_emp_t as lct;  
                   unfold isLCT in lct; simpl in lct;         
                   apply lem_open_at_lc_at with 0; assumption  ) 
          ; try rewrite Hps2; try rewrite Hps1

          ; try apply PFTCons; try apply PFTEmp; try discriminate 
          ; try apply FTApp with (FTBasic TBool) 
          ; try apply FTApp with (FTBasic TBool) 
          ; try ( apply FTApp with (FTBasic TBool); apply FTPrm || apply FTVar; 
                  simpl; intuition ) 
          ; try apply FTApp with (FTBasic b)
          ; try apply FTApp with (FTBasic b) 
          ; try assert ( FTFunc (FTBasic b) (FTFunc (FTBasic b) (FTBasic TBool)) 
                          = ftsubBV (erase (TRefn b ps)) 
                                    (FTFunc (FTBasic (BTV 0)) 
                                            (FTFunc (FTBasic (BTV 0)) (FTBasic TBool))))
              as H' by reflexivity
          ; try rewrite H' ; try rewrite B 
          ; try apply FTAppT with Base
          ; try apply FTVar ; try apply FTPrm 
          ; try apply WFFTBasic

          ; try pose proof (lem_free_subset_binds Empty (TRefn TBool ps) Base p_emp_t) as Hf
          ; try pose proof (lem_free_subset_binds Empty (TRefn TInt  ps) Base p_emp_t) as Hf
          ; simpl; simpl in Hf; destruct Hf as [Hfv Hftv]
          ; try (apply Hftv || apply subset_trans with empty)
          ; try apply subset_empty_l
          ; try apply lem_wftype_islct with Empty Base
          ; try discriminate
          ; simpl ; try rewrite B ; auto with *

          ; apply SFunc with empty 
          ; try apply SBase with empty; intros; try apply IFaith
          ; intros; unfold unbindT; simpl 
          ; apply SFunc with (singleton y)
          ; try apply SBase with (singleton y); intros; try apply IFaith
          ; intros; unfold unbindT; simpl
          ; apply SBase with (names_add y0 (singleton y)) 
          ; intros; unfold unbindP; simpl 
          ; apply IEvals2
          ; try set (qs := (openP_at 1 y1 (openP_at 2 y0 (openP_at 3 y ps)))) 
          ; ( match goal with 
              | [ |- EvalsTo (App (App (Prim Eqv)
                                  (App (App (AppT (Prim ?c) (TRefn ?b _)) _) _)) _) 
                             (App (App (Prim Eqv) (App (App (Prim ?c') _) _)) _) ] 
                        => assert (isCompatT c (TRefn b qs)) 
                              as pf by (constructor; trivial) ;
                           assert ( Prim c' = deltaT c (TRefn b qs) pf ) as delT
                              by (pose proof (deltaT_deltaT' c (TRefn b qs) pf) as D;
                                  simpl in D; injection D; trivial ) 
              end )
          ; apply lem_step_evals
          ; apply EApp1; apply EApp2; try apply EApp1; try apply EApp1
          ; trivial ; try constructor
          ; try rewrite delT ; try apply EPrimT ; trivial.
  Qed.

Lemma lem_deltaM_ty'c : forall (c:prim) (t:type) (v:expr),
    isMeasure c -> noExists t -> isMono t -> WFtype Empty t Star
                -> isValue v -> Hastype Empty v (tsubBTV t (intype c))
                -> exists e, Some e = deltaM' c v /\
                             Hastype Empty e (tsubBV v (tsubBTV t (ty' c))). 
Proof. intros c t v isMeas noex mono p_emp_t Hval; 
  induction Hval; intro p_v;
  destruct c eqn:C; simpl in isMeas; try contradiction;
  unfold tsubBTV in p_v; simpl in p_v;
  rewrite lem_push_empty in p_v;
  try apply lem_typing_hasftype in p_v as p_v'; try simpl in p_v';
  try apply lemma_list_values in p_v' as Hv;
  try constructor; try apply WFEEmpty; try assumption;
  try simpl in Hv; try contradiction;
  
  assert (isCompatT Eql (TRefn TInt  PEmpty)) as pfZ by (apply isCptT_EqlZ; trivial);
  assert ( Prim Eq  = deltaT Eql (TRefn TInt PEmpty) pfZ ) as delTZ
    by (pose proof (deltaT_deltaT' Eql (TRefn TInt PEmpty) pfZ) as D;
        simpl in D; injection D; trivial ).
  - (* v = Nil *) 
    assert (isCompatM c (Nil t0)) as pf by (rewrite C; constructor).
    assert (deltaM c (Nil t0) pf = (Ic 0)) as del
                by ( pose proof (deltaM_deltaM' c (Nil t0) pf) as D; 
                     subst c; simpl in D; injection D; trivial ).
    simpl; exists (Ic 0); split;
    try reflexivity; unfold tsubBTV; unfold tsubBV;
    simpl; rewrite lem_push_empty; try apply noex;
    (*try apply lem_typ_islc in p_v as Hlc; try apply WFEEmpty; 
    unfold isLC in Hlc; simpl in Hlc;*)
    try apply lem_wftype_islct in p_emp_t as Hlct; 
    pose proof lem_subBV_at_lc_at as [_ [H _]].
    rewrite H with t 1 (Nil t0) 0 0; 
    pose proof lem_open_at_lc_at as [_ [H1 _]]; intuition.
    inversion p_v'; apply lem_invert_nil in p_v as Hnil;
    try apply WFEEmpty; try apply WFList with Star; trivial;
    destruct Hnil as [_ [p_t0 _]].

    apply TSub 
        with (TRefn TInt (PCons (App (App (Prim Eq) (Ic 0)) (BV 0)) 
                                PEmpty)) Base
    ; try apply TSub with (self (TRefn TInt PEmpty) (Ic 0) Base) Base
    ; try apply SBase with empty; intros; unfold unbindP; simpl
    ; try ( apply IEvals; rewrite delTZ; apply lem_step_evals; 
            apply EApp1; apply EApp1; apply EPrimT; trivial )  
    ; try ( rewrite H1 with t  0 0 y; try apply Hlct;
            try rewrite H1 with t0 0 0 y; try apply H8;
            apply IEvals2; apply lem_step_evals;
            apply EApp1; apply EApp2; try rewrite <- del; 
            subst c; try apply EPrimM; constructor )  
    ; try apply TIC
    ; try apply WFRefn with empty
    ; try apply WFBase
    ; intros; unfold unbindP; simpl
    ; try apply PFTCons ; try apply PFTEmp
    ; try rewrite H1 with t  0 0 y
    ; try rewrite H1 with t0 0 0 y
    ; try apply FTApp with (FTBasic TInt)
    ; try apply FTApp with (FTBasic TInt)
    ; try apply FTApp with (FTList (erase t))
    ; assert (FTFunc (FTList (erase t)) (FTBasic TInt)
            = ftsubBV (erase t) (FTFunc (FTList (FTBasic (BTV 0))) 
                                        (FTBasic TInt)))
        as Henv by reflexivity
    ; try rewrite Henv ; try apply FTAppT with Star 
    ; try apply FTPrm 
    ; try (rewrite <- H2; apply FTNil with Star)
    ; try apply FTVar ; try apply FTIC
    ; try apply lem_weaken_wfft_top
    ; assert (erase_env Empty = FEmpty)
        as Henv2 by reflexivity; try rewrite <- Henv2
    ; try apply lem_erase_wftype ; try apply p_emp_t
    ; apply lem_free_subset_binds in p_emp_t as [Hfv Hftv]
    ; simpl in Hfv ; simpl in Hftv
    ; try apply subset_trans with empty
    ; try apply subset_empty_l
    ; try discriminate; simpl; auto.
  - (* v = Cons *) 
    apply lem_invert_tlist in p_v as p_v2;
    try apply WFList with Star; try apply WFEEmpty; trivial;
    try destruct p_v2 as [qs [_ p_v2]].

    destruct IHHval2 as [n Hn];
    unfold tsubBTV; simpl; rewrite lem_push_empty;
    try apply noex; try apply TSub with (TList t qs) Star;
    try apply WFList with Star; try apply SList with empty;
    try apply lem_sub_refl with Star; intros; try apply IFaith;
    trivial.

    destruct Hn as [Hn p_n_ty']. rewrite <- Hn.
    exists (App (Prim Succ) n); try split; try reflexivity.
    unfold tsubBV; simpl.
    unfold tsubBV in p_n_ty'; unfold tsubBTV in p_n_ty'; simpl in p_n_ty'.

    assert (WFtype Empty (TList t PEmpty) Star)
      as p_emp_lt by (apply WFList with Star; trivial).
    assert (Subtype Empty (TList t qs) (TList t PEmpty))
      as p_sub by 
      (apply SList with empty; try apply lem_sub_refl with Star;
      trivial; intros; apply IFaith).
    pose proof (TSub Empty v2 (TList t qs) (TList t PEmpty)
                  Star p_v2 p_emp_lt p_sub) as p_v2_lt.
    assert (tsubBTV t (intype Length) = TList t PEmpty)
      as Hsub by (unfold tsubBTV; simpl; 
                  rewrite lem_push_empty; trivial).
    rewrite <- Hsub in p_v2_lt.
    pose proof (TPrm Empty Length) as p_len_ty.
    pose proof (TAppT Empty (Prim Length) Star 
                  (TFunc (intype Length) (ty' Length)) t
                  p_len_ty mono noex p_emp_t) as p_lent.
    pose proof (TApp Empty (AppT (Prim Length) t)
                  (tsubBTV t (intype Length)) (tsubBTV t (ty' Length))
                  v2 p_lent p_v2_lt) as p_lenv2.

    apply lem_prim_compatM_in_tappappT in p_lenv2 as pf'; trivial.
    apply compatM_prop_set in pf' as pf.
    assert (deltaM Length v2 pf = n) as del
        by (pose proof (deltaM_deltaM' Length v2 pf) as D;
            rewrite <- Hn in D; injection D as D; apply D).
    assert (isCompatM Length (Cons t0 v1 v2)) as pfC
        by (constructor; apply pf).
    assert (deltaM Length (Cons t0 v1 v2) pfC = App (Prim Succ) n) as delC
        by (pose proof (deltaM_deltaM' Length (Cons t0 v1 v2) pfC) as D;
            simpl in D; rewrite <- Hn in D; injection D as D; apply D).
    pose proof (deltaM_evals Length v2 pf) as [n' ev_n'].

    try apply lem_wftype_islct in p_emp_t as Hlct. 
    try apply lem_ftyp_islc in p_v' as Hlc; 
    unfold isLC in Hlc; simpl in Hlc; destruct Hlc as [Hlc0 [Hlc1 Hlc2]];
    try apply lem_typ_islc in p_n_ty' as Hnlc; try apply WFEEmpty;
    pose proof lem_subBV_at_lc_at as [_ [H' _]].
    pose proof lem_open_at_lc_at as [Hope [Hopt _]].
    rewrite lem_push_empty in p_n_ty'; try apply noex.
    rewrite H' with t 1 (Cons t0 v1 v2) 0 0;
    try rewrite H' with t 1 v2 0 0 in p_n_ty'; auto.
    apply TSub with 
      (TExists
        (TRefn TInt 
          (PCons (App (App (Prim Eq) 
                          (App (AppT (Prim Length) t) v2)) (BV 0)) PEmpty))
        (TRefn TInt 
          (PCons (App (App (Prim Eq) 
                          (App (AppT (Prim Length) t) (Cons t0 v1 v2))) (BV 0)) PEmpty))
      ) Star;
    try apply SBind with empty; unfold isLCT; unfold unbindT; 
    simpl; intros;
    try rewrite Hope with v1 1 0 y;
    try rewrite Hope with v2 1 0 y;
    try rewrite Hopt with t0 1 0 y;
    try rewrite Hopt with t  1 0 y;
    try apply lem_sub_refl with Base;

    try apply TApp; try apply p_n_ty';
    (* typing obligation for Prim Succ *)
    (* current goal type for Succ:
      (TFunc 
        (TRefn TInt 
          (PCons (App (App (Prim Eq) (App (AppT (Prim Length) t) v2)) (BV 0)) 
            PEmpty)) 
        (TRefn TInt 
          (PCons (App (App (Prim Eq) (App (AppT (Prim Length) t) (Cons v1 v2))) (BV 0)) 
            PEmpty)))  *)
    try apply TSub with
      (TFunc
        (TRefn TInt 
          (PCons (App (App (Prim Eq) (Ic n')) (BV 0)) PEmpty))
        (TRefn TInt 
          (PCons (App (App (Prim Eq) (App (Prim Succ) (Ic n'))) (BV 0)) PEmpty))
      ) Star;
      
    try apply TSub with
      (TFunc
        (TRefn TInt PEmpty)
        (TRefn TInt 
          (PCons (App (App (Prim Eq) (App (Prim Succ) (BV 1))) (BV 0)) PEmpty))
      ) Star; try apply TPrm;

    try apply SFunc with empty; 
    unfold unbindT; simpl; intros;
    try apply SBase with (singleton y);
    try apply SBase with empty; intros; unfold unbindP; simpl;
    try rewrite Hope with v1 1 0 y;
    try rewrite Hope with v1 0 0 y0;
    try rewrite Hope with v2 0 0 y;   try rewrite Hope with v2 1 0 y;
    try rewrite Hope with v2 0 0 y0;
    try rewrite Hopt with t  0 0 y;   try rewrite Hopt with t  1 0 y;
    try rewrite Hopt with t  0 0 y0; 
    try rewrite Hopt with t0 1 0 y;
    try rewrite Hopt with t0 0 0 y0; 
    try apply IFaith;
    try assert (Subtype Empty 
              (TRefn TInt (PCons (App (App (Prim Eq) (Ic n')) (BV 0)) PEmpty)) 
              (self (TRefn TInt PEmpty) (Ic n') Base))
      by (simpl; unfold eqlPred; apply SBase with empty; intros;
          unfold unbindP; simpl;
          apply IEvals2; apply lemma_app_many; apply lemma_app_many;
          apply lem_step_evals; rewrite delTZ; apply EPrimT; trivial);
    try assert (y0 <> y)
      by (unfold not; intro Hyy0; apply elem_sing in Hyy0;
          apply H0 in Hyy0; contradiction);
    try assert (y =? y = true) as y_eqb 
      by (apply Nat.eqb_eq; reflexivity);
    try assert (y =? y0 = false) as y_neqb
      by (apply Nat.eqb_neq; auto);
    try assert 
      (ECons y0 (TRefn TInt PEmpty) 
          (ECons y (TRefn TInt 
                      (PCons (App (App (Prim Eq) (Ic n')) (BV 0)) PEmpty)) 
            Empty)
        = concatE (ECons y (TRefn TInt 
                      (PCons (App (App (Prim Eq) (Ic n')) (BV 0)) PEmpty)) 
                    Empty) (ECons y0 (TRefn TInt PEmpty) Empty))
      as Henv1 by reflexivity; try rewrite Henv1;
    try apply INarrow 
      with (self (TRefn TInt PEmpty) (Ic n') Base) Base Base;
    try assert
      (PCons (App (App (Prim Eq) (App (Prim Succ) (Ic n'))) (FV y0)) PEmpty
        = psubFV y (Ic n') 
            (PCons (App (App (Prim Eq) (App (Prim Succ) (FV y))) (FV y0)) PEmpty)
      ) as Hpreds
      by (unfold psubFV; rewrite y_eqb; rewrite y_neqb; reflexivity);
    try rewrite Hpreds;
    try apply IExactQ with (TRefn TInt PEmpty);
    try repeat apply WFEBind with Star;
    try apply TSub with (tyic n') Base; try apply TIC;
    unfold tyic; simpl; unfold eqlPred; simpl;
    try (apply SBase with (names_add y0 (singleton y));
         intros; unfold unbindP; simpl; apply IFaith);
    try apply SBase with empty; intros; unfold unbindP; simpl;
    try (apply IEvals2; apply lem_step_evals;
         apply EApp1; apply EApp1;
         rewrite delTZ; apply EPrimT; trivial);
    try rewrite y_eqb; try rewrite y_neqb;
    try (apply IEvals2;
         apply AddStep
            with (App (App (Prim Eq) 
                           (App (Prim Succ) (deltaM Length v2 pf))) (FV y0));
         try (apply EApp1; apply EApp2; try constructor;
              rewrite del; rewrite <- delC; apply EPrimM;
              constructor; trivial);
         apply lemma_app_many; apply lemma_app_many2;
         try apply lemma_app_many2; try constructor; apply ev_n');
    try (apply IEvals; apply lemma_app_many; 
         apply lemma_app_many2; try constructor;
         apply AddStep with (deltaM Length v2 pf);
         try apply EPrimM; try apply ev_n'; trivial);

    try apply WFFunc with Base Base empty; intros;
    unfold unbindT; simpl;
    try apply WFKind; try apply WFBase;
    try apply WFRefn with (names_add y0 (singleton y));
    try apply WFBase;
    try apply WFRefn with (singleton y);
    try apply WFBase;
    try apply WFRefn with empty; try apply WFBase;

    intros; try apply PFTCons; try apply PFTEmp; 
    fold open_at; fold openT_at; 
    try rewrite Hope with v1 0 0 y;   try rewrite Hope with v1 1 0 y;
    try rewrite Hope with v1 0 0 y0;
    try rewrite Hope with v2 0 0 y;   try rewrite Hope with v2 1 0 y;
    try rewrite Hope with v2 0 0 y0;
    try rewrite Hopt with t  0 0 y;   try rewrite Hopt with t  1 0 y;
    try rewrite Hopt with t  0 0 y0;
    try rewrite Hopt with t0 0 0 y;   try rewrite Hopt with t0 1 0 y;   
    try rewrite Hopt with t0 0 0 y0;
    try apply FTApp with (FTBasic TInt);
    try apply FTApp with (FTBasic TInt);
    try match goal with
        | [ |- HasFtype _ (App (Prim Succ) _) _ ]
            => try apply FTApp with (FTBasic TInt)
        | [ |- HasFtype _ (App (AppT _ _) _) _ ]
            => try apply FTApp with (FTList (erase t))
        end;

    assert (FTFunc (FTBasic TInt) (FTFunc (FTBasic TInt) (FTBasic TBool))
            = ftsubBV (erase (TRefn TInt PEmpty)) 
                (FTFunc (FTBasic (BTV 0)) 
                  (FTFunc (FTBasic (BTV 0)) (FTBasic TBool))))
      by (unfold ftsubBV; simpl; reflexivity);
    try rewrite H4;
    assert (FTFunc (FTList (erase t)) (FTBasic TInt)
            = ftsubBV (erase t) 
                (FTFunc (FTList (FTBasic (BTV 0))) (FTBasic TInt)))
      as H99 by (unfold ftsubBV; simpl; reflexivity);
    try rewrite H99;
    try match goal with
        | [ |- HasFtype _ (AppT (Prim Eql) _) _ ]
            => apply FTAppT with Base
        | [ |- HasFtype _ (AppT (Prim Length) _) _ ]
            => apply FTAppT with Star
        end;
    try apply FTPrm; try apply FTVar; try apply FTIC;
    try apply lem_weaken_ftyp_top;
    try apply lem_weaken_ftyp_top;
    apply lem_typing_hasftype in p_v2 as p_v2_er;

    try apply WFFTBasic;
    try apply lem_weaken_wfft_top;
    try apply lem_weaken_wfft_top;
    apply lem_erase_wftype in p_emp_t as p_emp_ert;
    simpl in p_emp_ert; 

    try discriminate; try apply WFEEmpty;
    try apply lem_islc_at_weaken with 0 0;
    try apply val_Ic;

    apply lem_free_subset_binds in p_emp_t as [Hfv Hftv];
    simpl in Hfv ; simpl in Hftv;
    try apply subset_trans with empty;    
    try apply subset_empty_l;
    unfold in_env; unfold not; simpl; 
    intuition; try apply lem_islc_at_weaken with 0 0; auto. 
Qed.

Lemma lem_invert_prim : forall (g:env) (pc:expr) (t:type),
  Hastype g pc t -> (forall (c : prim) (s_x s' : type),
    pc = Prim c -> WFEnv g -> Subtype g t (TFunc s_x s')
                -> WFtype g (TFunc s_x s') Star
                -> Subtype g (ty c) (TFunc s_x s')).
Proof. apply ( Hastype_ind
    ( fun (g:env) (pc:expr) (t:type) => forall (c : prim) (s_x s' : type),
        pc = Prim c -> WFEnv g -> Subtype g t (TFunc s_x s')
                -> WFtype g (TFunc s_x s') Star
                -> Subtype g (ty c) (TFunc s_x s'))
  ); try discriminate; intros.
  - (* isTPrm *) injection H as C; subst c0; assumption.
  - (* isTSub *) apply H0; try apply lem_sub_trans with t Star k Star;
    try (apply lem_typing_wf with e; assumption); assumption.
  Qed.
  
Lemma lem_delta_typ : forall (c:prim) (v:expr) (t_x t': type),
    isValue v -> Hastype Empty (Prim c) (TFunc t_x t') -> Hastype Empty v t_x
              -> exists e, Some e = delta' c v /\ Hastype Empty e (TExists t_x t').
Proof. intros c v t_x t' val p_c_txt' p_v_tx. inversion p_c_txt';
  assert (Hastype Empty (App (Prim c) v) (TExists t_x t')) as p_cv_txt'
    by (apply TApp; assumption);
  assert (isCompat c v) as pf 
    by (apply compat_prop_set;
        apply lem_prim_compat_in_tapp with (TExists t_x t'); assumption);
  exists (delta c v pf); rewrite delta_delta'; split; try reflexivity.
  - (* isTPrm *) assert (ty c = TFunc (intype c) (ty' c)) as Hty
        by (destruct c; simpl in H2; try discriminate H2; simpl; reflexivity);
    assert (~ isPoly c) as Hmono
        by (destruct c; simpl in Hty; try discriminate Hty; intuition);
    assert (~ isMeasure c) as nomeas
        by (destruct c; simpl in Hty; try discriminate Hty; intuition);
    rewrite Hty in H2; injection H2 as Htx Ht'; subst t_x t';
    apply TSub with (tsubBV v (ty' c)) Star;
    (* Hastype Empty (delta c v pf) (tsubBV v (ty' c)) *)
    pose proof (lem_delta_ty'c c v Hmono nomeas val p_v_tx); destruct H0; destruct H0;
    rewrite <- delta_delta' with c v pf in H0; injection H0 as H0; 
    subst x ; try apply H2;
    (* Subtype Empty (tsubBV v (ty' c)) (TExists (intype c) (ty' c)) *)
    try apply lem_witness_sub with Star; try apply WFEEmpty;
    (* WFtype Empty (TExists (intype c) (ty' c)) Star *)
    pose proof (lem_wf_ty' c Hmono); destruct H0 as [nms Hty'];
    try apply WFExis with Base nms;
    try apply lem_wf_intype; try apply Hty'; trivial.
  - (* isTSub *) 
    assert (Subtype Empty (ty c) (TFunc t_x t')) as p_tyc_txt'
        by (apply lem_invert_prim with (Prim c) (TFunc t_x t'); 
            try apply WFEEmpty; try apply lem_sub_refl with Star;
            destruct k; try (apply H0 || (apply WFKind; apply H0)); trivial);
    inversion p_tyc_txt'; try (destruct c; simpl in H5; discriminate H5);
    assert (ty c = TFunc (intype c) (ty' c)) as Hty
        by (destruct c; simpl in H5; try discriminate H5; simpl; reflexivity);
    assert (~ isPoly c) as Hmono
        by (destruct c; simpl in Hty; try discriminate Hty; intuition);
    assert (~ isMeasure c) as nomeas
        by (destruct c; simpl in Hty; try discriminate Hty; intuition);
    apply TSub with (tsubBV v (ty' c)) Star; subst g0 s2 t2;
    rewrite Hty in H5; injection H5 as Hs1 Ht1; subst s1 t1;
    assert (Hastype Empty v (intype c)) as p_v_in
      by (apply TSub with t_x Base; try apply lem_wf_intype; assumption);
    (* Hastype Empty (delta c v pf) (tsubBV v (ty' c)) *)
    pose proof (lem_delta_ty'c c v Hmono nomeas val p_v_in) as H';
    rewrite <- delta_delta' with c v pf in H';
    destruct H' as [x H']; destruct H';
    try rewrite <- delta_delta' with c v pf in H5; injection H5 as H5; 
    subst x ; try apply H6;
    (* Subtype Empty (tsubBV v (ty' c)) (TExists t_x t' *)
    try apply lem_sub_trans with (TExists t_x (ty' c)) Star Star Star;
    pose proof (lem_wf_ty' c Hmono); destruct H5 as [nms' Hty']; 
    try apply nomeas;
    pose proof (fresh_not_elem nms'); set (y := fresh nms') in H5;
    try apply lem_witness_sub with Star;
    try apply lem_subtype_in_exists with Star (union nms nms');
    try (intros y0 Hy0; apply not_elem_union_elim in Hy0;
         destruct Hy0; apply H10; assumption);    
    try apply lem_wftype_islct with Empty Star;
    try rewrite lem_tsubFV_unbindT with y v (ty' c);
    try (destruct c; simpl; unfold not; intro ff; apply ff);
    try apply lem_subst_wf_top with (intype c); try apply Hty';
    try apply lem_witness_sub with Star;
    (* WFtype Empty (TExists (intype c) (ty' c)) Star, etc *)
    inversion H0; try inversion H7;
    try apply WFExis with Star (union nms' nms0);
    try intros y0 Hy0; try apply not_elem_union_elim in Hy0;
    try destruct Hy0; destruct k0;
    try (apply H14 || (apply WFKind; apply H14));
    try apply lem_narrow_wf_top with (intype c); try apply Hty';
    try apply lem_typing_wf with v;
    try apply lem_typing_hasftype;
    try apply WFEEmpty;   simpl; intuition.
  Qed.

Lemma lem_invert_primTM : forall (g:env) (pc:expr) (t:type),
  Hastype g pc t -> (forall (c : prim) (k : kind) (s' : type),
    pc = Prim c -> WFEnv g -> Subtype g t (TPoly k s')
                -> WFtype g (TPoly k s') Star
                -> Subtype g (ty c) (TPoly k s')).
Proof. apply ( Hastype_ind
  ( fun (g:env) (pc:expr) (t:type) => forall (c: prim) (k:kind) (s':type),
        pc = Prim c -> WFEnv g -> Subtype g t (TPoly k s')
                    -> WFtype g (TPoly k s') Star
                    -> Subtype g (ty c) (TPoly k s'))
  ); try discriminate; intros.
  - (* isTPrm *) injection H as C; subst c0; assumption.
  - (* isTSub *) apply H0; try apply lem_sub_trans with t Star k Star;
    try (apply lem_typing_wf with e; assumption); assumption.
  Qed.

Lemma lem_tyeql_forallbase : forall (c:prim) (k:kind) (s:type),
    ~isMeasure c -> Subtype Empty (ty c) (TPoly k s) -> k = Base.
Proof. intros c k s nomeas p_tyc_ks; inversion p_tyc_ks;
  destruct c; simpl in H; try discriminate H;
  simpl in nomeas; try contradiction;
  injection H as Hk Hty'; subst k0; intuition. Qed.

Lemma lem_deltaT_typ : forall (c:prim) (t:type) (k:kind) (s': type),
  ~ isMeasure c -> isMono t -> noExists t 
        -> Hastype Empty (Prim c) (TPoly k s') -> WFtype Empty t k
        -> exists e, Some e = deltaT' c t /\ Hastype Empty e (tsubBTV t s').
Proof. intros c t k s' nomeas mono noex p_c_ks' p_emp_t; inversion p_c_ks';
  assert (Hastype Empty (AppT (Prim c) t) (tsubBTV t s')) as p_ct_s't
    by (apply TAppT with k; assumption);
  assert (isCompatT c t) as pf 
    by (apply compatT_prop_set;
        apply lem_prim_compatT_in_tappT with (tsubBTV t s'); assumption);
  exists (deltaT c t pf); rewrite <- deltaT_deltaT'; split; try reflexivity;
  try assert (Subtype Empty (ty c) (TPoly k s')) as p_tyc_ks' (* if TSub *)
        by (apply lem_invert_primTM with (Prim c) (TPoly k s'); 
            try apply WFEEmpty; try apply lem_sub_refl with Star;
            destruct k0; try (apply H0 || (apply WFKind; apply H0)); trivial);
  try inversion p_tyc_ks'; try (destruct c; simpl in H5; discriminate H5);
  assert (ty c = TPoly Base (TFunc (intype c) (ty' c))) as Hty
    by (destruct c; simpl in H2; try discriminate H2; 
        try simpl in H5; try discriminate H5; 
        try simpl in nomeas; try contradiction;
        simpl; reflexivity);
  assert (isPoly c) as Hpoly
    by (destruct c; simpl in Hty; try discriminate Hty; simpl; intuition);
  rewrite Hty in H2 || rewrite Hty in H5; 
  injection H2 as Hk Ht' || injection H5 as Hk Ht'.
  - (* isTPrm *) subst s'; subst k;
    pose proof (lem_deltaT_ty'c c t Hpoly noex p_emp_t); 
    destruct H0 as [e H0]; destruct H0;
    rewrite deltaT_deltaT' with c t pf in H0; injection H0 as H0; subst e; assumption.
  - (* isTSub *) inversion H0; try inversion H5; 
    pose proof (lem_wf_ty Empty c) as Htyc;
    rewrite Hty in Htyc; inversion Htyc; try inversion H15.
    subst k k0 k1 k2 k3 g0 g1 g2 t1 t2 t3 t4;
    apply TSub with (tsubBTV t (TFunc  (intype c) (ty' c))) Star;
    (* Hastype Empty (deltaT c t pf) (tsubBTV t (TFunc (intype c) (ty' c))) *)
    pose proof (lem_deltaT_ty'c c t Hpoly noex p_emp_t) as H';
    rewrite deltaT_deltaT' with c t pf in H';
    destruct H' as [x H']; destruct H'; injection H5 as H5; 
    subst x ; try apply H6;
    (* WFtype Empty (tsubFTV a t (unbind_tvT a s')) Star *)
    try apply lem_typing_wf with (AppT (Prim c) t); try apply p_ct_s't;
    (* Subtype Empty (tsubBTV t (TFunc (intype c) (ty' c))) (tsubBTV t s') *)
    pose proof (fresh_not_elem (union nms (union nms0 nms1))) as Ha; 
    set (a := fresh (union nms (union nms0 nms1))) in Ha;
    apply not_elem_union_elim in Ha; destruct Ha;
    apply not_elem_union_elim in H7; destruct H7;
    try rewrite lem_tsubFTV_unbind_tvT with a t (TFunc (intype c) (ty' c));
    try rewrite lem_tsubFTV_unbind_tvT with a t s';
    try apply lem_subst_tv_subtype_top with Base Star k_t; try apply H11;
    assert (~ in_env a Empty) as Htriv by intuition;
    pose proof (lem_free_bound_in_env Empty (TPoly Base s') Star a H0 Htriv) 
      as Hfr; simpl in Hfr; destruct Hfr;
      try (destruct c; simpl; unfold not; intro ff; apply ff);
    try apply WFEEmpty; simpl; auto;
    destruct k_t0; try apply H17; try apply WFKind; 
    try apply H17; auto.
  Qed.

Lemma lem_invert_primM  : forall (g:env) (pc:expr) (t:type),
  Hastype g pc t -> (forall (c : prim) (s_x s' t' : type),
    pc = AppT (Prim c) t' -> isMeasure c
                -> WFEnv g -> Subtype g t (TFunc s_x s')
                -> WFtype g (TFunc s_x s') Star
                -> Subtype g (tsubBTV t' (TFunc (intype c) (ty' c))) (TFunc s_x s')).
Proof. apply ( Hastype_ind
    ( fun (g:env) (pc:expr) (t:type) => forall (c : prim) (s_x s' t' : type),
        pc = AppT (Prim c) t' -> isMeasure c 
                -> WFEnv g -> Subtype g t (TFunc s_x s')
                -> WFtype g (TFunc s_x s') Star
                -> Subtype g (tsubBTV t' (TFunc (intype c) (ty' c))) (TFunc s_x s'))
  ); try discriminate; intros.
  - (* isTAppT *) injection H4 as C; subst e t;
    apply lem_typing_wf in H as p_g_ks; try apply H6;
    inversion p_g_ks; try inversion H4.
    assert (Subtype g (ty c) (TPoly k s))
      by (apply lem_invert_primTM with (Prim c) (TPoly k s);
          try apply lem_sub_refl with Star;
          try assumption; try reflexivity).
    destruct c; simpl in H5; try contradiction; subst g0 k0 t.
    pose proof (lem_wf_ty g Length) as p_g_tyc; 
    unfold ty in p_g_tyc; inversion p_g_tyc; try inversion H4.
    apply lem_sub_trans with (tsubBTV t' s) Star Star Star;
      try assumption;
    unfold ty in H13; inversion H13; subst k0 k t1 t2 g0; (* or simpl first *)
    set (a := fresh_var (union nms (union nms0 nms1)) g); subst g1 k1;
    pose proof (fresh_var_not_elem (union nms (union nms0 nms1)) g) as Ha; 
    destruct Ha;
    apply not_elem_union_elim in H4;  destruct H4;
    apply not_elem_union_elim in H16; destruct H16;
    try rewrite lem_tsubFTV_unbind_tvT 
      with a t' (TFunc (intype Length) (ty' Length));
    try rewrite lem_tsubFTV_unbind_tvT with a t' s;
    try apply lem_subst_tv_wf_top with Star;
    try apply lem_subst_tv_subtype_top with Star Star Star;
    destruct k_t0; try (apply WFKind; apply H11); try apply H11;
    destruct k_t;  try (apply WFKind; apply H10); try apply H10;
    try apply lem_free_bound_in_env with g (TPoly Star s) Star a 
      in p_g_ks as Hfree; try simpl in Hfree; try destruct Hfree;
    try apply wfenv_unique; simpl; auto.
  - (* isTSub *) apply H0; try apply lem_sub_trans with t Star k Star;
    try (apply lem_typing_wf with e; assumption); assumption.
  Qed.

Lemma lem_deltaM_typ : 
  forall (c:prim) (s:type) (v:expr) (t_x t:type),
    isMeasure c -> isValue v -> isCompatM c v
          -> Hastype Empty (AppT (Prim c) s) (TFunc t_x t) 
          -> Hastype Empty v t_x 
          -> exists e, Some e = deltaM' c v 
                /\ Hastype Empty e (TExists t_x t).
Proof.  intros c s v t_x t Hmeas Hval. 
  induction Hval; intros pf p_cs_txt p_v_tx; 
  destruct c; simpl in Hmeas; try contradiction;
  apply lem_typing_hasftype in p_cs_txt as p_cs_ertxt;
  apply lem_typing_hasftype in p_v_tx as p_v_ertx;
  apply lem_typing_wf in p_cs_txt as p_emp_txt;
  try apply WFEEmpty;
  simpl in p_cs_ertxt; simpl in p_v_ertx;
  inversion p_cs_ertxt; inversion H2; subst t';
  unfold ftsubBV in H1; simpl in H1;
  injection H1 as Hertx Hert;
  rewrite <- Hertx in p_v_ertx;
  apply lemma_list_values in p_v_ertx as Hlist;
  try constructor; trivial;
  try simpl in Hlist; try contradiction;

  apply lem_invert_primM 
    with Empty (AppT (Prim Length) s) (TFunc t_x t) Length t_x t s 
    in p_cs_txt as Hinv; try apply lem_sub_refl with Star;
    try apply WFEEmpty; trivial;
  assert (tsubBTV s (TFunc (intype Length) (ty' Length))
      = TFunc (tsubBTV s (intype Length)) (tsubBTV s (ty' Length)))
    as Htys by reflexivity; rewrite Htys in Hinv;
  inversion Hinv; subst g1 s1 t1 s2 t2;

  assert (WFtype Empty s Star) as p_emp_s
    by (apply (lem_appT_wf Empty (Prim Length) s t_x t);
        try apply WFEEmpty; trivial);
  apply lem_wftype_islct in p_emp_s as Hlct;
  pose proof lem_open_at_lc_at as [_ [H' _]];
  set (v := Cons t0 v1 v2) || set (v := Nil t0);


  assert (Hastype Empty (App (AppT (Prim Length) s) v) (TExists t_x t))
    as p_lenv_ext by (apply TApp; trivial);
  apply lem_typing_wf in p_lenv_ext as p_emp_ext; try apply WFEEmpty;
  try
  (* v = Nil *) (     
    apply lem_nil_instantiation_wf in p_v_tx as Hnil; try apply WFEEmpty;
    destruct Hnil as [p_emp_t0 [mono0 noex0]];
    pose proof (lem_deltaM_ty'c Length s (Nil t0));
    destruct H1 as [n Hn];
    try apply lem_appT_wf with (Prim Length) t_x t;
    try apply WFEEmpty; try apply val_Nil; trivial;
    simpl; try apply TSub with t_x Star; try apply H16;
    unfold tsubBTV; simpl; try rewrite lem_push_empty; 
    try apply WFList with Star; trivial;
    destruct Hn as [Hn p_n_int]; simpl in Hn;       
    exists n; split; try apply Hn;
    apply TSub with (tsubBV (Nil t0) (tsubBTV s (ty' Length))) Star;
    try assumption;
    apply SWitn with (Nil t0); try apply val_Nil; try assumption;
    inversion p_emp_ext; try subst t_x0 g1 (* t0*); try inversion H1;
    pose proof (fresh_varT_not_elem (union nms (*(union*) nms0 (*nms2)*)) Empty t) 
      as Hy;
    set (y:= fresh_varT (union nms (*(union*) nms0 (*nms2)*)) Empty t) in Hy; 
    destruct Hy as [Hfr [Hftv [Hnms Hemp]]];
    apply not_elem_union_elim in Hnms;   destruct Hnms   as [Hnms Hnms02];
    rewrite lem_tsubFV_unbindT with y (Nil t0) (tsubBTV s (ty' Length));
    try rewrite lem_tsubFV_unbindT with y (Nil t0) t;
    try apply lem_subst_subtype_top with t_x Star Star;
    try apply H18; try apply H19; try (apply WFKind; apply H22);
    try (destruct k2; apply H26 || (apply WFFTKind; apply H26))
  ) ;                      try
  (* v = Cons v1 v2*)   (
    pose proof (lem_deltaM_ty'c Length s (Cons t0 v1 v2));
    pose proof H16 as p_tx_ls; unfold tsubBTV in p_tx_ls;
    simpl in p_tx_ls; rewrite lem_push_empty in p_tx_ls; trivial;
    assert (Hastype Empty (Cons t0 v1 v2) (TList s PEmpty))
      as p_v_ls by (apply TSub with t_x Star;
                    try apply WFList with Star; trivial);
    destruct H1 as [n Hn];
    try apply val_Cons; unfold tsubBTV;  
    try (simpl; rewrite lem_push_empty); trivial;
    destruct Hn as [Hn p_n_int];
    exists n; split; try apply Hn;
    apply TSub with (tsubBV v (tsubBTV s (ty' Length))) Star;
    try assumption;
    apply SWitn with v; try apply val_Cons; try assumption;

    inversion p_emp_ext; try subst t_x0 g1 (*t0*); try inversion H1;
    set (y:= fresh_varT (union nms nms0) Empty t); 
    pose proof (fresh_varT_not_elem (union nms nms0) Empty t) as Hy;
    destruct Hy as [Hfr [Hftv [Hnms Hemp]]];
    apply not_elem_union_elim in Hnms; destruct Hnms   as [Hnms Hnms0];
    rewrite lem_tsubFV_unbindT with y v (tsubBTV s (ty' Length));
    try rewrite lem_tsubFV_unbindT with y v t;
    try apply lem_subst_subtype_top with t_x Star Star;
    try apply H18; try apply H19; try (apply WFKind; apply H22);
    try (destruct k2; apply H26 || (apply WFFTKind; apply H26))
  );
    unfold unbindT; unfold tsubBTV; simpl;
    try rewrite lem_push_empty; 
    assert (0 =? 0 = true) as H00 by intuition;
    try apply WFKind; try apply WFRefn with (singleton y);
    try apply WFBase; intros; 
    try apply PFTCons; try apply PFTEmp; fold openT_at;
    try rewrite H' with s 1 0 y;
    try rewrite H' with s 0 0 y0; try rewrite H00; 
    try apply FTApp with (FTBasic TInt);
    try apply FTApp with (FTBasic TInt);
    try apply FTApp with (erase t_x);
    try apply FTPrm; try apply FTVar;
    try apply lem_weaken_ftyp_top;
    try apply lem_weaken_ftyp_top; try rewrite Hert;
    try apply lem_islc_at_weaken with 0 0;
    try apply WFEEmpty; 
    try apply val_Nil; try apply val_Cons;
    try apply not_elem_union_intro;
    try apply not_elem_union_intro; 
    try apply (lem_free_bound_in_env Empty s Star y);
    try discriminate; unfold bound_inF; simpl; auto.
Qed.