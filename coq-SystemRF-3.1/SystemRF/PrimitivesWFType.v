Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFWellFormedness.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.PrimitivesFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.Typing.

Require Import ZArith.

(*-----------------------------------------------------------------------------
-- | Well-Formedness Facts about BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------*)

(* -- Lemma. Well-Formedness of Primitive types *)
Lemma lem_wf_tybc : forall (g:env) (b:bool), WFtype g (tybc b) Base.
Proof. intros ; apply WFRefn with (binds g)
              ; try apply WFBase ; intros 
              ; try apply PFTCons
              ; try apply PFTEmp
              ; try apply FTApp with (FTBasic TBool)
              ; try apply FTApp with (FTBasic TBool)
              ; assert ( FTFunc (FTBasic TBool) (FTFunc (FTBasic TBool) (FTBasic TBool))
                          = ftsubBV (erase (TRefn TBool PEmpty)) 
                              (FTFunc (FTBasic (BTV 0)) (FTFunc (FTBasic (BTV 0)) (FTBasic TBool))) )
                  as H1 by reflexivity ; try rewrite H1
              ; try apply FTAppT with Base
              ; try apply FTPrm
              ; try apply FTVar
              ; try apply FTBC
              ; try apply WFFTBasic
              ; try apply subset_empty_l
              ; unfold isLCT; simpl 
              ; try discriminate ; intuition.
              Qed.

Lemma lem_wf_tyic : forall (g:env) (n:Z), WFtype g (tyic n) Base.
Proof. intros ; apply WFRefn with (binds g)
              ; try apply WFBase ; intros 
              ; try apply PFTCons
              ; try apply PFTEmp
              ; try apply FTApp with (FTBasic TInt)
              ; try apply FTApp with (FTBasic TInt)
              ; assert ( FTFunc (FTBasic TInt) (FTFunc (FTBasic TInt) (FTBasic TBool))
                          = ftsubBV (erase (TRefn TInt PEmpty)) 
                              (FTFunc (FTBasic (BTV 0)) (FTFunc (FTBasic (BTV 0)) (FTBasic TBool))) )
                  as H1 by reflexivity ; try rewrite H1
              ; try apply FTAppT with Base
              ; try apply FTPrm
              ; try apply FTVar
              ; try apply FTIC
              ; try apply WFFTBasic
              ; try apply subset_empty_l
              ; unfold isLCT; simpl 
              ; try discriminate ; intuition.
              Qed.
              
Lemma lem_wf_ty : forall (g:env) (c:prim), WFtype g (ty c) Star.
Proof. destruct c ; try apply WFPoly with Star empty
          ; unfold unbind_tvT ; simpl ; intros
          ; ( match goal with 
              | [ |- WFtype (EConsT _ Base _) _ _] 
                                  => apply WFFunc with Base Star (names_add a' (binds g))
              | [ |- WFtype (EConsT _ Star _) _ _] 
                                  => apply WFFunc with Star Star (names_add a' (binds g))
              | [ |- _ ]                         => apply WFFunc with Base Star (binds g)
              end ) 
          ; unfold unbindT    ; simpl ; intros
          ; try apply WFFunc with Base Base (names_add y (names_add a' (binds g)))
          ; try apply WFFunc with Base Base (names_add y (binds g))
          ; unfold unbindT    ; simpl; intros
          ; try apply WFList with Star
          ; try apply WFVar
          ; try apply WFKind
          ; try apply WFBase 
          ; try apply WFRefn with (names_add y0 (names_add y (names_add a' (binds g))))
          ; try apply WFBase
          ; try apply WFRefn with (names_add y0 (names_add y (binds g)))
          ; try apply WFBase 
          ; try apply WFRefn with (names_add y (names_add a' (binds g)))
          ; try apply WFBase 
          ; try apply WFRefn with (names_add y (binds g))
          ; try apply WFBase  
          ; unfold unbindP ; simpl ; intros
          ; try apply PFTCons
          ; try apply PFTEmp
          ; ( match goal with 
              | [ |- HasFtype (FCons _ (FTBasic TBool) _) _ _] 
                                  => apply FTApp with (FTBasic TBool)
              | [ |- HasFtype (FCons _ (FTBasic TInt) _) _ _] 
                                  => apply FTApp with (FTBasic TInt)
              | [ |- _ ]                         => simpl
              end ) 
          ; ( match goal with 
              | [ |- HasFtype (FCons _ (FTBasic TBool) _) _ _] 
                                  => apply FTApp with (FTBasic TBool)
              | [ |- HasFtype (FCons _ (FTBasic TInt) _) _ _] 
                                  => apply FTApp with (FTBasic TInt)
              | [ |- _ ]                         => simpl
              end ) 
          ; try ( apply FTApp with (FTBasic TBool) 
                ; try apply FTApp with (FTBasic TBool)
                ; apply FTPrm || apply FTVar ) 
          ; try ( apply FTApp with (FTBasic TInt) 
                ; try apply FTApp with (FTBasic TInt) 
                ; apply FTPrm || apply FTIC || apply FTVar ) 
          ; ( match goal with 
              | [ |- HasFtype _ (App (App (AppT _ _) _) _) _] 
                                  => apply FTApp with (FTBasic (FTV a'))
              | [ |- HasFtype _ (App (AppT _ _) _) _] 
                                  => apply FTApp with (FTList (FTBasic (FTV a')))
              | [ |- _ ]          => simpl
              end )
          ; try apply FTApp with (FTBasic (FTV a'))
          ; try assert ( FTFunc (FTBasic (FTV a')) (FTFunc (FTBasic (FTV a')) (FTBasic TBool))
                            = ftsubBV (erase (TRefn (FTV a') PEmpty)) 
                                (FTFunc (FTBasic (BTV 0)) (FTFunc (FTBasic (BTV 0)) (FTBasic TBool))) )
                            as Heq by reflexivity ; try rewrite Heq
          ; try assert ( FTFunc (FTList (FTBasic (FTV a'))) (FTBasic TInt)
                            = ftsubBV (erase (TRefn (FTV a') PEmpty)) 
                                (FTFunc (FTList (FTBasic (BTV 0))) (FTBasic TInt)) )
                            as Heq' by reflexivity ; try rewrite Heq'
          ; ( match goal with 
              | [ |- HasFtype _ (AppT (Prim Length) _) _] 
                                  => apply FTAppT with Star
              | [ |- HasFtype _ (AppT _ _) _] 
                                  => apply FTAppT with Base
              | [ |- _ ]          => simpl
              end )
          ; try apply FTPrm              
          ; try apply FTVar 
                  ; try apply WFFTFV
                  ; try apply subset_empty_l ; try apply subset_sing_add
                  ; unfold isLCT 
          ;  simpl; try discriminate; intuition. 
          Qed.

Lemma lem_wf_intype : forall (g:env) (c:prim),  
    ~ isPoly c -> ~ isMeasure c -> WFtype g (intype c) Base.
Proof. intros g c H H'; assert (ty c = TFunc (intype c) (ty' c))
    by (destruct c; simpl; simpl in H; simpl in H'; contradiction || reflexivity).
  pose proof (lem_wf_ty g c); rewrite H0 in H1.
  inversion H1; try inversion H2; destruct k_x; try apply H5;
  destruct c; simpl in H5; inversion H5; simpl; 
  simpl in H'; try contradiction; try apply H8. Qed.

Lemma lem_wf_ty' : forall (c:prim), ~ isPoly c -> ~ isMeasure c
    -> exists (nms:names), forall (y:vname), 
        ~ Elem y nms -> WFtype (ECons y (intype c) Empty) (unbindT y (ty' c)) Star. 
Proof. intros c H H'; assert (ty c = TFunc (intype c) (ty' c))
    by (destruct c; simpl; simpl in H; simpl in H'; contradiction || reflexivity);
  pose proof (lem_wf_ty Empty c); rewrite H0 in H1;
  inversion H1; try inversion H2; exists nms; intros;
  destruct k; apply H6 || (apply WFKind; apply H6); apply H8. Qed.

(* -- Lemma. Constants Have Exact types *)
Lemma lem_tybc_exact : forall (g:env) (b:bool), 
    Subtype g (tybc b) (self (tybc b) (Bc b) Base).
Proof. intros; destruct b; unfold tybc; simpl; unfold eqlPred;
  apply SBase with (binds g); intros; unfold unbindP; simpl;
  apply IRepeat. Qed.
  
Lemma lem_tyic_exact : forall (g:env) (n:Z),
    Subtype g (tyic n) (self (tyic n) (Ic n) Base).
Proof. intros; unfold tyic; simpl; unfold eqlPred;
  apply SBase with (binds g); intros; unfold unbindP; simpl;
  apply IRepeat. Qed.