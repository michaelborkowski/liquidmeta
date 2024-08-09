Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.LocalClosure.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.PrimitivesFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.BasicPropsWellFormedness.
Require Import SystemRF.SystemFLemmasWellFormedness.
Require Import SystemRF.SystemFLemmasWeaken.
Require Import SystemRF.Typing.
Require Import SystemRF.LemmasWeakenWF.
Require Import SystemRF.LemmasWellFormedness.
Require Import SystemRF.LemmasTyping.
Require Import SystemRF.LemmasWeakenTyp.
Require Import SystemRF.LemmasSubtyping.
Require Import SystemRF.SubstitutionLemmaTyp.
Require Import SystemRF.LemmasNarrowing.
Require Import SystemRF.LemmasTransitive. 

Require Import ZArith.

Lemma lem_list_compatM : forall (v:expr),
  isList v -> isCompatM Length v.
Proof. induction v; intros; simpl in H; try contradiction;
  constructor; try apply IHv2; assumption. Qed.

Lemma lem_invert_nil' : forall (g:env) (nl:expr) (t:type),
  Hastype g nl t -> (forall (t0 s : type) (qs : preds),
    nl = Nil t0 -> WFEnv g -> Subtype g t (TList s qs)
             -> WFtype g (TList s qs) Star
             -> Subtype g t0 s /\ WFtype g t0 Star /\
                  isMono t0 /\ noExists t0 /\
                  Subtype g (TList t0 (PCons (eq (Ic 0) (length t0 (BV 0))) PEmpty)) 
                            (TList s qs)).
Proof. apply ( Hastype_ind
    ( fun (g:env) (nl:expr) (t:type) => forall (t0 s : type) (qs : preds),
        nl = Nil t0 -> WFEnv g -> Subtype g t (TList s qs)
            -> WFtype g (TList s qs) Star
            -> Subtype g t0 s /\ WFtype g t0 Star /\
                isMono t0 /\ noExists t0 /\
                Subtype g (TList t0 (PCons (eq (Ic 0) (length t0 (BV 0))) PEmpty)) 
                          (TList s qs))
  ); try discriminate; intros.
  - (* isTNil *) injection H2 as H2; subst t; repeat split;
    inversion H4;
    destruct k; try apply H1; try apply WFKind; trivial.
  - (* isTSub *) apply H0; 
    try apply lem_sub_trans with t Star k Star;
    try (apply lem_typing_wf with e; assumption); try assumption.
  Qed.      

Lemma lem_invert_nil : forall (g:env) (t0 t:type) (ps:preds),
    Hastype g (Nil t0) (TList t ps) -> WFEnv g 
            -> Subtype g t0 t /\ WFtype g t0 Star /\
                isMono t0 /\ noExists t0 /\
                Subtype g (TList t0 (PCons (eq (Ic 0) (length t0 (BV 0))) PEmpty))
                          (TList t ps).
Proof. intros. apply lem_invert_nil' with (Nil t0)  (TList t ps); 
  try apply lem_sub_refl with Star;
  try apply lem_typing_wf with (Nil t0); trivial.
 Qed.      

Lemma lem_nil_instantiation_wf' : forall (g:env) (nl:expr) (t:type),
  Hastype g nl t -> (forall (t0 s : type),
    nl = Nil t0 -> WFEnv g -> Subtype g t s
            -> WFtype g t0 Star /\ isMono t0 /\ noExists t0).
Proof. apply ( Hastype_ind
    ( fun (g:env) (nl:expr) (t:type) => forall (t0 s : type),
        nl = Nil t0 -> WFEnv g -> Subtype g t s
            -> WFtype g t0 Star /\ isMono t0 /\ noExists t0)
  ); try discriminate; intros.
  - (* isTNil *) injection H2 as H2; subst t; repeat split;
    destruct k; try apply H1; try apply WFKind; trivial.
  - (* isTSub *) apply H0 with t; trivial.
Qed.      

Lemma lem_nil_instantiation_wf : forall (g:env) (t0 t:type), 
    Hastype g (Nil t0) t -> WFEnv g 
            -> WFtype g t0 Star /\ isMono t0 /\ noExists t0.
Proof. intros; apply lem_nil_instantiation_wf' with (Nil t0) t t; 
  try apply lem_sub_refl with Star;
  try apply lem_typing_wf with (Nil t0); trivial.
Qed.

Lemma lem_invert_cons' : forall (g:env) (cns:expr) (t:type),
  Hastype g cns t -> (forall (v1 v2: expr) (t0 s : type) (qs : preds),
    cns = Cons t0 v1 v2 -> WFEnv g -> isValue v1 -> isValue v2
            -> Subtype g t (TList s qs)
            -> WFtype g (TList s qs) Star
            -> exists  ps, Subtype g t0 s /\ WFtype g t0 Star /\
                           isMono t0 /\ noExists t0 /\
                Hastype g v1 t0 /\ Hastype g v2 (TList t0 ps) /\
                Subtype g 
                  (TExists (TList t0 ps)
                      (TList t0 (PCons (eq (App (Prim Succ) (length t0 (BV 1))) 
                                           (length t0 (BV 0))) PEmpty))) 
                  (TList s  qs)).
Proof. apply ( Hastype_ind
    ( fun (g:env) (cns:expr) (t:type) => forall (v1 v2: expr) (t0 s : type) (qs : preds),
    cns = Cons t0 v1 v2 -> WFEnv g -> isValue v1 -> isValue v2
            -> Subtype g t (TList s qs)
            -> WFtype g (TList s qs) Star
            -> exists ps, Subtype g t0 s /\ WFtype g t0 Star /\
                          isMono t0 /\ noExists t0 /\ 
                Hastype g v1 t0 /\ Hastype g v2 (TList t0 ps) /\
                Subtype g 
                  (TExists (TList t0 ps)
                      (TList t0 (PCons (eq (App (Prim Succ) (length t0 (BV 1))) 
                                           (length t0 (BV 0))) PEmpty))) 
                  (TList s  qs))
  ); try discriminate; intros .
  - (* isTCons *) inversion H9; clear H2 H4; subst g0 t_x t1 t'.
    apply lem_typing_wf in H1 as p_g_t; try apply H6;
    apply lem_typing_wf in H3 as p_g_ltps; try apply H6;
    apply lem_wftype_islct in p_g_ltps as Hlct;
    unfold isLCT in Hlct; simpl in Hlct;
    destruct Hlct as [Hlct Hlcp].    
    pose proof lem_open_at_lc_at as [_ [Hopt Hopp]].
    pose proof lem_subFV_notin as Hnot; 
    destruct Hnot as [Hnot_e [Hnot_t _]].
    pose proof lem_islc_at_weaken as [_ [Hwkt Hwkp]].
    pose proof (fresh_var_not_elem nms g) as Hy;
    set ( y:= fresh_var nms g) in Hy;
    destruct Hy as [Hyn Hyg].
    apply lem_free_bound_in_env with g t Star y 
      in p_g_t as Hfr; try apply Hyg; 
    destruct Hfr as [Hfr Hftv].
    apply lem_free_bound_in_env with g (TList s qs) Star y 
      in H10 as Hfr'; try apply Hyg; simpl in Hfr';
    destruct Hfr' as [Hfr' Hftv']; 
    apply not_elem_union_elim in Hfr'  as [Hfr'  _];
    apply not_elem_union_elim in Hftv' as [Hftv' _];
    apply H16 in Hyn as p_yg_lt_ls;
    unfold unbindT in p_yg_lt_ls; simpl in p_yg_lt_ls;
    rewrite Hopt with t 0 0 y in p_yg_lt_ls; 
    rewrite Hopt with t 1 0 y in p_yg_lt_ls; 
    try apply Hwkt with 0 0; try apply Hlct; auto.
    inversion p_yg_lt_ls. subst g0 t1 p1 t2 p2.
    injection H5 as H5'; subst eH eT t0;
    exists ps; repeat try split; trivial;
    try (rewrite <- Hnot_t with t y v2;
         try rewrite <- Hnot_t with s y v2; trivial;
         apply lem_subst_subtype_top with (TList t ps) Star Star);
    try apply H13; try apply lem_weaken_wf_top; try apply p_g_t;
    try apply lem_wflist_wftype with qs Star;
    try apply wfenv_unique; trivial. 
  - (* isTSub *) apply H0; 
    try apply lem_sub_trans with t Star k Star;
    try (apply lem_typing_wf with e; assumption); assumption.
  Qed.

Lemma lem_invert_cons : forall (g:env) (v1 v2:expr) (t0 t:type) (ps:preds),
    Hastype g (Cons t0 v1 v2) (TList t ps) 
            -> WFEnv g -> isValue v1 -> isValue v2
            -> WFtype g (TList t ps) Star
            -> exists qs, Subtype g t0 t /\ WFtype g t0 Star /\
                      isMono t0 /\ noExists t0 /\
                Hastype g v1 t0 /\ Hastype g v2 (TList t0 qs) /\
                Subtype g 
                  (TExists (TList t0 qs)
                      (TList t0 (PCons (eq (App (Prim Succ) (length t0 (BV 1))) 
                                           (length t0 (BV 0))) PEmpty))) 
                  (TList t ps).
Proof. intros. apply lem_invert_cons' with (Cons t0 v1 v2) (TList t ps); 
  try apply lem_sub_refl with Star; trivial.
Qed.     

Lemma lem_invert_tlist' : forall (g:env) (ce:expr) (t:type),
  Hastype g ce t -> (forall (v1 v2 : expr) (t0 s : type) (qs : preds),
    ce = Cons t0 v1 v2 -> isValue v2
                       -> WFEnv g -> Subtype g t (TList s qs)
                       -> WFtype g (TList s qs) Star
                       -> exists (rs : preds), Hastype g v1 s /\
                            Hastype g v2 (TList s rs)).
Proof. apply ( Hastype_ind
    ( fun (g:env) (ce:expr) (t:type) 
      => forall (v1 v2 : expr) (t0 s : type) (qs : preds),
            ce = Cons t0 v1 v2 -> isValue v2
                    -> WFEnv g -> Subtype g t (TList s qs)
                    -> WFtype g (TList s qs) Star
                    -> exists (rs : preds), Hastype g v1 s /\
                        Hastype g v2 (TList s rs))
  ); try discriminate; intros.  
  - (* isTCons *) injection H5 as Hv1 Hv2; subst eH eT t0.
    apply lem_typing_wf in H1 as p_g_t;
    try apply lem_wftype_islct in p_g_t as Hlct;
    pose proof lem_open_at_lc_at as [_ [H' _]];
    pose proof lem_subFV_notin as [_ [Hsub _]]; trivial.
    inversion H8.
    set (y := fresh_var nms g); pose proof (fresh_var_not_elem nms g);
    destruct H15.
    apply (H14 y) in H15 as p_yg_sub; unfold unbindT in p_yg_sub; 
    simpl in p_yg_sub; inversion p_yg_sub.
    rewrite H' with t 0 0 y in H21; auto.
    apply lem_subst_subtype_top
      with g y v2 (TList t ps) t s Star Star in H21;
    try rewrite Hsub in H21; try rewrite Hsub in H21;
    try exists ps; try split; try apply H3;
    try match goal with
        | [ |- Hastype _ v1 _] => apply TSub with t Star
        | [ |- Hastype _ v2 _] => apply TSub with (TList t ps) Star
        end;
    try apply SList with nms; intros; try apply IRefl;
    try apply lem_typing_wf in H3 as p_g_tps;
    try apply lem_free_bound_in_env with g Star;
    apply lem_wflist_wftype in H9 as p_g_s; trivial;
    try apply lem_weaken_wf_top;
    try apply wfenv_unique; trivial.
    inversion p_g_tps; try inversion H24;
    try apply WFList with Star;
    try apply WFListR with nms1; try apply WFList with Star;
    try rewrite <- lem_erase_subtype with g t s;
    trivial.
  - (* TSub *) apply H0 with t0 qs;
    try apply lem_sub_trans with t Star k Star;
    try apply lem_typing_wf in H; trivial.
  Qed. 
    
Lemma lem_invert_tlist : forall (g:env) (v1 v2:expr) (t0 t:type) (ps:preds),
    Hastype g (Cons t0 v1 v2) (TList t ps) 
                  -> WFEnv g -> WFtype g (TList t ps) Star
                  -> isValue v1 -> isValue v2
                  -> exists qs:preds, Hastype g v1 t /\
                        Hastype g v2 (TList t qs).
Proof. intros; inversion H.
  apply lem_invert_tlist' with (Cons t0 v1 v2) s t0 ps; trivial.
 Qed.      

Lemma lem_list_eq_length: forall (g:env) (v:expr) (s:type) (rs:preds),
    Hastype g v (TList s rs) -> WFEnv g 
            -> isList v -> isValue v
            -> isMono s -> noExists s
            -> Hastype g v 
                       (TList s (PCons (eq (length s v)
                                           (length s (BV 0))) rs)). 
Proof. intros g; induction v; intros;
  simpl in H1; try contradiction;
  assert (WFtype g s Star) as p_g_s 
      by (apply lem_wflist_wftype with rs Star; 
          try apply lem_typing_wf with (Cons t v1 v2);
          try apply lem_typing_wf with (Nil t);   trivial);
  apply lem_typing_hasftype in H as p_v_ers; try apply H0;
  apply lem_wftype_islct in p_g_s as Hlcs;
  pose proof lem_open_at_lc_at as [Hope [Hopt _]];
  pose proof lem_islc_at_weaken as [Hwke [Hwkt _]];
  pose proof lem_subFV_notin as Hnot; 
  destruct Hnot as [Hnot_e [Hnot_t Hnot_p]].
  
  - (* Nil *) apply lem_invert_nil in H as H'; try apply H0.
    destruct H' as [H5 [H6 [H7 [H8 H9]]]].  
    apply TSub with 
      (TList t (PCons (eq (Ic 0) (length t (BV 0))) PEmpty)) Star;
    try apply TNil with Star (*k*);
    try apply lem_wflist_eq_length;
    try (apply lem_typing_wf with (Nil t); apply H || apply H0); trivial.

    inversion H9;
    apply SList with (union nms (binds g)); trivial; intros.
    apply not_elem_union_elim in H17; destruct H17;
    assert (
        unbindP y (PCons (eq (length s (Nil t)) 
                             (length s (BV 0))) rs)
            = strengthen 
                (unbindP y (PCons (eq (length s (Nil t)) 
                                      (length s (BV 0))) PEmpty)) 
                (unbindP y rs) )
        as Hpred by reflexivity. rewrite Hpred.
    apply IConj;
    unfold unbindP; simpl;
    apply lem_wftype_islct in H6 as Hlct;
    try rewrite Hopt with s' 0 0 y;
    try rewrite Hopt with s  0 0 y;
    try rewrite Hopt with t  0 0 y; trivial. 

    (* 1 *)
    assert (isCompatM Length (Nil t)) as pf
      by constructor.
    assert (Some (deltaM Length (Nil t) pf) 
              = Some (Ic 0)) 
      as delM by (rewrite deltaM_deltaM'; simpl; reflexivity).
    injection delM as delM. 

    apply ITrans with 
      (PCons (App (App (Prim Eq) (Ic 0)) 
                  (App (AppT (Prim Length) s) (FV y))) PEmpty);
    try apply ILenSub; try apply val_Ic;
    try apply lem_weaken_subtype_top with Star Star;
    try apply IEvals2; try apply lem_step_evals;
    try apply EApp1; try apply EApp2; try apply val_Prm;
    try rewrite <- delM; try apply EPrimM;
    try apply wfenv_unique; trivial.
    
    (* 2 *)
    apply H16 in H17 as Himpl;
    unfold unbindP in Himpl; simpl in Himpl;
    try rewrite Hopt with s' 0 0 y in Himpl;
    try rewrite Hopt with t  0 0 y in Himpl;
    try apply Himpl; trivial.

  - (* TCons *)
    assert (isList (Cons t v1 v2)) as Hv by (simpl; trivial).
    assert (isCompatM Length (Cons t v1 v2)) as pf
      by (apply lem_list_compatM; assumption). 
    inversion pf. remember H7 as pf'. subst t0 e es.
    inversion H2; subst t0 v0 v3.
    assert (Some (deltaM Length (Cons t v1 v2) pf) 
              = Some (App (Prim Succ) (deltaM Length v2 pf'))) 
      as delM by (rewrite deltaM_deltaM'; simpl;
                  rewrite <- deltaM_deltaM' with Length v2 pf';
                  reflexivity).
    injection delM as delM.
    
    apply lem_invert_cons in H as Hinv;
    try apply lem_typing_wf with (Cons t v1 v2); trivial.
    destruct Hinv as [qs [p_s'_s [p_g_s' 
        [mono [noex [p_e1_s' [p_e2_ls' p_g_ls'_ls]]]]]]].
    inversion p_g_ls'_ls. subst g0 t_x t0 t'.

    apply lem_typing_hasftype in p_e2_ls' as p_e2_erls'; try apply H0;
    apply lem_wftype_islct in p_g_s' as Hlcs'.

    (* continue here! *)

    apply TSub with     (* second subtyping obligation *)
      (TList t (PCons (eq (App (Prim Succ) (length t v2)) 
                           (length t (BV 0))) PEmpty)) Star;
    try apply TSub with  (* first subtyping obligation *)
      (TExists (TList t (PCons (eq (length t v2) (length t (BV 0))) qs))
        (TList t (PCons (eq (App (Prim Succ) (length t (BV 1))) 
                             (length t (BV 0))) PEmpty))) Star;
    try apply TCons; (*try apply IHv2;*)
    trivial;

    apply lem_typing_wf in H as p_g_ls;
    apply lem_typing_wf in p_e2_ls' as p_g_ls';
    try apply lem_typ_islc in p_e1_s' as Hlcv1;
    try apply lem_typ_islc in p_e2_ls' as Hlcv2;    
    try apply lem_wflist_eq_succ_length; 
    try apply lem_wflist_eq_length; 
    try apply WFList with Star; auto.

    (* prove first subtyping obligation *)
    try apply SBind with (binds g); intros;
    try assert (y =? y = true) 
      as Hyeq by (apply Nat.eqb_eq; reflexivity);
    unfold unbindT; simpl;
    try rewrite Hopt with t  0 0 y;
    try rewrite Hopt with t  1 0 y;
    unfold isLCT; simpl; try repeat split;
    try apply Hwke with 0 0;
    try apply Hwkt with 0 0; auto;
    try apply SList with (names_add y (binds g));
    try apply lem_sub_refl with Star;
    try (apply lem_weaken_wf_top; apply p_g_s' || apply H5);
    intros; try apply not_elem_names_add_elim in H6; try destruct H6;
    try assert (y =? y0 = false) 
      as Hnyeq by (apply Nat.eqb_neq; symmetry; trivial);
    unfold unbindP; simpl;
    try rewrite Hope with v2 0 0 y0;
    try rewrite Hopt with t  0 0 y0; trivial.

    try assert (
        PCons (App (App (Prim Eq) (App (Prim Succ) (App (AppT (Prim Length) t) v2))) 
                   (App (AppT (Prim Length) t) (FV y0))) PEmpty
      = (psubFV y v2
          (PCons (App (App (Prim Eq) (App (Prim Succ) (App (AppT (Prim Length) t) (FV y)))) 
                      (App (AppT (Prim Length) t) (FV y0))) PEmpty))
    ) as Htyp by (unfold psubFV; simpl; fold tsubFV;
                  rewrite Hnyeq; rewrite Hyeq; rewrite Hnot_t;
                  try apply lem_free_bound_in_env with g Star; trivial);
    try rewrite Htyp;
    try apply IExactLen with t qs;
    try apply lem_weaken_wf_top; try apply lem_weaken_wf_top;
    try apply not_elem_names_add_intro;
    try apply lem_fv_bound_in_env with g (TList t qs);
    try repeat apply not_elem_union_intro;
    fold freeTV; try apply lem_free_bound_in_env with g Star;
    simpl; intuition;

    try repeat apply lem_weaken_typ_top;
    try apply TSub with (TList t ps) Star;
    try apply SList with empty; intros; try apply IFaith; 
    try repeat apply WFEBind with Star;
    try repeat apply lem_weaken_wf_top;

    unfold unique; simpl; try repeat split; fold unique;
    try apply not_elem_names_add_intro; try repeat split;
    try apply lem_wflist_eq_length;
    try apply WFList with Star;
    try (apply wfenv_unique; apply H0); auto.

    pose proof (fresh_var_not_elem nms g);
    set (y0 := fresh_var nms g) in H5; destruct H5.
    apply H13 in H5 as p_yg_ls'_ls;
    unfold unbindT in p_yg_ls'_ls; simpl in p_yg_ls'_ls;
    try rewrite Hopt with t 0 0 y0 in p_yg_ls'_ls;
    try rewrite Hopt with t 1 0 y0 in p_yg_ls'_ls; 
    try apply Hwkt with 0 0; auto.
    inversion p_yg_ls'_ls; subst g0 t1 p1 t2 p2.

    apply SList with (names_add y0 (union (union nms nms0) (binds g))); 
    trivial; intros.
    apply not_elem_names_add_elim in H9; destruct H9.
    apply not_elem_union_elim in H12; destruct H12;
    apply not_elem_union_elim in H12; destruct H12;
    assert (
        unbindP y (PCons (eq (length s (Cons t v1 v2)) 
                             (length s (BV 0))) rs)
            = strengthen 
                (unbindP y (PCons (eq (length s (Cons t v1 v2)) 
                                      (length s (BV 0))) PEmpty)) 
                (unbindP y rs) )
        as Hpred by reflexivity. rewrite Hpred.
    apply IConj;
    unfold unbindP; simpl;
    try rewrite Hope with v1 0 0 y;
    try rewrite Hope with v2 0 0 y;
    try rewrite Hopt with t  0 0 y;
    try rewrite Hopt with s  0 0 y; trivial.

    (* 1:  Implies (ECons y (TList s' PEmpty) g) 
        (PCons (App (App (Prim Eq) (App (Prim Succ) (App (AppT (Prim Length) s') v2))) 
                                    (App (AppT (Prim Length) s') (FV y))) PEmpty) 
        (PCons (App (App (Prim Eq) (App (AppT (Prim Length) s) (Cons v1 v2))) 
                                    (App (AppT (Prim Length) s) (FV y))) PEmpty) *)
    apply ITrans with 
        (PCons (App (App (Prim Eq) (App (Prim Succ) (App (AppT (Prim Length) s) v2)))
                    (App (AppT (Prim Length) s) (FV y))) PEmpty);
    try apply ILenSub2;
    try apply lem_weaken_subtype_top with Star Star; 
    
    try apply ITrans with 
        (PCons (App (App (Prim Eq) (App (Prim Succ) (deltaM Length v2 pf'))) 
                    (App (AppT (Prim Length) s) (FV y))) PEmpty);
    try ( apply IEvals; apply lem_step_evals; 
          apply EApp1; apply EApp2; try apply EApp2;
          try apply val_Prm; trivial; apply EPrimM);
    try ( apply IEvals2; apply lem_step_evals; 
          apply EApp1; apply EApp2; try apply val_Prm;
          try apply EPrimM; rewrite <- delM; apply EPrimM);
    try apply wfenv_unique; trivial.
    
    (* 2:  Implies (ECons y (TList s' PEmpty) g) 
        (PCons (App (App (Prim Eq) (App (Prim Succ) (App (AppT (Prim Length) s') v2))) 
                                    (App (AppT (Prim Length) s') (FV y))) PEmpty) 
        (openP_at 0 y rs)
    
    *)
    apply H18 in H15 as Himpl; 
    unfold unbindP in Himpl; simpl in Himpl;
    try rewrite Hopt with t 0 0 y  in Himpl;
    try apply Himpl; trivial.

    assert (ECons y (TList t PEmpty) (ECons y0 (TList t qs) g)
            = concatE (ECons y0 (TList t qs) g) 
                      (ECons y (TList t PEmpty) Empty)
    ) as Henv by reflexivity; rewrite Henv in Himpl.
    apply ISub 
      with g (ECons y (TList t PEmpty) Empty) y0 v2 (TList t qs)
           (PCons (App (App (Prim Eq) (App (Prim Succ) (App (AppT (Prim Length) t) (FV y0)))) 
                       (App (AppT (Prim Length) t) (FV y))) PEmpty) 
           (openP_at 0 y rs)
      in Himpl; simpl in Himpl;
    try assert (y0 =? y0 = true) 
      as Hy0eq by (apply Nat.eqb_eq; reflexivity);
    try assert (y0 =? y = false) 
      as Hnyeq by (apply Nat.eqb_neq; symmetry; trivial);
    simpl in Hy0eq;  simpl in Hnyeq;
    try rewrite Hy0eq in Himpl;
    try rewrite Hnyeq in Himpl; clear Henv Hy0eq Hnyeq;
    try rewrite lem_commute_psubFV_unbindP in Himpl;
    try rewrite Hnot_p in Himpl;
    try rewrite Hnot_t in Himpl; try apply Himpl;
    
    try apply lem_free_bound_in_env with g Star;
    apply lem_free_bound_in_env with g (TList s rs) Star y0 
        in p_g_ls as Hfree; try simpl in Hfree;
    try destruct Hfree as [Hfree _];
    try apply not_elem_union_elim in Hfree as [_ Hfree];
    pose proof fv_open_at_elim as [_ [_ Hfvop]];

    try apply intersect_names_add_intro_r;
    try apply intersect_empty_r;
    try apply not_elem_names_add_intro;
    try (apply not_elem_subset with (names_add y (fvP rs));
         apply Hfvop || apply not_elem_names_add_intro);
    simpl; try split; try apply wfenv_unique; auto.
  Qed. 

Lemma lem_list_subtype_conj : 
  forall (g:env) (s:type) (ps:preds) (t:type) (q:expr) (qs:preds),
         Subtype g (TList s ps) (TList t (PCons q PEmpty))
      -> Subtype g (TList s ps) (TList t qs)
      -> Subtype g (TList s ps) (TList t (PCons q qs)).
Proof. intros. inversion H; subst g0 t1 p1 t2 p2;
  inversion H0; subst g0 t1 p1 t2 p2.
  apply SList with (union nms nms0); try apply H5;
  intros; unfold unbindP; simpl;
  assert (
    PCons (open_at 0 y q) (openP_at 0 y qs)
      = strengthen (PCons (open_at 0 y q) PEmpty) (openP_at 0 y qs)
    ) as Hqqs by reflexivity; rewrite Hqqs; 
  apply IConj; apply H7 || apply H9;
  apply not_elem_union_elim in H1; destruct H1; trivial.
  Qed.

Lemma lem_exists_list_subtype_conj : 
  forall (g:env) (t_x s:type) (ps:preds) (t:type) (q:expr) (qs:preds),
         Subtype g (TExists t_x (TList s ps)) (TList t (PCons q PEmpty))
      -> Subtype g (TExists t_x (TList s ps)) (TList t qs)
      -> Subtype g (TExists t_x (TList s ps)) (TList t (PCons q qs)).
Proof. intros. inversion H; subst g0 t_x0 t0 t';
  inversion H0; subst g0 t_x0 t0 t'.
  apply SBind with (union nms nms0); unfold isLCT in *;
  simpl in *; destruct H5; repeat destruct H4; auto;
  intros; apply not_elem_union_elim in H7; destruct H7; 
  unfold unbindT in *; simpl in *.
  apply lem_list_subtype_conj; apply H6 || apply H8; assumption.
  Qed.