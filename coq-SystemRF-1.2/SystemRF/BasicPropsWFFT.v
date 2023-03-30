Require Import Arith.

Require Import SystemRF.BasicDefinitions. 
Require Import SystemRF.Names.
Require Import SystemRF.LocalClosure.
Require Import SystemRF.SystemFWellFormedness.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.BasicPropsEnvironments.

(*------------------------------------------------------------------------------------------
-- | LEMMAS relating REFINEMENT ERASURE and WELL FORMEDNESS notions
------------------------------------------------------------------------------------------*)

Lemma lem_strengthen_wfft' : forall (g'xg : fenv) (t : ftype) (k : kind),
    WFFT g'xg t k -> ( forall (g:fenv) (x:vname) (t_x:ftype) (g':fenv),
        g'xg = concatF (FCons x t_x g) g' 
                           -> intersect (bindsF g) (bindsF g') = empty
                           -> ~ (in_envF x g) -> ~ (in_envF x g') 
                           -> WFFT (concatF g g') t k ).
Proof. apply ( WFFT_ind 
  (fun (g'xg : fenv) (t : ftype) (k : kind) => 
      forall (g:fenv) (x:vname) (t_x:ftype) (g':fenv),
          g'xg = concatF (FCons x t_x g) g' 
                         -> intersect (bindsF g) (bindsF g') = empty
                         -> ~ (in_envF x g) -> ~ (in_envF x g') 
                         -> WFFT (concatF g g') t k  ));
  intro env; intros; subst env.
  - apply WFFTBasic; assumption.
  - (* WFFTFV *) apply WFFTFV;
    apply lem_tvboundinF_strengthen in H; assumption.
  - (* WFFTFunc *) apply WFFTFunc with k1 k2; 
    apply H0 with x t_x || apply H2 with x t_x; intuition.
  - (* WFFTPoly *) apply WFFTPoly with k_t (names_add x (union nms (bindsF (concatF g g'))));
    intros; apply not_elem_names_add_elim in H1; destruct H1;
    apply not_elem_union_elim in H5; destruct H5;
    apply not_elem_concatF_elim in H6; destruct H6;
    assert (FConsT a k (concatF g g') = concatF g (FConsT a k g')) by reflexivity;
    rewrite H8; apply H0 with x t_x; unfold in_envF; simpl;
    try (apply not_elem_names_add_intro); try split; 
    try (apply intersect_names_add_intro_r);
    try assumption; intuition.
  - (* WFFTKind *) apply WFFTKind; apply H0 with x t_x; intuition.
  Qed.

Lemma lem_strengthen_wfft : 
  forall (g:fenv) (x:vname) (t_x:ftype) (g':fenv) (t:ftype) (k:kind),
    WFFT (concatF (FCons x t_x g) g') t k -> intersect (bindsF g) (bindsF g') = empty
                                          -> ~ (in_envF x g) -> ~ (in_envF x g') 
                                          -> WFFT (concatF g g') t k.
Proof. intros; apply lem_strengthen_wfft' with (concatF (FCons x t_x g) g') x t_x;
  intuition. Qed.

Lemma lem_strengthen_hasftype' : forall (g'xg : fenv) (e : expr) (t : ftype),
    HasFtype g'xg e t -> ( forall (g:fenv) (x:vname) (t_x:ftype) (g':fenv),
        g'xg = concatF (FCons x t_x g) g' 
                           -> intersect (bindsF g) (bindsF g') = empty
                           -> ~ (in_envF x g) -> ~ (in_envF x g') 
                           -> ~ Elem x (fv e)
                           -> HasFtype (concatF g g') e t ).
Proof. apply ( HasFtype_ind
  (fun (g'xg : fenv) (e : expr) (t : ftype) => 
      forall (g:fenv) (x:vname) (t_x:ftype) (g':fenv),
          g'xg = concatF (FCons x t_x g) g' 
                         -> intersect (bindsF g) (bindsF g') = empty
                         -> ~ (in_envF x g) -> ~ (in_envF x g') 
                         -> ~ Elem x (fv e)
                         -> HasFtype (concatF g g') e t ));
  intro env; intros; subst env.
  - (* FTBC *) apply FTBC.
  - (* FTIC *) apply FTIC.
  - (* FTVar *) apply FTVar; apply lem_boundinF_concatF in H;
    simpl in H; rewrite or_assoc in H; destruct H.
    * (* x = x0 *) destruct H; subst x0; simpl in H4; intuition.
    * (* otherw *) apply lem_boundinF_concatF in H; apply H.
  - (* FTPrm *) apply FTPrm.
  - (* FTAbs *) apply FTAbs with k (names_add x (union nms (bindsF (concatF g g'))));
    try apply lem_strengthen_wfft with x t_x; try assumption; intros;
    apply not_elem_names_add_elim in H2; destruct H2;
    apply not_elem_union_elim in H7; destruct H7;
    apply not_elem_concatF_elim in H8; destruct H8;
    assert (FCons y b (concatF g g') = concatF g (FCons y b g')) by reflexivity;
    rewrite H10; apply H1 with x t_x; unfold in_envF; simpl;
    try (apply not_elem_names_add_intro); try split; trivial;
    try apply not_elem_subset with (names_add y (fv e));
    try (apply not_elem_names_add_intro); try split; 
    try (apply intersect_names_add_intro_r); try apply fv_unbind_elim; intuition.
  - (* FTApp *) apply FTApp with b; apply H0 with x t_x || apply H2 with x t_x;
    simpl in H7; apply not_elem_union_elim in H7; destruct H7; trivial.
  - (* FTAbsT *) apply FTAbsT with (names_add x (union nms (bindsF (concatF g g'))));
    intros; apply not_elem_names_add_elim in H1; destruct H1;
    apply not_elem_union_elim in H6; destruct H6;
    apply not_elem_concatF_elim in H7; destruct H7;
    assert (FConsT a' k (concatF g g') = concatF g (FConsT a' k g')) by reflexivity;
    rewrite H9; apply H0 with x t_x; unfold in_envF; simpl;
    try (apply not_elem_names_add_intro); try split; trivial;
    try apply not_elem_subset with (names_add a' (fv e));
    try (apply not_elem_names_add_intro);
    try (apply intersect_names_add_intro_r); try apply fv_unbind_tv_elim; intuition.
  - (* FTAppT *) apply FTAppT with k; try apply H0 with x t_x;
    try apply lem_strengthen_wfft with x t_x; simpl in H10;
    apply not_elem_union_elim in H10; destruct H10;
    pose proof (lem_vbinds_cons_concatF g g' x t_x) as Hv; destruct Hv as [Hv Hvx];
    pose proof (lem_tvbinds_cons_concatF g g' x t_x) as Htv; destruct Htv as [Htv Htvx];
    trivial.
      * apply subset_add_elim with x; 
        try apply subset_trans with (vbindsF (concatF (FCons x t_x g) g')); trivial.
      * apply subset_trans with (tvbindsF (concatF (FCons x t_x g) g')); trivial.
  - (* FTLet *) apply FTLet with b (names_add x (union nms (bindsF (concatF g g'))));
    try apply H0 with x t_x; simpl in H7; 
    apply not_elem_union_elim in H7; destruct H7; trivial; intros;
    apply not_elem_names_add_elim in H8; destruct H8;
    apply not_elem_union_elim in H9; destruct H9;
    apply not_elem_concatF_elim in H10; destruct H10;
    assert (FCons y b (concatF g g') = concatF g (FCons y b g')) by reflexivity;
    rewrite H12; apply H2 with x t_x; unfold in_envF; simpl;
    try (apply not_elem_names_add_intro); try split; trivial;
    try apply not_elem_subset with (names_add y (fv e));
    try (apply not_elem_names_add_intro); try split; 
    try (apply intersect_names_add_intro_r); try apply fv_unbind_elim; intuition.
  - (* FTAnn *) apply FTAnn; try apply H4 with x t_x;
    simpl in H9; apply not_elem_union_elim in H9; destruct H9;
    pose proof (lem_vbinds_cons_concatF g g' x t_x) as Hv; destruct Hv as [Hv Hvx];
    pose proof (lem_tvbinds_cons_concatF g g' x t_x) as Htv; destruct Htv as [Htv Htvx];
    trivial.
    * apply subset_add_elim with x; 
      try apply subset_trans with (vbindsF (concatF (FCons x t_x g) g')); trivial.
    * apply subset_trans with (tvbindsF (concatF (FCons x t_x g) g')); trivial.
  - (* FTIf  *) apply FTIf; 
    apply H0 with x t_x || apply H2 with x t_x || apply H4 with x t_x;
    simpl in H9; apply not_elem_union_elim in H9; destruct H9;
    apply not_elem_union_elim in H9; destruct H9; trivial.
  Qed.

Lemma lem_strengthen_hasftype : 
  forall (g:fenv) (x:vname) (t_x:ftype) (g':fenv) (e:expr) (t:ftype),
    HasFtype (concatF (FCons x t_x g) g') e t 
                            -> intersect (bindsF g) (bindsF g') = empty
                            -> ~ (in_envF x g) -> ~ (in_envF x g') 
                            -> ~ Elem x (fv e)
                            -> HasFtype (concatF g g') e t.
Proof. intros; apply lem_strengthen_hasftype' with (concatF (FCons x t_x g) g') x t_x;
  intuition. Qed.

(*-------------------------------------------------------------------------------------------
-- | TECHNICAL LEMMAS relating to the abscence of dangling BOUND VARIABLES without a binder
-------------------------------------------------------------------------------------------*)

Lemma lem_ftyp_islc : forall (g:fenv) (e:expr) (t:ftype),
    HasFtype g e t -> isLC e.
Proof. intros; induction H; unfold isLC; simpl; intuition. 
  - (* FTAbs *) pose proof (fresh_not_elem nms);
    set (y := fresh nms) in H2; apply H1 in H2.
    revert H2; unfold isLC.
    apply lem_islc_at_after_open_at.
  - (* FTAbsT *) pose proof (fresh_not_elem nms);
    set (a' := fresh nms) in H1; apply H0 in H1.
    revert H1; unfold isLC.
    apply lem_islc_at_after_open_tv_at.
  - (* FTLet *) pose proof (fresh_not_elem nms);
    set (y := fresh nms) in H2; apply H1 in H2.
    revert H2; unfold isLC.
    apply lem_islc_at_after_open_at.
  Qed.

Lemma lem_pftyp_islcp : forall (g:fenv) (ps:preds),
    PHasFtype g ps -> isLCP ps.
Proof. intros; induction H; unfold isLCP; simpl; try split.
  apply lem_ftyp_islc with g (FTBasic TBool); apply H.
  apply IHPHasFtype. Qed.

Lemma lem_wfft_islcft : forall (g:fenv) (t:ftype) (k:kind),
    WFFT g t k -> isLCFT t.
Proof. intros; induction H; unfold isLCFT; simpl; intuition.
  - (* WFFTBasic *) destruct b; simpl in H; intuition.
  - (* WFFTPoly  *) assert (1 = 0 + 1) by intuition; rewrite H1.
    pose proof (fresh_varF_not_elem nms g); destruct H2.
    apply lem_islcft_at_after_openFT_at with (fresh_varF nms g).
    apply H0; assumption.
  Qed.