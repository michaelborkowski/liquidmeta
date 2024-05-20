Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.PrimitivesFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.BasicPropsWellFormedness.
Require Import SystemRF.Typing.
Require Import SystemRF.LemmasTyping.
Require Import SystemRF.LemmasSubtyping.
Require Import SystemRF.LemmasNarrowing.
Require Import SystemRF.LemmasTransitive. 

(* -- A collection of Lemmas about inverting typing judgements for abstraction types. In our
   --   system this is not trivial because TSub could be used finitely many times to produce
   --   the judgment. The key point is to use transitivity of subtyping to collapse a chain
   --   of applications of T-Sub to a single use of T-Sub *)

Lemma lem_invert_lambda : forall (g:env) (le:expr) (t:type),
  Hastype g le t -> (forall (e : expr) (s_x s : type),
    le = Lambda e -> WFEnv g -> Subtype g t (TFunc s_x s)
                  -> WFtype g (TFunc s_x s) Star
                  -> exists nms, forall (y:vname), (~ Elem y nms 
                      -> Hastype (ECons y s_x g) (unbind y e) (unbindT y s))).
Proof. apply ( Hastype_ind
    ( fun (g:env) (le:expr) (t:type) => forall (e : expr) (s_x s : type),
        le = Lambda e -> WFEnv g -> Subtype g t (TFunc s_x s) 
                      -> WFtype g (TFunc s_x s) Star
                      -> exists nms, forall (y:vname), (~ Elem y nms 
                          -> Hastype (ECons y s_x g) (unbind y e) (unbindT y s)))
  ); try discriminate; intros.
  - (* isTAbs *) inversion H4; injection H2 as H2; subst e0;   (* invert SFunc *)
    inversion H5; try inversion H2;                             (* invert WFFunc *)
    exists (union (union (union nms nms0) nms1) (binds g)); intros;
    repeat (apply not_elem_union_elim in H18; destruct H18);
    apply TSub with (unbindT y t) k;
    try apply lem_narrow_typ_top with t_x k_x0 k_x;
    try apply H0; try apply H16; try apply H12; 
    try apply wfenv_unique; try assumption.
  - (* isTSub *)
    apply H0; try apply lem_sub_trans with t Star k Star;
    try (apply lem_typing_wf with e; assumption); assumption.
  Qed.

Lemma lem_invert_tabs : forall (g:env) (e:expr) (t_x t:type),
    Hastype g (Lambda e) (TFunc t_x t) 
                  -> WFEnv g -> WFtype g (TFunc t_x t) Star
                  -> exists nms, forall (y:vname), (~ Elem y nms 
                          -> Hastype (ECons y t_x g) (unbind y e) (unbindT y t)).
Proof. intros; inversion H.
  - (* isTAbs *) exists nms; apply H7.
  - (* isTSub *) apply lem_invert_lambda with (Lambda e) s;
    destruct k; try (apply H3 || (apply WFKind; apply H3)); trivial.
  Qed.

Lemma lem_invert_lambdat : forall (g:env) (lke:expr) (t:type),
    Hastype g lke t -> ( forall (k:kind) (e:expr) (s:type),
        lke = LambdaT k e -> WFEnv g -> Subtype g t (TPoly k s)
                          -> WFtype g (TPoly k s) Star
                          -> exists nms, forall (a:vname), ( ~ Elem a nms 
                                -> Hastype (EConsT a k g) (unbind_tv a e) (unbind_tvT a s))).
Proof. apply ( Hastype_ind
    ( fun (g:env) (lke:expr) (t:type) => forall (k:kind) (e:expr) (s:type),
        lke = LambdaT k e -> WFEnv g -> Subtype g t (TPoly k s)
                          -> WFtype g (TPoly k s) Star
                          -> exists nms, forall (a:vname), ( ~ Elem a nms 
                               -> Hastype (EConsT a k g) (unbind_tv a e) (unbind_tvT a s)))  
  ); try discriminate; intros.
  - (* isTAbsT *) inversion (* of SPoly *) H3; injection H1 as H1 H1'; subst k0 e0;
    inversion (* of WFPoly *) H4; try inversion H1;
    exists (union (union (union nms nms0) nms1) (binds g)); intros;
    repeat (apply not_elem_union_elim in H15; destruct H15);
    apply TSub with (unbind_tvT a t) k_t;
    try apply H; try apply H12; try apply H7; trivial.
  - (* isTSub *) apply H0; try apply lem_sub_trans with t Star k Star;
    try (apply lem_typing_wf with e; assumption); assumption.
  Qed.

Lemma lem_invert_tabst : forall (g:env) (k:kind) (e:expr) (t:type),
    Hastype g (LambdaT k e) (TPoly k t) 
                  -> WFEnv g -> WFtype g (TPoly k t) Star
                  -> exists nms, forall (a:vname), (~ Elem a nms 
                          -> Hastype (EConsT a k g) (unbind_tv a e) (unbind_tvT a t)).
Proof. intros; inversion H.
  - (* isTAbs *) exists nms; assumption.
  - (* isTSub *) apply lem_invert_lambdat with (LambdaT k e) s; trivial.
  Qed.

Lemma lem_lambdaT_tpoly_same_kind' : forall (g:env) (lke:expr) (t:type),
    Hastype g lke t -> ( forall (k k':kind) (e:expr) (s:type),
        lke = LambdaT k e -> WFEnv g -> Subtype g t (TPoly k' s)
                          -> WFtype g (TPoly k' s) Star
                          -> k = k').
Proof. apply ( Hastype_ind
    ( fun (g:env) (lke:expr) (t:type) => forall (k k':kind) (e:expr) (s:type),
        lke = LambdaT k e -> WFEnv g -> Subtype g t (TPoly k' s)
                          -> WFtype g (TPoly k' s) Star
                          -> k = k') 
  ); try discriminate; intros.
  - (* isTAbsT *) inversion H3; injection H1 as Hk0 He0; subst k0; assumption.
  - (* isTSub *) apply H0 with e0 s0; try apply lem_sub_trans with t Star k Star;
    try assumption; try apply lem_typing_wf with e; trivial. Qed.

Lemma lem_lambdaT_tpoly_same_kind : forall (g:env) (k k':kind) (e:expr) (t:type),
    Hastype g (LambdaT k e) (TPoly k' t) -> WFEnv g -> WFtype g (TPoly k' t) Star  
                                        -> k = k'.
Proof. intros; inversion H.
  - (* isTAbsT *) reflexivity.
  - (* isTSub  *) apply lem_lambdaT_tpoly_same_kind'
       with g (LambdaT k e) s e t; trivial. Qed.

Lemma lem_exact_length_type : 
  forall (g:env) (v:expr) (t:type) (ps:preds) (k:kind),
    isList v -> isValue v 
      -> Hastype g v (TList t ps) -> WFtype g t k -> WFEnv g 
      -> Hastype g v (TList t (PCons (eq (length t (BV 0)) (length t v)) ps)).
Proof.  intros. destruct v;
  simpl in H; try contradiction.
  pose proof TNil. pose proof TCons.
  apply TSub with (TList t ps) Star.
  Focus 3. 
  apply SList with (binds g).
  Focus 2.
  intros.

Lemma lem_invert_cons : forall (g:env) (ce:expr) (t:type),
  Hastype g ce t -> (forall (v1 v2 : expr) (s : type),
    ce = Cons v1 v2 -> WFEnv g -> Subtype g t (TList s PEmpty)
                    -> WFtype g s Star
                    -> Hastype g v2 (TList s PEmpty)).
Proof. apply ( Hastype_ind
    ( fun (g:env) (ce:expr) (t:type) => forall (v1 v2 : expr) (s : type),
        ce = Cons v1 v2 -> WFEnv g -> Subtype g t (TList s PEmpty) 
                        -> WFtype g s Star
                        -> Hastype g v2 (TList s PEmpty))
  ); try discriminate; intros.
  - (* isTCons *) injection H5 as Hv1 Hv2; subst eH eT.
    apply lem_typing_wf in H1 as p_g_t; try apply H6.
    apply lem_wftype_islct in p_g_t as Hlct.
    apply TSub with 
      (TExists (TList t ps) 
        (TList t (PCons (eq (length t (BV 0)) 
                          (App (Prim Succ) (length t (BV 1)))) PEmpty)))
      Star; try apply H7.
    pose proof SBind as HSB.
    pose proof SWitn as HSW.
    apply TSub with 
      (tsubBV v2 (TList t (PCons (eq (length t (BV 0)) 
                                    (App (Prim Succ) (length t (BV 1)))) PEmpty)))
      Star.
    unfold tsubBV; simpl.
    pose proof lem_subBV_at_lc_at as [_ [Hsubt _]];
    repeat rewrite Hsubt with t 1 v2 0 0;
    try rewrite Hsubt with t 0 v2 0 0; auto.
    apply TSub with (TList t ps) Star; try apply H3.
    Focus 2.
    apply SList with (binds g); try apply lem_sub_refl with Star;
    try apply p_g_t; intros.
    
    
  
  
  inversion H5; subst eH eT. 
    inversion H7.
    set (y := fresh nms). pose proof (fresh_not_elem nms);
    apply (H14 y) in H15 as Hsub;
    unfold unbindT in Hsub; simpl in Hsub. inversion Hsub.
    apply lem_typing_wf in H1 as p_g_t;
    try apply lem_wftype_islct in p_g_t as Hlct;
    pose proof lem_open_at_lc_at as [_ [Hopen _]];
    try rewrite Hopen with t 0 0 y in H20. 
    pose proof SList.

    inversion H5; try inversion H2;                             (* invert WFFunc *)
    apply TSub with (TExists (TList t ps) (TList t (PCons (eq (length t (BV 0)) (App (Prim Succ) (length t (BV 1)))) PEmpty))) Star.
    try apply TCons. apply TCons.
    
    try apply lem_narrow_typ_top with t_x k_x0 k_x;
    try apply H0; try apply H16; try apply H12; 
    try apply wfenv_unique; try assumption.
  - (* isTSub *)
    apply H0; try apply lem_sub_trans with t Star k Star;
    try (apply lem_typing_wf with e; assumption); assumption.
  Qed.       

Lemma lem_invert_tlist : forall (g:env) (v1 v2:expr) (t:type),
    Hastype g (Cons v1 v2) (TList t PEmpty) 
                  -> WFEnv g -> WFtype g t Star
                  -> isValue v1 -> isValue v2
                  -> Hastype g v2 (TList t PEmpty).
Proof. intros; inversion H.
  - (* isTAbs *) exists nms; apply H7.
  - (* isTSub *) apply lem_invert_lambda with (Lambda e) s;
    destruct k; try (apply H3 || (apply WFKind; apply H3)); trivial.
  Qed.       