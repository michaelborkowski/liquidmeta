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

Lemma lem_appT_wf' : forall (g:env) (es:expr) (t:type),
    Hastype g es t -> ( forall (e:expr) (s s_x s':type),
        es = AppT e s -> WFEnv g -> Subtype g t (TFunc s_x s')
                      -> WFtype g (TFunc s_x s') Star
                      -> WFtype g s Star ).
Proof. apply ( Hastype_ind
    ( fun (g:env) (es:expr) (t:type) => forall (e:expr) (s s_x s':type),
        es = AppT e s -> WFEnv g -> Subtype g t (TFunc s_x s')
                      -> WFtype g (TFunc s_x s') Star
                      -> WFtype g s Star) 
); try discriminate; intros. 
  - (* isTAppT *) injection H4 as H4'; subst e0 s0;
    destruct k; try apply H3; apply WFKind; apply H3.
  - (* isTSub *) apply H0 with e0 s_x s';
    try apply lem_sub_trans with t Star k Star; trivial;
    try apply lem_typing_wf with e; trivial. Qed.

Lemma lem_appT_wf : forall (g:env) (e:expr) (t s_x s:type),
    Hastype g (AppT e t) (TFunc s_x s) 
        -> WFEnv g -> WFtype g (TFunc s_x s) Star  
        -> WFtype g t Star.
Proof. intros; inversion H.
  - (* isTAppT *) destruct k; try apply H9; apply WFKind; apply H9.
  - (* isTSub  *) apply lem_appT_wf'
        with (AppT e t) (TFunc s_x s) e s_x s; 
      try apply lem_sub_refl with Star; trivial. 
  Qed.    