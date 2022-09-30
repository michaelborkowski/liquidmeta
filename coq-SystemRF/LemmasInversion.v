Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
(*import SystemFWellFormedness*)
(*import SystemFTyping*)
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.BasicPropsWellFormedness.
Require Import SystemRF.Typing.
Require Import SystemRF.LemmasTyping.
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
                      -> Hastype (Cons y s_x g) (unbind y e) (unbindT y s))).
Proof. apply ( Hastype_ind
    ( fun (g:env) (le:expr) (t:type) => forall (e : expr) (s_x s : type),
        le = Lambda e -> WFEnv g -> Subtype g t (TFunc s_x s) 
                      -> WFtype g (TFunc s_x s) Star
                      -> exists nms, forall (y:vname), (~ Elem y nms 
                          -> Hastype (Cons y s_x g) (unbind y e) (unbindT y s)))
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
                          -> Hastype (Cons y t_x g) (unbind y e) (unbindT y t)).
Proof. intros; inversion H.
  - (* isTAbs *) exists nms; apply H7.
  - (* isTSub *) apply lem_invert_lambda with (Lambda e) s;
    destruct k; try (apply H3 || (apply WFKind; apply H3)); trivial.
  Qed.

(*
{-@ lem_lambdaT_tsub_no_sbind :: g:env -> k:kind -> e:expr -> s:type -> k':kind -> t:type
        -> { p_le_s:Hastype | propOf p_le_s == Hastype g (LambdaT k e) s && not (isTSub p_le_s) }
        -> { p_s_t:Subtype  | propOf p_s_t  == Subtype g s (TPoly k' t) }
        -> { pf:_ | isSPoly p_s_t } @-} -- && not (isSBind p_s_t) } @-}
lem_lambdaT_tsub_no_sbind :: env -> kind -> expr -> type -> kind -> type 
                                 -> Hastype -> Subtype -> Proof
lem_lambdaT_tsub_no_sbind g k e s k' t' p_le_s p_s_t = case p_s_t of
  (SPoly {}) -> ()
  (SBind {}) -> case p_le_s of
    (TAbsT {}) -> impossible "s must be TPoly"

{-@ lem_invert_tabst :: g:env -> k:kind -> e:expr -> t:type
       -> ProofOf(Hastype g (LambdaT k e) (TPoly k t)) -> ProofOf(WFEnv g)
       -> { p'_e_t:Hastype | propOf  p'_e_t == Hastype g (LambdaT k e) (TPoly k t) &&
                             isTAbsT p'_e_t } @-}
lem_invert_tabst :: env -> kind -> expr -> type -> Hastype -> WFEnv -> Hastype
lem_invert_tabst g k e t' p_le_kt' p_g_wf = case p_le_kt' of
  (TAbsT {}) -> p_le_kt'
  (TSub {}) 
    -> let (TSub _ _ _ s p_le_s _ k_t p_g_kt' p_s_t)
               = lem_collapse_sub g (LambdaT k e) (TPoly k t') p_g_wf p_le_kt'
         in case p_s_t of
              (SPoly n _ _ _ _ nms mk_p_s'_t')
                  -> TAbsT (max n n' + 1) g k e t' nms''' mk_p_e_t'
                where
                  {-@ mk_p_e_t' :: { a:vname | NotElem a nms''' }
                        -> { pf:Hastype | propOf pf ==
                                Hastype (ConsT a k g) (unbind_tv a e) (unbind_tvT a t') &&
                                          sizeOf pf <= max n n' + 1 } @-}
                   mk_p_e_t' a = TSub (max n n') (ConsT a k g) (unbind_tv a e) (unbind_tvT a s')
                                      (mk_p_e_s' a) (unbind_tvT a t') k_t' (mk_p_ag_t' a)
                                      (mk_p_s'_t' a)
                   (TAbsT n' _ _ _ s' nms'  mk_p_e_s')  = p_le_s
                   (WFPoly _ _ _ k_t' nms'' mk_p_ag_t') 
                     = lem_wfpoly_for_wf_tpoly' g k t' k_t p_g_kt'
                   nms'''      = unionEnv (union nms (union nms' nms'')) g
              (SBind {}) -> impossible ("by" ? lem_lambdaT_tsub_no_sbind g k e s k t' p_le_s p_s_t)

{-@ lem_lambdaT_tpoly_same_kind :: g:env -> k:kind -> e:expr -> k':kind -> t':type 
       -> { p_ke_k't':Hastype | propOf p_ke_k't' == Hastype g (LambdaT k e) (TPoly k' t') }
       -> ProofOf(WFEnv g) -> { pf:_              | k == k' } / [sizeOf p_ke_k't'] @-}
lem_lambdaT_tpoly_same_kind :: env -> kind -> expr -> kind -> type -> Hastype -> WFEnv -> Proof
lem_lambdaT_tpoly_same_kind g k e k' t' p_ke_k't' p_g_wf = case p_ke_k't' of
  (TAbsT {}) -> ()
  (TSub {})  -> case lem_collapse_sub g (LambdaT k e) (TPoly k' t') p_g_wf p_ke_k't' of
    (TSub _ _ _ s p_ke_s _ _ _ p_s_t) -> case p_s_t of
      (SPoly {}) -> case p_ke_s of
        (TAbsT {}) -> ()
      (SBind {}) -> impossible ("by" ? lem_lambdaT_tsub_no_sbind g k e s k' t' p_ke_s p_s_t)
*)