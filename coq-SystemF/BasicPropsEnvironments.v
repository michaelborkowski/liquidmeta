Require Import Lists.ListSet.

Require Import SystemRF.BasicDefinitions.  (* originally 350 lines*)
Require Import SystemRF.Names.
Require Import SystemRF.SystemFWellFormedness.
Require Import SystemRF.SystemFTyping.
(*import BasicPropsSubstitution*)

(*----------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of ENVIRONMENTS / BARE-TYPED ENVIRONMENTS
----------------------------------------------------------------------------*)

(*
{-@ concatE :: g:env -> { g':env | Set_emp (Set_cap (binds g) (binds g')) } 
                     -> { h:env | binds h   == (Set_cup (binds g)   (binds g')) &&
                                  vbinds h  == (Set_cup (vbinds g)  (vbinds g')) &&
                                  tvbinds h == (Set_cup (tvbinds g) (tvbinds g')) } @-}
concatE :: env -> env -> env
concatE g Empty          = g
concatE g (Cons  x t g') = Cons x t  (concatE g g')
concatE g (ConsT a k g') = ConsT a k (concatE g g')

{-@ lem_empty_concatE :: g:env -> { pf:_ | concatE Empty g == g } @-}
lem_empty_concatE :: env -> Proof
lem_empty_concatE Empty         = ()
lem_empty_concatE (Cons  x t g) = () ? lem_empty_concatE g
lem_empty_concatE (ConsT a k g) = () ? lem_empty_concatE g

{-@ lem_in_env_concat :: g:env -> { g':env | Set_emp (Set_cap (binds g) (binds g')) } 
      ->  x:vname -> {pf:_ | (in_env x (concatE g g')) <=> ((in_env x g) || (in_env x g'))} @-}
lem_in_env_concat :: env -> env -> vname -> Proof
lem_in_env_concat g Empty          x = ()
lem_in_env_concat g (Cons  y s g') x = () ? lem_in_env_concat g g' x 
lem_in_env_concat g (ConsT a k g') x = () ? lem_in_env_concat g g' x
*)

Lemma lem_erase_tsubFV : forall (x:vname) (v:expr) (t:type),
    isValue v -> erase (tsubFV x v t) = erase t.
Proof. intros; induction t; simpl.
  - (* TRefn *) reflexivity.
  - (* TFunc *) apply f_equal2; apply IHt1 || apply IHt2.
  - (* TExis *) apply IHt2.
  - (* TPoly *) apply f_equal; apply IHt.
  Qed.

(*
{-@ lem_erase_unbind_tvT :: a':vname -> t:type 
	-> { pf:_ | erase (unbind_tvT a' t) == unbindFT a' (erase t) } @-}
lem_erase_unbind_tvT :: vname -> type -> Proof
lem_erase_unbind_tvT a' t = lem_erase_open_tvT_at 0 a' t

{-@ lem_erase_open_tvT_at :: j:index -> a:vname -> t:type 
        -> { pf:_ | erase (open_tvT_at j a t) == openFT_at j a (erase t) } @-}
lem_erase_open_tvT_at :: index -> vname -> type -> Proof
lem_erase_open_tvT_at j a (TRefn   b  ps) = case b of
  (BTV a') -> () 
  _        -> ()
lem_erase_open_tvT_at j a (TFunc   t_z t) = () ? lem_erase_open_tvT_at j a t_z
                                               ? lem_erase_open_tvT_at j a t
lem_erase_open_tvT_at j a (TExists t_z t) = () ? lem_erase_open_tvT_at j a t
lem_erase_open_tvT_at j a (TPoly    k1 t) = () ? lem_erase_open_tvT_at (j+1) a t
*)

Lemma lem_erase_push : forall (ps:preds) (t:type),
    noExists t -> erase (push ps t) = erase t.
Proof. intros ps; destruct t; simpl; intuition. Qed.

Lemma lem_erase_tsubFTV : forall (a:vname) (t_a:type) (t:type),
    noExists t_a -> erase (tsubFTV a t_a t) = ftsubFV a (erase t_a) (erase t).
Proof. intros; induction t; simpl.
  - (* TRefn *) destruct b; try destruct (Nat.eqb a a0); simpl;
    try apply lem_erase_push; trivial.
  - (* TFunc *) apply f_equal2; apply IHt1 || apply IHt2.
  - (* TExis *) apply IHt2.
  - (* TPoly *) apply f_equal; apply IHt.
  Qed.

(*
{-@ lem_erase_tsubBTV :: t_a:Usertype -> t:type
        -> { pf:_ | erase (tsubBTV t_a t) == ftsubBV (erase t_a) (erase t) } @-}
lem_erase_tsubBTV :: type -> type -> Proof
lem_erase_tsubBTV t_a t = lem_erase_tsubBTV_at 0 t_a t

{-@ lem_erase_tsubBTV_at :: j:index -> t_a:Usertype -> t:type
        -> { pf:_ | erase (tsubBTV_at j t_a t) == ftsubBV_at j (erase t_a) (erase t) } @-}
lem_erase_tsubBTV_at :: index -> type -> type -> Proof
lem_erase_tsubBTV_at j t_a (TRefn   b   p) = case b of
  (BTV i) | i == j -> () ? lem_erase_push (psubBTV_at j t_a p) t_a 
  _                -> ()
lem_erase_tsubBTV_at j t_a (TFunc   t_z t) = () ? lem_erase_tsubBTV_at j t_a t_z
                                                ? lem_erase_tsubBTV_at j t_a t
lem_erase_tsubBTV_at j t_a (TExists t_z t) = () ? lem_erase_tsubBTV_at j t_a t
lem_erase_tsubBTV_at j t_a (TPoly    k' t) = () ? lem_erase_tsubBTV_at (j+1) t_a t
*)


Fixpoint concatF (g g'0 : fenv) : fenv :=
    match g'0 with
    | FEmpty          => g
    | (FCons  x t g') => FCons  x t (concatF g g')
    | (FConsT a k g') => FConsT a k (concatF g g')
    end.

Lemma lem_binds_concatF : forall (g g' : fenv),
    Subset (bindsF (concatF g g')) (union (bindsF g) (bindsF g')) /\
    Subset (union (bindsF g) (bindsF g')) (bindsF (concatF g g')).
Proof. intros; induction g'; simpl; unfold Subset; split
  ; try (unfold Subset in IHg'; destruct IHg')
  ; try (apply subset_refl)
  ; intros
  ; try ( apply set_add_elim in H1; apply subset_union_names_add_r;
          apply set_add_intro; destruct H1; try apply H in H1; intuition )
  ; try ( apply set_add_intro; apply subset_union_names_add_r in H1; 
          apply set_add_elim in H1; destruct H1; try apply H0 in H1; intuition ).
  Qed.

Lemma lem_vbinds_concatF : forall (g g' : fenv),
  Subset (union (vbindsF g) (vbindsF g')) (vbindsF (concatF g g')).
Proof. intros; induction g'; simpl; try apply subset_refl;
  try apply subset_trans with (names_add x (union (vbindsF g) (vbindsF g')));
  try apply subset_union_names_add_r;
  try apply subset_add_both_intro; apply IHg'.
  Qed.

Lemma lem_tvbinds_concatF : forall (g g' : fenv),
  Subset (union (tvbindsF g) (tvbindsF g')) (tvbindsF (concatF g g')).
Proof. intros; induction g'; simpl; try apply subset_refl;
  try apply subset_trans with (names_add a (union (tvbindsF g) (tvbindsF g')));
  try apply subset_union_names_add_r;
  try apply subset_add_both_intro; apply IHg'.
  Qed.

Lemma lem_vbinds_cons_concatF : forall (g g' : fenv) (x : vname) (t_x : ftype),
    Subset (vbindsF (concatF g g'))  (vbindsF (concatF (FCons x t_x g) g')) /\
    Subset (vbindsF (concatF (FCons x t_x g) g')) (names_add x (vbindsF (concatF g g'))).
Proof. intros; induction g'; split; simpl;
  try apply subset_add_both_intro; try (apply subset_add_intro; apply subset_refl);
  try apply subset_refl; try apply IHg';
  apply subset_trans with (names_add x0 (names_add x (vbindsF (concatF g g'))));
  try apply subset_add_both_intro; try apply subset_add_commute; apply IHg'.
  Qed.

Lemma lem_tvbinds_cons_concatF : forall (g g' : fenv) (x : vname) (t_x : ftype),
    Subset (tvbindsF (concatF g g')) (tvbindsF (concatF (FCons x t_x g) g')) /\
    Subset (tvbindsF (concatF (FCons x t_x g) g')) (tvbindsF (concatF g g')).
Proof. intros; induction g'; split; simpl;
  try apply subset_refl; try apply subset_add_both_intro; intuition. Qed.

Lemma lem_vbinds_consT_concatF : forall (g g' : fenv) (a : vname) (k : kind),
    Subset (vbindsF (concatF g g'))  (vbindsF (concatF (FConsT a k g) g')) /\
    Subset (vbindsF (concatF (FConsT a k g) g')) (vbindsF (concatF g g')).
Proof. intros; induction g'; split; simpl;
  try apply subset_refl; try apply subset_add_both_intro; intuition. Qed.

Lemma lem_tvbinds_consT_concatF : forall (g g' : fenv) (a : vname) (k : kind),
    Subset (tvbindsF (concatF g g')) (tvbindsF (concatF (FConsT a k g) g')) /\
    Subset (tvbindsF (concatF (FConsT a k g) g')) (names_add a (tvbindsF (concatF g g'))).
Proof. intros; induction g'; split; simpl;
  try apply subset_add_both_intro; try (apply subset_add_intro; apply subset_refl);
  try apply subset_refl; try apply IHg';
  apply subset_trans with (names_add a0 (names_add a (tvbindsF (concatF g g'))));
  try apply subset_add_both_intro; try apply subset_add_commute; apply IHg'.
  Qed.

Lemma not_elem_concatF_elim : forall (x : vname) (g g' : fenv),
    ~ Elem x (bindsF (concatF g g')) -> ~ Elem x (bindsF g) /\ ~ Elem x (bindsF g').
Proof. intros; assert 
    (Subset (union (bindsF g) (bindsF g')) (bindsF (concatF g g'))) 
  by apply lem_binds_concatF; pose proof (not_elem_subset x); 
  apply H1 in H0; try assumption. apply not_elem_union_elim in H0; assumption.
  Qed.

Lemma not_elem_concatF_intro : forall (x : vname) (g g' : fenv),
    ~ Elem x (bindsF g) -> ~ Elem x (bindsF g') -> ~ Elem x (bindsF (concatF g g')).
Proof. intros; pose proof (lem_binds_concatF g g'); destruct H1;
  pose proof (not_elem_subset x); apply H3 with (union (bindsF g) (bindsF g'));
  apply (not_elem_union_intro x (bindsF g) (bindsF g') H) in H0; 
  try assumption.
  Qed.

Lemma uniqueF_concatF : forall (g g' : fenv),
    uniqueF g -> uniqueF g' -> intersect (bindsF g) (bindsF g') = empty
              -> uniqueF (concatF g g').
Proof. intros; induction g'; simpl; try assumption; split;
  simpl in H0; destruct H0; simpl in H1;
  apply intersect_names_add_elim_r in H1; destruct H1;
  try (apply not_elem_concatF_intro with x g g' in H3 as H4 ||
       apply not_elem_concatF_intro with a g g' in H3 as H4 ; assumption);
  apply IHg' in H2; assumption.
  Qed.

Lemma lem_boundinF_concatF : forall (x:vname) (t:ftype) (g g':fenv),
  bound_inF x t (concatF g g') <-> bound_inF x t g \/ bound_inF x t g'.
Proof. intros; induction g'; simpl; intuition. Qed.

Lemma lem_boundinF_weaken : forall (x:vname) (t:ftype) (g g':fenv) (y:vname) (t_y:ftype),
  bound_inF x t (concatF g g') -> bound_inF x t (concatF (FCons y t_y g) g').
Proof. intros; apply lem_boundinF_concatF; simpl; 
  apply lem_boundinF_concatF in H; intuition. Qed.

Lemma lem_boundinF_weaken_tv : forall (x:vname) (t:ftype) (g g':fenv) (a:vname) (k:kind),
  bound_inF x t (concatF g g') -> bound_inF x t (concatF (FConsT a k g) g').
Proof. intros; apply lem_boundinF_concatF; simpl;
  apply lem_boundinF_concatF in H; intuition. Qed.

Lemma lem_tvboundinF_concatF : forall (a:vname) (k:kind) (g g':fenv),
  tv_bound_inF a k (concatF g g') <-> tv_bound_inF a k g \/ tv_bound_inF a k g'.
Proof. intros; induction g'; simpl; intuition. Qed.

Lemma lem_tvboundinF_weaken : forall (a:vname) (k:kind) (g g':fenv) (x:vname) (t:ftype),
  tv_bound_inF a k (concatF g g') -> tv_bound_inF a k (concatF (FCons x t g) g').
Proof. intros; apply lem_tvboundinF_concatF; simpl; 
  apply lem_tvboundinF_concatF; assumption. Qed.

Lemma lem_tvboundinF_weaken_tv : forall (a:vname) (k:kind) (g g':fenv) (a':vname) (k':kind),
  tv_bound_inF a k (concatF g g') -> tv_bound_inF a k (concatF (FConsT a' k' g) g').
Proof. intros; apply lem_tvboundinF_concatF; simpl;
  apply lem_tvboundinF_concatF in H; intuition. Qed.

Lemma lem_tvboundinF_strengthen : forall (a:vname) (k:kind) (g g':fenv) (x:vname) (t:ftype),
  tv_bound_inF a k (concatF (FCons x t g) g') -> tv_bound_inF a k (concatF g g').
Proof. intros; apply lem_tvboundinF_concatF in H; simpl in H;
  apply lem_tvboundinF_concatF; assumption. Qed.

(*

{-@ lem_empty_concatF :: g:fenv -> { pf:_ | concatF FEmpty g == g } @-}
lem_empty_concatF :: fenv -> Proof
lem_empty_concatF FEmpty         = ()
lem_empty_concatF (FCons  x t g) = () ? lem_empty_concatF g
lem_empty_concatF (FConsT a k g) = () ? lem_empty_concatF g

{-@ lem_erase_concat :: g:env -> g':env 
           -> { pf:_ |  erase_env (concatE g g') == concatF (erase_env g) (erase_env g') } @-}
lem_erase_concat :: env -> env -> Proof
lem_erase_concat g Empty          = ()
lem_erase_concat g (Cons  x t g') = () ? lem_erase_concat g g'
lem_erase_concat g (ConsT a k g') = () ? lem_erase_concat g g'
*)

(* -- -- -- -- -- -- -- -- -- -- -- --
   -- Substitutions in Environments --
   -- -- -- -- -- -- -- -- -- -- -- -- *)

(*
{-@ esubFV :: x:vname -> v:Value -> g:env 
      -> { g':env | binds g == binds g' && vbinds g == vbinds g' && tvbinds g == tvbinds g' } @-}
esubFV :: vname -> expr -> env -> env
esubFV x e_x Empty           = Empty
esubFV x e_x (Cons  z t_z g) = Cons z (tsubFV x e_x t_z) (esubFV x e_x g)
esubFV x e_x (ConsT a k   g) = ConsT a k                 (esubFV x e_x g)

{-@ lem_in_env_esub :: g:env -> x:vname -> v_x:Value -> y:vname
        -> { pf:_ | in_env y (esubFV x v_x g) <=> in_env y g } @-}
lem_in_env_esub :: env -> vname -> expr -> vname -> Proof
lem_in_env_esub Empty           x v_x y = ()
lem_in_env_esub (Cons  z t_z g) x v_x y = () ? lem_in_env_esub g x v_x y
lem_in_env_esub (ConsT a k   g) x v_x y = () ? lem_in_env_esub g x v_x y

{-@ lem_erase_esubFV :: x:vname -> v:Value -> g:env
        -> { pf:_ | erase_env (esubFV x v g) == erase_env g } @-}
lem_erase_esubFV :: vname -> expr -> env -> Proof
lem_erase_esubFV x e (Empty)       = ()
lem_erase_esubFV x e (Cons  y t g) = () ? lem_erase_esubFV x e g
                                        ? lem_erase_tsubFV x e t
lem_erase_esubFV x e (ConsT a k g) = () ? lem_erase_esubFV x e g

{-@ reflect esubFTV @-}
{-@ esubFTV :: a:vname -> t_a:Usertype -> g:env 
      -> { g':env | binds g == binds g' && vbinds g == vbinds g' && tvbinds g == tvbinds g' } @-}
esubFTV :: vname -> type -> env -> env
esubFTV a t_a Empty           = Empty
esubFTV a t_a (Cons  z t_z g) = Cons z (tsubFTV a t_a t_z) (esubFTV a t_a g)
esubFTV a t_a (ConsT a' k' g) = ConsT a' k'                (esubFTV a t_a g)

{-@ lem_in_env_esubFTV :: g:env -> a:vname -> t_a:Usertype -> y:vname
        -> { pf:_ | in_env y (esubFTV a t_a g) <=> in_env y g } @-}
lem_in_env_esubFTV :: env -> vname -> type -> vname -> Proof
lem_in_env_esubFTV Empty           a t_a y = ()
lem_in_env_esubFTV (Cons  z t_z g) a t_a y = () ? lem_in_env_esubFTV g a t_a y
lem_in_env_esubFTV (ConsT a' k' g) a t_a y = () ? lem_in_env_esubFTV g a t_a y

{-@ lem_erase_esubFTV :: a:vname -> t_a:Usertype -> g:env
        -> { pf:_ | erase_env (esubFTV a t_a g) == fesubFV a (erase t_a) (erase_env g) } @-}
lem_erase_esubFTV :: vname -> type -> env -> Proof
lem_erase_esubFTV a t_a (Empty)        = ()
lem_erase_esubFTV a t_a (Cons  y t g)  = () ? lem_erase_esubFTV a t_a g
                                            ? lem_erase_tsubFTV a t_a t
lem_erase_esubFTV a t_a (ConsT a' k g) = () ? lem_erase_esubFTV a t_a g
*)

(*  -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
    -- Substitutions in Systen F Environments --
    -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- *)

Fixpoint fesubFV (a:vname) (t_a:ftype) (g0:fenv) : fenv :=
    match g0 with 
    | FEmpty           => FEmpty
    | (FCons  z t_z g) => FCons z (ftsubFV a t_a t_z) (fesubFV a t_a g)
    | (FConsT a1  k g) => FConsT a1 k                 (fesubFV a t_a g)
    end.

Lemma fesubFV_bindsF : forall (a:vname) (t_a:ftype) (g:fenv),
    bindsF (fesubFV a t_a g) = bindsF g.
Proof. intros; induction g; simpl; try (rewrite IHg); reflexivity. Qed.

Lemma concatF_fesubFV_vbindsF : forall (g:fenv) (a:vname) (t_a:ftype) (g':fenv),
    vbindsF (concatF g (fesubFV a t_a g')) = vbindsF (concatF g g').
Proof. intros; induction g'; simpl; try (rewrite IHg'); reflexivity. Qed.

Lemma concatF_fesubFV_tvbindsF : forall (g:fenv) (a:vname) (t_a:ftype) (g':fenv),
  tvbindsF (concatF g (fesubFV a t_a g')) = tvbindsF (concatF g g').
Proof. intros; induction g'; simpl; try (rewrite IHg'); reflexivity. Qed.

Lemma fesubFV_uniqueF : forall (a:vname) (t_a:ftype) (g:fenv),
    uniqueF g -> uniqueF (fesubFV a t_a g).
Proof. intros; induction g; simpl; simpl in H; try reflexivity;
  destruct H; split; unfold in_envF; try (rewrite fesubFV_bindsF);
  apply IHg in H0; assumption. Qed.

Lemma lem_boundinF_fesubFV : forall (x:vname) (t:ftype) (a:vname) (t_a:ftype) (g:fenv),
    bound_inF x t g -> bound_inF x (ftsubFV a t_a t) (fesubFV a t_a g).
Proof. intros; induction g; simpl; simpl in H; try contradiction. 
  - destruct H; try destruct H; try subst x0; try subst t0.
    * left; auto.
    * right; apply IHg; assumption.
  - apply IHg; assumption.
  Qed. 

Lemma lem_tvboundinF_fesubFV : forall (a0:vname) (k0:kind) (a:vname) (t:ftype) (g:fenv),
    tv_bound_inF a0 k0 g <-> tv_bound_inF a0 k0 (fesubFV a t g).
Proof. intros; induction g; simpl; intuition. Qed.

(*-----------------------------------------------------------------------------------------
----- | TECHNICAL LEMMAS relating to FREE VARIABLES and SYSTEM F judgments
-----------------------------------------------------------------------------------------*)

(* -- Lemma. All free variables in a (System F) typed expression are bound in the (System F) environment *)
Lemma lem_fv_subset_bindsF : forall (g : fenv) (e : expr) (t : ftype),
    HasFtype g e t -> Subset (fv e) (vbindsF g) /\ Subset (ftv e) (tvbindsF g).
                    (*Subset (fv e) (bindsF g) /\ Subset (ftv e) (bindsF g) /\*)
Proof. intros g e t p_e_t. induction p_e_t; simpl; (*); split;*)
  try (simpl in IHp_e_t; destruct IHp_e_t as [IH1 IH2]); 
  (* Bc Ic Pr *) try (split; apply subset_empty_l);
  (* FTVar *)    try (split; apply subset_sing_l || apply subset_empty_l; 
                      apply lem_boundin_inenvF with b; assumption );
  (* App/AppT/Ann*) try (intuition; apply subset_union_intro_l; assumption).
  - (* FTAbs *) simpl in H1; 
    pose proof (fresh_varFE_not_elem  nms g e) as Hfr; destruct Hfr as [Hfv Hfr]; 
    destruct Hfr as [Hftv Hfr]; destruct Hfr as [Hnms Hg];
    apply H1 in Hnms; destruct Hnms; split.
      * apply subset_add_elim with (fresh_varFE nms g e); try assumption;
        apply subset_trans with (fv  (unbind (fresh_varFE nms g e) e));
        try (apply fv_unbind_intro); assumption.
      * apply subset_trans with (ftv (unbind (fresh_varFE nms g e) e));
        try (apply ftv_unbind_intro); assumption. 
  - (* FTAbsT *) simpl in H0.
    pose proof (fresh_varFE_not_elem  nms g e) as Hfr; destruct Hfr as [Hfv Hfr]; 
    destruct Hfr as [Hftv Hfr]; destruct Hfr as [Hnms Hg];
    apply H0 in Hnms; destruct Hnms; split.
      * apply subset_trans with (fv (unbind_tv (fresh_varFE nms g e) e));
        try (apply fv_unbind_tv_intro); assumption. 
      * apply subset_add_elim with (fresh_varFE nms g e); try assumption;
        apply subset_trans with (ftv (unbind_tv (fresh_varFE nms g e) e));
        try (apply ftv_unbind_tv_intro); assumption.
  - (* FTLet *) simpl in H0;
    pose proof (fresh_varFE_not_elem  nms g e) as Hfr; destruct Hfr as [Hfv Hfr]; 
    destruct Hfr as [Hftv Hfr]; destruct Hfr as [Hnms Hg];
    apply H0 in Hnms; destruct Hnms; split;
    apply subset_union_intro_l; try assumption.
    * apply subset_add_elim with (fresh_varFE nms g e); try assumption;
      apply subset_trans with (fv  (unbind (fresh_varFE nms g e) e));
      try (apply fv_unbind_intro); assumption.
    * apply subset_trans with (ftv (unbind (fresh_varFE nms g e) e));
      try (apply ftv_unbind_intro); assumption.
  Qed. 
  
Lemma lem_fv_bound_in_fenv : forall (g : fenv) (e : expr) (t : ftype) (x : vname),
    HasFtype g e t -> ~ (in_envF x g) -> ~ Elem x (fv e) /\ ~ Elem x (ftv e).
Proof. intros; unfold in_envF in H0;
  pose proof (vbindsF_subset g) as Hv;
  pose proof (tvbindsF_subset g) as Htv;
  apply lem_fv_subset_bindsF in H; intuition. Qed.


    
         (*
{-@ lem_fvp_bound_in_fenv :: g:fenv -> ps:preds -> ProofOf(PHasFtype g ps)
        -> { x:vname | not (in_envF x g) }
        -> { pf:_ | not (Set_mem x (fvP ps)) && not (Set_mem x (ftvP ps)) } / [predsize ps] @-}
lem_fvp_bound_in_fenv :: fenv -> preds -> PHasFtype -> vname -> Proof
lem_fvp_bound_in_fenv g ps (PFTEmp  _) x      = ()
lem_fvp_bound_in_fenv g ps (PFTCons _ p pf_p_bl ps' pf_ps'_bl) x      
    = () ? lem_fv_bound_in_fenv  g p (FTBasic TBool) pf_p_bl x
         ? lem_fvp_bound_in_fenv g ps' pf_ps'_bl x

{-@ lem_fvp_subset_bindsF :: g:fenv -> ps:preds -> ProofOf(PHasFtype g ps)
        -> { pf:_ | Set_sub (fvP ps) (bindsF g)  && Set_sub (ftvP ps) (bindsF g) &&
                    Set_sub (fvP ps) (vbindsF g) && Set_sub (ftvP ps) (tvbindsF g) } 
         / [predsize ps] @-}
lem_fvp_subset_bindsF :: fenv -> preds -> PHasFtype -> Proof
lem_fvp_subset_bindsF g ps (PFTEmp _)                          = ()
lem_fvp_subset_bindsF g ps (PFTCons _ p pf_p_bl ps' pf_ps'_bl)
    = () ? lem_fv_subset_bindsF  g p (FTBasic TBool) pf_p_bl
         ? lem_fvp_subset_bindsF g ps' pf_ps'_bl *)

Lemma lem_ffreeTV_bound_in_fenv : forall (g:fenv) (t:ftype) (k:kind) (a:vname),
    WFFT g t k -> ~ (in_envF a g) -> ~ Elem a (ffreeTV t).
Proof. intros g t k a p_g_t Ha; induction p_g_t; simpl.
  - (* WFFTBasic *) destruct b; intuition.
  - (* WFFTFV *) intuition; subst a0; apply lem_tvboundin_inenvF in H;
    apply tvbindsF_subset in H; intuition.
  - (* WFFTFunc *) apply not_elem_union_intro; intuition.
  - (* WFFTPoly *) pose proof (fresh_var_excludingF_not_elem nms g a);
    set (a' := fresh_var_excludingF nms g a) in H1;
    destruct H1; destruct H2.
    apply not_elem_subset with (ffreeTV (unbindFT a' t));
    try apply ffreeTV_openFT_at_intro; apply H0; 
    unfold in_envF; simpl; 
    try apply not_elem_names_add_intro; intuition.
  - (* WFFTKind *) intuition.
  Qed.