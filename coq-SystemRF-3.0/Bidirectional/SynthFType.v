Require Import SystemRF.BasicDefinitions. 
Require Import SystemRF.Names.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.SystemFWellFormedness.

From Equations Require Import Equations.

Require Import Arith.
Require Import ZArith.

Fixpoint edepth (e : expr) : nat :=
    match e with 
    | (Bc b)          => 0
    | (Ic n)          => 0
    | (Prim c)        => 0
    | (BV i)          => 0
    | (FV x)          => 0
    | (Lambda e)      => 1 + (edepth e)
    | (App e1 e2)     => 1 + max (edepth e1) (edepth e2)
    | (LambdaT k e)   => 1 + (edepth e)
    | (AppT e t)      => 1 + (edepth e)
    | (Let ex e)      => 1 + max (edepth ex) (edepth e)
    | (Annot e t)     => 1 + (edepth e)
    | (If e0 e1 e2)   => 1 + max (edepth e0) (max (edepth e1) (edepth e2))
    | Nil             => 0
    | (Cons e1 e2)    => 1 + max (edepth e1) (edepth e2)
    | (Switch e eN eC) => 1 + max (edepth e) (max (edepth eN) (edepth eC))
    | Error           => 0
    end.

Lemma edepth_open_at : forall (j:index) (y:vname) (e:expr),
    edepth (open_at j y e) = edepth e.
Proof. intros j y e; revert j; induction e; intros;
  simpl; try destruct (Nat.eqb j i); reflexivity || f_equal;
  apply IHe || f_equal; try apply f_equal2; 
  apply IHe1 || apply IHe2 || apply IHe3. Qed.

Lemma edepth_unbind : forall (y:vname) (e:expr),
    edepth (unbind y e) = edepth e.
Proof. intros; apply edepth_open_at; assumption. Qed.

(*** we need a stack env for BV deBruijn's and their ftypes ***)

Inductive deBruijnsF : Set := 
    | DFEmpty 
    | DFBind  (t : ftype) (d : deBruijnsF).

Fixpoint bv_bound_inF (i : index) (t : ftype) (d : deBruijnsF) : Prop :=
    match d with 
    | DFEmpty      => False
    | DFBind t' d' => match i with
                      | 0     => t = t'
                      | (S j) => bv_bound_inF j t d'
                      end
    end.                      

Fixpoint dflen (d : deBruijnsF) : nat :=
    match d with
    | DFEmpty       => 0
    | (DFBind t d') => dflen d' + 1
    end.    

Lemma lem_bvboundinF_upper_bound : forall (i:index) (t:ftype) (d:deBruijnsF),
    bv_bound_inF i t d -> i < dflen d.
Proof. induction i; intros; destruct d; try contradiction.
  - (* Base *) simpl; auto with *.
  - (* Ind *) simpl. rewrite <- plus_n_Sm; rewrite <- plus_n_O; auto with *.
  Qed.

Fixpoint concatDF (d d'0 : deBruijnsF) : deBruijnsF :=
    match d'0 with
    | DFEmpty       => d
    | (DFBind t d') => DFBind t (concatDF d d')
    end.    

Lemma lem_empty_concatDF : forall (d : deBruijnsF),
    concatDF DFEmpty d = d.
Proof. induction d; simpl; try rewrite IHd; reflexivity. Qed.    

Lemma lem_bvboundinF_append : forall (d : deBruijnsF) (i:index) (t t':ftype),
    bv_bound_inF i t (concatDF (DFBind t' DFEmpty) d) 
          ->   i < dflen d /\ bv_bound_inF i t d
            \/ i = dflen d /\ t = t'.
Proof. induction d; intros.
  - (* Base *) destruct i; simpl in H; right; intuition;
    destruct i; try contradiction.
  - (* Ind *) destruct i; simpl in H. 
      * (* 0 *) subst t0; simpl; left; auto with *.
      * (* S i *) apply IHd in H; destruct H; [left|right].
          + (* in d *) destruct H; split; simpl; auto with *.
          + (* at end *) simpl; rewrite <- plus_n_Sm; rewrite <- plus_n_O;
            destruct H; split; auto.
  Qed.

(*----------------------------------------------------------------------------
  --- | AUTOMATED INFERENCE of SYSTEM F WELL-FORMEDNESS JUDGMENTS
  --------------------------------------------------------------------------*)

Fixpoint isWFFT' (g:fenv) (d:deBruijnTVs) (t:ftype) (k:kind) : Prop :=
    match t with 
    | (FTBasic b)    => match b with
                        | (BTV i)  => btv_bound_in i Base d  \/
                                        (btv_bound_in i Star d /\ k = Star)
                        | (FTV a)  => (tv_bound_inF a Base g) \/ 
                                        (tv_bound_inF a Star g /\ k = Star)
                        end
    | (FTFunc t_x t) => k = Star /\ isWFFT' g d t_x Star  /\ isWFFT' g d t Star
    | (FTPoly k'  t) => k = Star /\ isWFFT' g (DTBind k' d) t Star
    | (FTList     t) => k = Star /\ isWFFT' g d t   Star
    end.

Fixpoint checkF' (g:fenv) (d:deBruijnsF) (e:expe) (t:ftype) : Prop := 
    match e with
    | (Bc b)          =>  t = FTBasic TBool 
    | (Ic n)          =>  t = FTBasic TInt 
    | (Prim c)        =>  t = erase_ty c 
    | (BV i)          =>  bv_bound_inF i t d
    | (FV x)          =>  bound_inF x t g
    | (Lambda e)      => 
        match t with
        | (FTFunc tx t')  => checkF' f (DFBind tx d) e t'
        | _               => False 
        end
    | (App e1 e2)     => 
        match ( synthF' g d e2 ) with
        | (Just tx)       => checkF' g d e1 (FTFunc tx t)
        | _               => False
        end
        
    | (LambdaT k e)   => 1 + (edepth e)
    | (AppT e t)      => 1 + (edepth e)
    | (Let ex e)      => 1 + max (edepth ex) (edepth e)
    | (Annot e t)     => 1 + (edepth e)
checkType g ae (AppT e t2) t    = case ( synthType g ae e ) of
    (Just (FTPoly Base t1))  -> ( t == ftsubBV (erase t2) t1 ) &&
                                ( isWFFT g ae (erase t2) Base ) && noExists t2 &&
                                  isLCT_at (bind_idx ae) (tv_bind_idx ae) t2 &&
                                ( S.isSubsetOf (free t2) (vbindsF g) ) &&
                                ( S.isSubsetOf (freeTV t2) (tvbindsF g) )  
    _                        -> False 
checkType g ae (Annot e liqt) t = ( checkType g ae e t ) && ( t == erase liqt ) &&
                               ( S.isSubsetOf (free liqt) (vbindsF g) ) &&
                               ( S.isSubsetOf (freeTV liqt) (tvbindsF g) ) && 
                                 isLCT_at (bind_idx ae) (tv_bind_idx ae) liqt
    | (If e0 e1 e2)   => 1 + max (edepth e0) (max (edepth e1) (edepth e2))
    | Nil             => 0
    | (Cons e1 e2)    => 1 + max (edepth e1) (edepth e2)
    | (Switch e eN eC) => 1 + max (edepth e) (max (edepth eN) (edepth eC))
    | Error           => False
    end

with synthF' (g:fenv) (d:deBruijnsF) (e:expe) : option ftype := 
    match e with 
:: FEnv -> AnonEnv -> { e:Expr | noDefnsBaseAppT e } 
        -> Maybe FType / [esize e] @-}
synthType :: FEnv -> AnonEnv -> Expr -> Maybe FType
synthType g ae (Bc b)          = Just ( FTBasic TBool )
synthType g ae (Ic n)          = Just ( FTBasic TInt )
synthType g ae (Prim c)        = Just ( erase_ty c )
synthType g ae (BV i)          = lookupAE i ae
synthType g ae (FV x)          = lookupF x g
    | (Lambda e)
synthType g ae (App e e')      = case ( synthType g ae e' ) of
    Nothing    -> Nothing
    (Just t')  -> case ( synthType g ae e ) of
        (Just (FTFunc t_x t)) -> if ( t_x == t' ) then Just t else Nothing
        _                     -> Nothing
    | (LambdaT k e)   => 1 + (edepth e)
synthType g ae (AppT e t2)     = case ( synthType g ae e ) of
    (Just (FTPoly Base t1)) -> (case ( isWFFT g ae (erase t2) Base && S.isSubsetOf (free t2) (vbindsF g) &&
                                       S.isSubsetOf (freeTV t2) (tvbindsF g) && noExists t2 &&
                                       isLCT_at (bind_idx ae) (tv_bind_idx ae) t2 ) of 
	True   -> Just (ftsubBV (erase t2) t1)
        False  -> Nothing)
    _                       -> Nothing 
    | (Let ex e)      => 1 + max (edepth ex) (edepth e)
synthType g ae (Annot e liqt)  = case ( checkType g ae e (erase liqt) && 
                                   S.isSubsetOf (free liqt) (vbindsF g) &&
                                   S.isSubsetOf (freeTV liqt) (tvbindsF g) && 
                                   isLCT_at (bind_idx ae) (tv_bind_idx ae) liqt ) of 
    True  -> Just (erase liqt)
    False -> Nothing
    | (If e0 e1 e2)   => 1 + max (edepth e0) (max (edepth e1) (edepth e2))
    | Nil             => 0
    | (Cons e1 e2)    => 1 + max (edepth e1) (edepth e2)
    | (Switch e eN eC) => 1 + max (edepth e) (max (edepth eN) (edepth eC))
    | Error           => 0
    end.

Definition isWFFT (g:fenv) (t:ftype) (k:kind) : Prop := isWFFT' g DTEmpty t k.



--        -> { a:Vname | not (in_envF a g) && not (Set_mem a (ffreeTV t)) } 
--                                         && not (Set_mem a (ffreeTV t)) } 
{-@ lem_checkType_unbindFT :: g:FEnv -> ae:AnonEnv -> i:Index -> k':Kind -> { e:Expr | noDefnsBaseAppT e }
        -> { t:FType| checkType g (AConsT i k' ae) e t } 
        -> { a:Vname | not (in_envF a g) && not (Set_mem a (fv e)) && not (Set_mem a (ftv e)) }
        -> { pf:_ | checkType (FConsT a k' g) ae (open_tv_at i a e) (openFT_at i a t) } / [esize e] @-}
lem_checkType_unbindFT :: FEnv -> AnonEnv -> Index -> Kind -> Expr -> FType  -> Vname -> Proof
lem_checkType_unbindFT g ae i k' (Bc _) t a         = ()
lem_checkType_unbindFT g ae i k' (Ic _) t a         = ()
lem_checkType_unbindFT g ae i k' (Prim _ ) t a      = () -- rej
lem_checkType_unbindFT g ae i k' (BV j) t a | j == i     = () -- rej, not relevant?
                                            | otherwise  = () ? toProof ( bound_inAE j t (AConsT i k' ae) === bound_inAE j t ae )
lem_checkType_unbindFT g ae i k' (FV x) t a | a == x     = () -- impossible!
                                            | otherwise  = () ? toProof ( bound_inF x t (FConsT a k' g) === bound_inF x t g)
lem_checkType_unbindFT g ae i k' (App e e') t a     = case ( synthType g (AConsT i k' ae) e' ) of
    (Just t')       -> () ? lem_checkType_unbindFT g ae i k' e (FTFunc t' t) a
                          ? lem_synthType_unbindFT g ae i k' e' t' a
--    _               -> () -- ? lem_synthType_unbindFT g ae i k' e' t' a
-- case ( synthType (FConsT a k' g) ae (open_tv_at i a e') ) of
lem_checkType_unbindFT g ae i k' (AppT e t2) t a    = case ( synthType g (AConsT i k' ae) e ) of
    (Just (FTPoly Base t1))  -> () ? lem_isWFFT_unbindFT    g ae i k' (erase t2) Base a
                                   ? lem_synthType_unbindFT g ae i k' e (FTPoly Base t1) a
--    _               -> impossible ("by lem" ? lem_synthType_unbindFT 
lem_checkType_unbindFT g ae i k' (Annot e liqt) t a = () ? lem_checkType_unbindFT g ae i k' e t {-(erase liqt)-} a
                                                         ? lem_erase_open_tvT_at i a liqt -- local cl?
--                                       && not (Set_mem a (ffreeTV t)) } 
{-@ lem_synthType_unbindFT :: g:FEnv -> ae:AnonEnv -> i:Index -> k':Kind -> { e:Expr | noDefnsBaseAppT e }
      -> { t:FType | synthType g (AConsT i k' ae) e  == Just t } 
      -> { a:Vname | not (in_envF a g) && not (Set_mem a (fv e)) && not (Set_mem a (ftv e)) }
      -> { pf:_ | synthType (FConsT a k' g) ae (open_tv_at i a e) == Just (openFT_at i a t) } / [esize e] @-}
lem_synthType_unbindFT :: FEnv -> AnonEnv -> Index -> Kind -> Expr -> FType  -> Vname -> Proof
lem_synthType_unbindFT g ae i k' (Bc _) t a         = ()
lem_synthType_unbindFT g ae i k' (Ic _) t a         = ()
lem_synthType_unbindFT g ae i k' (Prim _ ) t a      = ()
lem_synthType_unbindFT g ae i k' (BV j) t a         = () ? toProof (lookupAE j (AConsT i k' ae) === lookupAE j ae)
lem_synthType_unbindFT g ae i k' (FV x) t a         = () ? toProof (lookupF x (FConsT a k' g) === lookupF x g)
lem_synthType_unbindFT g ae i k' (App e e') t a     = case ( synthType g (AConsT i k' ae) e' ) of
    (Just t')       -> () ? lem_checkType_unbindFT g ae i k' e (FTFunc t' t) a
                          ? lem_synthType_unbindFT g ae i k' e' t' a 
lem_synthType_unbindFT g ae i k' (AppT e t2) t a    = case ( synthType g (AConsT i k' ae) e ) of
    (Just (FTPoly Base t1)) -> () ? lem_isWFFT_unbindFT    g ae i k' (erase t2) Base a
                                  ? lem_synthType_unbindFT g ae i k' e (FTPoly Base t1) a
lem_synthType_unbindFT g ae i k' (Annot e liqt) t a = () ? lem_checkType_unbindFT g ae i k' e t {-(erase liqt)-} a
                                                         ? lem_erase_open_tvT_at i a liqt
{-@ lem_check_synth :: g:FEnv -> { e:Expr | noDefnsBaseAppT e } 
        -> { t:FType | synthType g AEmpty e == Just t } -> { pf:_ | checkType g AEmpty e t } @-}
lem_check_synth :: FEnv -> Expr -> FType -> Proof
lem_check_synth g (Bc b) t         = case t of 
    (FTBasic TBool) -> ()
lem_check_synth g (Ic n) t         = case t of
    (FTBasic TInt)  -> () 
lem_check_synth g (Prim c) t       = ()
lem_check_synth g (FV x) t         = lem_lookup_boundinF x t g 
lem_check_synth g (App e e') t     = case (synthType g AEmpty e') of
    (Just t')       -> lem_check_synth g e (FTFunc t' t)   -- where  (Just t') = synthType g e' 
    Nothing         -> impossible ""
lem_check_synth g (AppT e t2) t    = case (synthType g AEmpty e) of 
    (Just (FTPoly Base t1))  -> ()
lem_check_synth g (Annot e liqt) t = ()

{-@ makeHasFType :: g:FEnv -> { e:Expr | noDefnsBaseAppT e } -> { t:FType | checkType g AEmpty e t }
        -> ProofOf(HasFType g e t) / [esize e] @-}
makeHasFType :: FEnv -> Expr -> FType -> HasFType
makeHasFType g (Bc b) t         = case t of
    (FTBasic TBool) -> FTBC g b
makeHasFType g (Ic n) t         = case t of
    (FTBasic TInt)  -> FTIC g n
makeHasFType g (Prim c) t       = FTPrm g c
makeHasFType g (FV x) t         = simpleFTVar g (x? lem_boundin_inenvF x t g ) t
makeHasFType g (App e e') t     = FTApp g e t' t pf_e_t't e' pf_e'_t'
  where
    (Just t')  = synthType g AEmpty e'
    pf_e_t't   = makeHasFType g e (FTFunc t' t)
    pf_e'_t'   = makeHasFType g e' (t' ? lem_check_synth g e' t')
makeHasFType g (AppT e rt) t    = case (synthType g AEmpty e) of 
  (Just (FTPoly Base t1)) -> FTAppT g e Base t1 pf_e_at1 rt pf_rt_wfft 
    where
      pf_e_at1        = makeHasFType g e (FTPoly Base t1 ? lem_check_synth g e (FTPoly Base t1)) 
      pf_rt_wfft      = makeWFFT g (erase rt ? lem_erase_freeTV rt
                                             ? toProof ( S.isSubsetOf (freeTV rt) (tvbindsF g) && 
                                                         S.isSubsetOf (tvbindsF g) (bindsF g) )) Base 
makeHasFType g (Annot e liqt) t = FTAnn g e t liqt pf_e_t
  where
    pf_e_t = makeHasFType g e t

{-@ reflect allNoDefnsBaseAppT @-}
allNoDefnsBaseAppT :: Preds -> Bool
allNoDefnsBaseAppT PEmpty       = True
allNoDefnsBaseAppT (PCons p ps) = noDefnsBaseAppT p && allNoDefnsBaseAppT ps

{-@ reflect checkPreds @-}
{-@ checkPreds :: FEnv -> AnonEnv -> { ps:Preds | allNoDefnsBaseAppT ps } -> Bool / [predsize ps] @-}
checkPreds :: FEnv -> AnonEnv -> Preds -> Bool
checkPreds g ae PEmpty       = True
checkPreds g ae (PCons p ps) = checkType g ae p (FTBasic TBool) && checkPreds g ae ps

{-@ makePHasFType :: g:FEnv -> { ps:Preds | allNoDefnsBaseAppT ps && checkPreds g AEmpty ps } 
       	-> ProofOf(PHasFType g ps) / [predsize ps] @-}
makePHasFType :: FEnv -> Preds -> PHasFType 
makePHasFType g PEmpty       = PFTEmp  g
makePHasFType g (PCons p ps) = PFTCons g p (makeHasFType g p (FTBasic TBool))
                                       ps (makePHasFType g ps)

Lemma lem_isWFFT_openFT_at : 
  forall (g:fenv) (t:ftype) (k:kind) (k':kind) (d:deBruijnTVs) (a:vname),
           isWFFT' g (concatD (DTBind k' DTEmpty) d) t k
        -> ~ in_envF a g 
        -> isWFFT' (FConsT a k' g) d (openFT_at (dtlen d) a t) k.
Proof. intros g; induction t.
  - (* FTBasic *) intros. destruct b; simpl in H; simpl; try apply I.
    * (* BTV *) 
      destruct H; simpl in H; try destruct H;
      apply lem_btvboundin_append in H; destruct H; destruct H;
      try assert (dtlen d =? i = true)
         by (apply Nat.eqb_eq; symmetry; apply H);
      try assert (dtlen d =? i = false)
         by (apply Nat.eqb_neq; auto with *); 
      rewrite H3 || rewrite H2; simpl; intuition.
    * (* FTV *) destruct H; [left|right]; try destruct H;
      try split; try right; trivial.
  - (* FTFunc *) intros; simpl; simpl in H; destruct H; destruct H1;
    split; try split; try apply IHt1; try apply IHt2; trivial.
  - (* FTPoly *) intros; simpl; simpl in H; destruct H; split;
    try apply IHt; trivial.
  - (* FTList *) intros; simpl; simpl in H; destruct H; split;
    try apply IHt; trivial.
  Qed.

Lemma lem_isWFFT_unbindFT : 
  forall (g:fenv) (t:ftype) (k:kind) (k':kind) (a:vname),
           isWFFT' g (DTBind k' DTEmpty) t k-> ~ in_envF a g 
        -> isWFFT (FConsT a k' g) (unbindFT a t) k.
Proof. intros; apply lem_isWFFT_openFT_at; simpl; trivial. Qed.

Example isWFFT_one : isWFFT FEmpty (FTList (FTBasic TInt)) Star.
Proof. unfold isWFFT; simpl; auto. Qed.

Example isWFFT_two : isWFFT FEmpty (FTPoly Base (FTBasic (BTV 0))) Star.
Proof. unfold isWFFT; simpl; auto. Qed.
  

Lemma makeWFFT' : forall (n:nat) (g:fenv) (t:ftype) (k:kind),
    fdepth t <= n   -> isWFFT g t k -> WFFT g t k.
Proof. intros n; induction n.
  - (* Base *) intros;
    assert (fdepth t = 0) by auto with *.
    destruct t; simpl in H1; try discriminate.
    destruct b; unfold isWFFT in H0; simpl in H0;
    destruct k; try destruct H0;
    try destruct H0; try discriminate;
    try (destruct i; contradiction);
    try (apply WFFTFV; apply H0);
    try apply WFFTKind; try apply WFFTFV; 
    try apply WFFTBasic; simpl; trivial.
  - (* Inductive *) intros.
    destruct t eqn:T;
    (* avoid proving base case again *)
    try (assert (fdepth t <= n) as Hbase
          by (rewrite T; simpl; auto with *);
         apply IHn; subst t; trivial);
    simpl in H; apply Nat.succ_le_mono in H.
    * (* FTFunc t1 t2 *)
      unfold isWFFT in H0; 
      destruct H0; destruct H1; subst k.
      apply WFFTFunc with Star Star; 
      apply IHn; try apply Nat.le_trans 
        with (Init.Nat.max (fdepth f1) (fdepth f2));
      try apply Nat.le_max_l;
      try apply Nat.le_max_r; trivial.
    * (* FTPoly k0 f *)
      unfold isWFFT in H0; destruct H0; subst k.
      apply WFFTPoly with Star (bindsF g);
      intros; apply IHn; try rewrite fdepth_unbindFT;
      try apply lem_isWFFT_unbindFT; trivial.
    * (* FTList f *) 
      unfold isWFFT in H0; destruct H0; subst k.
      apply WFFTList with Star; apply IHn; trivial.
  Qed.

Theorem makeWFFT : forall (g:fenv) (t:ftype) (k:kind),
    isWFFT g t k -> WFFT g t k.
Proof. intros. apply makeWFFT' with (fdepth t); trivial. Qed.