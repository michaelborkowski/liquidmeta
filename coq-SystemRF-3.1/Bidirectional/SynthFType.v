Require Import SystemRF.BasicDefinitions. 
Require Import SystemRF.Names.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.SystemFWellFormedness.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.Typing.
Require Import Bidirectional.Decidable.
Require Import Bidirectional.SynthWFFT.

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
    | Nil _           => 0
    | (Cons _ e1 e2)  => 1 + max (edepth e1) (edepth e2)
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

Lemma edepth_open_tv_at : forall (j:index) (a:vname) (e:expr),
    edepth (open_tv_at j a e) = edepth e.
Proof. intros j a e; revert j; induction e; intros;
  simpl; try destruct (Nat.eqb j i); reflexivity || f_equal;
  apply IHe || f_equal; try apply f_equal2; 
  apply IHe1 || apply IHe2 || apply IHe3. Qed.

Lemma edepth_unbind_tv : forall (a:vname) (e:expr),
    edepth (unbind_tv a e) = edepth e.
Proof. intros; apply edepth_open_tv_at; assumption. Qed.


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

Fixpoint lookupDF (i : index) (d : deBruijnsF) : option ftype :=
    match d with 
    | DFEmpty      => None
    | DFBind t' d' => match i with
                      | 0     => Some t'
                      | (S j) => lookupDF j d'
                      end
    end.

Lemma lem_lookupDF_bvboundinF : 
  forall (d : deBruijnsF) (i : index) (t : ftype) ,
    lookupDF i d = Some t -> bv_bound_inF i t d.
Proof. induction d; intros; destruct i;
  simpl in H; try discriminate; simpl.
  - injection H as H; auto.
  - apply IHd; trivial.
Qed.

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


Fixpoint lookupF (x : vname) (g : fenv) : option ftype :=
    match g with 
    | FEmpty          => None
    | FCons x' t' g'  => if (x =? x') then Some t' else lookupF x g'
    | FConsT a' k' g' => lookupF x g'
    end.
    
Lemma lem_lookupF_boundinF : 
  forall (g : fenv) (x : vname) (t : ftype) ,
    lookupF x g = Some t -> bound_inF x t g.
Proof. induction g; intros; 
  simpl in H; try discriminate; simpl.
  - destruct (x0 =? x) eqn:X.
    * left; injection H as H; split; apply Nat.eqb_eq in X; auto.
    * right; apply IHg; apply H.
  - apply IHg; apply H.
Qed.


(*----------------------------------------------------------------------------
  --- | AUTOMATED INFERENCE of SYSTEM F TYPING JUDGMENTS
  --------------------------------------------------------------------------*)

(* one version is computable function, the other is a mutually inductive
      prop that we prove is decidable using the first way *)

(* For the checkF'/synthF' functions, we can't use mutual recursion directly
      because the argument e isn't strictly decreasing: in one case
      `checkF' ... e` calls `synthF' ... e` but never vice-versa. One
      solution would be to use mutual well-founded recursion, but Equations
      does not suppor that yet. The remaining solution is to combine both
      into one function: *)

Inductive modeF : Set := ChkF (t : ftype) | SynF.

Definition modeFsize (m : modeF) : nat :=
  match m with 
  | ChkF _ => 1
  | SynF   => 0
  end.

Inductive resultF : modeF -> Set :=
    | resF_Chk : forall (b : bool) (t:ftype), resultF (ChkF t)
    | resF_Syn : forall ot : option ftype, resultF SynF.

(* It would be nice to write this as Fixpoints, however the last
    case in synthF' makes termination too tricky w/o Equations*)
Equations bidirCheckF' (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) 
                       (e:expr) (m : modeF) : resultF m 
  by wf (edepth e, modeFsize m) (lexprod _ _ lt lt ) :=
(* checkF' definitions *)
bidirCheckF' g df dtv (Lambda e') (ChkF t)    := 
    match t with
    | (FTFunc tx t')  => 
        match bidirCheckF' g (DFBind tx df) dtv e' (ChkF t') with
        | resF_Chk b _t' => resF_Chk (isWFFTb' g dtv tx Star 
                                        && ftype_eq t' _t' && b ) t
        | _              => resF_Chk false t
        end
    | _               => resF_Chk false t
    end;
bidirCheckF' g df dtv (LambdaT k e') (ChkF t) :=
    match t with
    | (FTPoly k' t')  => 
        match bidirCheckF' g df (DTBind k dtv) e' (ChkF t') with
        | resF_Chk b _t' => resF_Chk (kind_eq k k' 
                                        && ftype_eq t' _t' && b) t
        | _              => resF_Chk false t
        end
    | _               => resF_Chk false t
    end;
bidirCheckF' g df dtv (Let e_x e') (ChkF t)   :=
    match bidirCheckF' g df dtv e_x SynF with
    | resF_Syn (Some t_x)    => bidirCheckF' g (DFBind t_x df) dtv e' (ChkF t) 
    (*| resF_Syn None          => resF_Chk false t*)
    | _                      => resF_Chk false t
    end;
bidirCheckF' g df dtv (If e0 e1 e2) (ChkF t)  := 
    match bidirCheckF' g df dtv e0 (ChkF (FTBasic TBool)) with
    | resF_Chk b _ =>
        match bidirCheckF' g df dtv e1 (ChkF t) with
        | resF_Chk b' _ => 
            match bidirCheckF' g df dtv e2 (ChkF t) with
            | resF_Chk b'' _ => resF_Chk (b && b' && b'') t
            | _              => resF_Chk false t
            end
        | _             => resF_Chk false t
        end
    | _ => resF_Chk false t
    end;
bidirCheckF' g df dtv (Switch e eN eC) (ChkF t) := 
    match ( bidirCheckF' g df dtv e SynF ) with
    | resF_Syn (Some (FTList t0)) => 
        match bidirCheckF' g df dtv eN (ChkF t) with
        | resF_Chk b _ =>
            match bidirCheckF' g df dtv eC 
                               (ChkF (FTFunc t0 (FTFunc (FTList t0) t))) with
            | resF_Chk b' _ => resF_Chk (b && b') t
            | _             => resF_Chk false t
            end
        | _            => resF_Chk false t
        end
    (*| resF_Syn _                  => resF_Chk false t     *)
    | _                           => resF_Chk false t  
    end;
bidirCheckF' g df dtv e (ChkF t') :=
    match (bidirCheckF' g df dtv e SynF) with
    | resF_Syn (Some t'') => resF_Chk (ftype_eq t' t'') t'
                                (* no subtypes: exact match only *)
    (*| resF_Syn None       => resF_Chk false t'*)
    | _                   => resF_Chk false t'
    end;
(* synthF' definitions *)
bidirCheckF' g df dtv (Bc b) SynF      := resF_Syn (Some ( FTBasic TBool ));
bidirCheckF' g df dtv (Ic n) SynF      := resF_Syn (Some ( FTBasic TInt ));
bidirCheckF' g df dtv (Prim c) SynF    := resF_Syn (Some ( erase_ty c ));
bidirCheckF' g df dtv (BV i) SynF      := resF_Syn (lookupDF i df);
bidirCheckF' g df dtv (FV x) SynF      := resF_Syn (lookupF x g);
bidirCheckF' g df dtv (App e e') SynF  := 
    match ( bidirCheckF' g df dtv e SynF ) return (resultF SynF) with
    | resF_Syn (Some (FTFunc t_x t)) =>
        match ( bidirCheckF' g df dtv e (ChkF t_x) ) 
            return (resultF SynF) with
        | resF_Chk true  _t => resF_Syn (Some t)
        | resF_Chk false _ => resF_Syn None 
        | _                => resF_Syn None
        end
    | resF_Syn _                     => resF_Syn None
    | _                              => resF_Syn None
    end;
bidirCheckF' g df dtv (AppT e' rt) SynF :=
    match ( bidirCheckF' g df dtv e' SynF ) with
    | resF_Syn (Some (FTPoly k s))   =>  
        if (  isMonob rt && noExistsb rt          &&
              isLCT_atb (dflen df) (dtlen dtv) rt &&
              Subsetb (free rt) (vbindsF g)       && 
              Subsetb (freeTV rt) (tvbindsF g)    &&
              isWFFTb' g dtv (erase rt) Star )%bool
        then resF_Syn (Some (ftsubBV (erase rt) s))
        else resF_Syn None
    (*| resF_Syn _                   => resF_Syn None *)
    | _                            => resF_Syn None
    end ;
bidirCheckF' g df dtv (Annot e' rt) SynF :=
    match ( bidirCheckF' g df dtv e' (ChkF (erase rt)) ) with
    | resF_Chk true  _ => 
        if ( isLCT_atb (dflen df) (dtlen dtv) rt &&
             Subsetb (free rt) (vbindsF g)       &&
             Subsetb (freeTV rt) (tvbindsF g) )%bool
        then resF_Syn (Some (erase rt))
        else resF_Syn None
    (*| resF_Chk false _ => resF_Syn None*)
    | _                => resF_Syn None
    end;
bidirCheckF' g df dtv (Nil t) SynF        := 
    if isWFFTb' g dtv (erase t) Star
    then resF_Syn (Some (FTList (erase t)))
    else resF_Syn None;
bidirCheckF' g df dtv (Cons t eH eT) SynF :=
    match bidirCheckF' g df dtv eH (ChkF (erase t)) with 
    | resF_Chk true  _  => 
        match bidirCheckF' g df dtv eT (ChkF (FTList (erase t))) with
        | resF_Chk true  _ => resF_Syn (Some (FTList (erase t) ))
        | resF_Chk false _ => resF_Syn None 
        | _                => resF_Syn None
        end
    (*| resF_Chk false _ => resF_Syn None*)
    | _                => resF_Syn None
    end ;                            (* error or annotation needed: *)
bidirCheckF' g df dtv e0 SynF      := resF_Syn None.
  Obligation 8.
  pose proof Nat.le_max_l (edepth e) (edepth e');
  left; apply Nat.lt_succ_r; apply H.
  Defined.
  Obligation 9.
  pose proof Nat.le_max_l (edepth e) (edepth e');
  left; apply Nat.lt_succ_r; apply H.
  Defined.
  Obligation 13. (* of 27 *)
  pose proof Nat.le_max_l (edepth e_x) (edepth e');
  left; apply Nat.lt_succ_r; apply H.
  Defined.
  Obligation 14.
  pose proof Nat.le_max_r (edepth e_x) (edepth e');
  left; apply Nat.lt_succ_r; apply H.
  Defined.
  Obligation 17.
  pose proof Nat.le_max_l (edepth e0) (Nat.max (edepth e1) (edepth e2));
  left; apply Nat.lt_succ_r; apply H.
  Defined.
  Obligation 18. 
  pose proof Nat.le_max_l (edepth e1) (edepth e2);
  pose proof Nat.le_max_r (edepth e0) (Nat.max (edepth e1) (edepth e2));
  left; apply Nat.lt_succ_r; 
  apply Nat.le_trans with (Init.Nat.max (edepth e1) (edepth e2));
  assumption.
  Defined.
  Obligation 19.
  pose proof Nat.le_max_r (edepth e1) (edepth e2);
  pose proof Nat.le_max_r (edepth e0) (Nat.max (edepth e1) (edepth e2));
  left; apply Nat.lt_succ_r; 
  apply Nat.le_trans with (Init.Nat.max (edepth e1) (edepth e2));
  assumption.
  Defined.
  Obligation 22.
  pose proof Nat.le_max_l (edepth eH) (edepth eT);
  left; apply Nat.lt_succ_r; apply H.
  Defined.
  Obligation 23.
  pose proof Nat.le_max_r (edepth eH) (edepth eT);
  left; apply Nat.lt_succ_r; apply H.
  Defined.
  Obligation 24.
  pose proof Nat.le_max_l (edepth e) (Nat.max (edepth eN) (edepth eC));
  left; apply Nat.lt_succ_r; apply H.
  Defined.
  Obligation 25.
  pose proof Nat.le_max_l (edepth eN) (edepth eC);
  pose proof Nat.le_max_r (edepth e) (Nat.max (edepth eN) (edepth eC));
  left; apply Nat.lt_succ_r; 
  apply Nat.le_trans with (Init.Nat.max (edepth eN) (edepth eC));
  assumption.
  Defined.
  Obligation 26.
  pose proof Nat.le_max_r (edepth eN) (edepth eC);
  pose proof Nat.le_max_r (edepth e)  (Nat.max (edepth eN) (edepth eC));
  left; apply Nat.lt_succ_r; 
  apply Nat.le_trans with (Init.Nat.max (edepth eN) (edepth eC));
  assumption.
  Defined.


Definition checkF' (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) 
                   (e:expr) (t:ftype) : bool :=
    match bidirCheckF' g df dtv e (ChkF t) return bool with
    | resF_Chk true  _t => ftype_eq t _t
    | resF_Chk false _  => false 
    (*| resF_Chk b _ => b*)
    | _                 => false 
    end.

Definition synthF' (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) 
                  (e:expr) : option ftype :=
    match bidirCheckF' g df dtv e SynF return (option ftype) with
    | resF_Syn (Some t) => Some t 
    | resF_Syn None     => None
    | _CheckF           => None : option ftype
    end.

Definition checkF (g:fenv) (e:expr) (t:ftype) : bool := checkF' g DFEmpty DTEmpty e t.
Definition synthF (g:fenv) (e:expr) : option ftype := synthF' g DFEmpty DTEmpty e.

Inductive CheckF' : fenv -> deBruijnsF -> deBruijnTVs -> expr -> ftype -> Prop :=
    | FChkLam   : forall (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) (e':expr) (tx t':ftype),
        isWFFT' g dtv tx Star -> CheckF' g (DFBind tx df) dtv e' t' 
            -> CheckF' g df dtv (Lambda e') (FTFunc tx t')
    | FChkLamT  :  forall (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) 
                          (k:kind) (e:expr) (t:ftype),
        CheckF' g df (DTBind k dtv) e t -> CheckF' g df dtv (LambdaT k e) (FTPoly k t)
    | FChkLet   : forall (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) 
                         (e_x e':expr) (t_x t':ftype),
        SynthF' g df dtv e_x t_x -> CheckF' g (DFBind t_x df) dtv e' t'
            -> CheckF' g df dtv (Let e_x e') t'
    | FChkIf    : forall (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) 
                        (e0 e1 e2: expr) (t:ftype),
        CheckF' g df dtv e0 (FTBasic TBool)
            -> CheckF' g df dtv e1 t -> CheckF' g df dtv e2 t
            -> CheckF' g df dtv (If e0 e1 e2) t            
    | FChkSwit :  forall (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) (e eN eC:expr) (t t':ftype),
        SynthF' g df dtv e (FTList t) -> CheckF' g df dtv eN t'
            -> CheckF' g df dtv eC (FTFunc t (FTFunc (FTList t) t'))
            -> CheckF' g df dtv (Switch e eN eC) t'
    | FChkSyn   : forall (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) (e:expr) (t:ftype),
        SynthF' g df dtv e t -> CheckF' g df dtv e t 

with SynthF' : fenv -> deBruijnsF -> deBruijnTVs -> expr -> ftype -> Prop :=
    | FSynBC    : forall (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) (b:bool), 
        SynthF' g df dtv (Bc b) (FTBasic TBool)
    | FSynIC    : forall (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) (n:Z),
        SynthF' g df dtv (Ic n) (FTBasic TInt)
    | FSynPrm   : forall (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) (c:prim),
        SynthF' g df dtv (Prim c) (erase_ty c) 
    | FSynBV    : forall (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) (i:index) (t:ftype),
        bv_bound_inF i t df -> SynthF' g df dtv (BV i) t
    | FSynFV    : forall (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) (x:vname) (t:ftype),
        bound_inF x t g -> SynthF' g df dtv (FV x) t
    | FSynApp   : forall (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs)
                         (e e':expr) (t_x t:ftype),
        SynthF' g df dtv e (FTFunc t_x t) -> CheckF' g df dtv e t_x
            -> SynthF' g df dtv (App e e') t
    | FSynAppT  : forall (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) 
                         (e:expr) (k:kind) (s:ftype) (rt:type),
        isMono rt -> noExists rt -> isLCT_at (dflen df) (dtlen dtv) rt 
            -> Subset (free rt) (vbindsF g) -> Subset (freeTV rt) (tvbindsF g)
            -> isWFFT' g dtv (erase rt) Star
            -> SynthF' g df dtv e (FTPoly k s)
            -> SynthF' g df dtv (AppT e rt) (ftsubBV (erase rt) s)      
    | FSynAnn   : forall (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) (e:expr) (rt:type),
        isLCT_at (dflen df) (dtlen dtv) rt 
            -> Subset (free rt) (vbindsF g) -> Subset (freeTV rt) (tvbindsF g)
            -> CheckF' g df dtv e (erase rt) -> SynthF' g df dtv (Annot e rt) (erase rt)   
    | FChkNil   : forall (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) (t:type),
        isWFFT' g dtv (erase t) Star -> SynthF' g df dtv (Nil t) (FTList (erase t))
    | FSynCons  : forall (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) (eH eT:expr) (t:type),
        CheckF' g df dtv eH (erase t) -> CheckF' g df dtv eT (FTList (erase t))
            -> SynthF' g df dtv (Cons t eH eT) (FTList (erase t)).

Scheme CheckF_mutind  := Induction for CheckF'  Sort Prop
with   SynthF_mutind  := Induction for SynthF'  Sort Prop.
Combined Scheme BidirF_mutind from CheckF_mutind, SynthF_mutind.    

Definition CheckF (g:fenv) (e:expr) (t:ftype) : Prop := 
  CheckF' g DFEmpty DTEmpty e t.

Definition SynthF (g:fenv) (e:expr) (t:ftype) : Prop := 
  SynthF' g DFEmpty DTEmpty e t.

(* From the bidirectional algorithm to the declaritive bidirectional typing *)
Lemma lem_bidirCheckF'_CheckF'_helper : 
  forall (n:nat) (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs)         
         (e:expr) (t:ftype),
    (2 * edepth e + 1 <= n
        -> bidirCheckF' g df dtv e (ChkF t) = resF_Chk true t 
        -> CheckF' g df dtv e t) /\ 
    (2 * edepth e <= n
        -> bidirCheckF' g df dtv e SynF = resF_Syn (Some t) 
        -> SynthF' g df dtv e t).
Proof. intros n; induction n.
  - (* Base: n = 0 *) intros; split; intros;
    (assert (2 * edepth e + 1 = 0)  by auto with *) ||
    (assert (2 * edepth e = 0)      by auto with *);
    repeat (apply Nat.eq_add_0 in H1; destruct H1);
    try discriminate (* Chk mode is impossible *).
    destruct e;   simpl in H1; try discriminate H1;
    try rewrite bidirCheckF'_equation_2 in H0;
    try rewrite bidirCheckF'_equation_4 in H0;
    try rewrite bidirCheckF'_equation_6 in H0;
    try rewrite bidirCheckF'_equation_8 in H0;
    try rewrite bidirCheckF'_equation_10 in H0;
    try rewrite bidirCheckF'_equation_26 in H0;
    try rewrite bidirCheckF'_equation_32 in H0;
    try destruct (isWFFT'_dec g dtv (erase t0) Star) eqn:Hwf;
    try unfold isWFFTb' in H0; try rewrite Hwf in H0;
    injection H0 as H0;
    try subst t; try discriminate; try constructor;
    try apply lem_lookupDF_bvboundinF;
    try apply lem_lookupF_boundinF; trivial.
  - (* Inductive: n > 0 *) intros; split; intros;
    destruct e eqn:E;
    (* avoid proving base case again *)
    try ( assert (2 * edepth e <= n) as Hbase
            by (rewrite E; simpl; auto with *);
          apply IHn; subst e; assumption);
    simpl in H; apply Nat.succ_le_mono in H;

    try (
      (
        rewrite bidirCheckF'_equation_1 in H0;
        destruct (bidirCheckF' g df dtv (Bc b) SynF) eqn:H'
      ) || (
        rewrite bidirCheckF'_equation_3 in H0;
        destruct (bidirCheckF' g df dtv (Ic n0) SynF) eqn:H'
      ) || (
        rewrite bidirCheckF'_equation_5 in H0;
        destruct (bidirCheckF' g df dtv (Prim p) SynF) eqn:H'
      ) || (
        rewrite bidirCheckF'_equation_7 in H0;
        destruct (bidirCheckF' g df dtv (BV i) SynF) eqn:H'
      ) || (
        rewrite bidirCheckF'_equation_9 in H0;
        destruct (bidirCheckF' g df dtv (FV x) SynF) eqn:H'
      ) || (
        rewrite bidirCheckF'_equation_13 in H0;
        destruct (bidirCheckF' g df dtv (App e0_1 e0_2) SynF) eqn:H'
      ) || (
        rewrite bidirCheckF'_equation_17 in H0;
        destruct (bidirCheckF' g df dtv (AppT e0 t0) SynF) eqn:H'
      ) || (
        rewrite bidirCheckF'_equation_21 in H0;
        destruct (bidirCheckF' g df dtv (Annot e0 t0) SynF) eqn:H'
      ) || (
        rewrite bidirCheckF'_equation_25 in H0;
        destruct (bidirCheckF' g df dtv (Nil t0) SynF) eqn:H'
      ) || (
        rewrite bidirCheckF'_equation_27 in H0;
        destruct (bidirCheckF' g df dtv (Cons t0 e0_1 e0_2) SynF) eqn:H'
      ) || (
        rewrite bidirCheckF'_equation_31 in H0;
        destruct (bidirCheckF' g df dtv Error SynF) eqn:H'
      );
      try destruct ot; try discriminate;
      injection H0 as H0; 
      apply lem_ftype_eq in H0; subst f;
      apply FChkSyn; apply IHn; simpl; auto with *
    ).
  * (* FChkLam *) destruct t eqn:T;
    rewrite bidirCheckF'_equation_11 in H0; try discriminate;
    destruct (bidirCheckF' g (DFBind f1 df) dtv e0 (ChkF f2)) eqn:H';
    try discriminate; injection H0 as H0.
    apply Bool.andb_true_iff in H0; destruct H0;
    apply Bool.andb_true_iff in H0; destruct H0; subst b.
    apply FChkLam; try apply IHn; simpl;
    try apply lem_isWFFTb_isWFFT'; apply lem_ftype_eq in H2;
    subst t0; auto with * .   
  * (* FChkLamT *) destruct t eqn:T;
    rewrite bidirCheckF'_equation_15 in H0; try discriminate;
    destruct (bidirCheckF' g df (DTBind k dtv) e0 (ChkF f)) eqn:H';
    try discriminate; injection H0 as H0.
    apply Bool.andb_true_iff in H0; destruct H0;
    apply Bool.andb_true_iff in H0; destruct H0; subst b.
    apply lem_kind_eq in H0; subst k0;
    apply lem_ftype_eq in H2; subst f.
    apply FChkLamT; apply IHn; auto with *.  
  * (* FChkLet *) rewrite bidirCheckF'_equation_19 in H0;
    destruct (bidirCheckF' g df dtv e0_1 SynF) eqn:H';
    try destruct ot; try discriminate.
    apply FChkLet with f; apply IHn; auto with *.
  * (* FChkIf *) rewrite bidirCheckF'_equation_23 in H0;
    destruct (bidirCheckF' g df dtv e0_1 (ChkF (FTBasic TBool))) eqn:H';
    destruct (bidirCheckF' g df dtv e0_2 (ChkF t)) eqn:H'';
    try destruct (bidirCheckF' g df dtv e0_3 (ChkF t1)) eqn:H''';
    try discriminate; injection H0 as H0. 
    apply Bool.andb_true_iff in H0; destruct H0;
    apply Bool.andb_true_iff in H0; destruct H0; subst b b0 b1.
    apply FChkIf; apply IHn; auto with *.
(*      
  * (* FChkSwit *)
  * (* FSynBC  *)
  * (* FSynIC  *)
  * (* FSynPrm *)
  * (* FSynBV  *)
  * (* FSynFV  *)
  * (* FSynApp  *)
  * (* FSynAppT  *)
  * (* FSynAnn  *)
  * (* FChkNil  *)
  * (* FSynCons  *)
*)
  Admitted.  

Lemma lem_bidirCheckF'_CheckF' : 
  forall (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs)         
         (e:expr) (t:ftype),
    bidirCheckF' g df dtv e (ChkF t) = resF_Chk true t 
        -> CheckF' g df dtv e t.
Proof. intros; 
  apply lem_bidirCheckF'_CheckF'_helper with (2 * edepth e + 1);
  trivial. Qed.

Lemma lem_bidirCheckF'_SynthF' : 
  forall (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs)         
         (e:expr) (t:ftype),
    bidirCheckF' g df dtv e SynF = resF_Syn (Some t) 
        -> SynthF' g df dtv e t.
Proof. intros; 
  apply lem_bidirCheckF'_CheckF'_helper with (2 * edepth e);
  trivial. Qed.

Lemma lem_checkF'_CheckF' : 
  forall (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs)         
         (e:expr) (t:ftype),
    checkF' g df dtv e t = true -> CheckF' g df dtv e t.
Proof. intros. unfold checkF' in H. 
  destruct (bidirCheckF' g df dtv e  (ChkF t)) eqn:H1;
  try destruct b; try discriminate;
  apply lem_ftype_eq in H; subst t0.
  apply lem_bidirCheckF'_CheckF'; assumption. Qed.

Lemma lem_synthF'_SynthF' : 
  forall (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs)         
         (e:expr) (t:ftype),
    synthF' g df dtv e  = Some t -> SynthF' g df dtv e t.
Proof. intros. unfold synthF' in H. 
  destruct (bidirCheckF' g df dtv e  SynF) eqn:H1;
  try destruct ot; try discriminate;
  injection H as H; subst f.
  apply lem_bidirCheckF'_SynthF'; assumption. Qed.
         
         (*
Lemma lem_CheckF_open_tv_at : forall (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) 
                                     (e:expr) (t:ftype) (a:vname) (k:kind),
    CheckF' g df (concatDT (DTBind k DTEmpty) dtv) e t
        -> ~ in_envF a g 
        -> CheckF' (FConsT a k g) df dtv (open_tv_at (dtlen dtv) a e) t.
(* and SynthF *)
    
Lemma lem_CheckF_unbind_tv : forall (g:fenv) (e:expr) (t:ftype) (a:vname) (k:kind),
    CheckF' g DFEmpty (DTBind k DTEmpty) e t -> ~ in_envF a g 
        -> CheckF (FConsT a k g) (unbind_tv a e) t.
(* and SynthF *)
*)

(* For next time: this isn't easy because we can't do structural
    induction on CheckF'/SynthF' 
    -- the IH will only apply to a subtree, which would be 
        the check for e' w/ deBruijn envs when checking Lambda e'.
    -- but we need is to apply IH to (unbind y e') for any
        fresh enough y. 
    => we need to do the tricky induction on edepth e + 0/1 again *)

(* From declarative bidirectional typing to our typing judgment *)
Lemma lem_CheckF_SynthF_HasFtype : (
    forall (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) (e:expr) (t:ftype),
      CheckF' g df dtv e t -> df = DFEmpty 
                           -> dtv = DTEmpty -> HasFtype g e t ) /\ (
    forall (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) (e:expr) (t:ftype),
      SynthF' g df dtv e t -> df = DFEmpty 
                           -> dtv = DTEmpty -> HasFtype g e t ) .
Proof. apply ( BidirF_mutind
    (fun (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) 
         (e:expr) (t:ftype) (chk_e_t : CheckF' g df dtv e t) => 
        df = DFEmpty -> dtv = DTEmpty -> HasFtype g e t)
    (fun (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) 
         (e:expr) (t:ftype) (syn_e_t : SynthF' g df dtv e t) =>
        df = DFEmpty -> dtv = DTEmpty -> HasFtype g e t)
  ); intros.
  - apply FTAbs with Star (bindsF g).


(* standalone CheckF? *)
(* and SynthF *)


(* use below maybe *)
(* also a section of decidabili*)

(*
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

(* the only possible type a preds can have is FTBasic TBool *)
Fixpoint checkP' (g:fenv) (df:deBruijnsF) (dtv:deBruijnTVs) (ps:preds) : Prop :=
    match ps with 
    | PEmpty      => True
    | PCons q qs  => CheckF' g df dtv q (FTBasic TBool) /\ checkP' g df dtv qs
    end.

Definition checkP (g:fenv) (ps:preds) : Prop := checkP' g DFEmpty DTEmpty ps.


{-@ makePHasFType :: g:FEnv -> { ps:Preds | allNoDefnsBaseAppT ps && checkPreds g AEmpty ps } 
       	-> ProofOf(PHasFType g ps) / [predsize ps] @-}
makePHasFType :: FEnv -> Preds -> PHasFType 
makePHasFType g PEmpty       = PFTEmp  g
makePHasFType g (PCons p ps) = PFTCons g p (makeHasFType g p (FTBasic TBool))
                                       ps (makePHasFType g ps)

Lemma lem_isWFFT_openFT_at : 
  forall (g:fenv) (t:ftype) (k:kind) (k':kind) (d:deBruijnTVs) (a:vname),
           isWFFT' g (concatDT (DTBind k' DTEmpty) d) t k
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