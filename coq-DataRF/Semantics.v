Require Import Arith.
Require Import Lists.ListSet.

Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.

(*------------------------------------------------------------------------
----- | OPERATIONAL SEMANTICS (Small Step)
------------------------------------------------------------------------*)

(* E-Prim    c v -> delta(c,v)
-- E-App1    e e1 -> e' e1 if e->e'
-- E-App2    v e  -> v e'  if e->e'
-- E-AppAbs  (\x. e) v -> e[v/x]
-- E-primT   c [t] -> deltaT(c,t)
-- E-AppT    e [t] -> e' [t]   if   e->e'
-- E-AppTAbs (/\a. e) [t] -> e[t/a]
-- E-Let     let x=e_x in e -> let x=e'_x in e if e_x->e'_x
-- E-LetV    let x=v in e -> e[v/x]
-- E-Ann     e:t -> e':t  if e->e'
-- E-AnnV    v:t -> v  
-- E-Switch  switch e as -> switch e' as if e->e'
-- E-SwitchV switch (D v1 .. vn) as -> lookup()[v1/x1]...[vn/xn] *)

Inductive isCompat : prim -> expr -> Set :=   (* can't use Prop here*)
    | isCpt_And  : forall b, isCompat And (Bc b) 
    | isCpt_Or   : forall b, isCompat Or  (Bc b)      
    | isCpt_Not  : forall b, isCompat Not (Bc b)    
    | isCpt_Eqv  : forall b, isCompat Eqv (Bc b)      
    | isCpt_Imp  : forall b, isCompat Imp (Bc b)   
    | isCpt_Leq  : forall n, isCompat Leq (Ic n) 
    | isCpt_Leqn : forall n m, isCompat (Leqn n) (Ic m) 
    | isCpt_Eq   : forall n, isCompat Eq  (Ic n) 
    | isCpt_Eqn  : forall n m, isCompat (Eqn n) (Ic m).
    
Definition isCompat' (c:prim) (v:expr) : Prop := 
    match c, v with
    | And      , (Bc _)  => True
    | Or       , (Bc _)  => True
    | Not      , (Bc _)  => True
    | Eqv      , (Bc _)  => True
    | Imp      , (Bc _)  => True
    | Leq      , (Ic n)     => True
    | (Leqn n) , (Ic m)     => True
    | Eq       , (Ic n)     => True
    | (Eqn n)  , (Ic m)     => True
    | _        , _          => False
    end.

Lemma compat_prop_set : forall (c:prim) (v:expr),
    isCompat' c v -> isCompat c v.
Proof. intros c v cpt'. destruct c; destruct v; 
  simpl in cpt'; try contradiction. 
  - apply isCpt_And.
  - apply isCpt_Or.
  - apply isCpt_Not.
  - apply isCpt_Eqv.
  - apply isCpt_Imp.
  - apply isCpt_Leq.
  - apply isCpt_Leqn.
  - apply isCpt_Eq.
  - apply isCpt_Eqn. 
  Qed.
    
(* isCompat p e  -> { e':Value | Set_emp (fv e') && Set_emp (ftv e') } *)
Definition delta (c : prim) (v : expr) (pf : isCompat c v) : expr :=
    match pf with
    | isCpt_And b    => match b with 
                        | true  => Lambda (BV 0)
                        | false => Lambda (Bc false)
                        end
    | isCpt_Or b     => match b with  
                        | true  => Lambda (Bc true)
                        | false => Lambda (BV 0)
                        end
    | isCpt_Not b    => match b with 
                        | true  => Bc false
                        | false => Bc true
                        end
    | isCpt_Eqv b    => match b with
                        | true  => Lambda (BV 0)
                        | false => Prim Not   (* Lambda (App (Prim Not) (BV 0)) *)
                        end
    | isCpt_Imp b    => match b with 
                        | true  => Lambda (BV 0)
                        | false => Lambda (Bc true)
                        end
    | isCpt_Leq  n   => Prim (Leqn n)
    | isCpt_Leqn n m => Bc (n <=? m)
    | isCpt_Eq   n   => Prim (Eqn n)
    | isCpt_Eqn n m  => Bc (n =? m)
    end. 

Definition delta' (c : prim) (v : expr) : option expr :=
    match c, v with
    | And      , (Bc true)  => Some  (Lambda (BV 0))
    | And      , (Bc false) => Some  (Lambda (Bc false))
    | Or       , (Bc true)  => Some  (Lambda (Bc true))
    | Or       , (Bc false) => Some  (Lambda (BV 0))
    | Not      , (Bc true)  => Some  (Bc false)
    | Not      , (Bc false) => Some  (Bc true)
    | Eqv      , (Bc true)  => Some  (Lambda (BV 0))
    | Eqv      , (Bc false) => Some  (Prim Not)  (* Lambda (App (Prim Not) (BV 0))*)
    | Imp      , (Bc true)  => Some  (Lambda (BV 0))
    | Imp      , (Bc false) => Some  (Lambda (Bc true))
    | Leq      , (Ic n)     => Some  (Prim (Leqn n))
    | (Leqn n) , (Ic m)     => Some  (Bc (n <=? m))
    | Eq       , (Ic n)     => Some  (Prim (Eqn n))
    | (Eqn n)  , (Ic m)     => Some  (Bc (n =? m))
    | _        , _          => None 
    end.

Lemma delta_delta' : forall (c : prim) (v : expr) (pf : isCompat c v),
    Some (delta c v pf) = (delta' c v).
Proof. intros. destruct pf; try (destruct b); simpl; reflexivity. Qed.

Lemma delta_pf_indep : forall (c : prim) (v : expr) (pf pf' : isCompat c v),
    delta c v pf = delta c v pf'.
Proof. intros. assert (Some (delta c v pf) = Some (delta c v pf')).
  - transitivity (delta' c v); (apply delta_delta' || symmetry; apply delta_delta'). 
  - injection H. trivial. Qed. 

Inductive isCompatT : prim -> type -> Set :=
    | isCptT_EqlB  : forall t, erase t = FTBasic TBool  ->  isCompatT Eql t
    | isCptT_EqlZ  : forall t, erase t = FTBasic TInt   ->  isCompatT Eql t
    | isCptT_LeqlB : forall t, erase t = FTBasic TBool  ->  isCompatT Leql t
    | isCptT_LeqlZ : forall t, erase t = FTBasic TInt   ->  isCompatT Leql t.

Definition isCompatT' (c:prim) (t:type) : Prop := 
    match c, (erase t) with
    | Eql  , FTBasic TBool => True
    | Eql  , FTBasic TInt  => True
    | Leql , FTBasic TBool => True
    | Leql , FTBasic TInt  => True
    | _    , _             => False
    end. 

Lemma compatT_prop_set : forall (c:prim) (t:type),
    isCompatT' c t -> isCompatT c t.
Proof. intros c t cpt'. destruct c; destruct (erase t) eqn:T;  
  simpl in cpt'; try (rewrite T in cpt'); try contradiction;
  destruct b;  try contradiction.
  - apply isCptT_LeqlB; trivial.
  - apply isCptT_LeqlZ; trivial.
  - apply isCptT_EqlB; trivial.
  - apply isCptT_EqlZ; trivial.
  Qed.      

(*{ t:type | isCompatT c t } -> { e':Value | Set_emp (fv e') && Set_emp (ftv e') } *)
Definition deltaT (c : prim) (t : type) (pf : isCompatT c t) : expr :=
    match pf with
    | isCptT_EqlB  t _ => Prim Eqv
    | isCptT_EqlZ  t _ => Prim Eq
    | isCptT_LeqlB t _ => Prim Imp
    | isCptT_LeqlZ t _ => Prim Leq
    end.

Definition deltaT' (c : prim) (t : type) : option expr :=
    match c, (erase t) with
    | Eql  , FTBasic TBool  => Some (Prim Eqv)
    | Eql  , FTBasic TInt   => Some (Prim Eq)
    | Leql , FTBasic TBool  => Some (Prim Imp)
    | Leql , FTBasic TInt   => Some (Prim Leq)
    | _    , _              => None
    end.

Lemma deltaT_deltaT' : forall (c : prim) (t : type) (pf : isCompatT c t),
    deltaT' c t =  Some (deltaT c t pf).
Proof. intros. destruct pf as [t H|t H|t H|t H]; simpl; rewrite H; reflexivity. Qed.

Lemma deltaT_pf_indep : forall (c : prim) (t : type) (pf pf' : isCompatT c t),
    deltaT c t pf = deltaT c t pf'.
Proof. intros. assert (Some (deltaT c t pf) = Some (deltaT c t pf')).
  - apply eq_stepl with (deltaT' c t); apply deltaT_deltaT'.
  - injection H as H'; assumption. Qed.


  (* -- reflected functions for match scrutinees *)

Definition isSome {A : Type} (opx : option A) : Prop :=
    match opx with
    | None    => False
    | Some _  => True
    end.

Fixpoint altsIds (cs : alts) : set id :=
    match cs with
    | AEmpty           => empty
    | (ACons dc e cs)  => names_add (dcid dc) (altsIds cs)
    end.

Fixpoint altsLookup (i : id) (cs : alts) : option expr := 
    match cs with
    | AEmpty           => None
    | (ACons dc e cs)  => if i =? dcid dc then Some e else altsLookup i cs
    end.

(* predicate HasMatch DV AS =   Set_mem (dcid (dvdc DV)) (altsIds AS) && FullyApplied DV *)
Fixpoint isMatch (dc : dcons) (m : expr) (cs0 : alts) : Prop := 
    match cs0 with
    | AEmpty            => False
    | (ACons dc' m' cs) => (dc = dc' /\ m = m') \/ (~ dc = dc' /\ isMatch dc m cs)
    end.

Lemma isMatch_unique : forall (dc : dcons) (m m' : expr) (cs :alts),
    isMatch dc m cs -> isMatch dc m' cs -> m = m'.
Proof. intros dc m m'; induction cs; simpl; intros; try contradiction.
  destruct H; destruct H0; try destruct H; try destruct H0; try contradiction.
  - (* dc <> dc' *) subst m; subst m'; reflexivity.
  - (* dc =  dc' *) apply IHcs; assumption. Qed.

(* may want to prove something about subMany where given an input
     { dv:DataValue | argCount dv == arity (dvdc dv) } something nice about output *)
Fixpoint subMany_at (n : index) (dv e : expr) (pf : dataValue dv) : expr :=
    match pf with 
    | dval_Dc  dc  t        => subBTV t e
    | dval_App dv' v pf' _  => subMany_at (1+n) dv' (subBV_at n v e) pf'
    end.
    
Definition subMany  (dv : expr) (e : expr) (pf : dataValue dv) : expr :=
    subMany_at 0 dv e pf.

Fixpoint subMany_at' (n : index) (dv : expr) (e : expr) : option expr :=
    match dv with 
    | (AppT (Dc _) t) => Some (subBTV t e)
    | (App dv' v)     => subMany_at' (1+n) dv' (subBV_at n v e)
    | _               => None
    end.

Definition subMany' (dv : expr) (e : expr) : option expr := subMany_at' 0 dv e.

Lemma subMany_at_subMany_at' : 
  forall (n:index) (dv m : expr) (pf : dataValue dv),
    subMany_at' n dv m =  Some (subMany_at n dv m pf).
Proof. intros; generalize dependent m; generalize dependent n;
  induction pf as [dc|dv v Hdv IH Hv]; 
  intros n m; simpl; try rewrite IH; reflexivity. Qed.

Lemma subMany_subMany' : forall (dv m : expr) (pf : dataValue dv),
    subMany' dv m =  Some (subMany dv m pf).
Proof. unfold subMany; unfold subMany'; apply subMany_at_subMany_at'. Qed.

Lemma subMany_pf_indep : forall (dv m : expr) (pf pf' : dataValue dv),
    subMany dv m pf = subMany dv m pf'.
Proof. intros. assert (Some (subMany dv m pf) = Some (subMany dv m pf')).
- apply eq_stepl with (subMany' dv m); apply subMany_subMany'.
- injection H as H'; assumption. Qed.

Inductive Step : expr -> expr -> Prop :=
    | EPrim : forall (c:prim) (w : expr) (pf : isCompat c w), 
          isValue w -> Step (App (Prim c) w) (delta c w pf)
    | EApp1 : forall (e e' e1 : expr),
          Step e e' -> Step (App e e1) (App e' e1)
    | EApp2 : forall (e e' v : expr),
          isValue v -> Step e e' -> Step (App v e) (App v e')
    | EAppAbs : forall (e v : expr),
          isValue v -> Step (App (Lambda e) v) (subBV v e)
    | EPrimT : forall (c : prim) (t : type) (pf : isCompatT c t),
          noExists t -> Step (AppT (Prim c) t) (deltaT c t pf) 
    | EAppT : forall (e e' : expr) (t : type),
          noExists t -> Step e e' -> Step (AppT e t) (AppT e' t)
    | EAppTAbs : forall (k : kind) (e : expr) (t : type),
          noExists t -> Step (AppT (LambdaT k e) t) (subBTV t e)
    | ELet  : forall (e_x e_x' e : expr),
          Step e_x e_x' -> Step (Let e_x e) (Let e_x' e)
    | ELetV : forall (v : expr) (e : expr), 
          isValue v -> Step (Let v e) (subBV v e)
    | EAnn  : forall (e e' : expr) (t : type),
          Step e e' -> Step (Annot e t) (Annot e' t)
    | EAnnV : forall (v : expr) (t : type),
          isValue v -> Step (Annot v t) v
    | ESwitch : forall (e e' : expr) (cs : alts),      
          Step e e' -> Step (Switch e cs) (Switch e' cs)
    | ESwitchV : forall (dv : expr) (cs : alts) (pf : dataValue dv) (m : expr),
          fullyApplied dv pf -> isMatch (dvdc dv pf) m cs 
                -> Step (Switch dv cs) (subMany dv m pf) .

Inductive EvalsTo : expr -> expr -> Prop := 
    | Refl     : forall (e : expr),  EvalsTo e e
    | AddStep  : forall (e1 e2 e3 : expr), 
          Step e1 e2 -> EvalsTo e2 e3 -> EvalsTo e1 e3. 

(*--------------------------------------------------------------------------
----- | Properties of the OPERATIONAL SEMANTICS (Small Step)
--------------------------------------------------------------------------*)

(*  -- EvalsToP is the transitive/reflexive closure of StepP:  *)
Lemma lemma_evals_trans : forall (e1 e2 e3 : expr),
    EvalsTo e1 e2 -> EvalsTo e2 e3 -> EvalsTo e1 e3.
Proof. intros e1 e3 e4 ev_e1e3 ev_e3e4. induction ev_e1e3 as [e|_e1 e2 _e3 st_e1e2 ev_e2e3 IH]. 
  - apply ev_e3e4.
  - apply IH in ev_e3e4. apply AddStep with e2; assumption. Qed.

Lemma lem_step_evals : forall (e e' : expr), 
    Step e e' -> EvalsTo e e'.
Proof. intros e e' st_ee'. apply AddStep with e'. assumption. apply Refl. Qed.

Lemma lemma_add_step_after : forall (e e' e'' : expr),
    EvalsTo e e'  -> Step e' e'' -> EvalsTo e e''.
Proof. intros e e' e'' ev_e_e' st_e'_e''. induction ev_e_e' as [e|e e1 e' st_ee1 ev_e1e' IH].
  - apply AddStep with e''.  apply st_e'_e''.  apply Refl.
  - apply IH in st_e'_e'' as ev_e1_e''. apply AddStep with e1; assumption. Qed.
  
Lemma lemma_app_many : forall (e e' v : expr),
    EvalsTo e e' -> EvalsTo (App e v) (App e' v).
Proof. intros e e' v ev_e_e'. induction ev_e_e' as [e|e e1 e' st_ee1 ev_e1e' IH].
  - apply Refl.
  - apply AddStep with (App e1 v). 
      * apply EApp1; apply st_ee1.
      * apply IH. 
  Qed. 
  
Lemma lemma_app_many2 : forall (v : expr) (e e' : expr), 
    isValue v -> EvalsTo e e' -> EvalsTo (App v e) (App v e').
Proof. intros v e e' val ev_e_e'. induction ev_e_e' as [e|e e1 e' st_ee1 ev_e1e' IH].
  - apply Refl.
  - apply AddStep with (App v e1).
      * apply EApp2; assumption.
      * apply IH.
  Qed.

Lemma lemma_app_both_many : forall (e e' : expr) (v v' : expr),
    isValue v -> isValue v' -> EvalsTo e v -> EvalsTo e' v'
        -> EvalsTo (App e e') (App v v').
Proof. intros e e' v v' val val' ev_e_v ev_e'_v'. 
  apply lemma_evals_trans with (App v e').
  - apply lemma_app_many; assumption.
  - apply lemma_app_many2; assumption. Qed. 

Lemma lemma_appT_many : forall (e e' : expr) (t : type), 
    noExists t -> EvalsTo e e' -> EvalsTo (AppT e t) (AppT e' t).
Proof. intros e e' t ut ev_e_e'. induction ev_e_e' as [e|e e1 e' st_ee1 ev_e1e' IH].
  - apply Refl.
  - apply AddStep with (AppT e1 t).
      * apply EAppT; assumption.
      * apply IH. Qed.

Lemma lemma_let_many : forall (e_x e_x' e : expr),
    EvalsTo e_x e_x' -> EvalsTo (Let e_x e) (Let e_x' e).
Proof. intros e_x e_x' e ev_ex_ex'. induction ev_ex_ex' as [|e_x e_x1 e_x' st_exex1 ev_ex1ex' IH].
  - apply Refl.
  - apply AddStep with (Let e_x1 e); try (apply ELet); assumption. Qed.

Lemma lemma_annot_many : forall (e e':expr) (t:type),
    EvalsTo e e' -> EvalsTo (Annot e t) (Annot e' t).
Proof. intros e e' t ev_e_e'. induction ev_e_e' as [|e e1 e' st_ee1 ev_e1e' IH].
  - apply Refl.
  - apply AddStep with (Annot e1 t); try (apply EAnn); assumption. Qed.

(*--------------------------------------------------------------------------
----- | Basic LEMMAS of the OPERATIONAL SEMANTICS (Small Step)
--------------------------------------------------------------------------*)

Theorem lem_value_stuck : forall (e e' : expr), 
    Step e e' -> isValue e -> False.
Proof. intros e e' st_e_e'; induction st_e_e'; intro Hval; inversion Hval.
  - (* EPrim *) inversion H0; inversion H4.
  - (* EApp1 *) inversion H; apply IHst_e_e'; apply val_dv; apply H3.
  - (* EApp2 *) inversion H0; apply IHst_e_e'; apply H5.
  - (* EAppAbs *) inversion H0; inversion H4.
  - (* EPrimT *) inversion H0.
  - (* EAppT *) inversion H0; apply IHst_e_e'; subst e; apply val_Dc.
  - (* EAppTAbs *) inversion H0.
  - (* ELet *) inversion H.
  - (* ELetV *) inversion H0.
  - (* EAnn *) inversion H.
  - (* EAnnV *) inversion H0.
  - (* ESwitch *) inversion H.
  - (* ESwitchV *) inversion H1.
  Qed.

Lemma lem_value_refl : forall (v v' : expr),       (* unused: delete later! *)
    isValue v -> EvalsTo v v' ->  v = v'.
Proof. intros v v' v_val ev_v_v'. destruct ev_v_v' as [|v e1 v' st_ve1 ev_e1v'] eqn:E.
  - reflexivity.
  - apply lem_value_stuck in st_ve1 as H. contradiction. apply v_val. Qed.

Theorem lem_sem_det : forall (e e1 e2 : expr),
    Step e e1 -> Step e e2 ->  e1 = e2.
Proof. intros e. induction e; intros e' e'' st_ee' st_ee''; inversion st_ee'.
  - (* e->e1 is EPrim *) inversion st_ee''; subst e1; subst e2. 
      * (* e->e2 is EPrim *) injection H3 as H3. subst c. apply delta_pf_indep.
      * (* e->e2 is EApp1 *) apply lem_value_stuck in H6; 
        contradiction || constructor. 
      * (* e->e2 is EApp2 *) apply lem_value_stuck in H7; 
        contradiction || assumption.
      * (* e->e2 is EAppAbs *) discriminate.
  - (* e->e1 is EApp1 *) inversion st_ee''; subst e e1 e2.
      * (* e->e2 is EPrim *) apply lem_value_stuck in H2; contradiction || constructor. 
      * (* e->e2 is EApp1 *) apply IHe1 with e'0 e'1 in H2 as H'. rewrite H'; 
        reflexivity. assumption. 
      * (* e->e2 is EApp2 *) apply lem_value_stuck in H2; contradiction || assumption. 
      * (* EAppAbs *) apply lem_value_stuck in H2; contradiction || constructor.
  - (* e->e1 is EApp2 *) inversion st_ee''; subst e1 e2.
      * (* e->e2 is EPrim *) apply lem_value_stuck in H3; contradiction || assumption.
      * (* EApp1 *) apply lem_value_stuck in H7; contradiction || assumption.
      * (* EApp2 *) assert (e'0 = e'1). apply IHe2; assumption. rewrite H; reflexivity.
      * (* EAppAbs *) apply lem_value_stuck in H3; intuition. 
  - (* e->e1 is EAppAbs *) inversion st_ee''; subst e1 e2.
      * (* e->e2 is EPrim *) discriminate.
      * (* EApp1 *) apply lem_value_stuck in H6; contradiction || constructor.
      * (* EApp2 *) apply lem_value_stuck in H7; contradiction || assumption.
      * (* EAppAbs *) injection H3 as H'; rewrite H'; reflexivity.
  - (* e->e1 is EPrimT *) inversion st_ee''; subst e.
      * (* e->e2 is EPrimT *) injection H3 as Hc. subst c. apply deltaT_pf_indep.
      * (* EAppT *) apply lem_value_stuck in H7; contradiction || constructor.
      * (* EAppTAbs *) discriminate.
  - (* e->e1 is EAppT *) inversion st_ee''; subst e e0 t.
      * (* EPrimT *) apply lem_value_stuck in H3; contradiction || constructor.
      * (* EAppT *) apply IHe with e'0 e'1 in H3 as H'. rewrite H'. reflexivity. assumption.
      * (* EAppTAbs *) apply lem_value_stuck in H3; contradiction || constructor.
  - (* e->e1 is EAppTAbs*) inversion st_ee''; subst e t.
      * (* EPrimT *) discriminate.
      * (* EAppT *) apply lem_value_stuck in H7; contradiction || constructor.
      * (* EAppTAbs *) injection H3 as H'; subst e0; reflexivity.
  - (* e->e1 is ELet *) inversion st_ee''; subst e1 e2.
      * (* ELet *) apply IHe1 with e_x' e_x'0 in H2 as H'. rewrite H'. reflexivity. assumption.
      * (* ELetV *) apply lem_value_stuck in H2; contradiction || assumption.
  - (* e->e1 is ELetV *) inversion st_ee''; subst e1 e2.
      * (* ELet *) apply lem_value_stuck in H6; contradiction || assumption.
      * (* ELetV *) reflexivity.
  - (* e->e1 is EAnn *) inversion st_ee''; subst e t.
      * (* EAnn *) apply IHe with e'0 e'1 in H2 as H'. rewrite H'; reflexivity. assumption.
      * (* EAnnV *) subst e0 e''. apply lem_value_stuck in H2; contradiction || assumption.
  - (* e->e1 is EAnnV *) inversion st_ee''; subst e e' t.
      * (* EAnn *) apply lem_value_stuck in H6; contradiction || assumption.
      * (* EAnnV *) assumption.
  - (* e->e1 is ESwitch *) inversion st_ee''.
      * (* ESwitch *) apply IHe with e'0 e'1 in H2 as H'; try rewrite H'; 
        reflexivity || assumption.
      * (* ESwitchV *) apply lem_value_stuck in H2; try contradiction;
        apply val_dv; assumption.
  - (* e->e1 is ESwitchV *) inversion st_ee''.
      * (* ESwitch *) apply lem_value_stuck in H7; try contradiction;
        apply val_dv; assumption.
      * (* ESwitchV *) assert (dvdc e pf0 = dvdc e pf) by apply dvdc_pf_indep;
        rewrite H9 in H8; 
        assert (m0 = m) by (apply isMatch_unique with (dvdc e pf) cs; assumption);
        rewrite H10; apply subMany_pf_indep.
  Qed.

Lemma lem_evals_val_det : forall (e v1 v2 : expr), 
    isValue v1 -> isValue v2 -> EvalsTo e v1 -> EvalsTo e v2 ->  v1 = v2.
Proof. intros e v1 v2 val1 val2 ev_ev1 ev_ev2. 
  induction ev_ev1 as [v1|e e1 v1 st_ee1 ev_e1v1]; 
  inversion ev_ev2 as [_v2|_e e2 _v2 st_ee2 ev_e2v2].
  - (* Refl, Refl *) reflexivity. 
  - (* Refl, AddS *) apply lem_value_stuck in st_ee2; contradiction || apply val1.
  - (* AddS, Refl *) subst v2. apply lem_value_stuck in st_ee1; 
    contradiction || apply val2.
  - (* AddS, AddS *) apply IHev_e1v1. assumption.
      apply lem_sem_det with e e1 e2 in st_ee1 as Heq. rewrite Heq. all : assumption. 
  Qed. 
  
Lemma lem_decompose_evals : forall (e e' v : expr), 
    isValue v -> EvalsTo e e' -> EvalsTo e v -> EvalsTo e' v.
Proof. intros e e' v val ev_ee' ev_ev. induction ev_ee' as [ |e e1 e' st_ee1 ev_e1e' IH].
  - (* Refl *) assumption.
  - (* AddS *) inversion ev_ev as [ |_e e2 _v st_ee2 ev_e2v]. 
      * (* Refl *) subst e e0. apply lem_value_stuck in st_ee1; contradiction || apply val.
      * (* AddS *) apply IH. 
          apply lem_sem_det with e e1 e2 in st_ee1 as Heq. rewrite Heq. all:assumption. 
  Qed.