Require Import Arith.
Require Import ZArith.
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
-- E-PrimT   c [t] -> deltaT(c,t)
-- E-AppT    e [t] -> e' [t] id e->e'
-- E-AppTAbs (/\a. e) [t] -> e[t/a]
-- E-Let     let x=e_x in e -> let x=e'_x in e if e_x->e'_x
-- E-LetV    let x=v in e -> e[v/x]
-- E-Ann     e:t -> e':t  if e->e'
-- E-AnnV    v:t -> v  
-- E-If      if e0 then e1 else e2 -> if e0' then e1 else e2 if e0->e0'
-- E-IfT     if true  then e1 else e2 -> e1
-- E-IfF     if false then e1 else e2 -> e2
-- E-Cons1   (e:es) -> (e':es) if e->e'
-- E-Cons2   (v:es) -> (v:es') if es->es'
-- E-Switch  case e of ... -> case e' of ... if e->e'
-- E-SwitchN case Nil of { Nil -> eN ...} -> eN
-- E-SwitchC case (v1:v2) of { Cons x1 x2 -> eC x1 x2} -> (eC v1) v2 *)

(* We distinguish three kinds of Primitives:
    * Monomorphic, the prim is applied to an expr, semantics in delta
    * Polymorphic, the prim is applied to a type, semantics in deltaT
    * Measures, the polym prim is applied to type and expr, semantics in deltaM *)

Inductive isCompat : prim -> expr -> Set :=   (* can't use Prop here*)
    | isCpt_And  : forall b, isCompat And (Bc b) 
    | isCpt_Or   : forall b, isCompat Or  (Bc b)      
    | isCpt_Not  : forall b, isCompat Not (Bc b)    
    | isCpt_Eqv  : forall b, isCompat Eqv (Bc b)      
    | isCpt_Imp  : forall b, isCompat Imp (Bc b)   
    | isCpt_Leq  : forall n, isCompat Leq (Ic n) 
    | isCpt_Leqn : forall n m, isCompat (Leqn n) (Ic m) 
    | isCpt_Eq   : forall n, isCompat Eq  (Ic n) 
    | isCpt_Eqn  : forall n m, isCompat (Eqn n) (Ic m)
    | isCpt_Succ : forall n, isCompat Succ (Ic n).
    
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
    | Succ     , (Ic n)     => True 
    | _        , _          => False
    end.

Lemma compat_prop_set : forall (c:prim) (v:expr),
    isCompat' c v -> isCompat c v.
Proof. intros c v; intro cpt'; destruct c;
  destruct v; simpl in cpt'; try contradiction. 
  - apply isCpt_And.
  - apply isCpt_Or.
  - apply isCpt_Not.
  - apply isCpt_Eqv.
  - apply isCpt_Imp.
  - apply isCpt_Leq.
  - apply isCpt_Leqn.
  - apply isCpt_Eq.
  - apply isCpt_Eqn. 
  - apply isCpt_Succ.
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
    | isCpt_Leqn n m => Bc (Z.leb n m)
    | isCpt_Eq   n   => Prim (Eqn n)
    | isCpt_Eqn n m  => Bc (Z.eqb n m)
    | isCpt_Succ n   => Ic(1 + n) 
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
    | (Leqn n) , (Ic m)     => Some  (Bc (Z.leb n m))
    | Eq       , (Ic n)     => Some  (Prim (Eqn n))
    | (Eqn n)  , (Ic m)     => Some  (Bc (Z.eqb n m))
    | Succ     , (Ic n)     => Some  (Ic (1+n))
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

Lemma lem_delta_value : forall (c : prim) (v : expr) (pf : isCompat c v),
    isValue (delta c v pf).
Proof. intros. destruct pf; try destruct b; simpl;  
  try apply val_Lam; try apply val_Bc; try apply val_Prm;
  apply val_Ic. Qed.


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

Lemma deltaT_exchange_type : 
  forall (c:prim) (t t':type) (pf:isCompatT c t) (pf':isCompatT c t'),
    erase t = erase t' -> deltaT c t pf = deltaT c t' pf'.
Proof. intros. assert (deltaT' c t = deltaT' c t')
      by (inversion pf; simpl; rewrite <- H; rewrite H0; reflexivity);
  rewrite deltaT_deltaT' with c t  pf  in H0;
  rewrite deltaT_deltaT' with c t' pf' in H0;
  injection H0 as H0; apply H0. Qed.


(* For measures only *)
Inductive isCompatM : prim -> expr -> Set :=   (* can't use Prop here*)
    | isCptM_LNil : isCompatM Length Nil
    | isCptM_LCons : forall e es, isCompatM Length es -> isCompatM Length (Cons e es).
    
Fixpoint isCompatM' (c:prim) (v:expr) : Prop := 
    match c, v with
    | Length   , Nil        => True
    | Length  , (Cons _ es) => isCompatM' Length es 
    | _        , _          => False
    end.

Lemma compatM_prop_set : forall (c:prim) (v:expr),
    isCompatM' c v -> isCompatM c v.
Proof. intros c v; induction v; intro cpt';
  destruct c; simpl in cpt'; try contradiction. 
  - apply isCptM_LNil.
  - apply isCptM_LCons; apply IHv2; apply cpt'.
  Qed.
    
(* isCompat p e  -> { e':Value | Set_emp (fv e') && Set_emp (ftv e') } *)
Fixpoint deltaM (c : prim) (v : expr) (pf : isCompatM c v) : expr :=
    match pf with
    | isCptM_LNil           => Ic 0
    | isCptM_LCons _ es pf' => App (Prim Succ) (deltaM Length es pf')
    end.

Fixpoint deltaM' (c : prim) (v : expr) : option expr :=
    match c, v with
    | Length   , Nil        => Some  (Ic 0)
    | Length  , (Cons _ es) => match (deltaM' Length es) with
                               | Some e => Some (App (Prim Succ) e)
                               | None   => None
                               end
    | _        , _          => None 
    end.

Lemma deltaM_deltaM' : forall (c : prim) (v : expr) (pf : isCompatM c v),
    Some (deltaM c v pf) = (deltaM' c v).
Proof. intros c v pf; induction pf;
  try destruct b; simpl; try rewrite <- IHpf; try reflexivity. Qed.

Lemma deltaM_pf_indep : forall (c : prim) (v : expr) (pf pf' : isCompatM c v),
    deltaM c v pf = deltaM c v pf'.
Proof. intros. assert (Some (deltaM c v pf) = Some (deltaM c v pf')).
  - transitivity (deltaM' c v); (apply deltaM_deltaM' || symmetry; apply deltaM_deltaM'). 
  - injection H. trivial. Qed. 


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
    | EPrimM : forall (c : prim) (t : type) (w : expr) (pf : isCompatM c w),
          isValue w -> Step (App (AppT (Prim c) t) w) (deltaM c w pf) 
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
    | EIf : forall (e0 e0' e1 e2 : expr),
          Step e0 e0' -> Step (If e0 e1 e2) (If e0' e1 e2)
    | EIfT : forall (e1 e2 : expr), Step (If (Bc true ) e1 e2) e1    
    | EIfF : forall (e1 e2 : expr), Step (If (Bc false) e1 e2) e2 
    | ECons1: forall (e e' e1 : expr),
          Step e e' -> Step (Cons e e1) (Cons e' e1)
    | ECons2: forall (e e' v : expr),
          isValue v -> Step e e' -> Step (Cons v e) (Cons v e')
    | ESwitch: forall (e e' eN eC : expr),
          Step e e' -> Step (Switch e eN eC) (Switch e' eN eC)
    | ESwitchN: forall (eN eC : expr), Step (Switch Nil eN eC) eN
    | ESwitchC: forall (v1 v2 eN eC : expr),
          isValue v1 -> isValue v2 
            -> Step (Switch (Cons v1 v2) eN eC) (App (App eC v1) v2).

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

Lemma lemma_if_many : forall (e0 e0' e1 e2 : expr),
    EvalsTo e0 e0' -> EvalsTo (If e0 e1 e2) (If e0' e1 e2).
Proof. intros e0 e0' e1 e2 ev_e0_e0'; induction ev_e0_e0'.
  - apply Refl.
  - apply AddStep with (If e3 e1 e2); try apply EIf; assumption. Qed.

Lemma lemma_cons_many : forall (e e' v : expr),
    EvalsTo e e' -> EvalsTo (Cons e v) (Cons e' v).
Proof. intros e e' v ev_e_e'. induction ev_e_e' as [e|e e1 e' st_ee1 ev_e1e' IH].
  - apply Refl.
  - apply AddStep with (Cons e1 v). 
      * apply ECons1; apply st_ee1.
      * apply IH. 
  Qed. 
  
Lemma lemma_cons_many2 : forall (v : expr) (e e' : expr), 
    isValue v -> EvalsTo e e' -> EvalsTo (Cons v e) (Cons v e').
Proof. intros v e e' val ev_e_e'. induction ev_e_e' as [e|e e1 e' st_ee1 ev_e1e' IH].
  - apply Refl.
  - apply AddStep with (Cons v e1).
      * apply ECons2; assumption.
      * apply IH.
  Qed.

Lemma lemma_cons_both_many : forall (e e' : expr) (v v' : expr),
    isValue v -> isValue v' -> EvalsTo e v -> EvalsTo e' v'
        -> EvalsTo (Cons e e') (Cons v v').
Proof. intros e e' v v' val val' ev_e_v ev_e'_v'. 
  apply lemma_evals_trans with (Cons v e').
  - apply lemma_cons_many; assumption.
  - apply lemma_cons_many2; assumption. Qed.   

Lemma lemma_switch_many : forall (e0 e0' eN eC : expr),
    EvalsTo e0 e0' -> EvalsTo (Switch e0 eN eC) (Switch e0' eN eC).
Proof. intros e0 e0' e1 e2 ev_e0_e0'; induction ev_e0_e0'.
  - apply Refl.
  - apply AddStep with (Switch e3 e1 e2); try apply ESwitch; assumption. Qed.

Lemma deltaM_evals : forall (c : prim) (v : expr) (pf : isCompatM c v),
    exists n, EvalsTo (deltaM c v pf) (Ic n).
Proof. intros c v; induction pf.
  - (* Nil *) exists 0 %Z; simpl; constructor.
  - (* Cons *) destruct IHpf as [n' ev_n']; exists (Z.succ n').
    assert (isCompat Succ (Ic n')) as pfn' by constructor.
    assert (delta' Succ (Ic n') = Some (Ic (Z.succ n'))) as del'
        by (destruct n'; try destruct p; simpl; trivial).
    assert (delta Succ (Ic n') pfn' = Ic (Z.succ n')) as del
        by (rewrite <- delta_delta' with Succ (Ic n') pfn' in del'; 
            injection del'; trivial).
    simpl; apply lemma_evals_trans with (App (Prim Succ) (Ic n'));
    try apply lemma_app_many2;
    try rewrite <- del; try (apply lem_step_evals; apply EPrim);
    constructor || assumption.
    Qed.

(*--------------------------------------------------------------------------
----- | Basic LEMMAS of the OPERATIONAL SEMANTICS (Small Step)
--------------------------------------------------------------------------*)

Theorem lem_value_stuck : forall (e e' : expr), 
    Step e e' -> isValue e -> False.
Proof. intros e e' st_e_e'; induction st_e_e'; intro Hval; inversion Hval.
  - (* EPrimT *) subst c; inversion pf.
  - (* EPrimM *) apply IHst_e_e'; subst e; constructor.
  - (* ECons1 *) apply IHst_e_e'; assumption.
  - (* ECons2 *) apply IHst_e_e'; assumption.
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
      * (* e->e2 is EPrimM *) discriminate.
  - (* e->e1 is EApp1 *) inversion st_ee''; subst e e1 e2.
      * (* e->e2 is EPrim *) apply lem_value_stuck in H2; contradiction || constructor.  
      * (* e->e2 is EApp1 *) apply IHe1 with e'0 e'1 in H2 as H'. rewrite H'; 
        reflexivity. assumption. 
      * (* e->e2 is EApp2 *) apply lem_value_stuck in H2; contradiction || assumption. 
      * (* EAppAbs *) apply lem_value_stuck in H2; contradiction || constructor.
      * (* EPrimM *) inversion H2. 
          + (* e->e1 uses EPrimT *) inversion pf0; subst c; subst c0; inversion pf.
          + apply lem_value_stuck in H8; contradiction || constructor. 
  - (* e->e1 is EApp2 *) inversion st_ee''; subst e1 e2.
      * (* e->e2 is EPrim *) apply lem_value_stuck in H3; contradiction || assumption.
      * (* EApp1 *) apply lem_value_stuck in H7; contradiction || assumption.
      * (* EApp2 *) assert (e'0 = e'1). apply IHe2; assumption. rewrite H; reflexivity.
      * (* EAppAbs *) apply lem_value_stuck in H3; intuition.
      * (* EPrimM *) inversion pf; apply lem_value_stuck in H3; 
        contradiction || assumption.
  - (* e->e1 is EAppAbs *) inversion st_ee''; subst e1 e2.
      * (* e->e2 is EPrim *) discriminate.
      * (* EApp1 *) apply lem_value_stuck in H6; contradiction || constructor.
      * (* EApp2 *) apply lem_value_stuck in H7; contradiction || assumption.
      * (* EAppAbs *) injection H3 as H'; rewrite H'; reflexivity.
      * (* EPrimM *) discriminate.
  - (* e->e' is EPrimM *) inversion st_ee''; subst e1 e2.
      * (* EPrim *) discriminate.
      * (* EApp1 *) inversion pf; subst c; apply lem_value_stuck in H6; 
        contradiction || apply val_Len.
      * (* EApp2 *) apply lem_value_stuck in H7; contradiction || assumption.
      * (* EAppAbs *) discriminate.
      * (* EPrimM *) injection H3; intros; subst c0; apply deltaM_pf_indep.   
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
  - (* e->e1 is EIf  *) inversion st_ee''; subst e0 e1 e' e''.
      * (* EIf  *) apply IHe1 with e0' e0'0 in H3 as H'; try rewrite H'; trivial.
      * (* EIfT *) apply lem_value_stuck in H3; simpl in H3; contradiction || constructor.
      * (* EIfF *) apply lem_value_stuck in H3; simpl in H3; contradiction || constructor.
  - (* e->e1 is EIfT *) inversion st_ee''; subst e1 e' e''.
      * (* EIf  *) apply lem_value_stuck in H7; simpl in H7; contradiction || constructor.
      * (* EIfT *) reflexivity.
      * (* EIfF *) discriminate.
  - (* e->e1 is EIfF *) inversion st_ee''; subst e1 e' e''.
      * (* EIf  *) apply lem_value_stuck in H7; simpl in H7; contradiction || constructor.
      * (* EIfT *) discriminate.
      * (* EIfF *) reflexivity.
  - (* e->e1 is ECons1 *) inversion st_ee''; subst e e1 e2.
      * (* e->e2 is ECons1 *) apply IHe1 with e'0 e'1 in H2 as H'. rewrite H'; 
        reflexivity. assumption. 
      * (* e->e2 is ECons2 *) apply lem_value_stuck in H2; contradiction || assumption.
  - (* e->e1 is ECons2 *) inversion st_ee''; subst e1 e2.
      * (* ECons1 *) apply lem_value_stuck in H7; contradiction || assumption.
      * (* ECons2 *) assert (e'0 = e'1). apply IHe2; assumption. rewrite H; reflexivity.
  - (* e->e1 is ESwitch  *) inversion st_ee''; subst e' e''.
      * (* ESwitch  *) apply IHe1 with e'0 e'1 in H3 as H'; try rewrite H'; trivial.
      * (* ESwitchN *) subst e1 e; apply lem_value_stuck in H3; simpl in H3; 
          contradiction || constructor.
      * (* ESwitchC *) subst e1 e; apply lem_value_stuck in H3; simpl in H3;
          contradiction || constructor; trivial.
  - (* e->e1 is ESwitchN *) inversion st_ee''; subst e1 e' e''.
      * (* ESwitch  *) apply lem_value_stuck in H7; simpl in H7; contradiction || constructor.
      * (* ESwitchN *) reflexivity.
      * (* ESwitchC *) discriminate.
  - (* e->e1 is ESwitchC *) inversion st_ee''. subst e1 e' e''.
      * (* ESwitch  *) apply lem_value_stuck in H9; simpl in H9; contradiction || constructor; trivial.
      * (* ESwitchN *) subst e1; discriminate.
      * (* ESwitchC *) subst e1; injection H5 as H5' H5''; repeat f_equal; auto.
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