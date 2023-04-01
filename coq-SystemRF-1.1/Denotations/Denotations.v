Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.Semantics.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.LemmasTransitive.
Require Import Denotations.ClosingSubstitutions.

Require Import Arith Program.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Relations.Relation_Operators.

Fixpoint isMono (t0 : type) : Prop := 
    match t0 with         
    | (TRefn b ps)     => True  
    | (TFunc  t_x t)   => isMono t_x /\ isMono t
    | (TExists  t_x t) => isMono t_x /\ isMono t
    | (TPoly  k   t)   => False
    end.

Fixpoint quants (t : type) : nat :=
    match t with
    | (TRefn b ps)     => 0  
    | (TFunc  t_x t)   => max (quants t_x) (quants t)
    | (TExists  t_x t) => max (quants t_x) (quants t)
    | (TPoly  k   t)   => 1 + (quants t)
    end.

Definition quants_depth (t : type) : nat*nat := (quants t, depth t).

Definition lexico_lt (ns : nat*nat) (ms : nat*nat) : Prop :=
    match ns with
    | (n1, n2) => match ms with
                  | (m1, m2) => n1 < m1 \/ (n1 = m1 /\ n2 < m2)
                  end
    end.

Definition quants_depthR (t t' : type) : Prop := 
    quants t < quants t' \/ (quants t = quants t' /\ depth t < depth t').

(*------------------------------------------------------------------------------
----- | DENOTATIONAL SEMANTICS 
------------------------------------------------------------------------------*)

Inductive PEvalsTrue : preds -> Prop :=
    | PEEmp  : PEvalsTrue PEmpty
    | PECons : forall (p : expr) (ps : preds),
        EvalsTo p (Bc true) -> PEvalsTrue ps -> PEvalsTrue (PCons p ps).

Program Fixpoint Denotes (t : type) (v : expr) 
                         {measure (quants_depth t) lexico_lt} : Prop :=
  isValue v /\ HasFtype FEmpty v (erase t) /\ (
    match t with
    | (TRefn   b   ps) => PEvalsTrue (psubBV v ps) 
    | (TFunc   t_x t') => forall (v_x : expr),
        isValue v_x /\ Denotes t_x v_x /\ (exists (v' : expr), 
            isValue v' /\ EvalsTo (App v v_x) v' /\ Denotes (tsubBV v_x t') v'
        )
    | (TExists t_x t') => exists (v_x : expr),
        isValue v_x /\ Denotes t_x v_x /\ Denotes (tsubBV v_x t') v
    | (TPoly   k   t') => exists (t_a : type) (v' : expr),
        noExists t_a /\ WFtype Empty t_a k /\ isValue v' /\
          EvalsTo (AppT v t_a) v' /\ Denotes (tsubBTV t_a t') v'
    end
  ). 
  Obligation 1.  (* quants_depth t_x "<" quants_depth t *)
    pose proof Nat.le_max_l (quants t_x) (quants t') as Hq;
    pose proof Nat.le_max_l (depth  t_x) (depth  t') as Hd.
    apply Nat.lt_eq_cases in Hq; destruct Hq as [Hq|Hq]; simpl.
      * left. apply Hq.
      * right; split; try apply Hq. apply Nat.lt_succ_r; apply Hd.
  Qed.
  Obligation 2.  (* quants_depth (tsubBV v_x t') "<" quants_depth t *)
    pose proof Nat.le_max_r (quants t_x) (quants t') as Hq;
    pose proof Nat.le_max_r (depth  t_x) (depth  t') as Hd.
  
  simpl. intuition.
  
  Obligation 6. unfold well_founded.
  
Definition foo : nat := 5.

(*------------------------------------------------------------------------------
----- | ENTAILMENT 
------------------------------------------------------------------------------*)