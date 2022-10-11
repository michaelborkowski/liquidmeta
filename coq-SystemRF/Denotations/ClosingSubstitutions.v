Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.

(*------------------------------------------------------------------------- 
----- | CLOSING SUBSTITUTIONS 
-------------------------------------------------------------------------*)

(* closing substitutions (i.e. th(x), th(e), th(t)) proceed from the top/right of
 *   the typing env downwards/leftwards. In order for a closing substitution to be
 *   "well formed" it must be an element of the denotation 
 *   of the corresponding enivornment *)

Inductive csub :Set :=
    | CEmpty
    | CCons  (x : vname) (v_x : expr) (th : csub)
    | CConsT (a : vname) (t_a : type) (th : csub).
  
Fixpoint bindsC (th : csub) : names := 
    match th with 
    | CEmpty            => empty
    | (CCons  x v_x th) => names_add x (bindsC th)
    | (CConsT a t_a th) => names_add a (bindsC th)
    end.

Fixpoint vbindsC (th : csub) : names := 
    match th with 
    | CEmpty            => empty
    | (CCons  x v_x th) => names_add x (vbindsC th)
    | (CConsT a t_a th) => vbindsC th
    end.

Fixpoint tvbindsC (th : csub) : names := 
    match th with 
    | CEmpty            => empty
    | (CCons  x v_x th) => tvbindsC th
    | (CConsT a t_a th) => names_add a (tvbindsC th)
    end.

Definition in_csubst (x : vname) (th : csub) : Prop := Elem x (bindsC th).

Lemma vbindsC_subset : forall (th : csub), Subset (vbindsC th) (bindsC th).
Proof. unfold Subset; induction th; simpl.
  - trivial.
  - apply subset_add_both_intro; assumption.
  - apply subset_add_intro; assumption. Qed.
  
Lemma tvbindsC_subset : forall (th : csub), Subset (tvbindsC th) (bindsC th).
Proof. unfold Subset; induction th; simpl.
  - trivial.
  - apply subset_add_intro; assumption.
  - apply subset_add_both_intro; assumption. Qed. 

(* Should we add Fixpoint uniqueC ? *)
(* Should we add Lemma in_env_CCons ? *)  (* Should we add Lemma in_env_CConsT ? *)

Fixpoint bound_inC (x : vname) (v_x : expr) (th : csub) : Prop := 
    match th with
    | CEmpty             => False
    | (CCons  y v_y th)  => (x = y /\ v_x = v_y) \/ bound_inC x v_x th
    | (CConsT a t_a th)  => bound_inC x v_x th
    end.

Fixpoint tv_bound_inC :: vname -> Type -> csub -> Bool
tv_bound_inC a t CEmpty                                = False
tv_bound_inC a t (CCons  y  v' th) | (a == y)          = False
                                   | otherwise         = tv_bound_inC a t th
tv_bound_inC a t (CConsT a' t' th) | (a == a')         = (t == t')
                                   | otherwise         = tv_bound_inC a t th

{-@ reflect csubst @-}
{-@ csubst :: th:csub -> e:expr -> { e':expr | (isTerm e => isTerm e') && (isPred e => isPred e') } @-}
csubst :: csub -> expr -> expr
csubst CEmpty          e = e
csubst (CCons  x v th) e = csubst th (subFV x v e)
csubst (CConsT a t th) e = csubst th (subFTV a t e)

-- Idea: ctsubst th t = foldr (\(x,e) t' -> tsubFV x e t') t th 
{-@ reflect ctsubst @-}
{-@ ctsubst :: th:csub -> t:Type -> Type @-}
ctsubst :: csub -> Type -> Type
ctsubst CEmpty           t = t
ctsubst (CCons  x v  th) t = ctsubst th (tsubFV x v t)
ctsubst (CConsT a t' th) t = ctsubst th (tsubFTV a t' t)

{-@ reflect csubst_tv @-}
{-@ csubst_tv :: th:csub -> { a:vname | tv_in_csubst a th } 
        -> { t':UserType | Set_emp (free t') && Set_emp (freeTV t') &&
                           Set_emp (tfreeBV t') && Set_emp (tfreeBTV t') }@-}
csubst_tv :: csub -> vname -> Type
csubst_tv (CCons  x  v  th) a             = csubst_tv th a
csubst_tv (CConsT a' t' th) a | a' == a   = t'
                              | otherwise = csubst_tv th a

{-@ reflect concatCS @-}
{-@ concatCS :: th:csub -> { th':csub | Set_emp (Set_cap (bindsC th) (bindsC th')) }
                          -> { thC:csub | bindsC thC == Set_cup (bindsC th) (bindsC th') } @-}
concatCS :: csub -> csub -> csub
concatCS th CEmpty           = th
concatCS th (CCons  x v th') = CCons x v (concatCS th th')
concatCS th (CConsT a t th') = CConsT a t (concatCS th th')

(*@ reflect remove_fromCS @-}
{-@ remove_fromCS :: th:csub -> { x:vname | in_csubst x th}
        -> { th':csub | bindsC th' == Set_dif (bindsC th) (Set_sng x) } @-}
remove_fromCS :: csub -> vname -> csub
remove_fromCS (CCons  z v_z th) x | ( x == z ) = th
                                  | otherwise  = CCons  z v_z (remove_fromCS th x)
remove_fromCS (CConsT a t_a th) x | ( x == a ) = th
                                  | otherwise  = CConsT a t_a (remove_fromCS th x)

---------------------------------------------------------------------------
----- | PROPOSITIONS
---------------------------------------------------------------------------
  --- the Type of all Propositions

data Proposition where

    Entails :: Env -> expr -> Proposition
    ValueDenoted :: expr -> Type -> Proposition
    Denotes :: Type -> expr -> Proposition        -- e \in [[t]]
    DenotesEnv :: Env -> csub -> Proposition      -- th \in [[G]]

    -- Entailments
    Augmentedcsub   :: Env -> Env -> vname -> expr -> Type -> csub -> Proposition
    TVAugmentedcsub :: Env -> Env -> vname -> Type -> Kind -> csub -> Proposition *)