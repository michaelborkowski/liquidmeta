Fixpoint isValue (e: expr) : Prop :=
    match e with
    | Bc _          => True
    | Ic _          => True
    | Prim c        => True
    | Dc _          => True
    | FV _          => True
    | BV _          => True
    | Lambda   _    => True
    | LambdaT   k e => True
    | App e1 e2     => dataValue e1 /\ isValue e2
    | _             => False       
    end

with dataValue (e : expr) : Prop :=
    match e with  
    | Dc _          => True
    | App e1 e2     => dataValue e1 /\ isValue e2
    | _             => False
    end.

Lemma isValue_isValueI : forall (v : expr),
    (isValue v -> isValueI v) * (dataValue v -> dataValueI v ).
Proof. intros v; induction v; split; intro Hval; simpl; try contradiction; 
  try constructor; try apply dval_Dc; try apply dval_App;
  simpl in Hval; destruct Hval;  apply IHv1 || apply IHv2; assumption.
  Qed.

Definition fullyApplied (dv : expr) : Prop :=
    dataValue dv /\ argCount dv = option_map arity (dvdc dv).
    
Inductive fullyAppliedI : expr -> Set :=
    | fullyApp : forall dv pf, argCountI dv pf = arity (dvdcI dv pf) -> fullyAppliedI dv.

(********************************************************************************)

(* Inductive  hasMatch : expr -> alts -> Set :=
    |
    | matchCons : 

Inductive  hasMatch : expr -> alts -> Set :=
    | hasM : forall dv cs pf, 
            Elem (dcid (dvdcI dv pf)) (altsIds cs) -> fullyAppliedI dv -> hasMatch dv cs. 
Definition hasMatch' (dv : expr) (cs : alts) : Prop :=
    isSome (option_map (fun i : id => Elem i (altsIds cs)) (option_map dcid (dvdc dv))) /\ 
    fullyApplied dv.*)

(* 
        ESwitchV :: dv:DataValue -> { as:Alts | HasMatch dv as }
                      -> ProofOf(Step (Switch dv as) (subMatch dv as))

{-@ reflect altsIds @-}
altsIds :: Alts -> S.Set Id
altsIds AEmpty           = S.empty
altsIds (ACons dc e as)  = S.union (S.singleton (dcid dc)) (altsIds as)

{-@ reflect altsLookup @-}
{-@ altsLookup :: i:Id -> { as:Alts | Set_mem i (altsIds as) } -> Expr @-}
altsLookup :: Id -> Alts -> Expr
altsLookup i (ACons dc e as) | i == dcid dc  = e
                             | otherwise     = altsLookup i as

{-                     :: DataValue -> Alts -> Bool -}
{-@ predicate HasMatch DV AS =   Set_mem (dcid (dvdc DV)) (altsIds AS) && FullyApplied DV @-}

{-@ reflect getMatch @-}
{-@ getMatch :: dv:DataValue -> { as:Alts | HasMatch dv as } -> Expr @-}
getMatch :: Expr -> Alts -> Expr
getMatch dv as = altsLookup (dcid (dvdc dv)) as

{-@ reflect subMatch @-}
{-@ subMatch :: dv:DataValue -> { as:Alts | HasMatch dv as } -> Expr @-}
subMatch :: Expr -> Alts -> Expr
subMatch dv as = subMany dv (getMatch dv as)

{-@ reflect subMany @-}
{- @ subMany :: { dv:DataValue | argCount dv == arity (dvdc dv) } -> Expr -> Expr @-}
{-@ subMany :: DataValue -> Expr -> Expr @-}
subMany :: Expr -> Expr -> Expr
subMany (C (Dc _)) e = e
subMany (App dv v) e = subBV v (subMany dv e)                      
*)

Definition getMatch' (dv : expr) (cs : alts) : option expr :=
    option_map (fun i : id => altsLookup i cs) (option_map dcid (dvdc dv)).

Definition subMatch' (dv : expr) (cs : alts) : option expr :=
    option_map (subMany' dv) (getMatch' dv cs).