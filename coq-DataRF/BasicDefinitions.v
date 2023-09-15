Require Import Nat.
Require Import Lists.List.
Require Import Program.Basics.

Definition index := nat.
Definition vname := nat. (* can change this atoms later *)
Definition id    := nat.
Definition Arity := nat.

Record dcons := DCons {
    dcid    : id;
    arity   : Arity
}.

Record tcons := TCons {
    tcid    : id
}.

Inductive prim : Set :=
    | And 
    | Or 
    | Not 
    | Eqv 
    | Imp
    | Leq 
    | Leqn (n : nat)
    | Eq  
    | Eqn (n : nat)
    | Leql 
    | Eql.           (* Leql and Eql are polymorphic *)

Inductive basic : Set :=
    | TBool 
    | TInt                          
    | BTV   (i : index)
    | FTV   (a : vname).

    Definition isClosedBasic (b : basic) : Prop :=
        match b with
        | TBool => True
        | TInt  => True
        | _     => False
        end.

    Definition isBTV (b : basic) : Prop := 
        match b with
        | (BTV _) => True
        | _       => False
        end.  


(* ONLY types with Base kind may have non-trivial refinements. Star kinded type variables 
     may only have the refinement { x : [] }. *)
Inductive kind : Set := 
    | Base         (* B, base kind *)
    | Star.        (* *, star kind *)

Inductive expr : Set :=  
    | Bc (b : bool)                 (* True, False *)
    | Ic (n : nat)                  (* 0, 1, 2, *)
    | Prim (p : prim)               (* built-in primitive functions *)
    | Dc (d : dcons)
    | BV (i : index)                (* BOUND Variables: bound to a Lambda, Let or :t *)
    | FV (x : vname)                (* FREE Variables: bound in an environment *)
    | Lambda (e : expr)             (* \x.e          abstractions    (x is nameless) *)
    | App (e1 : expr) (e2 : expr)   (* e e'          applications *)
    | LambdaT (k : kind) (e : expr) (* /\a:k.e  type abstractions    (a is nameless) *)
    | AppT (e : expr) (t : type)    (* e [bt]   type applications *)
    | Let (e1 : expr) (e2 : expr)   (* let x = e1 in e2              (x is nameless) *)
    | Annot (e : expr) (t : type)   (* e : t *)
    | Switch (e : expr) (cs : alts)

with alts : Set :=
    | AEmpty
    | ACons  (d : dcons) (e : expr) (cs : alts)

with type : Set :=
    | TRefn   (b : basic) (ps : preds)   (* b{x0 : [p]} *)
    | TData   (tc: tcons) (t:type)  (ps: preds)  (* TODO: is this WLOG? *)
    | TFunc   (tx : type) (t : type)     (* x:t_x -> t *)
    | TExists (tx : type) (t : type)     (* \exists x:t_x. t *)
    | TPoly   (k : kind)  (t : type)     (* \forall a:k. t *)

with preds : Set :=               (* i.e. [expr] *)
    | PEmpty
    | PCons (p : expr) (ps : preds).

Scheme expr_mutind  := Induction for expr  Sort Set
with   alts_mutind  := Induction for alts  Sort Set
with   type_mutind  := Induction for type  Sort Set
with   preds_mutind := Induction for preds Sort Set.
Combined Scheme syntax_mutind from 
    expr_mutind, alts_mutind, type_mutind, preds_mutind.

    Definition isTRefn (t : type) : Prop  := 
        match t with
        | (TRefn _ _) => True
        | _           => False
        end.
    
    Definition isTFunc (t : type) : Prop  :=
        match t with 
        | (TFunc _ _) => True
        | _           => False
        end.
    
    Definition isTExists (t : type) : Prop  := 
        match t with
        | (TExists _ _) => True
        | _             => False
        end.
    
    Definition isTPoly (t : type) : Prop  :=
        match t with
        | (TPoly _ _) => True
        | _           => False
        end.  

Inductive isValue : expr -> Set := (* can't use Prop here *)
    | val_Bc   : forall b,   isValue (Bc b)
    | val_Ic   : forall n,   isValue (Ic n)
    | val_Prm  : forall c,   isValue (Prim c)
    | val_Dc   : forall dc,  isValue (Dc dc)
    | val_BV   : forall i,   isValue (BV i)
    | val_FV   : forall x,   isValue (FV x)
    | val_Lam  : forall e,   isValue (Lambda e)
    | val_LamT : forall k e, isValue (LambdaT k e)
    | val_dv   : forall dv,  dataValue dv -> isValue dv

with dataValue : expr -> Set :=
    | dval_Dc : forall dc t, dataValue (AppT (Dc dc) t)
    | dval_App : forall dv v, dataValue dv -> isValue v -> dataValue (App dv v).

Fixpoint dvdc (dv : expr) (pf : dataValue dv) : dcons :=
    match pf with
    | dval_Dc  dc _             => dc
    | dval_App dv v dv_pf v_pf  => dvdc dv dv_pf
    end.

Fixpoint argCount (dv: expr) (pf : dataValue dv) : nat :=
    match pf with
    | dval_Dc  _  _             => 0
    | dval_App dv v dv_pf v_pf  => S (argCount dv dv_pf)
    end.

Fixpoint dvdc' (dv : expr) : option dcons :=
    match dv with
    | AppT (Dc dc) _  => Some dc
    | App dv v        => dvdc' dv
    | _               => None
    end.

Fixpoint argCount' (dv : expr) : option nat :=
    match dv with
    | AppT (Dc _) _ => Some 0
    | App dv v      => option_map S (argCount' dv) 
    | _             => None
    end.

Lemma dvdc_dvdc' : forall (dv : expr) (pf : dataValue dv),
    dvdc' dv = Some (dvdc dv pf).
Proof. intros. induction pf as [dc|dv v Hdv IH Hv]; simpl;
  try rewrite IH; simpl; reflexivity. Qed.

Lemma dvdc_pf_indep : forall (dv : expr) (pf pf' : dataValue dv),
    dvdc dv pf = dvdc dv pf'.
Proof. intros. assert (Some (dvdc dv pf) = Some (dvdc dv pf')).
- apply eq_stepl with (dvdc' dv); apply dvdc_dvdc'.
- injection H as H'; assumption. Qed.

Definition fullyApplied (dv: expr) (pf : dataValue dv) : Prop :=
    argCount dv pf = arity (dvdc dv pf).

    (* These "usertypes" would also avoid issues of 
    --   deBruijn index shifting 
    --   in type variable substitution (in defining push) *)    
Fixpoint noExists (t0 : type) : Prop := 
    match t0 with         
    | (TRefn b ps)     => True  
    | (TData tc t ps)  => noExists t
    | (TFunc  t_x t)   => noExists t_x /\ noExists t
    | (TExists  t_x t) => False
    | (TPoly  k   t)   => noExists t
    end.

Fixpoint arrows (t : type) : nat := 
    match t with 
    | (TFunc t_x t)  => 1 + (arrows t)
    | _              => 0
    end.

Definition quant_arrows (t : type) : nat := 
    match t with 
    | (TPoly k t) => arrows t
    | _           => 0
    end.

Fixpoint quants (t : type) : nat :=
    match t with
    | (TPoly k t) => 1 + (quants t)
    | _e          => 0
    end.

Fixpoint outTC (t : type) : option tcons :=
    match t with 
    | (TFunc tx t)    => outTC t 
    | (TData tc t ps) => Some tc
    | _               => None
    end.

  (* --- DEFINITIONAL ENVIRONMENTS ---  
      -- not currently enforced: but we assume that every
      --     DCons id is globally unique *)
Record ddefn := DDefn {
    dddc    : dcons;
    ddtype  : type
}.

Inductive polarity : Set := 
    | Pos 
    | Neg 
    | Both 
    | Neither.

Definition (*Inductive*) ddefns (*: Set*) := list ddefn.
    (*| DDEmpty | DDCons (dd : ddefn) (dds : ddefns).*)

Record tdefn := TDefn { 
    tdtc     : tcons;
    vkind    : kind;
    vpolar   : polarity;
    tddcons  : ddefns 
}.        

Definition defs := list tdefn.

Definition defsIds (tds : defs) : list id :=
    map (compose tcid tdtc) tds.

Definition in_defs (tc : tcons) (ds : defs) : Prop := In (tcid tc) (defsIds ds).

Fixpoint uniqueDefs (tds : defs) : Prop :=
    match tds with
    | nil         => True
    | (td :: tds) => ~ in_defs (tdtc td) tds /\ uniqueDefs tds
    end.

Definition ddTypeMatch (tc : tcons) (dd : ddefn) :=
    quants (ddtype dd) = 1 /\ outTC (ddtype dd) = Some tc.

Definition tdIsValid (td : tdefn) : Prop := 
    Forall (ddTypeMatch (tdtc td)) (tddcons td) /\ tddcons td <> nil.

Definition isValid (tds : defs) : Prop := uniqueDefs tds /\ Forall tdIsValid tds. 

Fixpoint defined_in (tc : tcons) (dds : ddefns) (tds : defs) : Prop := 
    match tds with
    | nil         => False
    | (td :: tds) => (tc = tdtc td /\ dds = tddcons td) \/ defined_in tc dds tds
    end.

Fixpoint kind_defined_in (tc : tcons) (k : kind) (tds : defs) : Prop :=
    match tds with
    | nil         => False
    | (td :: tds) => (tc = tdtc td /\ k = vkind td) \/ kind_defined_in tc k tds
    end.

Fixpoint dc_defined_in (dc : dcons) (dt : type) (tds : defs) : Prop :=
    match tds with
    | nil         => False
    | (td :: tds) => In (DDefn dc dt) (tddcons td) \/ dc_defined_in dc dt tds
    end.

Fixpoint isLC_at (j_x : index) (j_a : index) (e : expr) : Prop  :=
    match e with
    | (Bc _)         => True
    | (Ic _)         => True
    | (Prim _)       => True
    | (Dc _)         => True
    | (BV i)         => i < j_x
    | (FV _)         => True
    | (Lambda e')    => isLC_at (j_x + 1) j_a e'
    | (App e1 e2)    => isLC_at j_x j_a e1    /\ isLC_at j_x j_a e2 
    | (LambdaT k e') => isLC_at j_x (j_a + 1) e'
    | (AppT e' t)    => isLC_at j_x j_a e'    /\ isLCT_at j_x j_a t 
    | (Let ex e')    => isLC_at j_x j_a ex    /\ isLC_at (j_x+1) j_a e'  
    | (Annot e' t)   => isLC_at j_x j_a e'    /\ isLCT_at j_x j_a t 
    | (Switch e cs)  => isLC_at j_x j_a e     /\ isLCA_at j_x j_a cs
    end

with isLCA_at (j_x : index) (j_a : index) (cs : alts) : Prop :=
    match cs with 
    | AEmpty          => True
    | (ACons dc e cs) => isLC_at (j_x + (arity dc)) (j_a + 1) e /\ isLCA_at j_x j_a cs
    end

with isLCT_at (j_x : index) (j_a : index) (t0 : type) : Prop := 
    match t0 with
    | (TRefn   b  rs) =>  
          match b with          
          | (BTV i) => i < j_a /\ isLCP_at (j_x+1) j_a rs
          | _       =>            isLCP_at (j_x+1) j_a rs
          end
    | (TData tc t ps) => isLCT_at j_x j_a t /\ isLCP_at (j_x+1) j_a ps
    | (TFunc   t_x t) => isLCT_at j_x j_a t_x /\ isLCT_at (j_x+1) j_a t
    | (TExists t_x t) => isLCT_at j_x j_a t_x /\ isLCT_at (j_x+1) j_a t
    | (TPoly   k   t) =>                         isLCT_at j_x (j_a+1) t
    end

with isLCP_at (j_x : index) (j_a : index) (ps0 : preds) : Prop := 
    match ps0 with
    | PEmpty       => True
    | (PCons p ps) => isLC_at j_x j_a p /\ isLCP_at j_x j_a ps
    end.

Definition isLC  (e  : expr)  : Prop := isLC_at  0 0 e.
Definition isLCA (cs : alts)  : Prop := isLCA_at 0 0 cs.
Definition isLCT (t  : type)  : Prop := isLCT_at 0 0 t.
Definition isLCP (ps : preds) : Prop := isLCP_at 0 0 ps.

Fixpoint open_at (j : index) (y : vname) (e : expr) : expr := 
    match e with
    | (Bc b)             => Bc b
    | (Ic n)             => Ic n
    | (Prim c)           => Prim c
    | (Dc dc)            => Dc dc
    | (BV i)             => if j =? i then FV y else BV i 
    | (FV x)             => FV x
    | (Lambda e')        => Lambda (open_at (j+1) y e')
    | (App e1 e2)        => App   (open_at j y e1)  (open_at j y e2)
    | (LambdaT k e')     => LambdaT k (open_at j y e')  
    | (AppT e' t)        => AppT  (open_at j y e')  (openT_at j y t)
    | (Let ex e')        => Let   (open_at j y ex) (open_at (j+1) y e')
    | (Annot e' t)       => Annot (open_at j y e')  (openT_at j y t)
    | (Switch e cs)      => Switch (open_at j y e)  (openA_at j y cs)
    end

with openA_at (j : index) (y : vname) (cs : alts) : alts :=
    match cs with
    | AEmpty          => AEmpty
    | (ACons dc e cs) => ACons dc (open_at (j + (arity dc)) y e) (openA_at j y cs)
    end

with openT_at (j : index) (y : vname) (t0 : type) : type :=
    match t0 with
    | (TRefn b ps)    => TRefn b                    (openP_at (j+1) y ps)
    | (TData tc t ps) => TData tc (openT_at j y t)  (openP_at (j+1) y ps)
    | (TFunc   t_z t) => TFunc   (openT_at j y t_z) (openT_at (j+1) y t)
    | (TExists t_z t) => TExists (openT_at j y t_z) (openT_at (j+1) y t)
    | (TPoly   k   t) => TPoly k (openT_at j y t) 
    end

with openP_at (j : index) (y : vname) (ps0 : preds) : preds  :=
    match ps0 with
    | PEmpty       => PEmpty
    | (PCons p ps) => PCons (open_at j y p) (openP_at j y ps)
    end.

Definition unbind  (y : vname) (e : expr)   : expr  :=  open_at 0 y e. 
Definition unbindA (y : vname) (cs : alts)  : alts  :=  openA_at 0 y cs.
Definition unbindT (y : vname) (t : type)   : type  :=  openT_at 0 y t.
Definition unbindP (y : vname) (ps : preds) : preds :=  openP_at 0 y ps.


Fixpoint open_tv_at (j : index) (a' : vname) (e0 : expr) : expr :=
    match e0 with
    | (Bc b)                       => Bc b
    | (Ic n)                       => Ic n
    | (Prim p)                     => Prim p
    | (Dc dc)                      => Dc dc
    | (BV i)                       => BV i    (* looking for type vars *)
    | (FV y)                       => FV y
    | (Lambda e)                   => Lambda    (open_tv_at j a' e)  
    | (App e e')                   => App       (open_tv_at j a' e)  (open_tv_at j a' e')
    | (LambdaT k e)                => LambdaT k (open_tv_at (j+1) a' e)
    | (AppT e t)                   => AppT      (open_tv_at j a' e)  (open_tvT_at j a' t)
    | (Let e1 e2  )                => Let       (open_tv_at j a' e1) (open_tv_at  j a' e2) 
    | (Annot e t)                  => Annot     (open_tv_at j a' e)  (open_tvT_at j a' t)
    | (Switch e cs)                => Switch    (open_tv_at j a' e)  (open_tvA_at j a' cs)
    end

with open_tvA_at (j : index) (a' : vname) (cs : alts) : alts  :=
    match cs with
    | AEmpty          => AEmpty
    | (ACons dc e cs) => ACons dc (open_tv_at (j + 1) a' e) (open_tvA_at j a' cs)    
    end

with open_tvT_at (j : index) (a' : vname) (t0 : type) : type  :=
    match t0 with
    | (TRefn b  ps)     => 
          match b with 
          | (BTV i)  => if j =? i then TRefn (FTV a') (open_tvP_at j a' ps) 
                                  else TRefn b        (open_tvP_at j a' ps)
          | _        =>                TRefn b        (open_tvP_at j a' ps) 
          end
    | (TData tc t ps)   => TData tc (open_tvT_at j a' t)   (open_tvP_at j a' ps)
    | (TFunc   t_z t)   => TFunc    (open_tvT_at j a' t_z) (open_tvT_at j a' t)
    | (TExists t_z t)   => TExists  (open_tvT_at j a' t_z) (open_tvT_at j a' t)
    | (TPoly   k  t)    => TPoly k  (open_tvT_at (j+1) a' t)
    end

with open_tvP_at (j : index) (a' : vname) (ps0 : preds) : preds  :=
    match ps0 with
    | PEmpty       => PEmpty
    | (PCons p ps) => PCons (open_tv_at j a' p) (open_tvP_at j a' ps)
    end.

Definition unbind_tv  (a' : vname) (e : expr) : expr  :=  open_tv_at 0 a' e.
Definition unbind_tvA (a' : vname) (cs: alts) : alts  :=  open_tvA_at 0 a' cs.
Definition unbind_tvT (a' : vname) (t : type) : type  :=  open_tvT_at 0 a' t.
Definition unbind_tvP (a' : vname) (ps : preds) : preds := open_tvP_at 0 a' ps.


(* deBruijn index shifting : only used to define push, not in the actual proof *)
Fixpoint shift_at (j k : index) (e : expr) : expr := 
    match e with
    | (Bc b)             => Bc b
    | (Ic n)             => Ic n
    | (Prim c)           => Prim c
    | (Dc dc)            => Dc dc
    | (BV i)             => if i <=? j then BV (i+1) else BV i 
    | (FV x)             => FV x
    | (Lambda e')        => Lambda (shift_at (j+1) k e')
    | (App e1 e2)        => App   (shift_at j k e1)  (shift_at j k e2)
    | (LambdaT k0 e')    => LambdaT k0 (shift_at j (k+1) e')  
    | (AppT e' t)        => AppT  (shift_at j k e')  (shiftT_at j k t)
    | (Let ex e')        => Let   (shift_at j k ex)  (shift_at (j+1) k e')
    | (Annot e' t)       => Annot (shift_at j k e')  (shiftT_at j k t)
    | (Switch e cs)      => Switch (shift_at j k e)  (shiftA_at j k cs)
    end

with shiftA_at (j k : index) (cs : alts) : alts :=
    match cs with    
    | AEmpty        => AEmpty
    | ACons dc e cs => ACons dc (shift_at (j+arity dc) k e) (shiftA_at j k cs)
    end

with shiftT_at (j k : index) (t0 : type) : type :=
    match t0 with
    | (TRefn b ps)    => TRefn b (shiftP_at (j+1) k ps)
    | (TData tc t ps) => TData tc (shiftT_at j k t)  (shiftP_at (j+1) k ps)  
    | (TFunc   t_z t) => TFunc   (shiftT_at j k t_z) (shiftT_at (j+1) k t)
    | (TExists t_z t) => TExists (shiftT_at j k t_z) (shiftT_at (j+1) k t)
    | (TPoly   k0  t) => TPoly k0 (shiftT_at j (k+1) t) 
    end

with shiftP_at (j k : index) (ps0 : preds) : preds  :=
    match ps0 with
    | PEmpty       => PEmpty
    | (PCons p ps) => PCons (shift_at j k p) (shiftP_at j k ps)
    end.

Definition shiftP (ps : preds) : preds := shiftP_at 0 0 ps.

  (*- TERM-LEVEL SUBSTITUTION -*)
Fixpoint subFV (x : vname) (v_x : expr) (e0 : expr) : expr :=
    match e0 with
    | (Bc b)                    => Bc b
    | (Ic n)                    => Ic n
    | (Prim p)                  => Prim p
    | (Dc dc)                   => Dc dc
    | (BV i)                    => BV i
    | (FV y)                    => if x =? y then v_x else FV y
    | (Lambda   e)              => Lambda    (subFV x v_x e)
    | (App e e')                => App   (subFV x v_x e)  (subFV x v_x e')
    | (LambdaT   k e)           => LambdaT   k (subFV x v_x e)
    | (AppT e bt)               => AppT  (subFV x v_x e) (tsubFV x v_x bt)
    | (Let   e1 e2)             => Let   (subFV x v_x e1) (subFV x v_x e2)
    | (Annot e t)               => Annot (subFV x v_x e) (tsubFV x v_x t) 
    | (Switch e cs)             => Switch (subFV x v_x e) (asubFV x v_x cs) 
    end

with asubFV (x : vname) (v_x : expr) (cs : alts) : alts :=
    match cs with
    | AEmpty          => AEmpty
    | (ACons dc e cs) => ACons dc (subFV x v_x e) (asubFV x v_x cs)
    end

with tsubFV (x : vname) (v_x : expr) (t0 : type) : type :=
    match t0 with
    | (TRefn  b r)     => TRefn b   (psubFV x v_x r)
    | (TData tc t ps)  => TData tc (tsubFV x v_x t)   (psubFV x v_x ps)
    | (TFunc  t_z t)   => TFunc    (tsubFV x v_x t_z) (tsubFV x v_x t)
    | (TExists  t_z t) => TExists  (tsubFV x v_x t_z) (tsubFV x v_x t)
    | (TPoly  k   t)   => TPoly    k                  (tsubFV x v_x t)
    end

with psubFV (x : vname) (v_x : expr) (ps0 : preds) : preds :=
    match ps0 with
    | PEmpty       => PEmpty
    | (PCons p ps) => PCons (subFV x v_x p) (psubFV x v_x ps)
    end.

Fixpoint strengthen (qs : preds) (rs : preds) : preds :=
    match qs with
    | PEmpty       => rs 
    | (PCons p ps) => PCons p (strengthen ps rs)
    end.

(* When substituting in for a type variable, say a{x:p}[t_a/a], where t_a is not a refined
--     basic type, then we need to express "t_a {x:p}" by pushing the refinement down into t_a.
--     For example a{x:p}[ ( \exists y:Int{y:q}. a'{z:r} )/a] becomes roughly speaking
--             \exists Int{y:q}. a'{z:r `And` p} *)
Fixpoint push (p : preds) (t0 : type) : type := 
    match t0 with
    | (TRefn   b     r)  => TRefn   b     (strengthen p r)
    | (TData   tc t  r)  => TData   tc t  (strengthen p r)
    | (TFunc     t_y t)  => TFunc     t_y t
    | (TExists   t_y t)  => TExists   t_y (push (shiftP p) t)
        (* wanted: match texists_not_usertype t_y t pf with end *)
    | (TPoly     k   t)  => TPoly     k   t
    end.    

Fixpoint subFTV (a : vname) (t_a : type) (e0 : expr) : expr :=
    match e0 with
    | (Bc b)                    => Bc b
    | (Ic n)                    => Ic n
    | (Prim p)                  => Prim p
    | (Dc dc)                   => Dc dc
    | (BV i)                    => BV i
    | (FV y)                    => FV y
    | (Lambda   e)              => Lambda     (subFTV a t_a e)
    | (App e e')                => App   (subFTV a t_a e)  (subFTV a t_a e')
    | (LambdaT    k e)          => LambdaT    k (subFTV a t_a e)
    | (AppT e t)                => AppT  (subFTV a t_a e) (tsubFTV a t_a t)
    | (Let   e1 e2)             => Let   (subFTV a t_a e1) (subFTV a t_a e2)
    | (Annot e t)               => Annot (subFTV a t_a e) (tsubFTV a t_a t) 
    | (Switch e cs)             => Switch (subFTV a t_a e) (asubFTV a t_a cs) 
    end

with asubFTV (a : vname) (t_a : type) (cs : alts) : alts  :=
    match cs with
    | AEmpty          => AEmpty
    | (ACons dc e cs) => ACons dc (subFTV a t_a e) (asubFTV a t_a cs)
    end

with tsubFTV (a : vname) (t_a : type) (t0 : type) : type  :=
    match t0 with
    | (TRefn b   r)        => match b with         
          | (FTV a')   => if a =? a' then push      (psubFTV a t_a r) t_a
                                     else TRefn b   (psubFTV a t_a r)
          | _          =>                 TRefn b   (psubFTV a t_a r)
          end
    | (TData tc t r)       => TData tc (tsubFTV a t_a t)     (psubFTV a t_a r)       
    | (TFunc     t_z t)    => TFunc      (tsubFTV a t_a t_z) (tsubFTV a t_a t)
    | (TExists   t_z t)    => TExists    (tsubFTV a t_a t_z) (tsubFTV a t_a t)
    | (TPoly      k  t)    => TPoly      k                   (tsubFTV a t_a t)
    end

with psubFTV (a : vname) (t_a : type) (ps0 : preds) : preds  :=
    match ps0 with
    | PEmpty       => PEmpty
    | (PCons p ps) => PCons (subFTV a t_a p) (psubFTV a t_a ps)
    end.

Fixpoint subBV_at (j : index) (v : expr) (e0 : expr) : expr :=
    match e0 with
    | (Bc b)             => Bc b
    | (Ic n)             => Ic n
    | (Prim c)           => Prim c
    | (Dc dc)            => Dc dc
    | (BV i)             => if j =? i then v else BV i
    | (FV x)             => FV x
    | (Lambda e)         => Lambda (subBV_at (j+1) v e)
    | (App e e')         => App   (subBV_at j v e)  (subBV_at j v e')
    | (LambdaT k e)      => LambdaT k (subBV_at j v e) 
    | (AppT e t)         => AppT  (subBV_at j v e)  (tsubBV_at j v t)
    | (Let ex e)         => Let   (subBV_at j v ex) (subBV_at (j+1) v e)
    | (Annot e t)        => Annot (subBV_at j v e)  (tsubBV_at j v t)
    | (Switch e cs)      => Switch (subBV_at j v e)  (asubBV_at j v cs)
    end

with asubBV_at (j : index) (v_x : expr) (cs : alts) : alts :=
    match cs with
    | AEmpty          => AEmpty
    | (ACons dc e cs) => ACons dc (subBV_at (j+(arity dc)) v_x e) (asubBV_at j v_x cs)
    end

with tsubBV_at (j : index) (v_x : expr) (t0 : type) : type :=
    match t0 with
    | (TRefn b ps)    => TRefn b (psubBV_at (j+1) v_x ps)  
    | (TData tc t ps) => TData tc (tsubBV_at j v_x t)  (psubBV_at (j+1) v_x ps)  
    | (TFunc   t_z t) => TFunc   (tsubBV_at j v_x t_z) (tsubBV_at (j+1) v_x t)
    | (TExists t_z t) => TExists (tsubBV_at j v_x t_z) (tsubBV_at (j+1) v_x t)
    | (TPoly   k  t)  => TPoly k (tsubBV_at j v_x t)  
    end

with psubBV_at (j : index) (v_x : expr) (ps0 : preds) : preds  := 
    match ps0 with
    | PEmpty       => PEmpty
    | (PCons p ps) => PCons (subBV_at j v_x p) (psubBV_at j v_x ps)
    end.

Definition subBV  (v : expr) (e : expr)   : expr  :=  subBV_at 0 v e.
Definition asubBV (v_x : expr) (cs: alts) : alts  :=  asubBV_at 0 v_x cs.
Definition tsubBV (v_x : expr) (t : type) : type  :=  tsubBV_at 0 v_x t.
Definition psubBV (v : expr) (ps : preds) : preds :=  psubBV_at 0 v ps.

Fixpoint subBTV_at (j : index) (t_a : type) (e0 : expr) : expr :=
    match e0 with
    | (Bc b)                       => Bc b
    | (Ic n)                       => Ic n
    | (Prim p)                     => Prim p
    | (Dc dc)                      => Dc dc
    | (BV i)                       => BV i 
    | (FV y)                       => FV y
    | (Lambda   e)                 => Lambda    (subBTV_at j t_a e)  
    | (App e e')                   => App       (subBTV_at j t_a e)  (subBTV_at j t_a e')
    | (LambdaT  k e)               => LambdaT k (subBTV_at (j+1) t_a e)
    | (AppT e t)                   => AppT      (subBTV_at j t_a e) (tsubBTV_at j t_a t)
    | (Let   e1 e2)                => Let       (subBTV_at j t_a e1) (subBTV_at j t_a e2) 
    | (Annot e t)                  => Annot     (subBTV_at j t_a e) (tsubBTV_at j t_a t)
    | (Switch e cs)                => Switch    (subBTV_at j t_a e) (asubBTV_at j t_a cs)
    end

with asubBTV_at (j : index) (t_a : type) (cs : alts) : alts :=
    match cs with
    | AEmpty          => AEmpty
    | (ACons dc e cs) => ACons dc (subBTV_at (j+1) t_a e) (asubBTV_at j t_a cs)
    end

with tsubBTV_at (j : index) (t_a : type) (t0 : type) : type :=
    match t0 with
    | (TRefn b   ps)     => 
          match b with
          | (BTV i) => if j =? i then push (psubBTV_at j t_a ps) t_a 
                                 else TRefn b (psubBTV_at j t_a ps) (* TExists y t_y (push x r[t_a/a] t')  *)
          | _       =>                TRefn b (psubBTV_at j t_a ps)    
          end
    | (TData tc t ps)    => TData tc (tsubBTV_at j t_a t)   (psubBTV_at j t_a ps)
    | (TFunc   t_z t)    => TFunc    (tsubBTV_at j t_a t_z) (tsubBTV_at j t_a t)  
    | (TExists t_z t)    => TExists  (tsubBTV_at j t_a t_z) (tsubBTV_at j t_a t)  
    | (TPoly   k  t)     => TPoly k  (tsubBTV_at (j+1) t_a t)
    end

with psubBTV_at (j : index) (t_a : type) (ps0 : preds) : preds :=
    match ps0 with
    | PEmpty       => PEmpty
    | (PCons p ps) => PCons (subBTV_at j t_a p) (psubBTV_at j t_a ps)
    end.

Definition subBTV  (t : type)   (e : expr)   : expr  :=  subBTV_at 0 t e.
Definition asubBTV (t_a : type) (cs : alts)  : alts  :=  asubBTV_at 0 t_a cs.
Definition tsubBTV (t_a : type) (t : type)   : type  :=  tsubBTV_at 0 t_a t.
Definition psubBTV (t_a : type) (ps : preds) : preds :=  psubBTV_at 0 t_a ps.


(* BARE TYPES: i.e. System F types. These still contain type polymorphism and type variables, 
     but all the refinements, dependent arrow binders, and existentials have been erased. *)

Inductive ftype : Set :=
    | FTBasic (b : basic)                (* b: Bool, Int, FTV a, BTV a *)
    | FTData  (tc : tcons) (t : ftype)
    | FTFunc  (t1 : ftype) (t2 : ftype)  (* bt -> bt' *)
    | FTPoly  (k : kind) (t : ftype).    (* \forall a:k. bt *)

    Definition isBaseF (t : ftype) : Prop  :=
        match t with
        | (FTBasic b)     => True
        | _               => False
        end.

    Definition isClosedBaseF (t : ftype) : Prop  :=
        match t with
        | (FTBasic TBool) => True
        | (FTBasic TInt)  => True
        | _               => False
        end.
    
    Definition isFTData (t : ftype) : Prop :=
        match t with
        | (FTData _ _) => True
        | _            => False
        end.

(* are both of these needed? *)
Fixpoint arrowsF (t:ftype) : nat := 
    match t with 
    | (FTFunc t_x t)  => 1 + (arrowsF t)
    | _               => 0
    end.

Fixpoint erase (t0 : type) : ftype :=
    match t0 with
    | (TRefn b r)     => FTBasic b
    | (TData tc t r)  => FTData tc (erase t)
    | (TFunc t_x t)   => FTFunc (erase t_x) (erase t)
    | (TExists t_x t) => (erase t)
    | (TPoly  k  t)   => FTPoly k (erase t)
    end.

Fixpoint isLCFT_at (j : index) (t0 : ftype) : Prop :=
    match t0 with
    | (FTBasic b)      => match b with
                          | (BTV i)   => i < j
                          | _         => True
                          end
    | (FTData tc t)    => isLCFT_at j t
    | (FTFunc t_x t)   => isLCFT_at j t_x /\ isLCFT_at j t
    | (FTPoly   k t)   => isLCFT_at (j+1) t
    end.

Definition isLCFT (t : ftype) : Prop  :=  isLCFT_at 0 t.

Fixpoint openFT_at (j : index) (a' : vname) (t0 : ftype) : ftype :=
    match t0 with
    | (FTBasic b)    => match b with   (* TODO put arg on left *)
                        | (BTV i) => if j =? i then FTBasic (FTV a') else FTBasic b
                        | _       => FTBasic b
                        end
    | (FTData tc  t) => FTData tc (openFT_at j a' t)
    | (FTFunc t_x t) => FTFunc (openFT_at j a' t_x) (openFT_at j a' t)
    | (FTPoly k   t) => FTPoly k (openFT_at (j+1) a' t)
    end.

Definition unbindFT (a' : vname) (t : ftype) : ftype := openFT_at 0 a' t.

Fixpoint ftsubFV (a : vname) (t_a : ftype) (t0 : ftype) : ftype :=
    match t0 with
    | (FTBasic b)     => match b with
                         | (FTV a')  => if a =? a' then t_a else FTBasic b
                         | _         => FTBasic b
                         end
    | (FTData tc  t)  => FTData tc (ftsubFV a t_a t)
    | (FTFunc t_z t)  => FTFunc (ftsubFV a t_a t_z) (ftsubFV a t_a t)
    | (FTPoly   k t)  => FTPoly k (ftsubFV a t_a t)
    end.

Fixpoint ftsubBV_at (j : index) (t_a : ftype) (t0 : ftype) : ftype :=
    match t0 with
    | (FTBasic   b)   =>  match b with
                          | (BTV i) => if j =? i then t_a else FTBasic b
                          | _       => FTBasic b
                          end
    | (FTData tc  t)  => FTData tc (ftsubBV_at j t_a t)
    | (FTFunc t_z t)  => FTFunc (ftsubBV_at j t_a t_z) (ftsubBV_at j t_a t)
    | (FTPoly  k  t)  => FTPoly k (ftsubBV_at (j+1) t_a t)
    end.
 
Definition ftsubBV (t_a : ftype) (t : ftype) : ftype  :=  ftsubBV_at 0 t_a t.