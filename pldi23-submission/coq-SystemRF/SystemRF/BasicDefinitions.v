Require Import Nat.

Definition index := nat.
Definition vname := nat. (* can change this atoms later *)

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
    | BV (i : index)                (* BOUND Variables: bound to a Lambda, Let or :t *)
    | FV (x : vname)                (* FREE Variables: bound in an environment *)
    | Lambda (e : expr)             (* \x.e          abstractions    (x is nameless) *)
    | App (e1 : expr) (e2 : expr)   (* e e'          applications *)
    | LambdaT (k : kind) (e : expr) (* /\a:k.e  type abstractions    (a is nameless) *)
    | AppT (e : expr) (t : type)    (* e [bt]   type applications *)
    | Let (e1 : expr) (e2 : expr)   (* let x = e1 in e2              (x is nameless) *)
    | Annot (e : expr) (t : type)   (* e : t *)

with type : Set :=
    | TRefn   (b : basic) (ps : preds)   (* b{x0 : [p]} *)
    | TFunc   (tx : type) (t : type)     (* x:t_x -> t *)
    | TExists (tx : type) (t : type)     (* \exists x:t_x. t *)
    | TPoly   (k : kind)  (t : type)     (* \forall a:k. t *)

with preds : Set :=               (* i.e. [expr] *)
    | PEmpty
    | PCons (p : expr) (ps : preds).

Scheme expr_mutind  := Induction for expr  Sort Set
with   type_mutind  := Induction for type  Sort Set
with   preds_mutind := Induction for preds Sort Set.
Combined Scheme syntax_mutind from expr_mutind, type_mutind, preds_mutind.

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

Definition isValue (e: expr) : Prop :=
    match e with
    | Bc _          => True
    | Ic _          => True
    | Prim c        => True
    | FV _          => True
    | BV _          => True
    | Lambda   _    => True
    | LambdaT   k e => True
    | _             => False         
    end.

Definition value := { v:expr | isValue v }.
Definition toExpr (v0 : value) : expr :=
    match v0 with 
    | exist _ e _ => e
    end.

Fixpoint noExists (t0 : type) : Prop := 
    match t0 with         
    | (TRefn b ps)     => True  
    | (TFunc  t_x t)   => noExists t_x /\ noExists t
    | (TExists  t_x t) => False
    | (TPoly  k   t)   => noExists t
    end.
(* This would also avoid issues of deBruijn index shifting 
--   in type variable substitution (in defining push) *)
Definition usertype := { t:type | noExists t }.
Definition toType (ut : usertype) : type :=
    match ut with
    | exist _ t _ => t
    end.

Lemma texists_not_usertype : forall (t_x t : type),
    noExists (TExists t_x t) -> False.
Proof. simpl. contradiction. Qed.

Fixpoint isLC_at (j_x : index) (j_a : index) (e : expr) : Prop  :=
    match e with
    | (Bc _)         => True
    | (Ic _)         => True
    | (Prim _)       => True
    | (BV i)         => i < j_x
    | (FV _)         => True
    | (Lambda e')    => isLC_at (j_x + 1) j_a e'
    | (App e1 e2)    => isLC_at j_x j_a e1    /\ isLC_at j_x j_a e2 
    | (LambdaT k e') => isLC_at j_x (j_a + 1) e'
    | (AppT e' t)    => isLC_at j_x j_a e'    /\ isLCT_at j_x j_a t 
    | (Let ex e')    => isLC_at j_x j_a ex    /\ isLC_at (j_x+1) j_a e'  
    | (Annot e' t)   => isLC_at j_x j_a e'    /\ isLCT_at j_x j_a t 
    end

with isLCT_at (j_x : index) (j_a : index) (t0 : type) : Prop := 
    match t0 with
    | (TRefn   b  rs) =>  match b with
                          | (BTV i) => i < j_a /\ isLCP_at (j_x+1) j_a rs
                          | _       =>            isLCP_at (j_x+1) j_a rs
                          end
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
Definition isLCT (t  : type)  : Prop := isLCT_at 0 0 t.
Definition isLCP (ps : preds) : Prop := isLCP_at 0 0 ps.

Fixpoint open_at (j : index) (y : vname) (e : expr) : expr := 
    match e with
    | (Bc b)             => Bc b
    | (Ic n)             => Ic n
    | (Prim c)           => Prim c
    | (BV i)             => if j =? i then FV y else BV i 
    | (FV x)             => FV x
    | (Lambda e')        => Lambda (open_at (j+1) y e')
    | (App e1 e2)        => App   (open_at j y e1)  (open_at j y e2)
    | (LambdaT k e')     => LambdaT k (open_at j y e')  
    | (AppT e' t)        => AppT  (open_at j y e')  (openT_at j y t)
    | (Let ex e')        => Let   (open_at j y ex) (open_at (j+1) y e')
    | (Annot e' t)       => Annot (open_at j y e')  (openT_at j y t)
    end

with openT_at (j : index) (y : vname) (t0 : type) : type :=
    match t0 with
    | (TRefn b ps)    => TRefn b (openP_at (j+1) y ps)
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
Definition unbindT (y : vname) (t : type)   : type  :=  openT_at 0 y t.
Definition unbindP (y : vname) (ps : preds) : preds :=  openP_at 0 y ps.


Fixpoint open_tv_at (j : index) (a' : vname) (e0 : expr) : expr :=
    match e0 with
    | (Bc b)                       => Bc b
    | (Ic n)                       => Ic n
    | (Prim p)                     => Prim p
    | (BV i)                       => BV i    (* looking for type vars *)
    | (FV y)                       => FV y
    | (Lambda e)                   => Lambda    (open_tv_at j a' e)  
    | (App e e')                   => App       (open_tv_at j a' e)  (open_tv_at j a' e')
    | (LambdaT k e)                => LambdaT k (open_tv_at (j+1) a' e)
    | (AppT e t)                   => AppT      (open_tv_at j a' e)  (open_tvT_at j a' t)
    | (Let e1 e2  )                => Let       (open_tv_at j a' e1) (open_tv_at  j a' e2) 
    | (Annot e t)                  => Annot     (open_tv_at j a' e)  (open_tvT_at j a' t)
    end

with open_tvT_at (j : index) (a' : vname) (t0 : type) : type  :=
    match t0 with
    | (TRefn b  ps)     => match b with 
          | (BTV i)  => if j =? i then TRefn (FTV a') (open_tvP_at j a' ps) 
                                  else TRefn b        (open_tvP_at j a' ps)
          | _        =>                TRefn b        (open_tvP_at j a' ps) 
          end
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
Definition unbind_tvT (a' : vname) (t : type) : type  :=  open_tvT_at 0 a' t.
Definition unbind_tvP (a' : vname) (ps : preds) : preds := open_tvP_at 0 a' ps.


(* deBruijn index shifting : only used to define push, not in the actual proof *)
Fixpoint shift_at (j k : index) (e : expr) : expr := 
    match e with
    | (Bc b)             => Bc b
    | (Ic n)             => Ic n
    | (Prim c)           => Prim c
    | (BV i)             => if i <=? j then BV (i+1) else BV i 
    | (FV x)             => FV x
    | (Lambda e')        => Lambda (shift_at (j+1) k e')
    | (App e1 e2)        => App   (shift_at j k e1)  (shift_at j k e2)
    | (LambdaT k0 e')    => LambdaT k0 (shift_at j (k+1) e')  
    | (AppT e' t)        => AppT  (shift_at j k e')  (shiftT_at j k t)
    | (Let ex e')        => Let   (shift_at j k ex)  (shift_at (j+1) k e')
    | (Annot e' t)       => Annot (shift_at j k e')  (shiftT_at j k t)
    end

with shiftT_at (j k : index) (t0 : type) : type :=
    match t0 with
    | (TRefn b ps)    => TRefn b (shiftP_at (j+1) k ps)
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
    | (BV i)                    => BV i
    | (FV y)                    => if x =? y then v_x else FV y
    | (Lambda   e)              => Lambda    (subFV x v_x e)
    | (App e e')                => App   (subFV x v_x e)  (subFV x v_x e')
    | (LambdaT   k e)           => LambdaT   k (subFV x v_x e)
    | (AppT e bt)               => AppT  (subFV x v_x e) (tsubFV x v_x bt)
    | (Let   e1 e2)             => Let   (subFV x v_x e1) (subFV x v_x e2)
    | (Annot e t)               => Annot (subFV x v_x e) (tsubFV x v_x t) 
    end

with tsubFV (x : vname) (v_x : expr) (t0 : type) : type :=
    match t0 with
    | (TRefn  b r)     => TRefn b   (psubFV x v_x r)
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
    | (BV i)                    => BV i
    | (FV y)                    => FV y
    | (Lambda   e)              => Lambda     (subFTV a t_a e)
    | (App e e')                => App   (subFTV a t_a e)  (subFTV a t_a e')
    | (LambdaT    k e)          => LambdaT    k (subFTV a t_a e)
    | (AppT e t)                => AppT  (subFTV a t_a e) (tsubFTV a t_a t)
    | (Let   e1 e2)             => Let   (subFTV a t_a e1) (subFTV a t_a e2)
    | (Annot e t)               => Annot (subFTV a t_a e) (tsubFTV a t_a t) 
    end

with tsubFTV (a : vname) (t_a : type) (t0 : type) : type  :=
    match t0 with
    | (TRefn b   r)        => match b with
          | (FTV a')   => if a =? a' then push      (psubFTV a t_a r) t_a
                                     else TRefn b   (psubFTV a t_a r)
          | _          =>                 TRefn b   (psubFTV a t_a r)
          end
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
    | (BV i)             => if j =? i then v else BV i
    | (FV x)             => FV x
    | (Lambda e)         => Lambda (subBV_at (j+1) v e)
    | (App e e')         => App   (subBV_at j v e)  (subBV_at j v e')
    | (LambdaT k e)      => LambdaT k (subBV_at j v e) 
    | (AppT e t)         => AppT  (subBV_at j v e)  (tsubBV_at j v t)
    | (Let ex e)         => Let   (subBV_at j v ex) (subBV_at (j+1) v e)
    | (Annot e t)        => Annot (subBV_at j v e)  (tsubBV_at j v t)
    end

with tsubBV_at (j : index) (v_x : expr) (t0 : type) : type :=
    match t0 with
    | (TRefn b ps)    => TRefn b (psubBV_at (j+1) v_x ps)  
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
Definition tsubBV (v_x : expr) (t : type) : type  :=  tsubBV_at 0 v_x t.
Definition psubBV (v : expr) (ps : preds) : preds :=  psubBV_at 0 v ps.

Fixpoint subBTV_at (j : index) (t_a : type) (e0 : expr) : expr :=
    match e0 with
    | (Bc b)                       => Bc b
    | (Ic n)                       => Ic n
    | (Prim p)                     => Prim p
    | (BV i)                       => BV i 
    | (FV y)                       => FV y
    | (Lambda   e)                 => Lambda    (subBTV_at j t_a e)  
    | (App e e')                   => App       (subBTV_at j t_a e)  (subBTV_at j t_a e')
    | (LambdaT  k e)               => LambdaT k (subBTV_at (j+1) t_a e)
    | (AppT e t)                   => AppT      (subBTV_at j t_a e) (tsubBTV_at j t_a t)
    | (Let   e1 e2)                => Let       (subBTV_at j t_a e1) (subBTV_at j t_a e2) 
    | (Annot e t)                  => Annot     (subBTV_at j t_a e) (tsubBTV_at j t_a t)
    end

with tsubBTV_at (j : index) (t_a : type) (t0 : type) : type :=
    match t0 with
    | (TRefn b   ps)     => match b with
          | (BTV i) => if j =? i then push (psubBTV_at j t_a ps) t_a 
                                 else TRefn b (psubBTV_at j t_a ps) (* TExists y t_y (push x r[t_a/a] t')  *)
          | _       =>                TRefn b (psubBTV_at j t_a ps)    
          end
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
Definition tsubBTV (t_a : type) (t : type)   : type  :=  tsubBTV_at 0 t_a t.
Definition psubBTV (t_a : type) (ps : preds) : preds :=  psubBTV_at 0 t_a ps.


(* BARE TYPES: i.e. System F types. These still contain type polymorphism and type variables, 
     but all the refinements, dependent arrow binders, and existentials have been erased. *)

Inductive ftype : Set :=
    | FTBasic (b : basic)                (* b: Bool, Int, FTV a, BTV a *)
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

Fixpoint erase (t0 : type) : ftype :=
    match t0 with
    | (TRefn b r)     => FTBasic b
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
    | (FTFunc t_z t)  => FTFunc (ftsubFV a t_a t_z) (ftsubFV a t_a t)
    | (FTPoly   k t)  => FTPoly k (ftsubFV a t_a t)
    end.

Fixpoint ftsubBV_at (j : index) (t_a : ftype) (t0 : ftype) : ftype :=
    match t0 with
    | (FTBasic   b)   =>  match b with
                          | (BTV i) => if j =? i then t_a else FTBasic b
                          | _       => FTBasic b
                          end
    | (FTFunc t_z t)  => FTFunc (ftsubBV_at j t_a t_z) (ftsubBV_at j t_a t)
    | (FTPoly  k  t)  => FTPoly k (ftsubBV_at (j+1) t_a t)
    end.
 
Definition ftsubBV (t_a : ftype) (t : ftype) : ftype  :=  ftsubBV_at 0 t_a t.