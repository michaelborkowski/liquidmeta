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

Inductive expr : Set :=  
    | Bc (b : bool)                 (* True, False *)
    | Ic (n : nat)                  (* 0, 1, 2, *)
    | Prim (p : prim)               (* built-in primitive functions *)
    | BV (i : index)                (* BOUND Variables: bound to a Lambda, Let or :t *)
    | FV (x : vname)                (* FREE Variables: bound in an environment *)
    | Lambda (e : expr)             (* \x.e          abstractions    (x is nameless) *)
    | App (e1 : expr) (e2 : expr)   (* e e'          applications *)
    | LambdaT (k : kind) (e : expr) (* /\a:k.e  type abstractions    (a is nameless) *)
    | AppT (e : expr) (t : ftype)   (* e [bt]   type applications *)
    | Let (e1 : expr) (e2 : expr)   (* let x = e1 in e2              (x is nameless) *)
    | Annot (e : expr) (t : ftype). (* e : t *)

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
    | (AppT e' t)    => isLC_at j_x j_a e'    /\ isLCFT_at j_a t 
    | (Let ex e')    => isLC_at j_x j_a ex    /\ isLC_at (j_x+1) j_a e'  
    | (Annot e' t)   => isLC_at j_x j_a e'    /\ isLCFT_at j_a t 
    end.

Definition isLC  (e  : expr)  : Prop := isLC_at  0 0 e.

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
    | (AppT e' t)        => AppT  (open_at j y e')  t
    | (Let ex e')        => Let   (open_at j y ex)  (open_at (j+1) y e')
    | (Annot e' t)       => Annot (open_at j y e')  t
    end.

Definition unbind  (y : vname) (e : expr)   : expr  :=  open_at 0 y e. 

Fixpoint openFT_at (j : index) (a' : vname) (t0 : ftype) : ftype :=
    match t0 with
    | (FTBasic b)    => match b with   
                        | (BTV i) => if j =? i then FTBasic (FTV a') else FTBasic b
                        | _       => FTBasic b
                        end
    | (FTFunc t_x t) => FTFunc (openFT_at j a' t_x) (openFT_at j a' t)
    | (FTPoly k   t) => FTPoly k (openFT_at (j+1) a' t)
    end.

Definition unbindFT (a' : vname) (t : ftype) : ftype := openFT_at 0 a' t.

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
    | (AppT e t)                   => AppT      (open_tv_at j a' e)  (openFT_at j a' t)
    | (Let e1 e2  )                => Let       (open_tv_at j a' e1) (open_tv_at  j a' e2) 
    | (Annot e t)                  => Annot     (open_tv_at j a' e)  (openFT_at j a' t)
    end.

Definition unbind_tv  (a' : vname) (e : expr) : expr  :=  open_tv_at 0 a' e.

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
    | (AppT e bt)               => AppT  (subFV x v_x e) bt
    | (Let   e1 e2)             => Let   (subFV x v_x e1) (subFV x v_x e2)
    | (Annot e t)               => Annot (subFV x v_x e) t
    end.

Fixpoint ftsubFV (a : vname) (t_a : ftype) (t0 : ftype) : ftype :=
    match t0 with
    | (FTBasic b)     => match b with
                         | (FTV a')  => if a =? a' then t_a else FTBasic b
                         | _         => FTBasic b
                         end
    | (FTFunc t_z t)  => FTFunc (ftsubFV a t_a t_z) (ftsubFV a t_a t)
    | (FTPoly   k t)  => FTPoly k (ftsubFV a t_a t)
    end.

Fixpoint subFTV (a : vname) (t_a : ftype) (e0 : expr) : expr :=
    match e0 with
    | (Bc b)                    => Bc b
    | (Ic n)                    => Ic n
    | (Prim p)                  => Prim p
    | (BV i)                    => BV i
    | (FV y)                    => FV y
    | (Lambda   e)              => Lambda     (subFTV a t_a e)
    | (App e e')                => App   (subFTV a t_a e)  (subFTV a t_a e')
    | (LambdaT    k e)          => LambdaT    k (subFTV a t_a e)
    | (AppT e t)                => AppT  (subFTV a t_a e) (ftsubFV a t_a t)
    | (Let   e1 e2)             => Let   (subFTV a t_a e1) (subFTV a t_a e2)
    | (Annot e t)               => Annot (subFTV a t_a e) (ftsubFV a t_a t) 
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
    | (AppT e t)         => AppT  (subBV_at j v e)  t
    | (Let ex e)         => Let   (subBV_at j v ex) (subBV_at (j+1) v e)
    | (Annot e t)        => Annot (subBV_at j v e)  t
    end.

Definition subBV  (v : expr) (e : expr)   : expr  :=  subBV_at 0 v e.

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

Fixpoint subBTV_at (j : index) (t_a : ftype) (e0 : expr) : expr :=
    match e0 with
    | (Bc b)                       => Bc b
    | (Ic n)                       => Ic n
    | (Prim p)                     => Prim p
    | (BV i)                       => BV i 
    | (FV y)                       => FV y
    | (Lambda   e)                 => Lambda    (subBTV_at j t_a e)  
    | (App e e')                   => App       (subBTV_at j t_a e)  (subBTV_at j t_a e')
    | (LambdaT  k e)               => LambdaT k (subBTV_at (j+1) t_a e)
    | (AppT e t)                   => AppT      (subBTV_at j t_a e) (ftsubBV_at j t_a t)
    | (Let   e1 e2)                => Let       (subBTV_at j t_a e1) (subBTV_at j t_a e2) 
    | (Annot e t)                  => Annot     (subBTV_at j t_a e) (ftsubBV_at j t_a t)
    end.

Definition subBTV  (t : ftype)   (e : expr)   : expr  :=  subBTV_at 0 t e.