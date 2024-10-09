Require Import SystemRF.BasicDefinitions. 
Require Import SystemRF.Names.
Require Import SystemRF.BasicPropsEnvironments.
Require Import SystemRF.SystemFWellFormedness.
Require Import SystemRF.SystemFTyping.
Require Import Bidirectional.Decidable.
Require Import Bidirectional.SynthWFFT.
Require Import Bidirectional.SynthFType.
Require Import Bidirectional.SynthWFtype.

From Equations Require Import Equations.

Require Import Arith.
Require Import ZArith.
Require Import Lists.ListSet.

Fixpoint lookup (x : vname) (g : env) : option type :=
    match g with 
    | Empty           => None
    | ECons x' t' g'  => if (x =? x') then Some t' else lookup x g'
    | EConsT a' k' g' => lookup x g'
    end.

(*----------------------------------------------------------------------------
  --- | ABSTRACT MODEL of VERIFICATION CONDITIONS
  --------------------------------------------------------------------------*)

Inductive sort : Set :=
    | Bool
    | Int
    | BTVar (i : index)
    | FTVar (a : vname)
    | List                  (* s : sort ? *)
    | Ignore.

Definition toSort (b : basic) : sort :=
    match b with 
    | TBool     => Bool
    | TInt      => Int
    | (BTV i)   => BTVar i
    | (FTV a)   => FTVar a
    end.

Inductive VC : Set :=
    | Pred (ps : preds)
    | Conj (c : VC) (c' : VC)
    | ForAll (b:sort) (ps:preds) (c : VC) (* nameless binder *)
    | ForAllFV (x:vname) (b:sort) (ps:preds) (c:VC).
        (* if we start w/ an Empty env then this case never occurs *)

Definition trueC : VC := Pred PEmpty.

Definition mkVC (t_x : type) (c : VC) : VC :=
    match t_x with
    | (TRefn b ps) => ForAll (toSort b) ps c
    | (TList t ps) => ForAll List       ps c
    | _            => ForAll Ignore PEmpty c
    end.

Definition mkVCFV (x : vname) (t_x : type) (c : VC) : VC :=
    match t_x with
    | (TRefn b ps) => ForAllFV x (toSort b) ps c
    | (TList t ps) => ForAllFV x List       ps c
    | _            => ForAllFV x Ignore PEmpty c
    end.

(*----------------------------------------------------------------------------
  --- | MODELLING VC/CONSTRAINTS AS COQ PROPS
  --------------------------------------------------------------------------*)

(* Draft solver: currently does not generate Props for polymoprhic VCs *)

Definition sortToCoqType (s : sort) : Type :=
    match s with
    | Bool      => Some bool
    | Int       => Some Z
    | BTVar i   => None (* TODO *)
    | FTVar a   => None (* TODO *)
    | List      => Some (list unit)
    | Ignore    => Some unit 
    end.

(*Fixpoint primToSetFn (p : prim) : 

Fixpoint exprToSet   (ss : sorts) ()*)

Fixpoint exprToProp (e : expr) : Prop := True. (* TODO *)

Fixpoint predsToProp (ss : sorts) (ps : preds) : Prop :=
    match ps with
    | PEmpty      => True
    | PCons p ps' => exprToProp p /\ predsToProp ps'
    end.

Fixpoint SMTtoProp' (*ss : sorts*) (c : VC) : Prop :=
    match c with
    | Pred ps             => predsToProp ps
    | Conj c c'           => SMTtoProp c /\ SMTtoProp c'
    | ForAll     b ps c   =>
        match sortToCoqType s with 
        | Some T => False (* TODO *)
        | None   => False
        end
    | ForAllFV x b ps c   => 
        match sortToCoqType s with 
        | Some T => forall (x:T), predsToProp ps -> SMTtoProp c
        | None   => False
        end
    end.

Definition SMTtoProp (c : VC) : Prop := SMTtoProp' (* *) c. 

(*----------------------------------------------------------------------------
  --- | AUTOMATED INFERENCE of SYSTEM RF TYPING JUDGMENTS
  --------------------------------------------------------------------------*)

(* SUBTYPING: Note that UNLIKE the metatheory, the Check/Syn0th definition
      is NOT mutually recursive with IsSub because existential types only
      every appear on the LHS of obligations to check and therefore we never
      have to guess or check a witness in S-Witn. *)

(* option is used because we can reject some obligations out of hand *)

Fixpoint isSubtype' (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (t t':type) : option VC :=
    match t, t' with 
    | (TRefn b ps, TRefn b' qs)    
          => if basic_eq b b'
             then Some (ForAll (toSort b) ps (Pred qs))
             else None
    | (TFunc s_x s', TFunc t_x t')  
          => match isSubtype' g dv dtv t_x s_x with
             | Some c_x 
                =>  match isSubtype' g (DVBind t_x dv) dtv s' t' with
                    | Some c  => Conj c_x (mkVC t_x c)
                    | None    => None
                    end
             | None => None
             end
    | (TExists s_x s, _) 
          => match isSubtype' g (DVBind s_x dv) dtv s (shiftT t') with
             | Some c => mkVC s_x c
             | None   => None
            end
    | (TPoly k s, TPoly k' s')   
          => if kind_eq k k'  (* we don't need to keep the kind info *)
             then isSubtype' g dv (DTBind k dtv) s s' (* so return c as-is*)
             else None
    | (TList s ps, TList s' qs)   
          => match isSubtype' g dv dtv s s' with
             | Some c => Conj (c (ForAll List ps (Pred qs)))
             | None   => None
             end
    end.      


(* here is where we might plug in our various models of constraint solvers *)
Inductive SMTValid : VC -> Prop :=
    (* dummy solver *)
    | SMTVtrivial  : SMTValid (Pred PEmpty)
    | SMTVquant    : forall (b:sort) (ps:preds) (c:VC),
        SMTValid c -> SMTValid (ForAll b ps c)
    | SMTVconj     : forall (c c' : VC), 
        SMTValid c -> SMTValid c' -> SMTValid (Conj c c')
    (* prove constraints in Coq *)
    | SMTVcoq      : forall (c:VC),
        SMTtoProp c -> SMTValid c.

Inductive Entails' : env -> deBruijns -> deBruijnTVs -> VC -> Prop :=
    | EntEmp    : forall (c:VC),
        SMTValid c -> Entails' Empty DVEmpty DTEmpty c
    | EntExtFV  : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (x:vname) (tx:type) (c:VC),
        Entails' g dv dtv (mkVCFV x tx c)  -> Entails' (ECons x tx g) dv dtv c
    | EntExtBV  : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (tx:type) (c:VC),
        Entails' g dv dtv (mkVC tx c)  -> Entails' g (DVBind tx dv) dtv c
    | EntExtBTV : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (k:kind) (c:VC),
        Entails' g dc dtv c -> Entails' g dv (DTBind k dtv) c.

Definition Entails (c:VC) : Prop := Entails' Empty DVEmpty DTEmpty c.

Inductive IsSubtype': env -> deBruijns -> deBruijnTVs -> type -> type -> Prop :=
    | SubRefn : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (b:basic) (ps qs:preds),
        Entails' g dv dtv (ForAll (toSort b) ps (Pred qs)) 
            -> IsSubtype' g dv dtv (TRefn b ps) (TRefn b qs)
    | SubFunc : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (s_x s' t_x t': type),
        IsSubtype' g dv dtv t_x s_x -> IsSubtype' g (DVBind t_x dv) dtv s' t' 
            -> IsSubtype' g dv dtv (TFunc s_x s') (TFunc t_x t')
    | SubExis : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (s_x s t:type),
        IsSubtype' g (DVBind s_x dv) dtv s (shiftT t') 
            -> IsSubtype' g dv dtv (TExists s_x s) t
    | SubPoly : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (k:kind) (s t:type),
        IsSubtype' g dv (DTBind k dtv) s t
            -> IsSubtype' g dv dtv (TPoly k s) (TPoly k t)
    | SubList : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (s t:type) (ps qs:preds),
        IsSubtype' g dv dtv s t
            -> Entails' g dv dtv (ForAll List ps (Pred qs))
            -> IsSubtype' g dv dtv (TList s ps) (TList t qs).

(* TYPING *)
(* one version is computable function, the other is a mutually inductive
      prop that we prove is decidable using the first way *)

Fixpoint check' (g:env) (dv:deBruijns) (dtv:deBruijnTVs) 
                (e:expr) (t:type) : option VC := 
    match e with          
    | (Lambda e')     => 
        match t with
        | (TFunc t_x t')  => 
            match isWFtypeb' g dv dtv t_x Star with
            | true  =>
                match check' g (DVBind t_x dv) dtv e' t' with
                | Some c  => Some (mkVC t_x c)
                | None    => None
                end
            | false => None
            end
        | _               => None 
        end
    | (LambdaT k e')  =>
        match t with
        | (TPoly k' t')   => 
            match kind_eq k k' with
            | true  => check' g dv (DTBind k dtv) e' t'
            | False => None
            end
        | _               => None
        end
    | (Let e_x e')    =>
        match isWFtypeb' g dv dtv t Star with
        | true  =>
            match synth' g dv dtv e_x with
            | Some ( c1, t_x )  =>
                match check' g (DVBind t_x dv) dtv e' t' with
                | Some c2 => Some (Conj c1 (mkVC t_x c2))
                | None    => None
                end
            | None              => None
            end
        | false => None
        end
    | (If e0 e1 e2)   => 
        match isWFtypeb' g dv dtv t Star with
        | true  => 
            match check' g dv dtv e0 (TRefn TBool PEmpty) with
            | Some c0 =>
                match check' g (DVBind (self (TRefn TBool PEmpty) (Bc true) Base) dv) 
                             dtv e1 (shiftT t) with
                | Some c1 =>
                    match check' g (DVBind (self (TRefn TBool PEmpty) (Bc false) Base) dv) 
                          dtv e2 (shiftT t) with
                    | Some c2 => Some (Conj c0 
                                        (Conj (mkVC (self (TRefn TBool PEmpty) (Bc true) Base) c1) 
                                           (mkVC (self (TRefn TBool PEmpty) (Bc false) Base) c2)))
                    | None    => None
                    end
                | None    => None
                end
            | None    => None
            end
        | false => None
        end
    | Nil             =>
        match t with 
        | (TList t' ps) =>
            match isMonob t' && noExistsb t' with
            | true  =>
                match isWFtypeb' g dv dtv (TList t' ps) Star with
                | true  => isSubtype' g dv dtv (TPoly k s) (TList t' ps)
                | false => None
                end
            | false => None
            end
        | _                 => None
        end
    | (Switch e eN eC) =>
        match isWFtypeb' g dv dtv t Star with
        | true  => 
            match synth' g dv dtv e with
            | Some (c, TList s ps)  =>
                match check' g (DVBind (TList s (PCons (eq (Ic 0) (length s (BV 0))) ps)) dv) 
                             dtv eN t with
                | Some cN =>
                    match check' g (DVBind (TList s (PCons (eq (App (Prim Succ) (length s (BV 1))) 
                                                    (length s (BV 0))) ps))
                                      (DVBind (TList s PEmpty) dv)) dtv eC
                            (TFunc s (TFunc (TList s (PCons (eq (length s (BV 2)) 
                                                          (length s (BV 0))) PEmpty)) t)) with
                    | Some cC => Some (Conj c (Conj (mkVC (TList s (PCons (eq (Ic 0) (length s (BV 0))) ps)) cN) 
                                                    (mkVC (TList s (PCons (eq (App (Prim Succ) (length s (BV 1))) 
                                                                              (length s (BV 0))) ps)) 
                                                          (mkVC (TList s PEmpty) cC))))
                    | None    => None
                    end
                | None    => None
                end
            | _                     => None
            end
        | false => None
        end
    | _               => 
        match (synth' g dv dtv e) with
        | Some (c, s) => 
            match isSubtype' g dv dtv s t with
            | Some c'   => Some (Conj c c')
            | None      => None
            end
        | None        => None
        end
    end

with synth' (g:env) (dv:deBruijns) (dtv:deBruijnTVs) 
            (e:expr) : option (VC * type) :=
    match e with
    | (Bc b)                => Some ( trueC, tybc b )
    | (Ic n)                => Some ( trueC, tyic n )
    | (Prim c)              => Some ( trueC, ty c )
    | (BV i)                => 
        match (lookupD i dv) with
        | Some t  => Some ( trueC, self t (BV i) Base )
        | None    => None
        end
    | (FV x)                => 
        match (lookup x g) with
        | Some t  => Some ( trueC, self t (FV x) Base )
        | None    => None
        end
    | (App e e')            => 
        match ( synth' g dv dtv e ) with
        | (Some (c, TFunc t_x t)) =>
            match ( check' g dv dtv e' t_x ) with
            | Some c'  => Some ( Conj c c', TExists t_x t )
            | _        => None
            end
        | _                     => None
        end
    | (AppT e' t)           =>
        match isMonob t && noExistsb t with
        | true  =>
            match isWFtypeb' g dv dtv t Star with
            | true  => 
                match synth' g dv dtv e with
                | Some (c, TPoly k s) => Some (c, tsubBTV t s)
                | _                   => None
                end
            | false => None
            end
        | false => None
        end
    | (Annot e' t)          =>
        match noExistsb t with
        | true  =>
            match ( check' g dv dtv e' t ) with
            | Some c  => Some ( c, t )
            | None    => None
            end
        | false => None
        end
    | Nil                   => 
        match c (* TODO *)
    | SynNil   : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (t : type),
        Check' g dv dtv Nil (TList t PEmpty)
            -> Synth' g dv dtv Nil (TList t (PCons (eq (Ic 0) (length t (BV 0))) PEmpty))    
    | SynCons  : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (eH eT:expr) (t:type),
        isMono t -> noExists t -> Synth' g dv dtv eT (TList t ps)
            -> Check' g dv dtv eH t 
            -> Synth' g dv dtv (Cons eH eT)
                (TExists (TList t ps) (TList t 
                  (PCons (eq (App (Prim Succ) (length t (BV 1))) (length t (BV 0))) PEmpty)))   
    | _                     => None (* Error or annotation is needed *)
    end.  
    (* isWFtypeb' g dv dtv t Star  *)

Inductive Check' : env -> deBruijns -> deBruijnTVs -> expr -> type -> Prop := 
    | ChkLam   : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (e':expr) (tx t':type),
        isWFtype' g dv dtv tx Star -> Check' g (DVBind tx dv) dtv e' t' 
            -> Check' g dv dtv (Lambda e') (TFunc tx t')
    | ChkLamT  :  forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (k:kind) (e:expr) (t:type),
        Check' g dv (DTBind k dtv) e t -> Check' g dv dtv (LambdaT k e) (TPoly k t)
    | ChkLet   : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) 
                        (e_x e':expr) (tx t':type),
        isWFtype' g dv dtv t Star -> Synth' g dv dtv e_x t_x
            -> Check' g (DVBind t_x dv) dtv e' t'
            -> Check' g dv dtv (Let e_x e') t'
    | ChkIf    : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) 
                        (e0 e1 e2: expr) (t:type),
        isWFtype' g dv dtv t Star -> Check' g dv dtv e0 (TRefn TBool PEmpty)
            -> Check' g (DVBind (self (TRefn TBool PEmpty) (Bc true)  Base) dv) dtv e1 (shiftT t)
            -> Check' g (DVBind (self (TRefn TBool PEmpty) (Bc false) Base) dv) dtv e2 (shiftT t)
            -> Check' g dv dtv (If e0 e1 e2) t
    | ChkNil   : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (t:type),
        isMono t -> noExists t -> isWFtype' g dv dtv t Star 
            -> Check' g dv dtv Nil (TList t PEmpty)
    | ChkSwit :  forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (e eN eC:expr) (t':type),
        isWFtype' g dv dtv t' Star -> Synth' g dv dtv e (TList t ps)
            -> Check' g (DVBind (TList t (PCons (eq (Ic 0) (length t (BV 0))) ps)) dv) dtv eN t'
            -> Check' g (DVBind (TList t (PCons (eq (App (Prim Succ) (length t (BV 1))) 
                                                    (length t (BV 0))) ps))
                          (DVBind (TList t PEmpty) dv)) dtv eC
                      (TFunc t (TFunc (TList t (PCons (eq (length t (BV 2)) 
                                                          (length t (BV 0))) PEmpty)) t'))
            -> Check' g dv dtv (Switch e eN eC) t'
    | ChkSyn   : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (e:expr) (s t:type),
        Synth' g dv dtv e s -> IsSubtype' g dv dtv s t 
            -> Check' g dv dtv e t 

with Synth' : env -> deBruijns -> deBruijnTVs -> expr -> type -> Prop := 
    | SynBC    : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (b:bool), 
        Synth' g dv dtv (Bc b) (tybc b)
    | SynIC    : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (n:Z),
        Synth' g dv dtv (Ic n) (tyic n)
    | SynPrm   : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (c:prim),
        Synth' g dv dtv (Prim c) (ty c) 
    | SynBV    : forall (g:env) (df:deBruijns) (dtv:deBruijnTVs) (i:index) (t:type),
        bv_bound_in i t dv -> Synth' g dv dtv (BV i) (self t (BV i) Base)
    | SynFV    : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (x:vname) (t:type),
        bound_in x t g -> Synth' g dv dtv (FV x) (self t (FV x) Base) 
    | SynApp   : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) 
                        (e e':expr) (t_x t:type),
        Synth' g dv dtv e (TFunc t_x t) -> Check' g dv dtv e t_x
            -> Synth' g dv dtv (App e e') (TExists t_x t)
    | SynAppT  : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) 
                        (e:expr) (k:kind) (s t:type),
        isMono t -> noExists t -> isWFtype' g dv dtv t Star
            -> Synth' g dv dtv e (TPoly k s)
            -> Synth' g dv dtv (AppT e t) (tsubBTV t s)
    | SynAnn   : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (e:expr) (t:type),
        noExists t -> Check' g dv dtv e t -> Synth' g dv dtv (Annot e t) t 
    | SynNil   : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (t : type),
        Check' g dv dtv Nil (TList t PEmpty)
            -> Synth' g dv dtv Nil (TList t (PCons (eq (Ic 0) (length t (BV 0))) PEmpty))    
    | SynCons  : forall (g:env) (dv:deBruijns) (dtv:deBruijnTVs) (eH eT:expr) (t:type),
        isMono t -> noExists t -> Synth' g dv dtv eT (TList t ps)
            -> Check' g dv dtv eH t 
            -> Synth' g dv dtv (Cons eH eT)
                (TExists (TList t ps) (TList t 
                  (PCons (eq (App (Prim Succ) (length t (BV 1))) (length t (BV 0))) PEmpty))).   