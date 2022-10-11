Require Import SystemF.BasicDefinitions.
Require Import SystemF.Names.
Require Import SystemF.SystemFWellFormedness.

(*-------------------------------------------------------------------------
----- | REFINEMENT TYPES of BUILT-IN PRIMITIVES
-------------------------------------------------------------------------*)

Definition erase_ty (c:prim) : ftype := (* Set_emp (ffreeTV t) && t == erase (ty c) && isLCFT t *)
    match c with
    | And      => FTFunc (FTBasic TBool) (FTFunc (FTBasic TBool) (FTBasic TBool))
    | Or       => FTFunc (FTBasic TBool) (FTFunc (FTBasic TBool) (FTBasic TBool))
    | Not      => FTFunc (FTBasic TBool) (FTBasic TBool)
    | Eqv      => FTFunc (FTBasic TBool) (FTFunc (FTBasic TBool) (FTBasic TBool))
    | Imp      => FTFunc (FTBasic TBool) (FTFunc (FTBasic TBool) (FTBasic TBool))
    | Leq      => FTFunc (FTBasic TInt)  (FTFunc (FTBasic TInt)  (FTBasic TBool))
    | (Leqn n) => FTFunc (FTBasic TInt)  (FTBasic TBool)
    | Eq       => FTFunc (FTBasic TInt)  (FTFunc (FTBasic TInt)  (FTBasic TBool))
    | (Eqn n)  => FTFunc (FTBasic TInt)  (FTBasic TBool)
    | Leql     => FTPoly Base (FTFunc (FTBasic (BTV 0))
                                      (FTFunc (FTBasic (BTV 0)) (FTBasic TBool)))
    | Eql      => FTPoly Base (FTFunc (FTBasic (BTV 0)) 
                                      (FTFunc (FTBasic (BTV 0)) (FTBasic TBool)))
    end.

Lemma erase_ty_ffreeTV : forall (c:prim), ffreeTV (erase_ty c) = empty.
Proof. destruct c; simpl; reflexivity. Qed. 

(*-----------------------------------------------------------------------------
----- | JUDGEMENTS : the Bare-Typing Relation
-----------------------------------------------------------------------------*)

Inductive HasFtype : fenv -> expr -> ftype -> Prop := 
    | FTBC   : forall (g:fenv) (b:bool),  HasFtype g (Bc b) (FTBasic TBool)
    | FTIC   : forall (g:fenv) (n:nat),   HasFtype g (Ic n) (FTBasic TInt)
    | FTVar  : forall (g:fenv) (x:vname) (b:ftype),
          bound_inF x b g -> HasFtype g (FV x) b
    | FTPrm  : forall (g:fenv) (c:prim), HasFtype g (Prim c) (erase_ty c)
    | FTAbs  : forall (g:fenv) (b:ftype) (k:kind) (e:expr) (b':ftype) (nms:names),
          WFFT g b k 
              -> (forall (y:vname), ~ Elem y nms -> HasFtype (FCons y b g) (unbind y e) b' )
              -> HasFtype g (Lambda e) (FTFunc b b')
    | FTApp  : forall (g:fenv) (e:expr) (b:ftype) (b':ftype) (e':expr),
          HasFtype g e (FTFunc b b') -> HasFtype g e' b -> HasFtype g (App e e') b'
    | FTAbsT : forall (g:fenv) (k:kind) (e:expr) (b:ftype) (nms:names),
          (forall (a':vname), ~ Elem a' nms
                    -> HasFtype (FConsT a' k g) (unbind_tv a' e) (unbindFT a' b) )
              -> HasFtype g (LambdaT k e) (FTPoly k b)
    | FTAppT : forall (g:fenv) (e:expr) (k:kind) (t':ftype) (rt:ftype),
          HasFtype g e (FTPoly k t') 
              -> WFFT g rt k -> HasFtype g (AppT e rt) (ftsubBV rt t')
    | FTLet  : forall (g:fenv) (e_x:expr) (b:ftype) (e:expr) (b':ftype) (nms:names),
          HasFtype g e_x b 
              -> (forall (y:vname), ~ Elem y nms -> HasFtype (FCons y b g) (unbind y e) b' )
              -> HasFtype g (Let e_x e) b'
    | FTAnn  : forall (g:fenv) (e:expr) (b:ftype),
          HasFtype g e b -> HasFtype g (Annot e b) b.