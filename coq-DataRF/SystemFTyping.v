Require Import SystemRF.BasicDefinitions. 
Require Import SystemRF.Names.
Require Import SystemRF.SystemFWellFormedness.

(*-------------------------------------------------------------------------
----- | REFINEMENT TYPES of BUILT-IN PRIMITIVES
-------------------------------------------------------------------------*)

Definition tybc (b:bool) : type := (*Set_emp (free t) && Set_emp (freeTV t) *)
    TRefn TBool (PCons (App (App (AppT (Prim Eql) (TRefn TBool PEmpty)) 
                                 (Bc b)) (BV 0))  PEmpty).

Definition tyic (n:nat) : type := (* Set_emp (free t) && Set_emp (freeTV t) *)
    TRefn TInt  (PCons (App (App (AppT (Prim Eql) (TRefn TInt  PEmpty))
                                 (Ic n)) (BV 0))  PEmpty).

Definition refn_pred (c:prim) : expr := (* Set_emp (fv p) && Set_emp (ftv p) *)
    match c with 
    | And      => App (App (Prim Eqv) 
                           (App (App (Prim And) (BV 2)) (BV 1))) (BV 0)
    | Or       => App (App (Prim Eqv) 
                           (App (App (Prim Or)  (BV 2)) (BV 1))) (BV 0)
    | Not      => App (App (Prim Eqv) (App (Prim Not) (BV 1))) (BV 0)
    | Eqv      => App (App (Prim Eqv) 
                           (App (App (Prim Eqv) (BV 2)) (BV 1))) (BV 0)
    | Imp      => App (App (Prim Eqv)
                           (App (App (Prim Imp) (BV 2)) (BV 1))) (BV 0)
    | Leq      => App (App (Prim Eqv) 
                           (App (App (Prim Leq) (BV 2)) (BV 1))) (BV 0)
    | (Leqn n) => App (App (Prim Eqv) 
                           (App (App (Prim Leq) (Ic n)) (BV 1))) (BV 0)
    | Eq       => App (App (Prim Eqv) 
                           (App (App (Prim Eq)  (BV 2)) (BV 1))) (BV 0)
    | (Eqn n)  => App (App (Prim Eqv) 
                           (App (App (Prim Eq)  (Ic n)) (BV 1))) (BV 0)
    | Leql     => App (App (Prim Eqv) 
                           (App (App (AppT (Prim Leql) (TRefn (BTV 0) PEmpty)) 
                                     (BV 2)) (BV 1))) (BV 0)
    | Eql      => App (App (Prim Eqv) 
                           (App (App (AppT (Prim Eql)  (TRefn (BTV 0) PEmpty)) 
                                     (BV 2)) (BV 1))) (BV 0)
    end.
         
Definition intype (c:prim ) : type := (* Set_emp (free t) && Set_emp (freeTV t) *)
    match c with 
    | And     => TRefn TBool   PEmpty 
    | Or      => TRefn TBool   PEmpty
    | Eqv     => TRefn TBool   PEmpty
    | Imp     => TRefn TBool   PEmpty
    | Not     => TRefn TBool   PEmpty
    | Leql    => TRefn (BTV 0) PEmpty
    | Eql     => TRefn (BTV 0) PEmpty
    | _       => TRefn TInt    PEmpty
    end.

Definition ty' (c:prim) : type := (*Set_emp (free t) && Set_emp (freeTV t) *)
    match c with
    | And      => TFunc (TRefn TBool PEmpty) (TRefn TBool (PCons (refn_pred And) PEmpty))
    | Or       => TFunc (TRefn TBool PEmpty) (TRefn TBool (PCons (refn_pred Or)  PEmpty))
    | Not      =>                             TRefn TBool (PCons (refn_pred Not) PEmpty)
    | Eqv      => TFunc (TRefn TBool PEmpty) (TRefn TBool (PCons (refn_pred Eqv) PEmpty))
    | Imp      => TFunc (TRefn TBool PEmpty) (TRefn TBool (PCons (refn_pred Imp) PEmpty))
    | Leq      => TFunc (TRefn TInt  PEmpty) (TRefn TBool (PCons (refn_pred Leq) PEmpty))
    | (Leqn n) =>                             TRefn TBool (PCons (refn_pred (Leqn n)) PEmpty)
    | Eq       => TFunc (TRefn TInt  PEmpty) (TRefn TBool (PCons (refn_pred Eq)  PEmpty)) 
    | (Eqn n)  =>                             TRefn TBool (PCons (refn_pred (Eqn n)) PEmpty)
    | Leql     => TFunc (TRefn (BTV 0) PEmpty) (TRefn TBool (PCons (refn_pred Leql) PEmpty))
    | Eql      => TFunc (TRefn (BTV 0) PEmpty) (TRefn TBool (PCons (refn_pred Eql) PEmpty))
    end.

Definition ty (c:prim) : type := (*Set_emp (free t) && Set_emp (freeTV t) *)
    match c with
    | And      => TFunc (intype And)      (ty' And)
    | Or       => TFunc (intype Or)       (ty' Or)
    | Not      => TFunc (intype Not)      (ty' Not)
    | Eqv      => TFunc (intype Eqv)      (ty' Eqv)
    | Imp      => TFunc (intype Imp)      (ty' Imp)
    | Leq      => TFunc (intype Leq)      (ty' Leq)
    | (Leqn n) => TFunc (intype (Leqn n)) (ty' (Leqn n))
    | Eq       => TFunc (intype Eq)       (ty' Eq)
    | (Eqn n)  => TFunc (intype (Eqn n))  (ty' (Eqn n))
    | Leql     => TPoly Base (TFunc (intype Leql) (ty' Leql))
    | Eql      => TPoly Base (TFunc (intype Eql)  (ty' Eql))
    end.

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

Definition inst_dtypeF (k : kind) (u : type) (t : ftype) : ftype :=
    ftsubBV t (erase u).

Inductive BijectionArrowsF : names -> ftype -> Type := (* can't use Prop here *)
    | BAF_nil    : forall tc t,       BijectionArrowsF nil (FTData tc t)
    | BAF_cons   : forall (x:vname) (xs:names) t_x t, 
          BijectionArrowsF xs t -> BijectionArrowsF (cons x xs) (FTFunc t_x t).

Fixpoint destructF (g : fenv) (xs : names) (u : ftype) 
                   (pf : BijectionArrowsF xs u) : fenv :=
    match pf with
    | BAF_nil  _ _            => g
    | BAF_cons x xs' u_x u' pf' => destructF (FCons x u_x g) xs' u' pf'
    end.
    (* it's not clear what the inductive Prop should be yet,
        and maybe it will depend on isValid ? *)

Fixpoint destructF' (g : fenv) (nms : names) (u : ftype) : option fenv :=
    match nms, u with
    | nil       , _             => Some g
    | cons x xs , FTFunc u_x u' => destructF' (FCons x u_x g) xs u'
    | _         , _             => None
    end.

Lemma destructF_destructF' : 
  forall (g : fenv) (xs : names) (u : ftype) (pf : BijectionArrowsF xs u),
      destructF' g xs u = Some (destructF g xs u pf).
Proof. intros; generalize dependent g; 
  induction pf as [tc t|x xs_ t_x t Hxs IH]; simpl;
  intros g; try rewrite IH; reflexivity. Qed.

Lemma destructF_pf_indep : 
  forall (g : fenv) (xs : names) (u : ftype) (pf pf' : BijectionArrowsF xs u),
    destructF g xs u pf = destructF g xs u pf'.
Proof. intros. assert (Some (destructF g xs u pf) = Some (destructF g xs u pf')).
- apply eq_stepl with (destructF' g xs u); apply destructF_destructF'.
- injection H as H'; assumption. Qed.    

Inductive HasFtype : fenv -> defs -> expr -> ftype -> Prop := 
    | FTBC   : forall (g:fenv) (ds:defs) (b:bool),  HasFtype g ds (Bc b) (FTBasic TBool)
    | FTIC   : forall (g:fenv) (ds:defs) (n:nat),   HasFtype g ds (Ic n) (FTBasic TInt)
    | FTVar  : forall (g:fenv) (ds:defs) (x:vname) (b:ftype),
          bound_inF x b g -> HasFtype g ds (FV x) b
    | FTPrm  : forall (g:fenv) (ds:defs) (c:prim),  HasFtype g ds (Prim c) (erase_ty c)
    | FTDC   : forall (g:fenv) (ds:defs) (dc : dcons) (dt : type), 
          dc_defined_in dc dt ds -> HasFtype g ds (Dc dc) (erase dt)
    | FTAbs  : forall (g:fenv) (ds:defs) (b:ftype) (k:kind) (e:expr) (b':ftype) (nms:names),
          WFFT g ds b k 
              -> (forall (y:vname), ~ Elem y nms -> HasFtype (FCons y b g) ds (unbind y e) b' )
              -> HasFtype g ds (Lambda e) (FTFunc b b')
    | FTApp  : forall (g:fenv) (ds:defs) (e:expr) (b:ftype) (b':ftype) (e':expr),
          HasFtype g ds e (FTFunc b b') -> HasFtype g ds e' b -> HasFtype g ds (App e e') b'
    | FTAbsT : forall (g:fenv) (ds:defs) (k:kind) (e:expr) (b:ftype) (nms:names),
          (forall (a':vname), ~ Elem a' nms
                    -> HasFtype (FConsT a' k g) ds (unbind_tv a' e) (unbindFT a' b) )
              -> HasFtype g ds (LambdaT k e) (FTPoly k b)
    | FTAppT : forall (g:fenv) (ds:defs) (e:expr) (k:kind) (t':ftype) (rt:type),
          HasFtype g ds e (FTPoly k t') 
              -> noExists rt -> Subset (free rt) (vbindsF g) 
                             -> Subset (freeTV rt) (tvbindsF g) -> isLCT rt
              -> WFFT g ds (erase rt) k -> HasFtype g ds (AppT e rt) (ftsubBV (erase rt) t')
    | FTLet  : forall (g:fenv) (ds:defs) (e_x:expr) (b:ftype) (e:expr) (b':ftype) (nms:names),
          HasFtype g ds e_x b 
              -> (forall (y:vname), ~ Elem y nms -> HasFtype (FCons y b g) ds (unbind y e) b' )
              -> HasFtype g ds (Let e_x e) b'
    | FTAnn  : forall (g:fenv) (ds:defs) (e:expr) (b:ftype) (t1:type),
          erase t1 = b  -> Subset (free t1) (vbindsF g) 
                        -> Subset (freeTV t1) (tvbindsF g) -> isLCT t1 
              -> HasFtype g ds e b -> HasFtype g ds (Annot e t1) b
    | FTSwit : forall (g:fenv) (ds:defs) (tc:tcons) (t':ftype) (dds:ddefns)
                      (e:expr) (cs:alts) (t:ftype),
          defined_in tc dds ds -> AHasFtype g ds tc t' dds cs t -> HasFtype g ds e (FTData tc t')
              -> HasFtype g ds (Switch e cs) t

with AHasFtype : fenv -> defs -> tcons -> ftype -> ddefns -> alts -> ftype -> Prop :=
    | AFTEmpty : forall (g:fenv) (ds:defs) (tc:tcons) (t' t:ftype),
          AHasFtype g ds tc t' nil AEmpty t
    | AFTCons  : forall (g:fenv) (ds:defs) (tc:tcons) (t':ftype) 
                        (dc:dcons) (k:kind) (u:type) (dds:ddefns) 
                        (e':expr) (cs:alts) (t:ftype) (nms:names),
          AHasFtype g ds tc t' dds cs t 
              -> (forall (xs:names) (pf:BijectionArrowsF xs (inst_dtypeF k u t')), 
                      (* -> len xs = arrows u (* arity dc *) *)
                      intersect xs nms = empty 
                          -> HasFtype (destructF g xs (inst_dtypeF k u t') pf) ds e' t ) 
              -> AHasFtype g ds tc t' (cons (DDefn dc (TPoly k u)) dds) (ACons dc e' cs) t.

Inductive PHasFtype : fenv -> defs -> preds -> Prop := 
    | PFTEmp  : forall (g:fenv) (ds:defs), PHasFtype g ds PEmpty
    | PFTCons : forall (g:fenv) (ds:defs) (p:expr) (ps:preds),
          HasFtype g ds p (FTBasic TBool) -> PHasFtype g ds ps 
              -> PHasFtype g ds (PCons p ps).