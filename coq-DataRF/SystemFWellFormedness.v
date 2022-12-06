Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.

(** Because the underyling System F types have type variables, we need a concept
  *   of well-formedness that works for the System F types and the System F
  *   binding environments containing System F types in the bindings. *)

(*-----------------------------------------------------------------------------
----- | JUDGEMENTS : WELL-FORMEDNESS of System F TYPES and ENVIRONMENTS
-----------------------------------------------------------------------------*)

  (* --- Well-Formedness of (System) F types *)

Inductive WFFT : fenv -> defs -> ftype -> kind -> Prop :=
    | WFFTBasic : forall (g : fenv) (ds : defs) (b : basic),
           isClosedBasic b  ->  WFFT g ds (FTBasic b) Base
    | WFFTFV    : forall (g : fenv) (ds : defs) (a : vname) (k : kind), 
          tv_bound_inF a k g -> WFFT g ds (FTBasic (FTV a)) k
    | WFFTFunc  : forall (g : fenv) (ds : defs) (t1 : ftype) (k1 : kind) (t2 : ftype) (k2 : kind),
          WFFT g ds t1 k1 -> WFFT g ds t2 k2 -> WFFT g ds (FTFunc t1 t2) Star
    | WFFTPoly  : forall (g : fenv) (ds : defs) (k : kind) (t : ftype) (k_t : kind) (nms : names),
          ( forall (a:vname), ~ Elem a nms -> WFFT (FConsT a k g) ds (unbindFT a t) k_t )
              -> WFFT g ds (FTPoly k t) Star
    | WFFTData  : forall (g : fenv) (ds : defs) (tc : tcons) (t : ftype) (k_t : kind),
          tcKind tc ds = Some k_t -> WFFT g ds t k_t -> WFFT g ds (FTData tc t) Base
    | WFFTKind  : forall (g : fenv) (ds : defs) (t : ftype),
          WFFT g ds t Base -> WFFT g ds t Star.

Inductive WFFE : fenv -> defs -> Prop := 
    | WFFEmpty : forall (ds : defs), WFFE FEmpty ds
    | WFFBind  : forall (g : fenv) (ds : defs) (x : vname) (t : ftype) (k : kind),
          WFFE g ds -> ~ (in_envF x g) -> WFFT g ds t k -> WFFE (FCons x t g) ds
    | WFFBindT : forall (g : fenv) (ds : defs) (a : vname)             (k : kind),
          WFFE g ds -> ~ (in_envF a g)                  -> WFFE (FConsT a k g) ds.

Lemma wffe_uniqueF : forall (g : fenv) (ds : defs),
    WFFE g ds -> uniqueF g.
Proof. intros g ds p_g; induction p_g; simpl; trivial; split; assumption. Qed.