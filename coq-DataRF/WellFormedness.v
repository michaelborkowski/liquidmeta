Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.SystemFTyping.

(*-----------------------------------------------------------------------------
----- | JUDGEMENTS : WELL-FORMEDNESS of TYPES and ENVIRONMENTS
-----------------------------------------------------------------------------*)

  (* --- Well-Formedness of types *)

Inductive WFtype : env -> defs -> type -> kind -> Prop :=
    | WFBase : forall (g : env) (ds : defs) (b : basic),
          isClosedBasic b -> WFtype g ds (TRefn b PEmpty) Base
    | WFRefn : forall (g : env) (ds : defs) (b : basic) (ps : preds) (nms : names),
          WFtype g ds (TRefn b PEmpty) Base -> ps <> PEmpty 
              -> ( forall (y:vname), ~ Elem y nms 
                      -> PHasFtype (FCons y (FTBasic b) (erase_env g)) ds (unbindP y ps) )
              -> WFtype g ds (TRefn b ps) Base
    | WFVar : forall (g : env) (ds : defs) (a : vname) (k : kind),
          tv_bound_in a k g -> WFtype g ds (TRefn (FTV a) PEmpty) k
    | WFFunc : forall (g : env) (ds : defs) (t_x : type) (k_x : kind) 
                      (t : type) (k : kind) (nms : names),
          WFtype g ds t_x k_x
              -> (forall (y:vname), ~ Elem y nms -> WFtype (Cons y t_x g) ds (unbindT y t) k )
              -> WFtype g ds (TFunc t_x t) Star
    | WFExis : forall (g : env) (ds : defs) (t_x : type) (k_x : kind) 
                      (t : type) (k : kind) (nms : names), 
          WFtype g ds t_x k_x
              -> (forall (y:vname), ~ Elem y nms -> WFtype (Cons y t_x g) ds (unbindT y t) k )
              -> WFtype g ds (TExists t_x t) k
    | WFPoly : forall (g : env) (ds : defs) (k : kind) (t : type) (k_t : kind) (nms : names),
          (forall (a':vname), ~ Elem a' nms -> WFtype (ConsT a' k g) ds (unbind_tvT a' t) k_t )
              -> WFtype g ds (TPoly k t) Star
    | WFData : forall (g : env) (ds : defs) (tc : tcons) (t : type) (k_t : kind)
                      (ps : preds) (nms : names),
          kind_defined_in tc k_t ds -> WFtype g ds t k_t 
              -> ( forall (y:vname), ~ Elem y nms
                      -> PHasFtype (FCons y (FTData tc (erase t)) (erase_env g)) ds (unbindP y ps) )
              -> WFtype g ds (TData tc t ps) Base
    | WFKind : forall (g : env) (ds : defs) (t : type), 
          WFtype g ds t Base -> WFtype g ds t Star.

  (* --- Well-formedness of Environments *)

Inductive WFEnv : env -> defs -> Prop :=
    | WFEEmpty : forall (ds : defs), WFEnv Empty ds
    | WFEBind  : forall (g : env) (ds : defs) (x : vname) (t : type) (k : kind),
          WFEnv g ds -> ~ (in_env x g) -> WFtype g ds t k -> WFEnv (Cons x t g) ds
    | WFEBindT : forall (g : env) (ds : defs) (a : vname) (k : kind),
          WFEnv g ds -> ~ (in_env a g)                    -> WFEnv (ConsT a k g) ds.

Lemma wfenv_unique : forall (g : env) (ds : defs),
    WFEnv g ds -> unique g.
Proof. intros g ds p_g; induction p_g; simpl; trivial; split; assumption. Qed.