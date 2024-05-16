Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.SystemFTyping.

(*-----------------------------------------------------------------------------
----- | JUDGEMENTS : WELL-FORMEDNESS of TYPES and ENVIRONMENTS
-----------------------------------------------------------------------------*)

  (* --- Well-Formedness of types *)

Inductive WFtype : env -> type -> kind -> Prop :=
    | WFBase : forall (g : env) (b : basic),
          isClosedBasic b -> WFtype g (TRefn b PEmpty) Base
    | WFRefn : forall (g : env) (b : basic) (ps : preds) (nms : names),
          WFtype g (TRefn b PEmpty) Base -> ps <> PEmpty 
              -> ( forall (y:vname), ~ Elem y nms 
                      -> PHasFtype (FCons y (FTBasic b) (erase_env g)) (unbindP y ps) )
              -> WFtype g (TRefn b ps) Base
    | WFVar : forall (g : env) (a : vname) (k : kind),
          tv_bound_in a k g -> WFtype g (TRefn (FTV a) PEmpty) k
    | WFFunc : forall (g : env) (t_x : type) (k_x : kind) (t : type) (k : kind) (nms : names),
          WFtype g t_x k_x
              -> (forall (y:vname), ~ Elem y nms -> WFtype (ECons y t_x g) (unbindT y t) k )
              -> WFtype g (TFunc t_x t) Star
    | WFExis : forall (g : env) (t_x : type) (k_x : kind) (t : type) (k : kind) (nms : names), 
          WFtype g t_x k_x
              -> (forall (y:vname), ~ Elem y nms -> WFtype (ECons y t_x g) (unbindT y t) k )
              -> WFtype g (TExists t_x t) k
    | WFPoly : forall (g : env) (k : kind) (t : type) (k_t : kind) (nms : names),
          (forall (a':vname), ~ Elem a' nms -> WFtype (EConsT a' k g) (unbind_tvT a' t) k_t )
              -> WFtype g (TPoly k t) Star
    | WFList  : forall (g : env) (t : type) (k_t : kind),
          WFtype g t k_t -> WFtype g (TList t PEmpty) Star
    | WFListR : forall (g : env) (t : type) (ps : preds) (nms : names),
          WFtype g (TList t PEmpty) Star -> ps <> PEmpty 
              -> ( forall (y:vname), ~ Elem y nms 
                      -> PHasFtype (FCons y (FTList (erase t)) (erase_env g)) (unbindP y ps) )
              -> WFtype g (TList t ps) Star
    | WFKind : forall (g : env) (t : type), WFtype g t Base -> WFtype g t Star.            

  (* --- Well-formedness of Environments *)

Inductive WFEnv : env -> Prop :=
    | WFEEmpty : WFEnv Empty
    | WFEBind  : forall (g : env) (x : vname) (t : type) (k : kind),
          WFEnv g -> ~ (in_env x g) -> WFtype g t k -> WFEnv (ECons x t g)
    | WFEBindT : forall (g : env) (a : vname) (k : kind),
          WFEnv g -> ~ (in_env a g)                 -> WFEnv (EConsT a k g).

Lemma wfenv_unique : forall (g : env),
    WFEnv g -> unique g.
Proof. intros g p_g; induction p_g; simpl; trivial; split; assumption. Qed.