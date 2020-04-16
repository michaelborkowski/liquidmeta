{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-}
{- @ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Typing where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Syntax
import Environments
import Semantics
import BareTyping
import WellFormedness

-- force these into scope
semantics = (Step, EvalsTo)
typing = (HasBType, WFType, WFEnv)

-----------------------------------------------------------------------------
----- | JUDGEMENTS : the Typing Relation and the Subtyping Relation
-----------------------------------------------------------------------------

  --- the Typing Judgement

data HasTypeP where
    HasType :: Env -> Expr -> Type -> HasTypeP -- HasType G e t means G |- e : t

data HasType where 
    TBC   :: Env -> Bool -> HasType
    TIC   :: Env -> Int -> HasType
    TVar1 :: Env -> Vname -> Type -> HasType
    TVar2 :: Env -> Vname -> Type -> HasType -> Vname -> Type -> HasType
    TPrm  :: Env -> Prim -> HasType
    TAbs  :: Env -> Vname -> Type -> WFType -> Expr -> Type 
              -> Vname -> HasType -> HasType
    TApp  :: Env -> Expr -> Vname -> Type -> Type -> HasType 
              -> Expr -> HasType -> HasType
    TLet  :: Env -> Expr -> Type -> HasType -> Vname -> Expr
              -> Type -> WFType -> Vname -> HasType -> HasType
    TAnn  :: Env -> Expr -> Type -> HasType -> HasType
    TSub  :: Env -> Expr -> Type -> HasType -> Type -> WFType -> Subtype -> HasType

{-@ data HasType where
    TBC   :: g:Env -> b:Bool -> ProofOf(HasType g (Bc b) (tybc b))
 |  TIC   :: g:Env -> n:Int -> ProofOf(HasType g (Ic n) (tyic n))
 |  TVar1 :: g:Env -> { x:Vname | not (in_env x g) } -> t:Type 
                -> ProofOf(HasType (Cons x t g) (FV x) t)
 |  TVar2 :: g:Env -> { x:Vname | in_env x g } -> t:Type -> ProofOf(HasType g (FV x) t)
                -> { y:Vname | y != x && not (in_env y g) && not (Set_mem y (free t)) } -> s:Type 
                -> ProofOf(HasType (Cons y s g) (FV x) t)
 |  TPrm  :: g:Env -> c:Prim -> ProofOf(HasType g (Prim c) (ty c))
 |  TAbs  :: g:Env -> x:Vname -> t_x:Type -> ProofOf(WFType g t_x) 
                -> e:Expr -> t:Type 
                -> { y:Vname | not (in_env y g) && not (Set_mem y (fv e)) &&
                                                   not (Set_mem y (free t)) } 
                -> ProofOf(HasType (Cons y t_x g) (unbind x y e) (unbindT x y t))
                -> ProofOf(HasType g (Lambda x e) (TFunc x t_x t))
 |  TApp  :: g:Env -> e:Expr -> x:Vname -> t_x:Type -> t:Type
                -> ProofOf(HasType g e (TFunc x t_x t)) 
                -> e':Expr -> ProofOf(HasType g e' t_x) 
                -> ProofOf(HasType g (App e e') (TExists x t_x t))
 |  TLet  :: g:Env -> e_x:Expr -> t_x:Type -> ProofOf(HasType g e_x t_x)
                -> x:Vname -> e:Expr -> t:Type -> ProofOf(WFType g t)
                -> { y:Vname | not (in_env y g) && not (Set_mem y (fv e)) &&
                                                   not (Set_mem y (free t)) }
                -> ProofOf(HasType (Cons y t_x g) (unbind x y e) (unbindT x y t))
                -> ProofOf(HasType g (Let x e_x e) t)
 |  TAnn  :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
                -> ProofOf(HasType g (Annot e t) t)
 |  TSub  :: g:Env -> e:Expr -> s:Type -> ProofOf(HasType g e s) -> t:Type 
                -> ProofOf(WFType g t) -> ProofOf(Subtype g s t) 
                -> ProofOf(HasType g e t) @-} -- @-}


------------------------------------------------------------------------------
----- | SUBTYPING
------------------------------------------------------------------------------

data SubtypeP where
    Subtype :: Env -> Type -> Type -> SubtypeP

data Subtype where
    SBase :: Env -> Vname -> Base -> Pred -> Vname -> Pred -> Vname -> Entails -> Subtype
    SFunc :: Env -> Vname -> Type -> Vname -> Type -> Subtype
               -> Type -> Type -> Vname -> Subtype -> Subtype
    SWitn :: Env -> Expr -> Type -> HasType -> Type -> Vname -> Type
               -> Subtype -> Subtype
    SBind :: Env -> Vname -> Type -> Type -> Type -> Vname -> Subtype -> Subtype

{-@ data Subtype where
    SBase :: g:Env -> v1:Vname -> b:Base -> p1:Pred -> v2:Vname -> p2:Pred 
               -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p2)) }
               -> ProofOf(Entails ( Cons y (TRefn b v1 p1) g) (unbind v2 y p2))
               -> ProofOf(Subtype g (TRefn b v1 p1) (TRefn b v2 p2))
 |  SFunc :: g:Env -> x1:Vname -> s1:Type -> { x2:Vname | not (in_env x2 g) } -> s2:Type
               -> ProofOf(Subtype g s2 s1) -> t1:Type -> t2:Type
               -> { y:Vname | not (in_env y g) && not (Set_mem y (free t1)) 
                                               && not (Set_mem y (free t2)) }
               -> ProofOf(Subtype (Cons y s2 g) (unbindT x1 y t1) (unbindT x2 y t2))
               -> ProofOf(Subtype g (TFunc x1 s1 t1) (TFunc x2 s2 t2))
 |  SWitn :: g:Env -> e:Value  -> t_x:Type -> ProofOf(HasType g e t_x) 
               -> t:Type -> x:Vname -> t':Type -> ProofOf(Subtype g t (tsubBV x e t'))
               -> ProofOf(Subtype g t (TExists x t_x t'))
 |  SBind :: g:Env -> x:Vname -> t_x:Type -> t:Type -> {t':Type | not Set_mem x (free t')} 
               -> { y:Vname | not (in_env y g) && not (Set_mem y (free t))
                                               && not (Set_mem y (free t')) }
               -> ProofOf(Subtype (Cons y t_x g) (unbindT x y t) t')
               -> ProofOf(Subtype g (TExists x t_x t) t')
@-} 

{-@ lem_erase_subtype :: g:Env -> t1:Type -> t2:Type -> ProofOf(Subtype g t1 t2)
               -> { pf:_ | erase t1 == erase t2 } @-}
lem_erase_subtype :: Env -> Type -> Type -> Subtype -> Proof
lem_erase_subtype g t1 t2 (SBase _g x1 b p1 x2 p2 y _) = ()
lem_erase_subtype g t1 t2 (SFunc _g x1 s1 x2 s2 p_s2_s1 t1' t2' y p_t1'_t2')
    = () ? lem_erase_subtype g s2 s1 p_s2_s1
         ? lem_erase_tsubBV x1 (FV y) t1' ? lem_erase_tsubBV x2 (FV y) t2'
         ? lem_erase_subtype (Cons y s2 g) (unbindT x1 y t1') (unbindT x2 y t2') p_t1'_t2'  
lem_erase_subtype g t1 t2 (SWitn _g v t_x p_v_tx _t1 x t' p_t1_t'v)
    = toProof ( erase t1 ? lem_erase_subtype g t1 (tsubBV x v t') p_t1_t'v
            === erase (tsubBV x v t') ? lem_erase_tsubBV x v t'
            === erase t' === erase (TExists x t_x t') )
lem_erase_subtype g t1 t2 (SBind _g x t_x t _t2 y p_t_t')
    = () ? lem_erase_subtype (Cons y t_x g) (unbindT x y t) t2 p_t_t'
         ? lem_erase_tsubBV x (FV y) t

{-@ lem_erase_th_sub :: g:Env -> t1:Type -> t2:Type -> ProofOf(Subtype g t1 t2)
               -> th:CSubst -> { pf:_ | erase (ctsubst th t1) == erase (ctsubst th t2) } @-}
lem_erase_th_sub :: Env -> Type -> Type -> Subtype -> CSubst -> Proof
lem_erase_th_sub g t1 t2 p_t1_t2 th = toProof ( erase (ctsubst th t1) 
                                              ? lem_erase_ctsubst th t1
                                            === erase t1 ? lem_erase_subtype g t1 t2 p_t1_t2
                                            === erase t2 ? lem_erase_ctsubst th t2
                                            === erase (ctsubst th t2) ) 

-------------------------------------------------------------------------
----- | ENTAILMENTS and DENOTATIONAL SEMANTICS 
-------------------------------------------------------------------------

data EntailsP where
    Entails :: Env -> Pred -> EntailsP

data Entails where
    EntPred :: Env -> Pred -> (CSubst -> DenotesEnv -> EvalsTo) -> Entails

{-@ data Entails where
    EntPred :: g:Env -> p:Pred 
               -> (th:CSubst -> ProofOf(DenotesEnv g th) 
                             -> ProofOf(EvalsTo (csubst th p) (Bc True)) )
               -> ProofOf(Entails g p) @-} 

-- We say the proposition ValueDenoted e t holds if there exists a value v such that
--     * e \many v, and
--     * v \in [[ t ]].
data ValueDenotedP where
    ValueDenoted :: Expr -> Type -> ValueDenotedP

{-@ data ValueDenoted where 
    ValDen :: e:Expr -> t:Type -> v:Value -> ProofOf(EvalsTo e v)
                                  -> ProofOf(Denotes t v) -> ProofOf(ValueDenoted e t) @-}
data ValueDenoted where     
    ValDen :: Expr -> Type -> Expr -> EvalsTo -> Denotes -> ValueDenoted


data DenotesP where 
    Denotes :: Type -> Expr -> DenotesP    -- e \in [[t]]

data Denotes where
    DRefn :: Base -> Vname -> Pred -> Expr -> HasBType -> EvalsTo -> Denotes
    DFunc :: Vname -> Type -> Type -> Expr -> HasBType
              -> (Expr -> Denotes -> ValueDenoted) -> Denotes
    DExis :: Vname -> Type -> Type -> Expr -> HasBType
              -> Expr -> Denotes -> Denotes -> Denotes
{-@ data Denotes where
    DRefn :: b:Base -> x:Vname -> p:Pred -> v:Value  
              -> ProofOf(HasBType BEmpty v (BTBase b))
              -> ProofOf(EvalsTo (subBV x v p) (Bc True)) 
              -> ProofOf(Denotes (TRefn b x p) v)
  | DFunc :: x:Vname -> t_x:Type -> t:Type -> v:Value  
              -> ProofOf(HasBType BEmpty v (erase (TFunc x t_x t)))
              -> ( v_x:Value -> ProofOf(Denotes t_x v_x)
                             -> ProofOf(ValueDenoted (App v v_x) (tsubBV x v_x t)) ) 
              -> ProofOf(Denotes (TFunc x t_x t) v)
  | DExis :: x:Vname -> t_x:Type -> t:Type -> v:Value 
              -> ProofOf(HasBType BEmpty v (erase t)) 
              -> v_x:Value -> ProofOf(Denotes t_x v_x)
              -> ProofOf(Denotes (tsubBV x v_x t) v)
              -> ProofOf(Denotes (TExists x t_x t) v)  @-} -- @-}

{-@ get_btyp_from_den :: t:Type -> v:Value -> ProofOf(Denotes t v)
              -> ProofOf(HasBType BEmpty v (erase t)) @-}
get_btyp_from_den :: Type -> Expr -> Denotes -> HasBType    
get_btyp_from_den t v (DRefn _ _ _ _ pf_v_b _)     = pf_v_b
get_btyp_from_den t v (DFunc _ _ _ _ pf_v_b _)     = pf_v_b
get_btyp_from_den t v (DExis _ _ _ _ pf_v_b _ _ _) = pf_v_b

{-@ lem_den_nofv :: v:Value -> t:Type -> ProofOf(Denotes t v) 
        -> { pf:_ | Set_emp (fv v) } @-}
lem_den_nofv :: Expr -> Type -> Denotes -> Proof
lem_den_nofv v t den_t_v = lem_fv_subset_bindsB BEmpty v (erase t) pf_v_bt
  where
    pf_v_bt = get_btyp_from_den t v den_t_v

{-@ get_obj_from_dfunc :: x:Vname -> s:Type -> t:Type -> v:Value 
        -> ProofOf(Denotes (TFunc x s t) v) -> v':Value 
        -> ProofOf(Denotes s v') -> ProofOf(ValueDenoted (App v v') (tsubBV x v' t)) @-}  
get_obj_from_dfunc :: Vname -> Type -> Type -> Expr -> Denotes 
                                    -> Expr -> Denotes -> ValueDenoted
get_obj_from_dfunc x s t v (DFunc _ _ _ _ _ prover) v' den_s_v' = prover v' den_s_v' 

-- Denotations of Environments, [[g]]. There are two cases:
--   1. [[ Empty ]] = { CEmpty }.
--   2. [[ Cons x t g ]] = { CCons x v_x th | Denotes th(t) v_x && th \in [[ g ]] }
data DenotesEnvP where 
    DenotesEnv :: Env -> CSubst -> DenotesEnvP 

data DenotesEnv where
    DEmp :: DenotesEnv
    DExt :: Env -> CSubst -> DenotesEnv -> Vname -> Type -> Expr 
               -> Denotes -> DenotesEnv
{-@ data DenotesEnv where 
    DEmp :: ProofOf(DenotesEnv Empty CEmpty)
 |  DExt :: g:Env -> th:CSubst -> ProofOf(DenotesEnv g th) 
               -> { x:Vname | not (in_env x g) } -> t:Type 
               -> v:Value -> ProofOf(Denotes (ctsubst th t) v)
               -> ProofOf(DenotesEnv (Cons x t g) (CCons x v th)) @-}

