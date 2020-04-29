{-# LANGUAGE GADTs #-}

{-  @ LIQUID "--no-termination" @-}
{-  @ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Typing where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import BasicProps

-- we must force these into scope for LH
semantics = (Step, EvalsTo)
typing = (HasBType, WFType, WFEnv)

{-@ reflect foo3 @-}   
foo3 x = Just x 
foo3 :: a -> Maybe a 


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
----- | CLOSING SUBSTITUTIONS 
-------------------------------------------------------------------------

-- closing substitutions (i.e. th(x), th(e), th(t)) proceed from the top/right of
--   the typing env downwards/leftwards

data CSubst = CEmpty
            | CCons Vname Expr CSubst
{-@ data CSubst  where
    CEmpty :: CSubst
  | CCons  :: x:Vname -> v:Value -> th:CSubst -> CSubst @-}

{-@ reflect bindsC @-}
bindsC :: CSubst -> S.Set Vname
bindsC CEmpty         = S.empty
bindsC (CCons x v th) = S.union (S.singleton x) (bindsC th)

{-@ measure uniqueC @-}
uniqueC :: CSubst -> Bool
uniqueC CEmpty         = True
uniqueC (CCons x v th) = (uniqueC th) && not (S.member x (bindsC th))

{-@ reflect csubst @-}
csubst :: CSubst -> Expr -> Expr
csubst CEmpty         e = e
csubst (CCons x v th) e = csubst th (subFV x v e)

-- Idea: ctsubst th t = foldr (\(x,e) t' -> tsubFV x e t') t th 
{-@ reflect ctsubst @-}
ctsubst :: CSubst -> Type -> Type
ctsubst CEmpty         t = t
ctsubst (CCons x v th) t = ctsubst th (tsubFV x v t)

{-@ reflect concatCS @-}
concatCS :: CSubst -> CSubst -> CSubst
concatCS th CEmpty          = th
concatCS th (CCons x v th') = CCons x v (concatCS th th')

  --- various distributive properties of csubst and ctsubst

{-@ lem_csubst_bc :: th:CSubst -> b:Bool -> { pf:_ | csubst th (Bc b) == Bc b } @-}
lem_csubst_bc :: CSubst -> Bool -> Proof
lem_csubst_bc (CEmpty)       b = ()
lem_csubst_bc (CCons x v th) b = () ? lem_csubst_bc th b

{-@ lem_csubst_ic :: th:CSubst -> n:Int -> { pf:_ | csubst th (Ic n) == Ic n } @-}
lem_csubst_ic :: CSubst -> Int -> Proof
lem_csubst_ic (CEmpty)       n = ()
lem_csubst_ic (CCons x v th) n = () ? lem_csubst_ic th n

{-@ lem_csubst_prim :: th:CSubst -> c:Prim -> { pf:_ | csubst th (Prim c) == Prim c } @-}
lem_csubst_prim :: CSubst -> Prim -> Proof
lem_csubst_prim (CEmpty)       c = ()
lem_csubst_prim (CCons x v th) c = () ? lem_csubst_prim th c

{-@ lem_csubst_lambda :: th:CSubst -> x:Vname 
        -> e:Expr -> { pf:_ | csubst th (Lambda x e) == Lambda x (csubst th e) } @-}
lem_csubst_lambda :: CSubst -> Vname -> Expr -> Proof
lem_csubst_lambda (CEmpty)       x e = ()
lem_csubst_lambda (CCons y v th) x e = () ? lem_csubst_lambda th x (subFV y v e)

{-@ lem_csubst_app :: th:CSubst -> e:Expr -> e':Expr 
               -> { pf:_ | csubst th (App e e') == App (csubst th e) (csubst th e') } @-}
lem_csubst_app :: CSubst -> Expr -> Expr -> Proof
lem_csubst_app (CEmpty)       e e' = ()
lem_csubst_app (CCons y v th) e e' = () ? lem_csubst_app th (subFV y v e) (subFV y v e')

{-@ lem_csubst_let :: th:CSubst -> x:Vname -> e_x:Expr -> e:Expr 
        -> { pf:_ | csubst th (Let x e_x e) == Let x (csubst th e_x) (csubst th e) } @-}
lem_csubst_let :: CSubst -> Vname -> Expr -> Expr -> Proof
lem_csubst_let (CEmpty)       x e_x e = ()
lem_csubst_let (CCons y v th) x e_x e = () ? lem_csubst_let th x (subFV y v e_x) (subFV y v e)

{-@ lem_csubst_annot :: th:CSubst -> e:Expr
        -> t:Type -> { pf:_ | csubst th (Annot e t) == Annot (csubst th e) (ctsubst th t) } @-}
lem_csubst_annot :: CSubst -> Expr -> Type -> Proof
lem_csubst_annot (CEmpty)       e t = ()
lem_csubst_annot (CCons y v th) e t = () ? lem_csubst_annot th (subFV y v e) (tsubFV y v t)

{-@ lem_ctsubst_refn :: th:CSubst -> b:Base -> x:Vname -> p:Expr
               -> { pf:_ | ctsubst th (TRefn b x p) == TRefn b x (csubst th p) } @-}
lem_ctsubst_refn :: CSubst -> Base -> Vname -> Expr -> Proof
lem_ctsubst_refn (CEmpty)       b x p = ()
lem_ctsubst_refn (CCons y v th) b x p = toProof ( ctsubst (CCons y v th) (TRefn b x p)
                                              === ctsubst th (tsubFV y v (TRefn b x p))
                                              === ctsubst th (TRefn b x (subFV y v p))
                                                ? lem_ctsubst_refn th b x (subFV y v p)
                                              === TRefn b x (csubst th (subFV y v p)) 
                                              === TRefn b x (csubst (CCons y v th) p) )

{-@ lem_ctsubst_func :: th:CSubst -> x:Vname -> t_x:Type -> t:Type
        -> { pf:_ | ctsubst th (TFunc x t_x t) == TFunc x (ctsubst th t_x) (ctsubst th t) } @-}  
lem_ctsubst_func :: CSubst -> Vname -> Type -> Type -> Proof
lem_ctsubst_func (CEmpty)       x t_x t = ()
lem_ctsubst_func (CCons y v th) x t_x t 
    = () ? lem_ctsubst_func th x (tsubFV y v t_x) (tsubFV y v t) 

{-@ lem_ctsubst_exis :: th:CSubst -> x:Vname -> t_x:Type -> t:Type
        -> {pf:_ | ctsubst th (TExists x t_x t) == TExists x (ctsubst th t_x) (ctsubst th t)} @-}  
lem_ctsubst_exis :: CSubst -> Vname -> Type -> Type -> Proof
lem_ctsubst_exis (CEmpty)       x t_x t = ()
lem_ctsubst_exis (CCons y v th) x t_x t 
    = () ? lem_ctsubst_exis th x (tsubFV y v t_x) (tsubFV y v t) 


  --- Various properties of csubst/ctsubst and free/bound variables

{-@ lem_csubst_nofv :: th:CSubst -> { e:Expr | Set_emp (fv e) }
        -> { pf:_ | csubst th e == e } @-}
lem_csubst_nofv :: CSubst -> Expr -> Proof
lem_csubst_nofv (CEmpty)       e = ()
lem_csubst_nofv (CCons x v th) e = () ? lem_csubst_nofv th e
                                      ? toProof ( subFV x v e === e )

{-@ lem_ctsubst_nofree :: th:CSubst -> { t:Type | Set_emp (free t) }
        -> { pf:_ | ctsubst th t == t } @-}
lem_ctsubst_nofree :: CSubst -> Type -> Proof
lem_ctsubst_nofree (CEmpty)       t = ()
lem_ctsubst_nofree (CCons x v th) t = () ? lem_ctsubst_nofree th t
                                         ? toProof ( tsubFV x v t === t )

{-@ lem_csubst_freeBV :: th:CSubst -> e:Expr
        -> { pf:_ | freeBV (csubst th e) == freeBV e } @-}
lem_csubst_freeBV :: CSubst -> Expr -> Proof
lem_csubst_freeBV (CEmpty)       e = ()
lem_csubst_freeBV (CCons x v th) e = () ? lem_csubst_freeBV th (subFV x v e)
                         ? toProof ( freeBV (subFV x v e) === freeBV e )

{-@ lem_ctsubst_tfreeBV :: th:CSubst -> t:Type
        -> { pf:_ | tfreeBV (ctsubst th t) == tfreeBV t } @-}
lem_ctsubst_tfreeBV :: CSubst -> Type -> Proof
lem_ctsubst_tfreeBV (CEmpty)       t = ()
lem_ctsubst_tfreeBV (CCons x v th) t = () ? lem_ctsubst_tfreeBV th (tsubFV x v t)
                         ? toProof ( tfreeBV (tsubFV x v t) === tfreeBV t )

{-@ lem_csubst_value :: th:CSubst -> v:Value  
        -> { pf:_ | isValue (csubst th v) && Set_emp (freeBV (csubst th v)) } @-}
lem_csubst_value :: CSubst -> Expr -> Proof
lem_csubst_value (CEmpty)         v = ()
lem_csubst_value (CCons y v_y th) v = () ? lem_csubst_value th (subFV y v_y v)

{-@ lem_ctsubst_head_not_free :: x:Vname -> v_x:Value -> th:CSubst 
        -> { t:Type | not (Set_mem x (free t)) } 
        -> { pf:_ | ctsubst (CCons x v_x th) t == ctsubst th t } @-}
lem_ctsubst_head_not_free :: Vname -> Expr -> CSubst -> Type -> Proof
lem_ctsubst_head_not_free x v_x th t = toProof ( ctsubst (CCons x v_x th) t
                                             === ctsubst th (tsubFV x v_x t)
                                             === ctsubst th t )

  --- Commutative laws relating csubst/ctsubst and subBV/tsubBV 

{-@ lem_csubst_subBV :: x:Vname -> v:Value -> bt:BType 
           -> ProofOf(HasBType BEmpty v bt) -> th:CSubst -> p:Expr
           -> { pf:_ | csubst th (subBV x v p) == subBV x v (csubst th p) } @-}
lem_csubst_subBV :: Vname -> Expr -> BType -> HasBType -> CSubst -> Expr -> Proof
lem_csubst_subBV x v bt pf_v_b (CEmpty)         p = ()
lem_csubst_subBV x v bt pf_v_b (CCons y v_y th) p 
    = () ? lem_commute_subFV_subBV1 x v 
                   (y `withProof` lem_fv_bound_in_benv BEmpty v bt pf_v_b y) v_y p
         ? lem_csubst_subBV x v bt pf_v_b th (subFV y v_y p)

{-@ lem_ctsubst_tsubBV :: x:Vname -> v:Value -> bt:BType
           -> ProofOf(HasBType BEmpty v bt) -> th:CSubst -> t:Type
           -> { pf:_ | ctsubst th (tsubBV x v t) == tsubBV x v (ctsubst th t) } @-}
lem_ctsubst_tsubBV :: Vname -> Expr -> BType -> HasBType -> CSubst -> Type -> Proof
lem_ctsubst_tsubBV x v bt pf_v_b (CEmpty)         t = ()
lem_ctsubst_tsubBV x v bt pf_v_b (CCons y v_y th) t 
    = () ? lem_commute_tsubFV_tsubBV1 x v 
                   (y `withProof` lem_fv_bound_in_benv BEmpty v bt pf_v_b y) v_y t
         ? lem_ctsubst_tsubBV x v bt pf_v_b th (tsubFV y v_y t)

{-@ lem_csubst_and_unbind :: x:Vname -> y:Vname 
           -> v:Value -> bt:BType -> ProofOf(HasBType BEmpty v bt)
           -> th:CSubst -> { p:Expr | not (Set_mem y (fv p)) }
           -> { pf:_ | csubst (CCons y v th) (unbind x y p) == subBV x v (csubst th p) } @-}
lem_csubst_and_unbind :: Vname -> Vname -> Expr -> BType -> HasBType -> CSubst -> Expr -> Proof
lem_csubst_and_unbind x y v b pf_v_b th p = toProof ( csubst (CCons y v th) (unbind x y p)
                                                  === csubst th (subFV y v (unbind x y p))
                                                    ? lem_subFV_unbind x y v p
                                                  === csubst th (subBV x v p)
                                                    ? lem_csubst_subBV x v b pf_v_b th p
                                                  === subBV x v (csubst th p) )

{-@ lem_ctsubst_and_unbindT :: x:Vname -> y:Vname
           -> v:Value -> bt:BType -> ProofOf(HasBType BEmpty v bt)
           -> th:CSubst -> { t:Type | not (Set_mem y (free t)) }
           -> { pf:_ | ctsubst (CCons y v th) (unbindT x y t) == tsubBV x v (ctsubst th t) } @-}
lem_ctsubst_and_unbindT :: Vname -> Vname -> Expr -> BType -> HasBType 
           -> CSubst -> Type -> Proof
lem_ctsubst_and_unbindT x y v bt pf_v_b th t = toProof ( ctsubst (CCons y v th) (unbindT x y t)
                                                   === ctsubst th (tsubFV y v (unbindT x y t))
                                                     ? lem_tsubFV_unbindT x y v t
                                                   === ctsubst th (tsubBV x v t)
                                                     ? lem_ctsubst_tsubBV x v bt pf_v_b th t
                                                   === tsubBV x v (ctsubst th t) )

{-@ lem_commute_ctsubst_tsubBV :: th:CSubst -> x:Vname -> v:Value -> t:Type
           -> { pf:_ | ctsubst th (tsubBV x v t) == tsubBV x (csubst th v) (ctsubst th t) } @-} 
lem_commute_ctsubst_tsubBV :: CSubst -> Vname -> Expr -> Type -> Proof
lem_commute_ctsubst_tsubBV (CEmpty)         x v t = () 
lem_commute_ctsubst_tsubBV (CCons y v_y th) x v t 
    = () ? lem_commute_tsubFV_tsubBV x v y v_y t
         ? lem_commute_ctsubst_tsubBV th x (subFV y v_y v) (tsubFV y v_y t)

{-@ lem_erase_ctsubst :: th:CSubst -> t:Type 
               -> { pf:_ | erase (ctsubst th t) == erase t } @-}
lem_erase_ctsubst :: CSubst -> Type -> Proof
lem_erase_ctsubst (CEmpty)       t = ()
lem_erase_ctsubst (CCons y v th) t = toProof ( erase (ctsubst (CCons y v th) t)
                                           === erase (ctsubst th (tsubFV y v t))
                                             ? lem_erase_ctsubst th (tsubFV y v t)
                                           === erase (tsubFV y v t)
                                             ? lem_erase_tsubFV y v t
                                           === erase t )

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

