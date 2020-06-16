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

import Basics
import BasicProps
import STLCLemmas
import STLCSoundness

-- we must force these into scope for LH
semantics = (Step, EvalsTo)
typing = (HasBType, WFType, WFEnv)

{-@ reflect foo3 @-}   
foo3 x = Just x 
foo3 :: a -> Maybe a 


-----------------------------------------------------------------------------
----- | JUDGEMENTS : the Typing Relation and the Subtyping Relation
-----------------------------------------------------------------------------

{-@ lem_tsubFV_self1 :: z:Vname -> z':Vname -> t:Type -> { x:Vname | x == z }
        -> { pf:_ | tsubFV z (FV z') (self t x) == self (tsubFV z (FV z') t) z' } @-}
lem_tsubFV_self1 :: Vname -> Vname -> Type -> Vname -> Proof
lem_tsubFV_self1 z z' (TRefn b w p) x = case b of
  TBool -> () 
  TInt  -> () 
lem_tsubFV_self1 z z' t x             = ()

{-@ lem_tsubFV_self2 :: z:Vname -> v:Value -> t:Type -> { x:Vname | x != z }
        -> { pf:_ | tsubFV z v (self t x) == self (tsubFV z v t) x } @-}
lem_tsubFV_self2 :: Vname -> Expr -> Type -> Vname -> Proof
lem_tsubFV_self2 z v (TRefn b w p) x = case b of
  TBool -> ()
  TInt  -> ()
lem_tsubFV_self2 z v t x             = ()

{-@ reflect selfify @-} 
{-@ selfify :: p:Pred -> b:Base -> z:Vname -> x:Vname 
        -> { p':Pred | fv p' == Set_cup (fv p) (Set_sng x) && 
                       TRefn b z p' == self (TRefn b z p) x } @-}
selfify :: Pred -> Base -> Vname -> Vname -> Pred
selfify p TBool z x = App (App (Prim And) p) (App (App (Prim Eqv) (BV z)) (FV x))
selfify p TInt  z x = App (App (Prim And) p) (App (App (Prim Eq)  (BV z)) (FV x))

{-@ reflect self @-}
{-@ self :: t:Type -> x:Vname -> { t':Type | Set_sub (free t') (Set_cup (free t) (Set_sng x)) &&
                                             tfreeBV t' == tfreeBV t && erase t == erase t' } @-}
self :: Type -> Vname -> Type
self (TRefn b z p) x = case b of
  TBool -> TRefn b z (App (App (Prim And) p) (App (App (Prim Eqv) (BV z)) (FV x)))
  TInt  -> TRefn b z (App (App (Prim And) p) (App (App (Prim Eq)  (BV z)) (FV x)))
self t             x = t

{-@ reflect equals @-}
{-@ equals :: b:Base -> { c:Prim | Set_emp (fv (Prim c)) && Set_emp (freeBV (Prim c)) } @-}
equals :: Base -> Prim
equals TBool = Eqv
equals TInt  = Eq

{-@ lem_tsubFV_value_self :: b:Base -> z:Vname -> p:Pred -> { x:Vname | not (Set_mem x (fv p)) }
        -> v:Value -> { pf:_ | tsubFV x v (self (TRefn b z p) x) 
                                == TRefn b z (App (App (Prim And) p)
                                                  (App (App (Prim (equals b)) (BV z)) v)) } @-}
lem_tsubFV_value_self :: Base -> Vname -> Pred -> Vname -> Expr -> Proof
lem_tsubFV_value_self b z p x v = toProof ( subFV x v p === p )


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
                -> ProofOf(HasType (Cons x t g) (FV x) (self t x))
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
                -> ProofOf(HasType g e t) @-} 

{-@ lazy typSize @-}
{-@ measure typSize @-}
{-@ typSize :: HasType -> { v:Int | v >= 0 } @-}
typSize :: HasType -> Int
typSize (TBC {})                             = 1
typSize (TIC {})                             = 1
typSize (TVar1 {})                           = 1
typSize (TVar2 _ _ _ p_x_b _ _)              = (typSize p_x_b)   + 1
typSize (TPrm {})                            = 1
typSize (TAbs _ _ _ _ _ _ _ p_e_b')          = (typSize p_e_b')  + 1
typSize (TApp _ _ _ _ _ p_e_bb' _ p_e'_b)    = (typSize p_e_bb') + (typSize p_e'_b)   + 1
typSize (TLet _ _ _ p_ex_b _ _ _ _ _ p_e_b') = (typSize p_ex_b)  + (typSize p_e_b')   + 1
typSize (TAnn _ _ _ p_e_b)                   = (typSize p_e_b)   + 1
typSize (TSub _ _ _ p_e_s _ _ p_s_t)         = (typSize p_e_s)   + (subtypSize p_s_t) + 1

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

-- edited SFunc 5/5/20: was -> { x2:Vname | not (in_Env x2 g) }. x2 is a BV so there's no
--     possibility for collision with the FV's in the environment g.
{-@ data Subtype where
    SBase :: g:Env -> v1:Vname -> b:Base -> p1:Pred -> v2:Vname -> p2:Pred 
               -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p2)) }
               -> ProofOf(Entails ( Cons y (TRefn b v1 p1) g) (unbind v2 y p2))
               -> ProofOf(Subtype g (TRefn b v1 p1) (TRefn b v2 p2))
 |  SFunc :: g:Env -> x1:Vname -> s1:Type -> x2:Vname -> s2:Type
               -> ProofOf(Subtype g s2 s1) -> t1:Type -> t2:Type
               -> { y:Vname | not (in_env y g) && not (Set_mem y (free t1)) 
                                               && not (Set_mem y (free t2)) }
               -> ProofOf(Subtype (Cons y s2 g) (unbindT x1 y t1) (unbindT x2 y t2))
               -> ProofOf(Subtype g (TFunc x1 s1 t1) (TFunc x2 s2 t2))
 |  SWitn :: g:Env -> e:Value  -> t_x:Type -> ProofOf(HasType g e t_x) 
               -> t:Type -> x:Vname -> t':Type -> ProofOf(Subtype g t (tsubBV x e t'))
               -> ProofOf(Subtype g t (TExists x t_x t'))
 |  SBind :: g:Env -> x:Vname -> t_x:Type -> t:Type -> {t':Type | not Set_mem x (tfreeBV t')} 
               -> { y:Vname | not (in_env y g) && not (Set_mem y (free t))
                                               && not (Set_mem y (free t')) }
               -> ProofOf(Subtype (Cons y t_x g) (unbindT x y t) t')
               -> ProofOf(Subtype g (TExists x t_x t) t')
@-}

{-@ lazy subtypSize @-}
{-@ measure subtypSize @-}
{-@ subtypSize :: Subtype -> { v:Int | v >= 0 } @-}
subtypSize :: Subtype -> Int
subtypSize (SBase {})                              = 1
subtypSize (SFunc _ _ _ _ _ p_s2_s1 _ _ _ p_t1_t2) = (subtypSize p_s2_s1) + (subtypSize p_t1_t2) + 1
subtypSize (SWitn _ _ _ p_e_tx _ _ _ p_t_t')       = (subtypSize p_t_t')  + (typSize p_e_tx)     + 1
subtypSize (SBind _ _ _ _ _ _ p_t_t')              = (subtypSize p_t_t')  + 1
 

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
--   the typing env downwards/leftwards. In order for a closing substitution to be
--   "well formed" it must be an element of the denotation the corresponding enivornment

data CSubst = CEmpty
            | CCons Vname Expr CSubst
  deriving (Show)
{-@ data CSubst  where
    CEmpty :: CSubst
  | CCons  :: x:Vname -> { v:Value | Set_emp (fv v) } -> { th:CSubst | not (in_csubst x th ) } 
                      -> { th':CSubst | bindsC th' == Set_cup (Set_sng x) (bindsC th) } @-}

{-@ reflect bindsC @-}
bindsC :: CSubst -> S.Set Vname
bindsC CEmpty         = S.empty
bindsC (CCons x v th) = S.union (S.singleton x) (bindsC th)

{-@ reflect in_csubst @-}
in_csubst :: Vname -> CSubst -> Bool
in_csubst x th = S.member x (bindsC th)

{-@ reflect bound_inC @-}
bound_inC :: Vname -> Expr -> CSubst -> Bool
bound_inC x v CEmpty                              = False
bound_inC x v (CCons y v' th) | (x == y)          = (v == v')
                              | otherwise         = bound_inC x v th

{-{-@ measure uniqueC @-}
uniqueC :: CSubst -> Bool
uniqueC CEmpty         = True
uniqueC (CCons x v th) = (uniqueC th) && not (S.member x (bindsC th))

{-@ lem_env_uniqueC :: th:CSubst -> { pf:_ | uniqueC th } @-}
lem_env_uniqueC :: CSubst -> Proof
lem_env_uniqueC CEmpty         = ()
lem_env_uniqueC (CCons x v th) = () ? lem_env_uniqueC th-}

{-@ reflect csubst @-}
csubst :: CSubst -> Expr -> Expr
csubst CEmpty         e = e
csubst (CCons x v th) e = csubst th (subFV x v e)

-- Idea: ctsubst th t = foldr (\(x,e) t' -> tsubFV x e t') t th 
{-@ reflect ctsubst @-}
ctsubst :: CSubst -> Type -> Type
ctsubst CEmpty         t = t
ctsubst (CCons x v th) t = ctsubst th (tsubFV x v t)

{-@ lem_unroll_ctsubst_left :: th:CSubst -> { x:Vname | not (in_csubst x th) } 
        -> { v_x:Value | Set_emp (fv v_x) } ->  t:Type
        -> { pf:_ | ctsubst (CCons x v_x th) t == tsubFV x v_x (ctsubst th t) } @-}
lem_unroll_ctsubst_left :: CSubst -> Vname -> Expr -> Type -> Proof
lem_unroll_ctsubst_left CEmpty           x v_x t = ()
lem_unroll_ctsubst_left (CCons y v_y th) x v_x t = toProof ( ctsubst (CCons x v_x (CCons y v_y th)) t
                                                         === ctsubst (CCons y v_y th) (tsubFV x v_x t)
                                                         === ctsubst th (tsubFV y v_y (tsubFV x v_x t))
                                                           ? lem_subFV_notin x v_x v_y
                                                           ? toProof ( subFV x v_x v_y === v_y )
                                                         === ctsubst th (tsubFV y (subFV x v_x v_y) (tsubFV x v_x t))
                                                           ? lem_commute_tsubFV y v_y x v_x t
                                                         === ctsubst th (tsubFV x v_x (tsubFV y v_y t))
                                                         === ctsubst (CCons x v_x th) (tsubFV y v_y t)
                                                           ? lem_unroll_ctsubst_left th x v_x (tsubFV y v_y t)
                                                         === tsubFV x v_x (ctsubst th (tsubFV y v_y t))
                                                         === tsubFV x v_x (ctsubst (CCons y v_y th) t) )

{-@ reflect concatCS @-}
{-@ concatCS :: th:CSubst -> { th':CSubst | Set_emp (Set_cap (bindsC th) (bindsC th')) }
                          -> { thC:CSubst | bindsC thC == Set_cup (bindsC th) (bindsC th') } @-}
concatCS :: CSubst -> CSubst -> CSubst
concatCS th CEmpty          = th
concatCS th (CCons x v th') = CCons x v (concatCS th th')

{-@ lem_in_csubst_concatCS :: th:CSubst -> { th':CSubst | Set_emp (Set_cap (bindsC th) (bindsC th')) }   
      -> x:Vname -> {pf:_ | (in_csubst x (concatCS th th')) <=> ((in_csubst x th) || (in_csubst x th'))} @-} 
lem_in_csubst_concatCS :: CSubst -> CSubst -> Vname -> Proof
lem_in_csubst_concatCS th CEmpty          x = () 
lem_in_csubst_concatCS th (CCons y v th') x = () ? lem_in_csubst_concatCS th th' x 

{-@ lem_binds_cons_concatCS :: th:CSubst -> {  th':CSubst | Set_emp (Set_cap (bindsC th) (bindsC th')) }
      -> { x:Vname | not (Set_mem x (bindsC th)) && not (Set_mem x (bindsC th')) } 
      -> { v_x:Value | Set_emp (fv v_x) }
      -> { pf:_ | Set_sub (bindsC (concatCS th th')) (bindsC (concatCS (CCons x v_x th) th')) &&
             bindsC (concatCS (CCons x v_x th) th') == Set_cup (Set_cup (bindsC th) (Set_sng x)) (bindsC th') } @-}
lem_binds_cons_concatCS :: CSubst -> CSubst -> Vname -> Expr -> Proof
lem_binds_cons_concatCS th CEmpty          x v_x = ()
lem_binds_cons_concatCS th (CCons y s th') x v_x = () ? lem_binds_cons_concatCS th th' x v_x


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

{-@ lem_csubst_bv :: th:CSubst -> y:Vname -> { pf:_ | csubst th (BV y) == BV y } @-}
lem_csubst_bv :: CSubst -> Vname -> Proof
lem_csubst_bv (CEmpty)       y = ()
lem_csubst_bv (CCons x v th) y = () ? lem_csubst_bv th y

{-@ lem_csubst_fv :: th:CSubst -> { y:Vname | not (in_csubst y th) } -> { pf:_ | csubst th (FV y) == FV y } @-} 
lem_csubst_fv :: CSubst -> Vname -> Proof
lem_csubst_fv (CEmpty)       y = ()
lem_csubst_fv (CCons x v th) y = () ? lem_csubst_fv th y 

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

{-@ lem_ctsubst_self_refn :: th:CSubst -> b:Base -> z:Vname -> p:Pred -> x:Vname 
        -> { pf:_ | ctsubst th (self (TRefn b z p) x) == 
		        TRefn b z (App (App (Prim And) (csubst th p)) 
                                       (App (App (Prim (equals b)) (BV z)) (csubst th (FV x)))) } @-}
lem_ctsubst_self_refn :: CSubst -> Base -> Vname -> Pred -> Vname -> Proof
lem_ctsubst_self_refn th b z p x  
          = toProof ( ctsubst th (self (TRefn b z p) x)
                  === ctsubst th (TRefn b z (App (App (Prim And) p) (App (App (Prim (equals b)) (BV z)) (FV x))))
                    ? lem_ctsubst_refn th b z (selfify p b z x)
                  === TRefn b z (csubst th (App (App (Prim And) p) (App (App (Prim (equals b)) (BV z)) (FV x))))
                    ? lem_csubst_app th (App (Prim And) p) (App (App (Prim (equals b)) (BV z)) (FV x))
                  === TRefn b z (App (csubst th (App (Prim And) p)) 
                                     (csubst th (App (App (Prim (equals b)) (BV z)) (FV x))))
                    ? lem_csubst_app th (Prim And) p
                    ? lem_csubst_app th (App (Prim (equals b)) (BV z)) (FV x)
                  === TRefn b z (App (App (csubst th (Prim And)) (csubst th p))
                                     (App (csubst th (App (Prim (equals b)) (BV z))) (csubst th (FV x))))
                    ? lem_csubst_prim th And 
                    ? lem_csubst_app th (Prim (equals b)) (BV z) 
                  === TRefn b z (App (App (Prim And) (csubst th p))
                                     (App (App (csubst th (Prim (equals b))) (csubst th (BV z))) (csubst th (FV x))))
                    ? lem_csubst_prim th (equals b)
                    ? lem_csubst_bv th z
                  === TRefn b z (App (App (Prim And) (csubst th p))
                                     (App (App (Prim (equals b)) (BV z)) (csubst th (FV x)))) ) 

{-@ lem_ctsubst_self_refn_notin :: th:CSubst -> b:Base -> z:Vname -> p:Pred -> { x:Vname | not (in_csubst x th) }
        -> { pf:_ | ctsubst th (self (TRefn b z p) x) == self (ctsubst th (TRefn b z p)) x } @-}
lem_ctsubst_self_refn_notin :: CSubst -> Base -> Vname -> Pred -> Vname -> Proof
lem_ctsubst_self_refn_notin th b z p x 
          = toProof ( ctsubst th (self (TRefn b z p) x) 
                    ? lem_ctsubst_self_refn th b z p x 
                  === TRefn b z (App (App (Prim And) (csubst th p))
                                (App (App (Prim (equals b)) (BV z)) (csubst th (FV x)))) 
                    ? lem_csubst_fv th x
                  === TRefn b z (App (App (Prim And) (csubst th p)) 
                                (App (App (Prim (equals b)) (BV z)) (FV x))) 
                  === TRefn b z (selfify (csubst th p) b z x)
                  === self (TRefn b z (csubst th p)) x
                    ? lem_ctsubst_refn th b z p
                  === self (ctsubst th (TRefn b z p)) x )

{-@ lem_ctsubst_self_notin :: th:CSubst -> t:Type -> { x:Vname | not (in_csubst x th) }
        -> { pf:_ | ctsubst th (self t x) == self (ctsubst th t) x } @-}
lem_ctsubst_self_notin :: CSubst -> Type -> Vname -> Proof
lem_ctsubst_self_notin th (TRefn b z p)      x = () ? lem_ctsubst_self_refn_notin th b z p x
lem_ctsubst_self_notin th (TFunc z t_z t')   x = () ? lem_ctsubst_func th z t_z t'
lem_ctsubst_self_notin th (TExists z t_z t') x = () ? lem_ctsubst_exis th z t_z t'


-- TODO: this. TODO: lem_ctsubst_fv
  --- Various properties of csubst/ctsubst and free/bound variables

{-@ lem_csubst_binds :: g:Env -> th:CSubst -> ProofOf(DenotesEnv g th) 
        -> { pf:_ | binds g == bindsC th } @-}
lem_csubst_binds :: Env -> CSubst -> DenotesEnv -> Proof
lem_csubst_binds g th DEmp                                            = ()
lem_csubst_binds g th (DExt g' th' den_g'_th' x t_x v_x den_th'tx_vx) 
    = () ? lem_csubst_binds g' th' den_g'_th'

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

{-@ lem_ctsubst_head_not_free :: x:Vname -> { v_x:Value | Set_emp (fv v_x) } 
        -> { th:CSubst | not (Set_mem x (bindsC th)) }
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
           -> { th:CSubst | not (Set_mem y (bindsC th)) } -> { p:Expr | not (Set_mem y (fv p)) }
           -> { pf:_ | csubst (CCons y v th) (unbind x y p) == subBV x v (csubst th p) } @-}
lem_csubst_and_unbind :: Vname -> Vname -> Expr -> BType -> HasBType -> CSubst -> Expr -> Proof
lem_csubst_and_unbind x y v b pf_v_b th p = toProof ( 
       csubst (CCons y (v  ? lem_fv_subset_bindsB BEmpty v b pf_v_b) th) (unbind x y p) 
   === csubst th (subFV y v (unbind x y p))
     ? lem_subFV_unbind x y v p
   === csubst th (subBV x v p)
     ? lem_csubst_subBV x v b pf_v_b th p
   === subBV x v (csubst th p) )

{-@ lem_ctsubst_and_unbindT :: x:Vname -> y:Vname
           -> v:Value -> bt:BType -> ProofOf(HasBType BEmpty v bt)
           -> { th:CSubst | not (Set_mem y (bindsC th)) } -> { t:Type | not (Set_mem y (free t)) }
           -> { pf:_ | ctsubst (CCons y v th) (unbindT x y t) == tsubBV x v (ctsubst th t) } @-}
lem_ctsubst_and_unbindT :: Vname -> Vname -> Expr -> BType -> HasBType 
           -> CSubst -> Type -> Proof
lem_ctsubst_and_unbindT x y v bt pf_v_b th t = toProof ( 
       ctsubst (CCons y (v ? lem_fv_subset_bindsB BEmpty v bt pf_v_b) th) (unbindT x y t)
   === ctsubst th (tsubFV y v (unbindT x y t))
     ? lem_tsubFV_unbindT x y v t
   === ctsubst th (tsubBV x v t)
     ? lem_ctsubst_tsubBV x v bt pf_v_b th t
   === tsubBV x v (ctsubst th t) )

{-@ lem_commute_csubst_subBV :: th:CSubst -> x:Vname -> v:Value -> e:Expr
           -> { pf:_ | csubst th (subBV x v e) == subBV x (csubst th v) (csubst th e) } @-} 
lem_commute_csubst_subBV :: CSubst -> Vname -> Expr -> Expr -> Proof
lem_commute_csubst_subBV (CEmpty)         x v e = () 
lem_commute_csubst_subBV (CCons y v_y th) x v e 
    = () ? lem_commute_subFV_subBV x v y v_y e
         ? lem_commute_csubst_subBV th x (subFV y v_y v) (subFV y v_y e)

{-@ lem_commute_ctsubst_tsubBV :: th:CSubst -> x:Vname -> v:Value -> t:Type
           -> { pf:_ | ctsubst th (tsubBV x v t) == tsubBV x (csubst th v) (ctsubst th t) } @-} 
lem_commute_ctsubst_tsubBV :: CSubst -> Vname -> Expr -> Type -> Proof
lem_commute_ctsubst_tsubBV (CEmpty)         x v t = () 
lem_commute_ctsubst_tsubBV (CCons y v_y th) x v t 
    = () ? lem_commute_tsubFV_tsubBV x v y v_y t
         ? lem_commute_ctsubst_tsubBV th x (subFV y v_y v) (tsubFV y v_y t)

{-@ lem_csubst_no_more_fv :: th:CSubst -> { v_x:Value | Set_sub (fv v_x) (bindsC th) }
        -> { pf:_ | Set_emp (fv (csubst th v_x)) } @-}
lem_csubst_no_more_fv :: CSubst -> Expr -> Proof
lem_csubst_no_more_fv CEmpty v_x           = ()
lem_csubst_no_more_fv (CCons y v_y th) v_x = () ? lem_csubst_no_more_fv th (subFV y v_y v_x)

{-@ lem_ctsubst_no_more_fv :: th:CSubst -> { t:Type | Set_sub (free t) (bindsC th) }
        -> { pf:_ | Set_emp (free (ctsubst th t)) } @-}
lem_ctsubst_no_more_fv :: CSubst -> Type -> Proof
lem_ctsubst_no_more_fv CEmpty           t = ()
lem_ctsubst_no_more_fv (CCons y v_y th) t = () ? lem_ctsubst_no_more_fv th (tsubFV y v_y t)

{-@ lem_csubst_subFV :: th:CSubst -> { x:Vname | not (in_csubst x th) } 
        -> { v_x:Value | Set_sub (fv v_x) (bindsC th) } -> e:Expr
        -> { pf:_ | csubst th (subFV x v_x e) == csubst th (subFV x (csubst th v_x) e) } @-}
lem_csubst_subFV :: CSubst -> Vname -> Expr -> Expr -> Proof
lem_csubst_subFV  CEmpty            x v_x e = ()
lem_csubst_subFV  (CCons y v_y th)  x v_x e = () ? toProof (-- case den_g_th of
  -- (DExt _ _ _ _ _ _ den_thty_vy) -> () ? toProof (
        csubst (CCons y v_y th) (subFV x (csubst (CCons y v_y th) v_x 
                                    ? lem_csubst_value (CCons y v_y th) v_x) e)
        ? lem_csubst_value (CCons y v_y th) v_x
    === csubst th (subFV y v_y (subFV x (csubst (CCons y v_y th) v_x) e))
        ? lem_commute_subFV x (csubst (CCons y v_y th) v_x) y v_y e
        ? lem_subFV_value y v_y (csubst (CCons y v_y th) v_x)
    === csubst th (subFV x (subFV y v_y (csubst (CCons y v_y th) v_x)) (subFV y v_y e))   
        ? lem_csubst_no_more_fv (CCons y v_y th) v_x
    === csubst th (subFV x (csubst (CCons y v_y th) v_x) (subFV y v_y e))
        ? lem_csubst_value th (subFV y v_y v_x ? lem_subFV_value y v_y v_x)
    === csubst th (subFV x (csubst th (subFV y v_y v_x)) (subFV y v_y e))
        ? lem_csubst_subFV th x (subFV y v_y v_x) (subFV y v_y e)
    === csubst th (subFV x (subFV y v_y v_x) (subFV y v_y e))
        ? lem_commute_subFV x v_x y v_y e 
    === csubst th (subFV y v_y (subFV x v_x e))
    === csubst (CCons y v_y th) (subFV x v_x e) )
    
{-@ lem_ctsubst_tsubFV :: th:CSubst -> { x:Vname | not (in_csubst x th) } 
        -> { v_x:Value | Set_sub (fv v_x) (bindsC th) } -> t:Type
        -> { pf:_ | ctsubst th (tsubFV x v_x t) == ctsubst th (tsubFV x (csubst th v_x) t) } @-}
lem_ctsubst_tsubFV :: CSubst -> Vname -> Expr -> Type -> Proof
lem_ctsubst_tsubFV  CEmpty            x v_x t = ()
lem_ctsubst_tsubFV  (CCons y v_y th)  x v_x t = () ? toProof (-- case den_g_th of
  -- (DExt _ _ _ _ _ _ den_thty_vy) -> () ? toProof (
        ctsubst (CCons y v_y th) (tsubFV x (csubst (CCons y v_y th) v_x 
                                     ? lem_csubst_value (CCons y v_y th) v_x) t)
        ? lem_csubst_value (CCons y v_y th) v_x
    === ctsubst th (tsubFV y v_y (tsubFV x (csubst (CCons y v_y th) v_x) t))
        ? lem_commute_tsubFV x (csubst (CCons y v_y th) v_x) y v_y t
        ? lem_subFV_value y v_y (csubst (CCons y v_y th) v_x)
    === ctsubst th (tsubFV x (subFV y v_y (csubst (CCons y v_y th) v_x)) (tsubFV y v_y t))   
        ? lem_csubst_no_more_fv (CCons y v_y th) v_x
    === ctsubst th (tsubFV x (csubst (CCons y v_y th) v_x) (tsubFV y v_y t))
        ? lem_csubst_value th (subFV y v_y v_x ? lem_subFV_value y v_y v_x)
    === ctsubst th (tsubFV x (csubst th (subFV y v_y v_x)) (tsubFV y v_y t))
        ? lem_ctsubst_tsubFV th x (subFV y v_y v_x) (tsubFV y v_y t)
    === ctsubst th (tsubFV x (subFV y v_y v_x) (tsubFV y v_y t))
        ? lem_commute_tsubFV x v_x y v_y t 
    === ctsubst th (tsubFV y v_y (tsubFV x v_x t))
    === ctsubst (CCons y v_y th) (tsubFV x v_x t) )
   
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

  --- Closing Substitutions and Technical Operations


{-@ reflect change_varCS @-}
{-@ change_varCS :: th:CSubst ->  { x:Vname | in_csubst x th } 
        -> { y:Vname | y == x || not (in_csubst y th) } 
        -> { th':CSubst | bindsC th' == Set_cup (Set_sng y) (Set_dif (bindsC th) (Set_sng x))} @-} 
change_varCS :: CSubst -> Vname -> Vname -> CSubst
change_varCS CEmpty           x y = CEmpty
change_varCS (CCons z v_z th) x y | ( x == z ) = CCons y v_z th
                                  | otherwise  = CCons z v_z (change_varCS th x y)

{-@ reflect remove_fromCS @-}
{-@ remove_fromCS :: th:CSubst -> { x:Vname | in_csubst x th}
        -> { th':CSubst | bindsC th' == Set_dif (bindsC th) (Set_sng x) } @-}
remove_fromCS :: CSubst -> Vname -> CSubst
remove_fromCS (CCons z v_z th) x | ( x == z ) = th
                                 | otherwise  = CCons z v_z (remove_fromCS th x)

        -- -> { e:Expr | Set_sub (fv e) (bindsC th ) && ( x == y || not (Set_mem y (fv e))) }
{-@ lem_change_var_in_csubst :: th:CSubst -> { x:Vname | in_csubst x th }
        -> { y:Vname  | y == x || not (in_csubst y th) }
        -> { e:Expr   | x == y || not (Set_mem y (fv e)) }
        -> { pf:Proof | csubst th e == csubst (change_varCS th x y) (subFV x (FV y) e) } @-}
lem_change_var_in_csubst :: CSubst -> Vname -> Vname -> Expr -> Proof
lem_change_var_in_csubst (CCons z v_z th) x y e = case (x == z) of
  (True)  -> toProof ( csubst (change_varCS (CCons z v_z th) x y) (subFV x (FV y) e)
                   === csubst (CCons y v_z th) (subFV x (FV y) e)
                   === csubst th (subFV y v_z (subFV x (FV y) e)) 
                     ? lem_chain_subFV x y v_z e 
                   === csubst th (subFV x v_z e)	
                   === csubst (CCons z v_z th) e  ) 
  (False) -> toProof ( csubst (change_varCS (CCons z v_z th) x y) (subFV x (FV y) e)
                   === csubst (CCons z v_z (change_varCS th x y)) (subFV x (FV y) e)
                   === csubst (change_varCS th x y) (subFV z v_z (subFV x (FV y) e))
                     ? lem_commute_subFV x (FV y) z v_z e
                   === csubst (change_varCS th x y) (subFV x (subFV z v_z (FV y)) (subFV z v_z e)) 
                     ? lem_change_var_in_csubst th x y (subFV z v_z e) 
                   === csubst th (subFV z v_z e)
                   === csubst (CCons z v_z th) e )

        -- -> { t:Type | Set_sub (free t) (bindsC th ) && ( x == y || not (Set_mem y (free t))) }
{-@ lem_change_var_in_ctsubst :: th:CSubst -> { x:Vname | in_csubst x th }
        -> { y:Vname  | y == x || not (in_csubst y th) }
        -> { t:Type   | x == y || not (Set_mem y (free t)) }
        -> { pf:Proof | ctsubst th t == ctsubst (change_varCS th x y) (tsubFV x (FV y) t) } @-}
lem_change_var_in_ctsubst :: CSubst -> Vname -> Vname -> Type -> Proof
lem_change_var_in_ctsubst (CCons z v_z th) x y t = case (x == z) of
  (True)  -> () ? lem_chain_tsubFV x y v_z t 
  (False) -> () ? lem_commute_tsubFV x (FV y) z v_z t
                ? lem_change_var_in_ctsubst th x y (tsubFV z v_z t)

{-@ lem_change_var_back :: th:CSubst -> { x:Vname | in_csubst x th }
        -> { y:Vname | (y == x || not (in_csubst y th)) } 
        -> { pf:Proof | change_varCS (change_varCS th x y) y x == th } @-}
lem_change_var_back :: CSubst -> Vname -> Vname -> Proof
lem_change_var_back CEmpty           x y              = ()
lem_change_var_back (CCons z v_z th) x y | ( x == z ) = ()
                                         | otherwise  = () ? lem_change_var_back th x y

--        -> { e:Expr | Set_sub (fv e) (bindsC th) && not (Set_mem x (fv e)) }
{-@ lem_remove_csubst :: th:CSubst -> { x:Vname | in_csubst x th}
        -> { e:Expr | not (Set_mem x (fv e)) }
        -> { pf:Proof | csubst th e == csubst (remove_fromCS th x) e } @-}
lem_remove_csubst :: CSubst -> Vname -> Expr -> Proof
lem_remove_csubst (CCons z v_z th) x e = case ( x == z ) of
  (True)  -> toProof ( csubst (remove_fromCS (CCons x v_z th) x) e
                   === csubst th e  
                   === csubst th (subFV x v_z e)
                   === csubst (CCons x v_z th) e)
  (False) -> toProof ( csubst (remove_fromCS (CCons z v_z th) x) e
                   === csubst (CCons z v_z (remove_fromCS th x)) e
                     ? lem_remove_csubst th x (subFV z v_z e)
                   === csubst (CCons z v_z th) e )

{-@ lem_remove_ctsubst :: th:CSubst -> { x:Vname | in_csubst x th}
        -> { t:Type | not (Set_mem x (free t)) }
        -> { pf:Proof | ctsubst th t == ctsubst (remove_fromCS th x) t } @-}
lem_remove_ctsubst :: CSubst -> Vname -> Type -> Proof
lem_remove_ctsubst (CCons z v_z th) x t = case ( x == z ) of
  (True)  -> toProof ( ctsubst (remove_fromCS (CCons x v_z th) x) t
                   === ctsubst th t  
                   === ctsubst th (tsubFV x v_z t)
                   === ctsubst (CCons x v_z th) t)
  (False) -> toProof ( ctsubst (remove_fromCS (CCons z v_z th) x) t
                   === ctsubst (CCons z v_z (remove_fromCS th x)) t
                     ? lem_remove_ctsubst th x (tsubFV z v_z t)
                   === ctsubst (CCons z v_z th) t )


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
              -> ProofOf(Denotes (TExists x t_x t) v)  @-} -- @- }

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
               -> { v:Value | Set_emp (fv v) } -> ProofOf(Denotes (ctsubst th t) v)
               -> ProofOf(DenotesEnv (Cons x t g) (CCons x v th)) @-}

{-@ lem_binds_env_th :: g:Env -> th:CSubst -> ProofOf(DenotesEnv g th) -> { pf:_ | binds g == bindsC th } @-}
lem_binds_env_th :: Env -> CSubst -> DenotesEnv -> Proof
lem_binds_env_th g th DEmp                                      = ()
lem_binds_env_th g th (DExt g' th' den_g'_th' x t v den_th't_v) = () ? lem_binds_env_th g' th' den_g'_th'

{-@ lem_change_var_denote :: th:CSubst -> t:Type -> { v:Value | Set_emp (fv v) }
      -> ProofOf(Denotes (ctsubst th t) v) -> { x:Vname | (in_csubst x th) } 
      -> { y:Vname | y == x || ( not (in_csubst y th) && not (Set_mem y (free t))) } 
      -> ProofOf(Denotes (ctsubst (change_varCS th x y) (tsubFV x (FV y) t)) v ) @-}
lem_change_var_denote :: CSubst -> Type -> Expr -> Denotes -> Vname -> Vname -> Denotes
lem_change_var_denote th t v den_tht_v x y = den_tht_v ? lem_change_var_in_ctsubst th x y t

{-@ lem_remove_var_denote :: th:CSubst -> t:Type -> { v:Value | Set_emp (fv v) }
      -> ProofOf(Denotes (ctsubst th t) v) -> { x:Vname | in_csubst x th && not (Set_mem x (free t)) } 
      -> ProofOf(Denotes (ctsubst (remove_fromCS th x) t) v) @-}
lem_remove_var_denote :: CSubst -> Type -> Expr -> Denotes -> Vname -> Denotes
lem_remove_var_denote th t v den_tht_v x = den_tht_v ? lem_remove_ctsubst th x t

{-@ lem_change_var_denote_env :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
      -> th:CSubst -> ProofOf(DenotesEnv (concatE (Cons x t_x g) g') th)
      -> { y:Vname | (y == x || not (in_csubst y th)) && not (in_env y g) && not (in_env y g') } 
      -> ProofOf(DenotesEnv (concatE (Cons y t_x g) (esubFV x (FV y) g')) (change_varCS th x y)) @-}
lem_change_var_denote_env :: Env -> Vname -> Type -> Env -> WFEnv -> CSubst 
                                 -> DenotesEnv -> Vname -> DenotesEnv
lem_change_var_denote_env g x t_x Empty            p_env_wf th den_env_th y  = case den_env_th of
  (DExt env' th' den_env'_th' _x _tx v_x den_th'tx_vx) -> DExt env' th' den_env'_th' y t_x v_x den_th'tx_vx
lem_change_var_denote_env g x_ t_x (Cons z t_z g') p_env_wf th den_env_th y_ = case den_env_th of
  (DExt env' th' den_env'_th' _z _tz v_z den_th'tz_vz) -- env' == concatE (Cons x t_x g) g'
    -> DExt (concatE (Cons y t_x g) (esubFV x (FV y) g')) (change_varCS th' x y) den_env'y_th'y
            z (tsubFV x (FV y) t_z) v_z den_th'ytzy_vz
      where
        (WFEBind _ p_env'_wf _ _ p_env'_tz) = p_env_wf -- tODO remove this
        x              = x_ ? lem_binds_env_th (concatE (Cons x_ t_x g) g') th' den_env'_th'
                            ? lem_in_env_concat g g' x_
        y              = y_ ? lem_binds_env_th (concatE (Cons x t_x g) g') th' den_env'_th' 
                            ? lem_in_env_concat g g' y_
                            ? lem_in_env_concat (Cons x t_x g) g' y_
                            ? lem_free_subset_binds (concatE (Cons x t_x g) g') t_z p_env'_tz 
        den_env'y_th'y = lem_change_var_denote_env g x t_x g' p_env'_wf th' den_env'_th' y 
        den_th'ytzy_vz = lem_change_var_denote th' t_z v_z den_th'tz_vz x y

{-@ lem_remove_var_denote_env :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
       -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
       -> ProofOf(WFEnv (concatE g g'))
       -> th:CSubst -> ProofOf(DenotesEnv (concatE (Cons x t_x g) g') th)
       -> ProofOf(DenotesEnv (concatE g g') (remove_fromCS th x )) @-}
lem_remove_var_denote_env :: Env -> Vname -> Type -> Env -> WFEnv -> CSubst 
                                 -> DenotesEnv -> DenotesEnv
lem_remove_var_denote_env g x  t_x Empty           p_g'g_wf  th den_env_th = case den_env_th of
  (DExt env' th' den_env'_th'_ _ _tx v_x den_th'tx_vx) -> den_env'_th'
            ? toProof ( remove_fromCS (CCons x v_x th') x === th' ) 
            ? toProof ( CCons x v_x th' === th )
      where
        den_env'_th' = den_env'_th'_ ? lem_binds_env_th env' th' den_env'_th'_
lem_remove_var_denote_env g x_ t_x (Cons z t_z g') p_zg'g_wf th den_env_th = case den_env_th of
  (DEmp)                                               -> impossible "th != CEmpty"
  (DExt env' th' den_env'_th' _z _tz v_z den_th'tz_vz) -- env' == concatE (Cons x t_x g) g' 
    -> DExt (concatE g g') (remove_fromCS th' x) den_env''_th'' z t_z v_z den_th''tz_vz
            ? toProof ( remove_fromCS (CCons z v_z th') x === CCons z v_z (remove_fromCS th' x) )
            ? toProof ( CCons z v_z th' === th )
      where
        (WFEBind _ p_g'g_wf _ _ p_g'g_tz) = p_zg'g_wf
        x              = x_ ? lem_binds_env_th (concatE (Cons x_ t_x g) g') th' den_env'_th'
                            ? lem_in_env_concat g g' x_ 
                            ? lem_in_env_concat g (Cons z t_z g') x_
                            ? lem_free_bound_in_env (concatE g g') t_z p_g'g_tz x_
        den_env''_th'' = lem_remove_var_denote_env g x t_x g' p_g'g_wf th' den_env'_th'
        den_th''tz_vz  = lem_remove_var_denote th' t_z v_z den_th'tz_vz x



{-@ lem_csubst_hasbtype' :: g:Env -> e:Expr -> t:Type -> ProofOf(HasBType (erase_env g) e (erase t))
        -> th:CSubst -> ProofOf(DenotesEnv g th) -> ProofOf(HasBType BEmpty (csubst th e) (erase t)) @-} 
lem_csubst_hasbtype' :: Env -> Expr -> Type -> HasBType -> CSubst -> DenotesEnv -> HasBType
lem_csubst_hasbtype' Empty           e t p_e_t th den_g_th = case den_g_th of 
  (DEmp)                                           -> p_e_t ? lem_binds_env_th Empty th den_g_th
lem_csubst_hasbtype' (Cons x t_x g') e t p_e_t th den_g_th = case den_g_th of
  (DExt g' th' den_g'_th' _x _tx v_x den_th'tx_vx) -> p_the_t
    where
      p_emp_vx_tx = get_btyp_from_den (ctsubst th' t_x) v_x den_th'tx_vx
                                      ? lem_erase_ctsubst th' t_x
      p_g'_vx_tx  = lem_weaken_many_btyp BEmpty (erase_env g') v_x (erase t_x) p_emp_vx_tx
                                         ? lem_empty_concatB (erase_env g')
      p_evx_t     = lem_subst_btyp (erase_env g') BEmpty x v_x (erase t_x) p_g'_vx_tx -- ? lem_empty_concatE g')
                                   e (erase t) p_e_t ? lem_erase_tsubFV x v_x t
      p_the_t     = lem_csubst_hasbtype' g' (subFV x v_x e) (tsubFV x v_x t) p_evx_t th' den_g'_th' 

