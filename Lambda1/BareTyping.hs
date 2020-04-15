{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-}
{- @ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module BareTyping where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Syntax
import Environments
import Semantics

-- we must force these into scope for LH
semantics = (Step, EvalsTo)

-----------------------------------------------------------------------------
----- | JUDGEMENTS : the Bare-Typing Relation and the Typing Relation
-----------------------------------------------------------------------------

data HasBTypeP where
    HasBType :: BEnv -> Expr -> BType -> HasBTypeP 

data HasBType where
    BTBC   :: BEnv -> Bool -> HasBType
    BTIC   :: BEnv -> Int -> HasBType
    BTVar1 :: BEnv -> Vname -> BType -> HasBType 
    BTVar2 :: BEnv -> Vname -> BType -> HasBType -> Vname -> BType -> HasBType
    BTPrm  :: BEnv -> Prim -> HasBType
    BTAbs  :: BEnv -> Vname -> BType -> Expr -> BType -> Vname -> HasBType -> HasBType
    BTApp  :: BEnv -> Expr -> BType -> BType -> HasBType 
              -> Expr -> HasBType -> HasBType
    BTLet  :: BEnv -> Expr -> BType -> HasBType -> Vname -> Expr
              -> BType -> Vname -> HasBType -> HasBType
    BTAnn  :: BEnv -> Expr -> BType -> Type -> HasBType -> HasBType

{-@ data HasBType where
    BTBC   :: g:BEnv -> b:Bool -> ProofOf(HasBType g (Bc b) (BTBase TBool))
 |  BTIC   :: g:BEnv -> n:Int -> ProofOf(HasBType g (Ic n) (BTBase TInt))
 |  BTVar1 :: g:BEnv -> { x:Vname | not (in_envB x g) } -> b:BType 
                -> ProofOf(HasBType (BCons x b g) (FV x) b)
 |  BTVar2 :: g:BEnv -> { x:Vname | in_envB x g } -> b:BType -> ProofOf(HasBType g (FV x) b)
                -> { y:Vname | y != x && not (in_envB y g) } -> b':BType 
                -> ProofOf(HasBType (BCons y b' g) (FV x) b)
 |  BTPrm  :: g:BEnv -> c:Prim  -> ProofOf(HasBType g (Prim c) (erase (ty c)))
 |  BTAbs  :: g:BEnv -> x:Vname -> b:BType -> e:Expr -> b':BType
                -> { y:Vname | not (in_envB y g) && not (Set_mem y (fv e)) }
                -> ProofOf(HasBType (BCons y b g) (unbind x y e) b')
                -> ProofOf(HasBType g (Lambda x e) (BTFunc b b'))
 |  BTApp  :: g:BEnv -> e:Expr -> b:BType -> b':BType
                -> ProofOf(HasBType g e (BTFunc b b')) 
                -> e':Expr -> ProofOf(HasBType g e' b) 
                -> ProofOf(HasBType g (App e e') b')
 |  BTLet  :: g:BEnv -> e_x:Expr -> b:BType -> ProofOf(HasBType g e_x b)
                -> x:Vname -> e:Expr -> b':BType 
                -> { y:Vname | not (in_envB y g) && not (Set_mem y (fv e)) }
                -> ProofOf(HasBType (BCons y b g) (unbind x y e) b')
                -> ProofOf(HasBType g (Let x e_x e) b')
 |  BTAnn  :: g:BEnv -> e:Expr -> b:BType 
                -> { t1:Type | (erase t1 == b) && Set_sub (free t1) (bindsB g) && Set_emp (tfreeBV t1) }
                -> ProofOf(HasBType g e b) -> ProofOf(HasBType g (Annot e t1) b)  @-} 

-- TODO: refactor without impossible
{-@ simpleBTVar :: g:BEnv -> { x:Vname | in_envB x g} -> { t:BType | bound_inB x t g } 
                -> ProofOf(HasBType g (FV x) t) @-}
simpleBTVar :: BEnv -> Vname -> BType -> HasBType
simpleBTVar g x t = case g of
  (BCons y s g') ->  case (x == y, t == s) of   -- g = Empty is impossible
        (True, True) -> BTVar1 g' x t           -- x = y but t != s is impossible
        (False, _)   -> BTVar2 g' x t (simpleBTVar g' x t) y s

-- Lemma. All free variables in a (bare) typed expression are bound in the (bare) environment
{-@ lem_fv_bound_in_benv :: g:BEnv -> e:Expr -> t:BType -> ProofOf(HasBType g e t)
                -> { x:Vname | not (in_envB x g) }
                -> { pf:_ | not (Set_mem x (fv e)) } @-}
lem_fv_bound_in_benv :: BEnv -> Expr -> BType -> HasBType -> Vname -> Proof
lem_fv_bound_in_benv g e t (BTBC _g b) x      = ()
lem_fv_bound_in_benv g e t (BTIC _g n) x      = ()
lem_fv_bound_in_benv g e t (BTVar1 _ y _t) x  = ()
lem_fv_bound_in_benv g e t (BTVar2 _ y _t p_y_t z t') x = ()
lem_fv_bound_in_benv g e t (BTPrm _g c) x     = ()
lem_fv_bound_in_benv g e t (BTAbs _g y t_y e' t' y' p_e'_t') x 
    = case ( x == y' ) of
        (True)  -> ()
        (False) -> () ? lem_fv_bound_in_benv (BCons y' t_y g) (unbind y y' e') t' p_e'_t' x
lem_fv_bound_in_benv g e t (BTApp _g e1 t_y t' p_e1_tyt' e2 p_e2_ty) x 
    = () ? lem_fv_bound_in_benv g e1 (BTFunc t_y t') p_e1_tyt' x
         ? lem_fv_bound_in_benv g e2 t_y p_e2_ty x
lem_fv_bound_in_benv g e t (BTLet _g e_y t_y p_ey_ty y e' t' y' p_e'_t') x 
    = case ( x == y' ) of
        (True)  -> () ? lem_fv_bound_in_benv g e_y t_y p_ey_ty x
        (False) -> () ? lem_fv_bound_in_benv g e_y t_y p_ey_ty x
                      ? lem_fv_bound_in_benv (BCons y' t_y g) (unbind y y' e') t' p_e'_t' x
lem_fv_bound_in_benv g e t (BTAnn _g e' _t ann_t p_e'_t) x 
    = () ? lem_fv_bound_in_benv g e' t p_e'_t x


-------------------------------------------------------------------------
----- | REFINEMENT TYPES of BUILT-IN PRIMITIVES
-------------------------------------------------------------------------

{-@ reflect tybc @-} -- Refined Constant Typing
tybc :: Bool -> Type
tybc True  = TRefn TBool 1 (App (App (Prim Eqv) (BV 1)) (Bc True))
tybc False = TRefn TBool 1 (App (App (Prim Eqv) (BV 1)) (Bc False))

{-@ reflect tyic @-}
tyic :: Int -> Type
tyic n = TRefn TInt 1 (App (App (Prim Eq) (BV 1)) (Ic n))

{-@ reflect refn_pred @-} -- 
refn_pred :: Prim -> Pred
refn_pred And      = App (App (Prim Eqv) (FV 3)) 
                               (App (App (Prim And) (FV 1)) (FV 2)) 
refn_pred Or       = App (App (Prim Eqv) (FV 3)) 
                               (App (App (Prim Or) (FV 1)) (FV 2)) 
refn_pred Not      = App (App (Prim Eqv) (FV 3)) 
                           (App (Prim Not) (FV 1)) 
refn_pred Eqv      = App (App (Prim Eqv) (FV 3))
                               (App (App (Prim Or) 
                                    (App (App (Prim And) (FV 1)) (FV 2)))
                                    (App (App (Prim And) (App (Prim Not) (FV 1)))
                                         (App (Prim Not) (FV 2))))
refn_pred Leq      = App (App (Prim Eqv) (FV 3))
                               (App (App (Prim Leq) (FV 1)) (FV 2)) 
refn_pred (Leqn n) = App (App (Prim Eqv) (FV 3))
                           (App (App (Prim Leq) (Ic n)) (FV 2)) 
refn_pred Eq       = App (App (Prim Eqv) (FV 3))
                               (App (App (Prim Eq) (FV 1)) (FV 2))
refn_pred (Eqn n)  = App (App (Prim Eqv) (FV 3))
                           (App (App (Prim Eq) (Ic n)) (FV 2))

{-@ reflect ty @-} -- Primitive Typing
ty :: Prim -> Type
ty And      = TFunc 1 (TRefn TBool 4 (Bc True)) 
                  (TFunc 2 (TRefn TBool 5 (Bc True)) 
                      (TRefn TBool 3 
                          (App (App (Prim Eqv) (BV 3)) 
                               (App (App (Prim And) (BV 1)) (BV 2)) )))
ty Or       = TFunc 1 (TRefn TBool 4 (Bc True)) 
                  (TFunc 2 (TRefn TBool 5 (Bc True)) 
                      (TRefn TBool 3 
                          (App (App (Prim Eqv) (BV 3)) 
                               (App (App (Prim Or) (BV 1)) (BV 2)) )))
ty Not      = TFunc 1 (TRefn TBool 4 (Bc True)) 
                  (TRefn TBool 3
                      (App (App (Prim Eqv) (BV 3)) 
                           (App (Prim Not) (BV 1)) ))
ty Eqv      = TFunc 1 (TRefn TBool 4 (Bc True))
                  (TFunc 2 (TRefn TBool 5 (Bc True))  
                      (TRefn TBool 3
                          (App (App (Prim Eqv) (BV 3))
                               (App (App (Prim Or) 
                                    (App (App (Prim And) (BV 1)) (BV 2)))
                                    (App (App (Prim And) (App (Prim Not) (BV 1)))
                                         (App (Prim Not) (BV 2)))))))
ty Leq      = TFunc 1 (TRefn TInt 4 (Bc True)) 
                  (TFunc 2 (TRefn TInt 5 (Bc True)) 
                      (TRefn TBool 3
                          (App (App (Prim Eqv) (BV 3))
                               (App (App (Prim Leq) (BV 1)) (BV 2)) )))
ty (Leqn n) = TFunc 2 (TRefn TInt 5 (Bc True)) 
                  (TRefn TBool 3
                      (App (App (Prim Eqv) (BV 3))
                           (App (App (Prim Leq) (Ic n)) (BV 2)) )) 
ty Eq       = TFunc 1 (TRefn TInt 4 (Bc True)) 
                  (TFunc 2 (TRefn TInt 5 (Bc True)) 
                      (TRefn TBool 3
                          (App (App (Prim Eqv) (BV 3))
                               (App (App (Prim Eq) (BV 1)) (BV 2)) )))
ty (Eqn n)  = TFunc 2 (TRefn TInt 5 (Bc True)) 
                  (TRefn TBool 3
                      (App (App (Prim Eqv) (BV 3))
                           (App (App (Prim Eq) (Ic n)) (BV 2)) ))

