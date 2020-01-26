{-# LANGUAGE GADTs #-}

-- The following module presents a mechanization of the proofs of type
-- soundness and termination for a Simply Typed Lambda Calculus
-- and is based on Lecture notes "Well-typed Programs Don't Go Wrong"
-- and "Type Soundness and Termination in One Easy Lemma" by Nadia
-- Polikarpova for CSE 130 at UC San Diego.

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--short-names" @-}

module Semantics where

import Language.Haskell.Liquid.ProofCombinators 
import Syntax

---------------------------------------------------------------------------
----- | PRELIMINARIES
---------------------------------------------------------------------------

{-@ measure propOf :: a -> b @-}
{-@ type ProofOf E = { proofObj:_ | propOf proofObj = E } @-}

----------------------------------------------------------------------
----- INFERENCE RULES (proof trees)
----------------------------------------------------------------------

  --- OPERATIONAL SEMANTICS (BIG Step)

-- E-Num env; n  ==> n
-- E-Var env; x ==> v 
-- E-Add env; e1 + e2 ==> n if env1; e1 ==> n1 etc...
-- E-Abs env; (\x. e) ==> <E,x,e>
-- E-App env; e1 e2 ==> v if env; e1 ==> <env',x,e>, 
--                           env; e2 ==> v2, and (Cons x v2 env) e ==> v

data BStepP where
    BStep :: Env -> Expr -> Value -> BStepP

data BStep where
    ENum :: Env -> Int -> BStep
    EVar :: Env -> Vname -> Value -> BStep
    EAdd :: Env -> Expr -> Int -> BStep -> Expr -> Int -> BStep -> Int -> BStep
    EAbs :: Env -> Vname -> Expr -> BStep
    EApp :: Env -> Expr -> Env -> Vname -> Expr -> BStep -> Expr -> Value -> BStep
                 -> Value -> BStep -> BStep

{-@ data BStep where 
    ENum :: env:Env -> n:Int -> ProofOf(BStep env (N n) (VNum n))
 |  EVar :: env:Env -> x:Vname -> { v:Value | bound_in x v env } -> ProofOf(BStep env (V x) v)
 |  EAdd :: env:Env -> e1:Expr -> n1:Int -> ProofOf(BStep env e1 (VNum n1))
              -> e2:Expr -> n2:Int -> ProofOf(BStep env e2 (VNum n2))
              -> { n:Int | n == n1 + n2 } -> ProofOf(BStep env (Add e1 e2) (VNum n))
 |  EAbs :: env:Env -> x:Vname -> e:Expr 
              -> ProofOf(BStep env (Lambda x e) (VCls env x e))
 |  EApp :: env:Env -> e1:Expr -> env':Env -> x:Vname -> e:Expr
              -> ProofOf(BStep env e1 (VCls env' x e))
              -> e2:Expr -> v2:Value -> ProofOf(BStep env e2 v2)
              -> v:Value -> ProofOf(BStep (Cons x v2 env') e v)
              -> ProofOf(BStep env (App e1 e2) v) @-} -- @-}

----- the Typing Relation

data HasTypeP where
    HasType :: Ctx -> Expr -> Type -> HasTypeP -- HasType G e t means G |- e : t

data HasType where 
    TNum :: Ctx -> Int -> HasType
    TVar :: Ctx -> Vname -> Type -> HasType
    TAdd :: Ctx -> Expr -> HasType -> Expr -> HasType -> HasType
    TAbs :: Ctx -> Vname -> Type -> Expr -> Type -> HasType -> HasType
    TApp :: Ctx -> Expr -> Type -> Type -> HasType 
              -> Expr -> HasType -> HasType

{-@ data HasType where
    TNum :: g:Ctx -> n:Int -> ProofOf(HasType g (N n) TInt)
 |  TVar :: g:Ctx -> x:Vname -> {t:Type | bound_in_ctx x t g} -> ProofOf(HasType g (V x) t)
 |  TAdd :: g:Ctx -> e1:Expr -> ProofOf(HasType g e1 TInt) -> e2:Expr 
                -> ProofOf(HasType g e2 TInt) -> ProofOf(HasType g (Add e1 e2) TInt)
 |  TAbs :: g:Ctx -> x:Vname -> t:Type -> e:Expr -> t':Type
                -> ProofOf(HasType (CCons x t g) e t')
                -> ProofOf(HasType g (Lambda x e) (TFunc t t'))
 |  TApp :: g:Ctx -> e1:Expr -> t:Type -> t':Type -> ProofOf(HasType g e1 (TFunc t t')) 
                -> e2:Expr -> ProofOf(HasType g e2 t) 
                -> ProofOf(HasType g (App e1 e2) t')  @-} -- @-}

data WBValueP where
    WBValue :: Value -> Type -> WBValueP

data WBValue where
    WBVNum :: Int -> WBValue
    WBVCls :: Env -> Vname -> Expr -> Type -> Type 
                -> (Value -> WBValue -> (Value, (BStep, WBValue))) -> WBValue
  
{-@ data WBValue where
    WBVNum :: n:Int -> ProofOf(WBValue (VNum n) TInt)
 |  WBVCls :: env:Env -> x:Vname -> e:Expr -> t:Type -> t':Type
        -> (v:Value -> ProofOf(WBValue v t) 
             -> (Value, (BStep, WBValue))<{\v' pfs -> 
                    (propOf (fst pfs) == BStep (Cons x v env) e v') && (propOf (snd pfs) == WBValue v' t')}>)
        -> ProofOf(WBValue (VCls env x e) (TFunc t t')) @-}

data WBEnvP where
    WBEnv :: Env -> Ctx -> WBEnvP

data WBEnv where
    WBEmpty :: WBEnv
    WBCons  :: Env -> Vname -> Value -> Type -> Ctx -> WBValue -> WBEnv -> WBEnv

{-@ data WBEnv where
    WBEmpty :: ProofOf(WBEnv Empty CEmpty)
 |  WBCons  :: env:Env -> x:Vname -> v:Value -> t:Type -> g:Ctx
                -> ProofOf(WBValue v t) -> ProofOf(WBEnv env g)
                -> ProofOf(WBEnv (Cons x v env) (CCons x t g)) @-} -- @-}

-- We've changed E-Var and T-Var because the original rules seem to make it impossible
--   to derive typing or big step judgements for many valid expressions with more than
--   one variable such as [ x:=2, y:=3 ] ; x + y ==> 5 and [x:Int,y:Int] |- x + y : Int.
--                       x:=v \in env                 x:t \in g
--                      --------------[E-Var]       -------------[T-Var]
--                       env; x ==> v                g |- x : t
--
-- But then we need to prove that inverting rule [E-Bnd] (our WBCons) works when x:=v or 
-- x:t aren't on top of the environment/context.

-- Lemma. If E :: G and (x:t) \in G then there exists v such that 
--     1) v :: T, and 
--     2) (x:=v) \in env

{-@ lem_lookup_in_wbenv :: env:Env -> x:Vname -> t:Type
                -> { g:Ctx | bound_in_ctx x t g} -> ProofOf(WBEnv env g)
                -> (Value, WBValue)<{\v pf -> (bound_in x v env) && (propOf pf == WBValue v t)}>  @-}
lem_lookup_in_wbenv :: Env -> Vname -> Type -> Ctx -> WBEnv -> (Value, WBValue)
lem_lookup_in_wbenv env x t g WBEmpty      = impossible "ctx can't be empty"
lem_lookup_in_wbenv (Cons x1 v1 env1) x t (CCons _x1 t1 g1) (WBCons _env1 _ _ _ _g1 p_vt p_e1g1)
    | x == x1    = (v1, p_vt)
    | otherwise  = lem_lookup_in_wbenv env1 x t g1 p_e1g1

