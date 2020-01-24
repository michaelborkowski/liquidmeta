{-# LANGUAGE GADTs #-}

-- The following module presents a mechanization of the proofs of type
-- soundness and termination for a Simply Typed Lambda Calculus
-- and is based on Lecture notes "Well-typed Programs Don't Go Wrong"
-- and "Type Soundness and Termination in One Easy Lemma" by Nadia
-- Polikarpova for CSE 130 at UC San Diego.

--{-@ LIQUID "--higherorder" @-}
--{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--short-names" @-}

module STLC where

import Prelude hiding (foldr)
import Language.Haskell.Liquid.ProofCombinators 
--import qualified Data.Set as S

---------------------------------------------------------------------------
----- | PRELIMINARIES
---------------------------------------------------------------------------

{-@ measure propOf :: a -> b @-}
{-@ type ProofOf E = { proofObj:_ | propOf proofObj = E } @-}

{-@ reflect foldr @-}
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f i []     = i
foldr f i (x:xs) = f x (foldr f i xs)

---------------------------------------------------------------------------
----- | TERMS and TYPES of our language
---------------------------------------------------------------------------
  ---   Term level expressions 

type Vname = String

data Expr = N Int                -- 0, 1, 2, ...
          | V Vname              -- x
          | Add Expr Expr        -- e1 + e2
          | Lambda Vname Expr    -- \x -> e
          | App Expr Expr        -- e1 e2
  deriving (Eq, Show) -- TODO: will I need | Crash

data Value = VNum Int            -- 
           | VCls Env Vname Expr -- <E, x, e>
  deriving (Eq, Show)

{-@ reflect subst @-}
--{-@ subst :: Vname -> { v:Expr | isValue v } -> Expr -> Expr @-}
subst :: Vname -> Expr -> Expr -> Expr
subst x e_x (N n)                     = N n
subst x e_x (V y) | x == y            = e_x
                  | otherwise         = V y
subst x e_x (Add e1 e2)               = Add (subst x e_x e1) (subst x e_x e2)
subst x e_x (Lambda y e) | x == y     = Lambda y e
                         | otherwise  = Lambda y (subst x e_x e)
subst x e_x (App e e')                = App (subst x e_x e) (subst x e_x e')

data Env = Empty                         -- type Env = [(Vname, Value)]	
         | Cons Vname Value Env
  deriving (Eq, Show)

{-@ reflect in_env @-}
in_env :: Vname -> Env -> Bool
in_env x Empty                    = False
in_env x (Cons y v g) | x == y    = True
                      | otherwise = in_env x g

{-@ reflect bound_in @-}
bound_in :: Vname -> Value -> Env -> Bool
bound_in x v Empty                     = False
bound_in x v (Cons y v' g) | x == y    = (v == v')
                           | otherwise = bound_in x v g

{-@ reflect lookup_env @-}
lookup_env :: Vname -> Env -> Maybe Value
lookup_env x Empty                    = Nothing
lookup_env x (Cons y v g) | x == y    = Just v
                          | otherwise = lookup_env x g

  ---   TYPES

data Type = TInt                -- Int
          | TFunc Type Type     -- t -> t'
  deriving (Eq, Show)

data Ctx = CEmpty               -- type Ctx = [(Vname, Type)]	
         | CCons Vname Type Ctx
  deriving (Show)

{-@ reflect in_ctx @-}
in_ctx :: Vname -> Ctx -> Bool
in_ctx x CEmpty                    = False
in_ctx x (CCons y t g) | x == y    = True
                       | otherwise = in_ctx x g

{-@ reflect bound_in_ctx @-}
bound_in_ctx :: Vname -> Type -> Ctx -> Bool
bound_in_ctx x t CEmpty                     = False
bound_in_ctx x t (CCons y t' g) | x == y    = (t == t')
                                | otherwise = bound_in_ctx x t g

{-@ reflect lookup_ctx @-}
lookup_ctx :: Vname -> Ctx -> Maybe Type
lookup_ctx x CEmpty                    = Nothing
lookup_ctx x (CCons y t g) | x == y    = Just t
                           | otherwise = lookup_ctx x g

{-@ measure tsize @-}
tsize :: Type -> Int
tsize (TInt)	     = 0
tsize (TFunc t t')   = (tsize t') + 1

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

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- Main Lemma: If G |- e : t and env :: g then exists v
-- --               such that E; e ==> v and v :: T. 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

{-@ main_lemma :: e:Expr -> t:Type -> env:Env -> g:Ctx 
                -> ProofOf(HasType g e t) -> ProofOf(WBEnv env g)
                -> (Value, (BStep, WBValue))<{\v pfs ->
                      (propOf (fst pfs) == BStep env e v) && (propOf (snd pfs) == WBValue v t)}> @-} 
main_lemma :: Expr -> Type -> Env -> Ctx -> HasType -> WBEnv
                -> (Value, (BStep, WBValue))
main_lemma e t env g (TNum _g n)    _       = (VNum n, (ENum env n, WBVNum n))
  -- Case T-Num: e = (N n) and t = Int
main_lemma e t env g (TVar _g x _t) p_env_g = (v, (EVar env x v, p_v_t))
  where
    (v, p_v_t) = lem_lookup_in_wbenv env x t g p_env_g
  -- Case T-Var: e = (V x)
main_lemma e t env g (TAdd _g e1 p_e1_Int e2 p_e2_Int) p_env_g = (VNum n, (bstep_e, WBVNum n))
  where
    (VNum n1, (bstep_e1, p_wb_v1)) = main_lemma e1 TInt env g p_e1_Int p_env_g
    (VNum n2, (bstep_e2, p_wb_v2)) = main_lemma e2 TInt env g p_e2_Int p_env_g
    n                         = n1 + n2
    bstep_e                   = EAdd env e1 n1 bstep_e1 e2 n2 bstep_e2 n
  -- Case T-Add: e = (Add e1 e2)
main_lemma e t env g (TAbs _g x t1 e' t2 p_e2_t2) p_env_g = (VCls env x e', (bstep_e, wb_clos))
  where
    bstep_e = EAbs env x e'
    wb_clos = WBVCls env x e' t1 t2 behaves_on_arg
      where
        behaves_on_arg v1 p_v1_t1 = (v2, (bstep_e', p_v2_t2))
          where
            p_cons_env = WBCons env x v1 t1 g p_v1_t1 p_env_g
            (v2, (bstep_e', p_v2_t2)) = main_lemma e' t2 (Cons x v1 env) (CCons x t1 g) p_e2_t2 p_cons_env
  -- Case T-Abs: e = (Lambda x e') 
main_lemma e t env g (TApp _g e1 t2 _t p_e1_t2t e2 p_e2_t2) p_env_g = (v, (bstep_e1e2, p_v_t)) 
  where 
    (VCls env' x' e', (bstep_e1, WBVCls _env' _x' _e' _ _ behaves_on_arg)) 
      = main_lemma e1 (TFunc t2 t) env g p_e1_t2t p_env_g
    (v2, (bstep_e2, p_v2_t2)) = main_lemma e2 t2 env g p_e2_t2 p_env_g
    (v, (bstep_e', p_v_t)) = behaves_on_arg v2 p_v2_t2
    bstep_e1e2 = EApp env e1 env' x' e' bstep_e1 e2 v2 bstep_e2 v bstep_e'

{-@ thm_success :: e:Expr -> t:Type -> ProofOf(HasType CEmpty e t)
                    -> (Value, BStep)<{\v pf -> propOf pf == BStep Empty e v}> @-}
thm_success :: Expr -> Type -> HasType -> (Value, BStep)
thm_success e t p_e_t = (v, bstep_e)
  where
    (v, (bstep_e, p_v_t)) = main_lemma e t Empty CEmpty p_e_t WBEmpty
