{-# LANGUAGE GADTs #-}

-- The following module presents a mechanization of the proofs of type
-- soundness and termination for a Simply Typed Lambda Calculus
-- and is based on Lecture notes "Well-typed Programs Don't Go Wrong"
-- and "Type Soundness and Termination in One Easy Lemma" by Nadia
-- Polikarpova for CSE 130 at UC San Diego.

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--short-names" @-}

module Syntax where

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
