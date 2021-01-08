{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Test where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S


{- @ type Vname =  { v:Int | v >= 0 } @-} 
type Vname = Int

data Prim = Conj | And | Or | Not | Eqv  -- Conj is the same as And but it will only appear in
          | Leq | Leqn Int               --     refinements, and in particular, never in a value
          | Eq  | Eqn Int | Eql          --     being substituted
  deriving (Eq, Show)                 -- Eql is polymorphic. TODO: add Leql and Lqb

{-@ data Expr [esize] @-}
data Expr = Bc Bool                   -- True, False
          | Ic Int                    -- 0, 1, 2, ...
          | Prim Prim                 -- built-in primitive functions 
          | BV Vname                  -- BOUND Variables: bound to a Lambda, Let or :t
          | FV Vname                  -- FREE Variables: bound in an environment
          | Lambda Vname Expr         -- \x.e          abstractions
          | App Expr Expr             -- e e'          applications
          | LambdaT Vname Kind Expr   -- /\a:k.e  type abstractions
          | AppT Expr Type            -- e [bt]   type applications (NB: bare type inside)
          | Let Vname Expr Expr       -- let x = e1 in e2
          | Annot Expr Type           -- e : t
  deriving (Eq, Show)

{-@ lazy esize @-}
{-@ measure esize @-}
{-@ esize :: e:Expr -> { v:Int | v >= 0 } @-}
esize :: Expr -> Int
esize (Bc True)	        = 0
esize (Bc _)  		= 1
esize (Ic _)		= 1
esize (Prim _)          = 1
esize (BV _)            = 1
esize (FV _)            = 1
esize (Lambda x e)      = (esize e)   + 1
esize (App e e')        = (esize e)   + (esize e') + 1
esize (LambdaT a k e)   = (esize e)   + 1
esize (AppT e t)        = (esize e)   + (tsize t) + 1
esize (Let x e_x e)     = (esize e_x) + (esize e) + 1
esize (Annot e t)       = (esize e)   + (tsize t) + 1


  ---   TYPES

data Basic = TBool         -- Bool
           | TInt          -- Int
           | BTV     Vname   -- a                    -- NEW!
           | FTV     Vname   -- a                    -- NEW!
  deriving (Eq, Show)

data Kind = Base         -- B, base kind
          | Star         -- *, star kind
  deriving (Eq, Show)

{-@ type RVname =  { v:Int | v == 0 } @-} 
type RVname = Int
-- this stands in for the above b/c LH isn't inferring all refn binders are equal
--data RVname = Z deriving (Eq, Show)

{-@ data Type [tsize] where 
        TRefn   :: Basic -> RVname -> Expr -> Type  
      | TFunc   :: Vname -> Type  -> Type -> Type 
      | TExists :: Vname -> Type  -> Type -> Type 
      | TPoly   :: Vname -> Kind  -> Type -> Type @-} -- @-}
data Type = TRefn   Basic Vname Expr     -- b{x0 : p}
          | TFunc   Vname Type Type      -- x:t_x -> t
          | TExists Vname Type Type      -- \exists x:t_x. t
          | TPoly   Vname Kind Type      -- \forall a:k. t
  deriving (Eq, Show)

{-@ lazy tsize @-}
{-@ measure tsize @-}
{-@ tsize :: t:Type -> { v:Int | v >= 0 } @-} 
tsize :: Type -> Int
tsize (TRefn b v r)         = (esize r) + 1
tsize (TFunc x t_x t)       = (tsize t_x) + (tsize t) + 1
tsize (TExists x t_x t)     = (tsize t_x) + (tsize t) + 1
tsize (TPoly a k   t)       = (tsize t)   + 1

{-@ reflect isTRefn @-}
isTRefn :: Type -> Bool
isTRefn (TRefn {}) = True
isTRefn _          = False

{-@ lem_rvname_equal ::  t:Type  ->  t':Type 
        -> { t'':Type | t'' == t' } @-}
lem_rvname_equal :: Type -> Type -> Type
lem_rvname_equal (TRefn b x p) (TRefn b' y q) = TRefn b' x q ? toProof ( x === y )
lem_rvname_equal t             t'             = t'

