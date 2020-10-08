{-# LANGUAGE GADTs #-}

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality" @-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module TestBasics where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

---------------------------------------------------------------------------
----- | TERMS of our language
---------------------------------------------------------------------------
  ---   Term level expressions 
  ---   We use the locally named representation for variables
  ---     "free" variables are ints because easier to pick fresh ones
  ---     "bound" ones also ints 

{- @ type Vname =  Nat @-} -- > 0 or not?
type Vname = Int

data Prim = And | Or | Not | Eqv
          | Leq | Leqn Int 
          | Eq  | Eqn Int | Eql       -- Eql is polymorphic
  deriving (Eq, Show)

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
          | Crash
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
esize Crash             = 1

{-@ type Value = { v:Expr | isValue v } @-}

{-@ reflect isValue @-} -- meaning: is a syntactic value
isValue :: Expr -> Bool
isValue (Bc _)          = True
isValue (Ic _)          = True
isValue (Prim _)        = True
isValue (FV _)          = True 
isValue (BV _)          = True -- Lambda 2.1: changed mind: now bound variables a legal value 
                               -- even though we want all values to be
isValue (Lambda x e)    = True --     well-formed as expressions
isValue (LambdaT a k e) = True
isValue Crash           = True
isValue _               = False

{-@ reflect freeBV @-}
{-@ freeBV :: e:Expr -> S.Set Vname / [esize e] @-}
freeBV :: Expr -> S.Set Vname
freeBV (Bc _)          = S.empty
freeBV (Ic _)          = S.empty
freeBV (Prim _)        = S.empty
freeBV (BV x)          = S.singleton x
freeBV (FV x)          = S.empty
freeBV (Lambda x e)    = S.difference (freeBV e) (S.singleton x)
freeBV (App e e')      = S.union (freeBV e) (freeBV e') 
freeBV (LambdaT a k e) = freeBV e                                 -- bound type variables are not same set 
         -- formerly     S.difference (freeBV e) (S.singleton a)  -- /\ 1. \ 1. (BTV 1)   isn't hidden
freeBV (AppT e t)      = S.union (freeBV e)  (tfreeBV t)          
freeBV (Let x ex e)    = S.union (freeBV ex) (S.difference (freeBV e) (S.singleton x))
freeBV (Annot e t)     = S.union (freeBV e)  (tfreeBV t) 
freeBV Crash           = S.empty

{-@ reflect freeBTV @-}
{-@ freeBTV :: e:Expr -> S.Set Vname / [esize e] @-}
freeBTV :: Expr -> S.Set Vname
freeBTV (Bc _)          = S.empty
freeBTV (Ic _)          = S.empty
freeBTV (Prim _)        = S.empty
freeBTV (BV x)          = S.empty
freeBTV (FV x)          = S.empty
freeBTV (Lambda x e)    = freeBTV e
freeBTV (App e e')      = S.union (freeBTV e)   (freeBTV e') 
freeBTV (LambdaT a k e) = S.difference (freeBTV e) (S.singleton a)  
freeBTV (AppT e t)      = S.union (freeBTV e)  (tfreeBTV t)          
freeBTV (Let x ex e)    = S.union (freeBTV ex)  (freeBTV e)
freeBTV (Annot e t)     = S.union (freeBTV e)  (tfreeBTV t) 
freeBTV Crash           = S.empty

{-@ reflect fv @-}
{-@ fv :: e:Expr -> S.Set Vname / [esize e] @-}
fv :: Expr -> S.Set Vname
fv (Bc _)          = S.empty
fv (Ic _)          = S.empty
fv (Prim _)        = S.empty
fv (BV _)          = S.empty
fv (FV x)          = S.singleton x
fv (Lambda x e)    = fv e 
fv (App e e')      = S.union (fv e) (fv e')
fv (LambdaT a k e) = fv e
fv (AppT e t)      = S.union (fv e) (free t)
fv (Let x ex e)    = S.union (fv ex) (fv e)
fv (Annot e t)     = S.union (fv e) (free t) -- fv e
fv (Crash)         = S.empty

{-@ reflect ftv @-}
{-@ ftv :: e:Expr -> S.Set Vname / [esize e] @-}
ftv :: Expr -> S.Set Vname
ftv (Bc _)          = S.empty
ftv (Ic _)          = S.empty
ftv (Prim _)        = S.empty
ftv (BV _)          = S.empty
ftv (FV x)          = S.empty -- differs from fv
ftv (Lambda x e)    = ftv e 
ftv (App e e')      = S.union (ftv e) (ftv e')
ftv (LambdaT a k e) = ftv e
ftv (AppT e t)      = S.union (ftv e) (freeTV t)
ftv (Let x ex e)    = S.union (ftv ex) (ftv e) 
ftv (Annot e t)     = S.union (ftv e) (freeTV t) -- fv e
ftv (Crash)         = S.empty

  --- TERM-LEVEL SUBSTITUTION

{-@ reflect subBV @-} --substitute a value for x, which is a BOUND var
{-@ subBV :: x:Vname ->  v:Value -> e:Expr 
                     -> { e':Expr | Set_sub (fv e) (fv e') &&
                                    Set_sub (fv e') (Set_cup (fv e) (fv v)) &&
                                    Set_sub (ftv e) (ftv e') &&
                                    Set_sub (ftv e') (Set_cup (ftv e) (ftv v)) &&
                                    Set_sub (freeBV e')  (Set_cup (Set_dif (freeBV e) (Set_sng x)) (freeBV v)) &&
                                    Set_sub (Set_dif (freeBV e) (Set_sng x)) (freeBV e') &&
                                    Set_sub (freeBTV e') (Set_cup (freeBTV e) (freeBTV v)) &&
                                    Set_sub (freeBTV e) (freeBTV e') } / [esize e] @-} 
subBV :: Vname -> Expr -> Expr -> Expr
subBV x v_x (Bc b)                    = Bc b
subBV x v_x (Ic n)                    = Ic n
subBV x v_x (Prim p)                  = Prim p
subBV x v_x (BV y) | x == y           = v_x
                   | otherwise        = BV y
subBV x v_x (FV y)                    = FV y
subBV x v_x (Lambda y e) | x == y     = Lambda y e  -- not the same x anymore
                         | otherwise  = Lambda y (subBV x v_x e)
subBV x v_x (App e e')                = App   (subBV x v_x e)  (subBV x v_x e')
subBV x v_x (LambdaT a k e)           = LambdaT a k (subBV x v_x e) -- we're looking for a term var
subBV x v_x (AppT e t)                = AppT  (subBV x v_x e) (tsubBV x v_x t)
subBV x v_x (Let y e1 e2) | x == y    = Let y (subBV x v_x e1) e2 -- not the same x anymore
                          | otherwise = Let y (subBV x v_x e1) (subBV x v_x e2)
subBV x v_x (Annot e t)               = Annot (subBV x v_x e) (tsubBV x v_x t)
subBV x v_x Crash                     = Crash  

type Pred = Expr 

  ---   TYPES

data Basic = TBool         -- Bool
           | TInt          -- Int
           | BTV     Vname   -- a                    -- NEW!
           | FTV     Vname   -- a                    -- NEW!
  deriving (Eq, Show)

data Kind = Base         -- B, base kind
          | Star         -- *, star kind
  deriving (Eq, Show)

{-@ data Type [tsize] where 
    TRefn   :: Basic -> Vname -> Pred -> Type; 
    TFunc   :: Vname -> Type  -> Type -> Type;
    TExists :: Vname -> Type  -> Type -> Type;
    TPoly   :: Vname -> Kind  -> Type -> Type @-} -- @-}
data Type = TRefn   Basic Vname Pred     -- b{x : p}
          | TFunc   Vname Type Type      -- x:t_x -> t
          | TExists Vname Type Type      -- \exists x:t_x. t
          | TPoly   Vname Kind Type      -- \forall a:k. t
  deriving (Eq, Show)

  -- ONLY types with Base Kind may have non-trivial refinements. Star kinded type variables 
  --     may only have the refinement { x : Bc True }.


{-@ lazy tsize @-}
{-@ measure tsize @-}
{-@ tsize :: t:Type -> { v:Int | v >= 0 } @-} 
tsize :: Type -> Int
--tsize (TRefn b v (Bc True)) = 1
tsize (TRefn b v r)         = (esize r) + 1
tsize (TFunc x t_x t)       = (tsize t_x) + (tsize t) + 1
tsize (TExists x t_x t)     = (tsize t_x) + (tsize t) + 1
tsize (TPoly a k   t)       = (tsize t)   + 1

{-@ reflect free @-} -- free TERM variables
{-@ free :: t:Type -> S.Set Vname / [tsize t] @-}
free :: Type -> S.Set Vname
free (TRefn b v r)      = fv r
free (TFunc x t_x t)    = S.union (free t_x) (free t) 
free (TExists x t_x t)  = S.union (free t_x) (free t) 
free (TPoly a k   t)    = free t

{-@ reflect freeTV @-} -- free TYPE variables
{-@ freeTV :: t:Type -> S.Set Vname / [tsize t] @-}
freeTV :: Type -> S.Set Vname
freeTV (TRefn b v r)      = case b of --S.union (ftv r) (freeBasicTV b)
  (FTV a)      -> S.union (S.singleton a) (ftv r)
  _            -> ftv r
freeTV (TFunc x t_x t)    = S.union (freeTV t_x) (freeTV t) 
freeTV (TExists x t_x t)  = S.union (freeTV t_x) (freeTV t) 
freeTV (TPoly a k   t)    = freeTV t

{-@ reflect tfreeBV @-}
{-@ tfreeBV :: t:Type -> S.Set Vname / [tsize t] @-}
tfreeBV :: Type -> S.Set Vname
tfreeBV (TRefn b x r)     = S.difference (freeBV r) (S.singleton x)
tfreeBV (TFunc x t_x t)   = S.union (tfreeBV t_x) (S.difference (tfreeBV t) (S.singleton x))
tfreeBV (TExists x t_x t) = S.union (tfreeBV t_x) (S.difference (tfreeBV t) (S.singleton x))
tfreeBV (TPoly a  k  t)   = (tfreeBV t)

{-@ reflect tfreeBTV @-}
{-@ tfreeBTV :: t:Type -> S.Set Vname / [tsize t] @-}
tfreeBTV :: Type -> S.Set Vname
tfreeBTV (TRefn b x r)     = case b of --freeBTV r
  (BTV a)     -> S.union (S.singleton a) (freeBTV r)
  _           -> freeBTV r
tfreeBTV (TFunc x t_x t)   = S.union (tfreeBTV t_x) (tfreeBTV t) 
tfreeBTV (TExists x t_x t) = S.union (tfreeBTV t_x) (tfreeBTV t) 
tfreeBTV (TPoly a  k  t)   = S.difference (tfreeBTV t) (S.singleton a)

{-@ reflect tsubBV @-}
{-@ tsubBV :: x:Vname -> v_x:Value -> t:Type  
                -> { t':Type | Set_sub (free t) (free t') &&
                               Set_sub (free t') (Set_cup (fv v_x) (free t)) &&
                               Set_sub (freeTV t) (freeTV t') &&
                               Set_sub (freeTV t') (Set_cup (ftv v_x) (freeTV t)) &&
                               Set_sub (tfreeBV t') (Set_cup (Set_dif (tfreeBV t) (Set_sng x)) (freeBV v_x)) &&
                               Set_sub (Set_dif (tfreeBV t) (Set_sng x)) (tfreeBV t') &&
                               Set_sub (tfreeBTV t') (Set_cup (tfreeBTV t) (freeBTV v_x)) &&
                               Set_sub (tfreeBTV t) (tfreeBTV t') } / [tsize t] @-} 
tsubBV :: Vname -> Expr -> Type -> Type
tsubBV x v_x (TRefn b y r)     
  | x == y                     = TRefn b y r
  | otherwise                  = TRefn b y  (subBV x v_x r)
tsubBV x v_x (TFunc z t_z t)   
  | x == z                     = TFunc   z (tsubBV x v_x t_z) t
  | otherwise                  = TFunc   z (tsubBV x v_x t_z) (tsubBV x v_x t)
tsubBV x v_x (TExists z t_z t) 
  | x == z                     = TExists z (tsubBV x v_x t_z) t
  | otherwise                  = TExists z (tsubBV x v_x t_z) (tsubBV x v_x t)
tsubBV x v_x (TPoly a  k  t)   = TPoly   a k                  (tsubBV x v_x t)
