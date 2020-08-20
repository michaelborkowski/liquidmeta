{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Basics where

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
          | Eq  | Eqn Int
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
esize (Bc _)	        = 1
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
-- Formerly: In a value, all BV must be bound to a binder within the expression. 
{- @ type Value = { v:Expr | isValue v && Set_emp (freeBV v) } @-}

{-@ reflect isValue @-} -- meaning: is a syntactic value
isValue :: Expr -> Bool
isValue (Bc _)          = True
isValue (Ic _)          = True
isValue (Prim _)        = True
isValue (FV _)          = True -- bound variables not a legal value because we want all values to be
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

--  removed for now:                    ( (freeBV e) == (freeBV e') ) &&
{-@ reflect subFV @-} -- substitute a value for a term variable in a term 
{-@ subFV :: x:Vname -> v:Value -> e:Expr 
                     -> { e':Expr | (Set_mem x (fv e) || e == e') &&
                      ( Set_sub (fv e) (Set_cup (Set_sng x) (fv e')) ) &&
                      ( Set_sub (fv e') (Set_cup (fv v) (Set_dif (fv e) (Set_sng x)))) &&
                      ( (not (Set_mem x (fv v))) => not (Set_mem x (fv e')) ) && 
                        Set_sub (ftv e) (ftv e') &&
                        Set_sub (ftv e') (Set_cup (ftv e) (ftv v)) &&
                      ( (isValue v && isValue e) => isValue e' ) } / [esize e] @-}
subFV :: Vname -> Expr -> Expr -> Expr
subFV x v_x (Bc b)                    = Bc b
subFV x v_x (Ic n)                    = Ic n
subFV x v_x (Prim p)                  = Prim p
subFV x v_x (BV y)                    = BV y
subFV x v_x (FV y) | x == y           = v_x 
                   | otherwise        = FV y
subFV x v_x (Lambda y e)              = Lambda  y (subFV x v_x e)
subFV x v_x (App e e')                = App   (subFV x v_x e)  (subFV x v_x e')
subFV x v_x (LambdaT a k e)           = LambdaT a k (subFV x v_x e)
subFV x v_x (AppT e bt)               = AppT  (subFV x v_x e) (tsubFV x v_x bt)
subFV x v_x (Let y e1 e2)             = Let y (subFV x v_x e1) (subFV x v_x e2)
subFV x v_x (Annot e t)               = Annot (subFV x v_x e) (tsubFV x v_x t) 
subFV x v_x Crash                     = Crash

--  removed for now:                    ( (freeBV e) == Set_cup (tfreeBV t) (freeBV e') ) &&
{-@ reflect subFTV @-} -- substitute a type for a type variable in a term 
{-@ subFTV :: a:Vname -> t:Type -> e:Expr 
                     -> { e':Expr | (Set_mem a (ftv e) || e == e') &&
                      ( Set_sub (ftv e) (Set_cup (Set_sng a) (ftv e')) ) &&
                      ( Set_sub (ftv e') (Set_cup (freeTV t) (Set_dif (ftv e) (Set_sng a)))) &&
                      ( (not (Set_mem a (freeTV t))) => not (Set_mem a (ftv e')) ) && 
                        Set_sub (fv e) (fv e') &&
                        Set_sub (fv e') (Set_cup (fv e) (free t)) &&
                      ( isValue e => isValue e' ) } / [esize e] @-}
subFTV :: Vname -> Type -> Expr -> Expr
subFTV a t_a (Bc b)                    = Bc b
subFTV a t_a (Ic n)                    = Ic n
subFTV a t_a (Prim p)                  = Prim p
subFTV a t_a (BV y)                    = BV y
subFTV a t_a (FV y)                    = FV y
subFTV a t_a (Lambda y e)              = Lambda  y  (subFTV a t_a e)
subFTV a t_a (App e e')                = App   (subFTV a t_a e)  (subFTV a t_a e')
subFTV a t_a (LambdaT a' k e)          = LambdaT a' k (subFTV a t_a e)
subFTV a t_a (AppT e bt)               = AppT  (subFTV a t_a e) (tsubFTV a t_a bt)
subFTV a t_a (Let y e1 e2)             = Let y (subFTV a t_a e1) (subFTV a t_a e2)
subFTV a t_a (Annot e t)               = Annot (subFTV a t_a e) (tsubFTV a t_a t) 
subFTV a t_a Crash                     = Crash

--  removed for now:                                  freeBV e' == Set_dif (freeBV e) (Set_sng x) &&
{-@ reflect subBV @-} --substitute a value for x, which is a BOUND var
{-@ subBV :: x:Vname ->  v:Value -> e:Expr 
                     -> { e':Expr | Set_sub (fv e) (fv e') &&
                                    Set_sub (fv e') (Set_cup (fv e) (fv v)) &&
                                    Set_sub (ftv e) (ftv e') &&
                                    Set_sub (ftv e') (Set_cup (ftv e) (ftv v)) &&
                                    ( esize v != 1  || esize e == esize e' )} / [esize e] @-}
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

--  removed for now:                       Set_sub (freeBV e') (Set_cup (tfreeBV t) (freeBV e)) &&
{-@ reflect subBTV @-} -- substitute in a type for a BOUND TYPE var
{-@ subBTV :: a:Vname -> t:Type -> e:Expr 
                     -> { e':Expr | Set_sub (fv e) (fv e') &&
                                    Set_sub (fv e') (Set_cup (fv e) (free t)) &&
                                    Set_sub (ftv e) (ftv e') &&
                                    Set_sub (ftv e') (Set_cup (ftv e) (freeTV t)) &&
                                    ( tsize t != 1  || esize e == esize e' )} / [esize e] @-}
subBTV :: Vname -> Type -> Expr -> Expr
subBTV a t_a (Bc b)                       = Bc b
subBTV a t_a (Ic n)                       = Ic n
subBTV a t_a (Prim p)                     = Prim p
subBTV a t_a (BV y)                       = BV y -- looking for type vars
subBTV a t_a (FV y)                       = FV y
subBTV a t_a (Lambda y e)                 = Lambda y (subBTV a t_a e)
subBTV a t_a (App e e')                   = App   (subBTV a t_a e)  (subBTV a t_a e')
subBTV a t_a (LambdaT a' k e) | a == a'   = LambdaT a' k e
                              | otherwise = LambdaT a' k (subBTV a t_a e)
subBTV a t_a (AppT e t)                   = AppT  (subBTV a t_a e) (tsubBTV a t_a t)
subBTV a t_a (Let y e1 e2)                = Let y (subBTV a t_a e1) (subBTV a t_a e2)
subBTV a t_a (Annot e t)                  = Annot (subBTV a t_a e) (tsubBTV a t_a t)
subBTV a t_a Crash                        = Crash  

--  removed for now:                         Set_sub (freeBV e') (freeBV e) &&
--  captured by reflection:                  (unbind x y e == subBV x (FV y) e) &&
-- swapped out for now                                   ftv e == ftv e' &&
{-@ reflect unbind @-} -- unbind converts (BV x) to (FV y) in e --TODO revisit refinment
{-@ unbind :: x:Vname -> y:Vname -> e:Expr 
                    -> { e':Expr | Set_sub (fv e) (fv e') && 
                                   Set_sub (fv e') (Set_cup (Set_sng y) (fv e)) &&
                                   Set_sub (ftv e) (ftv e') && Set_sub (ftv e') (ftv e) &&
                                   esize e == esize e' } / [esize e] @-}
unbind :: Vname -> Vname -> Expr -> Expr
unbind x y e = subBV x (FV y) e

-- removed for now:                         Set_Sub (freeBV e') (freeBV e)  &&
-- captured by reflection:                  (unbind_tv a a' e == subBTV a (FTV a') e) &&
{-@ reflect unbind_tv @-} -- unbind converts (BV x) to (FV y) in e -- TODO revisit refinement
{-@ unbind_tv :: a:Vname -> a':Vname -> e:Expr 
                    -> { e':Expr | Set_sub (ftv e) (ftv e') && 
                                   Set_sub (ftv e') (Set_cup (Set_sng a') (ftv e)) &&
                                   fv e == fv e' &&
                                   esize e == esize e' } / [esize e] @-}
unbind_tv :: Vname -> Vname -> Expr -> Expr
unbind_tv a a' e = subBTV a (FTV a') e

-- TODO: revisit freeBV/tfreeBV: the two types of bound vars makes it difficult to talk about the 
--           change in the set of bound vars following a substitution.
-- TODO: may need to break this out into freeBV and ffreeTVV etc, or maybe I can avoid it altogether

  ---   Refinement Level: Names, Terms (in FO), FO Predicates, SMT Formulae

type Pred = Expr -- refinements are arbitrary expresions with base type Bool


  ---   TYPES

data Basic = TBool         -- Bool
           | TInt          -- Int
  deriving (Eq, Show)

data Kind = Base         -- B, base kind
          | Star         -- *, star kind
  deriving (Eq, Show)

{-@ data Type [tsize] @-}
data Type = TRefn   Basic Vname Pred     -- b{x : p}
          | BTV     Vname   -- a
          | FTV     Vname   -- a
          | TFunc   Vname Type Type      -- x:t_x -> t
          | TExists Vname Type Type      -- \exists x:t_x. t
          | TPoly   Vname Kind Type      -- \forall a:k. t
  deriving (Eq, Show)

{-@ lazy tsize @-}
{-@ measure tsize @-}
{-@ tsize :: t:Type -> { v:Int | v >= 0 } @-} 
tsize :: Type -> Int
tsize (TRefn b v r)     = (esize r) + 1
tsize (BTV a)           = 1
tsize (FTV a)           = 1
tsize (TFunc x t_x t)   = (tsize t_x) + (tsize t) + 1
tsize (TExists x t_x t) = (tsize t_x) + (tsize t) + 1
tsize (TPoly a k   t)   = (tsize t)   + 1

{-@ reflect free @-} 
{-@ free :: t:Type -> S.Set Vname / [tsize t] @-}
free :: Type -> S.Set Vname
free (TRefn b v r)      = fv r
free (BTV a)            = S.empty
free (FTV a)            = S.empty
free (TFunc x t_x t)    = S.union (free t_x) (free t) 
free (TExists x t_x t)  = S.union (free t_x) (free t) 
free (TPoly a k   t)    = free t

{-@ reflect freeTV @-} 
{-@ freeTV :: t:Type -> S.Set Vname / [tsize t] @-}
freeTV :: Type -> S.Set Vname
freeTV (TRefn b v r)      = (ftv r)
freeTV (BTV a)            = S.empty
freeTV (FTV a)            = S.singleton a
freeTV (TFunc x t_x t)    = S.union (freeTV t_x) (freeTV t) 
freeTV (TExists x t_x t)  = S.union (freeTV t_x) (freeTV t) 
freeTV (TPoly a k   t)    = freeTV t

{-@ reflect tfreeBV @-}
{-@ tfreeBV :: t:Type -> S.Set Vname / [tsize t] @-}
tfreeBV :: Type -> S.Set Vname
tfreeBV (TRefn b x r)     = S.difference (freeBV r) (S.singleton x)
tfreeBV (BTV a)           = S.empty
tfreeBV (FTV a)           = S.empty
tfreeBV (TFunc x t_x t)   = S.union (tfreeBV t_x) (S.difference (tfreeBV t) (S.singleton x))
tfreeBV (TExists x t_x t) = S.union (tfreeBV t_x) (S.difference (tfreeBV t) (S.singleton x))
tfreeBV (TPoly a  k  t)   = (tfreeBV t)

{-@ reflect tfreeBTV @-}
{-@ tfreeBTV :: t:Type -> S.Set Vname / [tsize t] @-}
tfreeBTV :: Type -> S.Set Vname
tfreeBTV (TRefn b x r)     = freeBTV r
tfreeBTV (BTV a)           = S.singleton a
tfreeBTV (FTV a)           = S.empty
tfreeBTV (TFunc x t_x t)   = S.union (tfreeBTV t_x) (tfreeBTV t) 
tfreeBTV (TExists x t_x t) = S.union (tfreeBTV t_x) (tfreeBTV t) 
tfreeBTV (TPoly a  k  t)   = S.difference (tfreeBTV t) (S.singleton a)

--  removed for now:              ( tfreeBV t == tfreeBV t' ) &&
{-@ reflect tsubFV @-}
{-@ tsubFV :: x:Vname -> e:Value -> t:Type  
         -> { t':Type | ( Set_mem x (free t) || t == t' ) && 
                        ( Set_sub (free t) (Set_cup (Set_sng x) (free t'))) &&
                ( Set_sub (free t') (Set_cup (fv e) (Set_dif (free t) (Set_sng x))) ) &&
                        Set_sub (freeTV t) (freeTV t') &&
                        Set_sub (freeTV t') (Set_cup (ftv e) (freeTV t)) &&
                ( (not (Set_mem x (fv e))) => not (Set_mem x (free t')) ) } / [tsize t] @-}
tsubFV :: Vname -> Expr -> Type -> Type
tsubFV x v_x (TRefn b z r)     = TRefn b z  (subFV x v_x r)
tsubFV x v_x (BTV a)           = BTV a
tsubFV x v_x (FTV a)           = FTV a
tsubFV x v_x (TFunc z t_z t)   = TFunc   z (tsubFV x v_x t_z) (tsubFV x v_x t)
tsubFV x v_x (TExists z t_z t) = TExists z (tsubFV x v_x t_z) (tsubFV x v_x t)
tsubFV x v_x (TPoly a k   t)   = TPoly   a k                  (tsubFV x v_x t)

--  removed for now:               tfreeBV t' == Set_cup (tfreeBV t_a) (tfreeBV t) &&
{-@ reflect tsubFTV @-}
{-@ tsubFTV :: a:Vname -> t_a:Type -> t:Type  
         -> { t':Type | ( Set_mem a (freeTV t) || t == t' ) && 
                        ( Set_sub (freeTV t) (Set_cup (Set_sng a) (freeTV t'))) &&
                ( Set_sub (freeTV t') (Set_cup (freeTV t_a) (Set_dif (freeTV t) (Set_sng a))) ) &&
                        Set_sub (free t) (free t') &&
                        Set_sub (free t') (Set_cup (free t_a) (free t)) && 
                ( (not (Set_mem a (freeTV t_a))) => not (Set_mem a (freeTV t')) ) } / [tsize t] @-}
tsubFTV :: Vname -> Type -> Type -> Type
tsubFTV a t_a (TRefn b x r)        = TRefn b x (subFTV a t_a r)
tsubFTV a t_a (BTV a')             = BTV a' 
tsubFTV a t_a (FTV a') | a == a'   = t_a
                       | otherwise = FTV a'
tsubFTV a t_a (TFunc   z t_z t)    = TFunc   z  (tsubFTV a t_a t_z) (tsubFTV a t_a t)
tsubFTV a t_a (TExists z t_z t)    = TExists z  (tsubFTV a t_a t_z) (tsubFTV a t_a t)
tsubFTV a t_a (TPoly   a' k  t)    = TPoly   a' k                   (tsubFTV a t_a t)

--  removed for now                          tfreeBV t' == Set_dif (tfreeBV t) (Set_sng x) &&
{-@ reflect tsubBV @-}
{-@ tsubBV :: x:Vname -> v_x:Value -> t:Type  
                    -> { t':Type | Set_sub (free t) (free t') &&
                                   Set_sub (free t') (Set_cup (fv v_x) (free t)) &&
                                   Set_sub (freeTV t) (freeTV t') &&
                                   Set_sub (freeTV t') (Set_cup (ftv v_x) (freeTV t)) &&
                                   ( esize v_x != 1 || tsize t == tsize t' ) } / [tsize t] @-}
tsubBV :: Vname -> Expr -> Type -> Type
tsubBV x v_x (TRefn b y r)     
  | x == y                     = TRefn b y r
  | otherwise                  = TRefn b y  (subBV x v_x r)
tsubBV x v_x (BTV a)           = BTV a -- can only subst a type in here
tsubBV x v_x (FTV a)           = FTV a 
tsubBV x v_x (TFunc z t_z t)   
  | x == z                     = TFunc   z (tsubBV x v_x t_z) t
  | otherwise                  = TFunc   z (tsubBV x v_x t_z) (tsubBV x v_x t)
tsubBV x v_x (TExists z t_z t) 
  | x == z                     = TExists z (tsubBV x v_x t_z) t
  | otherwise                  = TExists z (tsubBV x v_x t_z) (tsubBV x v_x t)
tsubBV x v_x (TPoly a  k  t)   = TPoly   a k                  (tsubBV x v_x t)

--  removed for now:      tfreeBV t' == Set_cup (tfreeBV t_a) (Set_dif (tfreeBV t) (Set_sng a)) &&
{-@ reflect tsubBTV @-}
{-@ tsubBTV :: a:Vname -> t_a:Type -> t:Type  
                    -> { t':Type | Set_sub (free t) (free t') &&
                                   Set_sub (free t') (Set_cup (free t_a) (free t)) &&
                                   Set_sub (freeTV t) (freeTV t') &&
                                   Set_sub (freeTV t') (Set_cup (freeTV t_a) (freeTV t)) && 
                                   ( tsize t_a != 1 || tsize t == tsize t' ) } / [tsize t] @-}
tsubBTV :: Vname -> Type -> Type -> Type
tsubBTV a t_a (TRefn b y r)        = TRefn b y   (subBTV a t_a r) -- looking for BTV, not BV
tsubBTV a t_a (BTV a') | a == a'   = t_a
                       | otherwise = BTV a'
tsubBTV a t_a (FTV a')             = FTV a' 
tsubBTV a t_a (TFunc z t_z t)      = TFunc   z  (tsubBTV a t_a t_z) (tsubBTV a t_a t)
tsubBTV a t_a (TExists z t_z t)    = TExists z  (tsubBTV a t_a t_z) (tsubBTV a t_a t)
tsubBTV a t_a (TPoly a' k  t)      
  | a == a'                        = TPoly   a' k t  -- not the same a' anymore
  | otherwise                      = TPoly   a' k (tsubBTV a t_a t)

--  removed for now:                           tfreeBV t' == Set_dif (tfreeBV t) (Set_sng x) &&
--  captuerd by reflection:                             (unbindT x y t == tsubBV x (FV y) t) &&
{-@ reflect unbindT @-}
{-@ unbindT :: x:Vname -> y:Vname -> t:Type 
                       -> { t':Type | Set_sub (free t) (free t') &&
                                      Set_sub (free t') (Set_cup (Set_sng y) (free t)) &&
                                      freeTV t == freeTV t' &&
                                      tsize t == tsize t' } / [tsize t] @-} 
unbindT :: Vname -> Vname -> Type -> Type
unbindT x y t = tsubBV x (FV y) t

--  removed for now:                           tfreeBV t' == Set_dif (tfreeBV t) (Set_sng a) &&
--  captured by reflection:                      (unbind_tvT a a' t == tsubBTV a (FTV a') t) &&
{-@ reflect unbind_tvT @-}
{-@ unbind_tvT :: a:Vname -> a':Vname -> t:Type 
                       -> { t':Type | Set_sub (freeTV t) (freeTV t') &&
                                      Set_sub (freeTV t') (Set_cup (Set_sng a') (freeTV t)) &&
                                      free t == free t' &&
                                      tsize t == tsize t' } / [tsize t] @-} 
unbind_tvT :: Vname -> Vname -> Type -> Type
unbind_tvT a a' t = tsubBTV a (FTV a') t

---------------------------------------------------------------------------
----- | PRELIMINARIES
---------------------------------------------------------------------------

{-@ measure propOf :: a -> b @-}
{-@ type ProofOf E = { proofObj:_ | propOf proofObj = E } @-}

{-@ reflect withProof @-}
{-@ withProof :: x:a -> b -> { v:a | v = x } @-}
withProof :: a -> b -> a
withProof x _ = x

{-@ reflect max @-}
max :: Int -> Int -> Int
max x y = if x >= y then x else y

---------------------------------------------------------------------------
----- | SYNTAX, continued
---------------------------------------------------------------------------

  --- TYPING ENVIRONMENTS ---

data Env = Empty                         -- type Env = [(Vname, Type) or Vname]	
         | Cons  Vname Type Env          
         | ConsT Vname Kind Env
  deriving (Show)
{-@ data Env where 
    Empty :: Env
  | Cons  :: x:Vname -> t:Type -> { g:Env | not (in_env x g) } -> Env 
  | ConsT :: a:Vname -> k:Kind -> { g:Env | not (in_env a g) } -> Env @-}

{-@ measure envsize @-}
{-@ envsize :: Env -> { n:Int | n >= 0 } @-}
envsize :: Env -> Int
envsize Empty         = 0
envsize (Cons  _ _ g) = envsize g + 1
envsize (ConsT _ _ g) = envsize g + 1

{-@ reflect fresh_var @-}
{-@ fresh_var :: g:Env -> { x:Vname | not (in_env x g) } @-}
fresh_var :: Env -> Vname
fresh_var g = maxpList g

{-@ reflect fresh_var_excluding @-}
{-@ fresh_var_excluding :: g:Env -> x:Vname 
                -> { y:Vname | not (in_env y g) && y != x } @-}
fresh_var_excluding :: Env -> Vname -> Vname
fresh_var_excluding g x = if in_env x g then maxpList g
                          else maxpList (Cons x (TRefn TBool x (Bc True)) g)
 
{-@ reflect maxpList @-}
{-@ maxpList :: g:Env -> { x:Vname | (in_env x g) => (x < maxpList g) } @-}
maxpList :: Env -> Int
maxpList Empty         = 1
maxpList (Cons n t g)  = withProof (max (1+n) (maxpList g))
                              (lem_maxp_list1 (Cons n t g)  (max (1+n) (maxpList g)))
maxpList (ConsT n k g) = withProof (max (1+n) (maxpList g))
                              (lem_maxp_list1 (ConsT n k g) (max (1+n) (maxpList g)))

{-@ reflect lem_maxp_list1 @-}
{-@ lem_maxp_list1 :: g:Env -> x:Vname -> { pf:_ | (in_env x g) => (x < maxpList g) } @-} 
lem_maxp_list1 :: Env -> Vname -> Bool
lem_maxp_list1 Empty             x = True
lem_maxp_list1 (Cons n t Empty)  x = True -- fresh_var [n] === n+1
lem_maxp_list1 (Cons n t g)      x 
    = case (x>n) of    
        True  -> True `withProof` (lem_maxp_list1 g x)
        False -> True   
lem_maxp_list1 (ConsT n k Empty) x = True -- fresh_var [n] === n+1
lem_maxp_list1 (ConsT n k g)     x 
    = case (x>n) of    
        True  -> True `withProof` (lem_maxp_list1 g x)
        False -> True   

{-@ reflect in_env @-}              -- any kind of variable
in_env :: Vname -> Env -> Bool
in_env x g = S.member x (binds g) 

{-@ reflect bound_in @-}            -- term variables only
bound_in :: Vname -> Type -> Env -> Bool
bound_in x t Empty                                 = False
bound_in x t (Cons y t' g) | (x == y)              = (t == t')
                           | otherwise             = bound_in x t g
bound_in x t (ConsT a k g) | (x == a)              = False
                           | otherwise             = bound_in x t g

{-@ reflect tv_bound_in @-}         -- type variables only
tv_bound_in :: Vname -> Kind -> Env -> Bool
tv_bound_in a k Empty                                   = False
tv_bound_in a k (Cons x t g)    | (a == x)              = False
                                | otherwise             = tv_bound_in a k g
tv_bound_in a k (ConsT a' k' g) | (a == a')             = (k == k')
                                | otherwise             = tv_bound_in a k g

{-@ reflect binds @-}
binds :: Env -> S.Set Vname
binds Empty         = S.empty
binds (Cons x t g)  = S.union (S.singleton x) (binds g)
binds (ConsT a k g) = S.union (S.singleton a) (binds g)


  --- BARE TYPES: i.e. System F types. These still contain type polymorphism and type variables, 
  --    but all the refinements, dependent arrow binders, and existentials have been erased.

data FType = FTBasic Basic               -- b
           | FTBV   Vname                -- BOUND type variables
           | FTFV   Vname                -- FREE type variables
           | FTFunc FType FType          -- bt -> bt'
           | FTPoly Vname Kind FType     -- \forall a. bt 
  deriving (Eq, Show)

{-@ measure ftsize @-}
{-@ ftsize :: t:FType -> { v:Int | v >= 0 } @-} 
ftsize :: FType -> Int
ftsize (FTBasic b)      = 1
ftsize (FTBV a)         = 1
ftsize (FTFV a)         = 1
ftsize (FTFunc t_x   t) = (ftsize t_x) + (ftsize t) + 1
ftsize (FTPoly a  k  t) = (ftsize t)   + 1

{-@ reflect erase @-}
erase :: Type -> FType
erase (TRefn b v r)     = FTBasic b
erase (BTV a)           = FTBV a
erase (FTV a)           = FTFV a
erase (TFunc x t_x t)   = FTFunc (erase t_x) (erase t)
erase (TExists x t_x t) = (erase t)
erase (TPoly a  k  t)   = FTPoly a k (erase t)

-- there are no term vars in a Bare Type, only type ones
{-@ reflect ffreeTV @-} 
{-@ ffreeTV :: t:FType -> S.Set Vname / [ftsize t] @-}
ffreeTV :: FType -> S.Set Vname
ffreeTV (FTBasic b)      = S.empty
ffreeTV (FTBV a)         = S.empty
ffreeTV (FTFV a)         = S.singleton a
ffreeTV (FTFunc t_x t)   = S.union (ffreeTV t_x) (ffreeTV t) 
ffreeTV (FTPoly a k t)   = ffreeTV t

{-@ reflect ftsubFV @-}
{-@ ftsubFV :: a:Vname -> t_a:FType -> t:FType  
         -> { t':FType | ( Set_mem a (ffreeTV t) || t == t' ) && 
                        ( Set_sub (ffreeTV t) (Set_cup (Set_sng a) (ffreeTV t'))) &&
                ( Set_sub (ffreeTV t') (Set_cup (ffreeTV t_a) (Set_dif (ffreeTV t) (Set_sng a))) ) &&
                ( (not (Set_mem a (ffreeTV t_a))) => not (Set_mem a (ffreeTV t')) ) } / [ftsize t] @-}
ftsubFV :: Vname -> FType -> FType -> FType
ftsubFV a t_a (FTBasic b)           = FTBasic b 
ftsubFV a t_a (FTBV a')             = FTBV a' 
ftsubFV a t_a (FTFV a') | a == a'   = t_a
                        | otherwise = FTFV a'
ftsubFV a t_a (FTFunc t_z t)        = FTFunc (ftsubFV a t_a t_z) (ftsubFV a t_a t)
ftsubFV a t_a (FTPoly a' k t)       = FTPoly a' k (ftsubFV a t_a t)

{-@ reflect ftsubBV @-} 
{-@ ftsubBV :: a:Vname -> t_a:FType -> t:FType  
                    -> { t':FType | Set_sub (ffreeTV t) (ffreeTV t') &&
                                    Set_sub (ffreeTV t') (Set_cup (ffreeTV t_a) (ffreeTV t)) &&
                                    ( ftsize t_a != 1 || ftsize t == ftsize t' ) } / [ftsize t] @-}
ftsubBV :: Vname -> FType -> FType -> FType
ftsubBV a t_a (FTBasic   b)         = FTBasic b
ftsubBV a t_a (FTBV a') | a == a'   = t_a
                        | otherwise = FTBV a'
ftsubBV a t_a (FTFV a')             = FTFV a' 
ftsubBV a t_a (FTFunc t_z t)        = FTFunc (ftsubBV a t_a t_z) (ftsubBV a t_a t)
ftsubBV a t_a (FTPoly a' k  t)      
  | a == a'                         = FTPoly a' k t  -- not the same a' anymore
  | otherwise                       = FTPoly a' k (ftsubBV a t_a t)

{-@ reflect unbindFT @-}
{-@ unbindFT :: a:Vname -> a':Vname -> t:FType 
                       -> { t':FType | Set_sub (ffreeTV t) (ffreeTV t') &&
                                       Set_sub (ffreeTV t') (Set_cup (Set_sng a') (ffreeTV t)) &&
                                       ftsize t == ftsize t' } / [ftsize t] @-} 
unbindFT :: Vname -> Vname -> FType -> FType
unbindFT a a' t = ftsubBV a (FTFV a') t
 


  --- BARE-TYPING ENVIRONMENTS

data FEnv = FEmpty                       -- type FEnv = [(Vname, FType) or Vname]
          | FCons  Vname FType FEnv
          | FConsT Vname Kind  FEnv
  deriving (Show) 
{-@ data FEnv where
    FEmpty :: FEnv
  | FCons  :: x:Vname -> t:FType -> { g:FEnv | not (in_envF x g) } -> FEnv 
  | FConsT :: x:Vname -> k:Kind  -> { g:FEnv | not (in_envF x g) } -> FEnv @-}

{-@ measure fenvsize @-}
{-@ fenvsize :: FEnv -> { n:Int | n >= 0 } @-}
fenvsize :: FEnv -> Int
fenvsize FEmpty         = 0
fenvsize (FCons  _ _ g) = fenvsize g + 1
fenvsize (FConsT _ _ g) = fenvsize g + 1

{-@ reflect fresh_varF @-}
{-@ fresh_varF :: g:FEnv -> { x:Vname | not (in_envF x g) } @-}
fresh_varF :: FEnv -> Vname
fresh_varF g = maxpListF g

{-@ reflect fresh_var_excludingF @-}
{-@ fresh_var_excludingF :: g:FEnv -> x:Vname 
                -> { y:Vname | not (in_envF y g) && y != x } @-}
fresh_var_excludingF :: FEnv -> Vname -> Vname
fresh_var_excludingF g x = if in_envF x g then maxpListF g
                           else maxpListF (FCons x (FTBasic TBool) g)
 
{-@ reflect maxpListF @-}
{-@ maxpListF :: g:FEnv -> { x:Vname | (in_envF x g) => (x < maxpListF g) } @-}
maxpListF :: FEnv -> Int
maxpListF FEmpty         = 1
maxpListF (FCons n t g)  = withProof (max (1+n) (maxpListF g))
                              (lem_maxp_listF (FCons  n t g) (max (1+n) (maxpListF g)))
maxpListF (FConsT n k g) = withProof (max (1+n) (maxpListF g))
                              (lem_maxp_listF (FConsT n k g) (max (1+n) (maxpListF g)))

{-@ reflect lem_maxp_listF @-}
{-@ lem_maxp_listF :: g:FEnv -> x:Vname -> { pf:_ | (in_envF x g) => (x < maxpListF g) } @-} 
lem_maxp_listF :: FEnv -> Vname -> Bool
lem_maxp_listF FEmpty               x = True
lem_maxp_listF (FCons n t FEmpty)   x = True -- fresh_var [n] === n+1
lem_maxp_listF (FCons n t g)        x 
    = case (x>n) of    
        True  -> True `withProof` (lem_maxp_listF g x)
        False -> True   
lem_maxp_listF (FConsT n k FEmpty)  x = True -- fresh_var [n] === n+1
lem_maxp_listF (FConsT n k g)       x 
    = case (x>n) of    
        True  -> True `withProof` (lem_maxp_listF g x)
        False -> True   

{-@ reflect in_envF @-}
in_envF :: Vname -> FEnv -> Bool
in_envF x g = S.member x (bindsF g) 

{-@ reflect lookupF @-}
{- @ lookupF :: x:Vname -> g:FEnv -> { mt:Maybe FType | (mt == Just t) => bound_inF x t g } @-}
lookupF :: Vname -> FEnv -> Maybe FType
lookupF x FEmpty                      = Nothing
lookupF x (FCons  y t g) | x == y     = Just t
                         | otherwise  = lookupF x g
lookupF x (FConsT a k g) | x == a     = Nothing
                         | otherwise  = lookupF x g

{-@ reflect bound_inF @-}
{- @ bound_inF :: x:Vname -> t:FType -> g:FEnv 
        -> { b:Bool | (not b || in_envF x g) && (lookupF x g == Just t => bound_inF x t g)} @-}
bound_inF :: Vname -> FType -> FEnv -> Bool
bound_inF x t FEmpty                                  = False
bound_inF x t (FCons  y t' g) | (x == y)              = (t == t')
                              | otherwise             = bound_inF x t g
bound_inF x t (FConsT a k  g) | (x == a)              = False
                              | otherwise             = bound_inF x t g

{-@ lem_lookup_boundinF :: x:Vname -> t:FType -> { g:FEnv | lookupF x g == Just t }
        -> { pf:_ | bound_inF x t g } @-}
lem_lookup_boundinF :: Vname -> FType -> FEnv -> Proof
lem_lookup_boundinF x t (FCons  y s g) | x == y    = ()
                                       | otherwise = lem_lookup_boundinF x t g
lem_lookup_boundinF x t (FConsT a k g) | x == a    = impossible ""
                                       | otherwise = lem_lookup_boundinF x t g

{-@ lem_boundin_inenvF :: x:Vname -> t:FType -> { g:FEnv | bound_inF x t g}
        -> { pf:_ | in_envF x g } @-}
lem_boundin_inenvF :: Vname -> FType -> FEnv -> Proof
lem_boundin_inenvF x t (FCons y s g)  | x == y    = ()
                                      | otherwise = lem_boundin_inenvF x t g 
lem_boundin_inenvF x t (FConsT a k g) | x == a    = impossible ""
                                      | otherwise = lem_boundin_inenvF x t g 

{-@ reflect bindsF @-}
bindsF :: FEnv -> S.Set Vname
bindsF FEmpty         = S.empty
bindsF (FCons  x t g) = S.union (S.singleton x) (bindsF g)
bindsF (FConsT a k g) = S.union (S.singleton a) (bindsF g)


{-@ reflect erase_env @-}
{-@ erase_env :: g:Env -> { g':FEnv | binds g == bindsF g' } @-}
erase_env :: Env -> FEnv
erase_env Empty         = FEmpty
erase_env (Cons  x t g) = FCons  x (erase t) (erase_env g)
erase_env (ConsT a k g) = FConsT a k         (erase_env g)

