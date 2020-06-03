{-# LANGUAGE GADTs #-}

{-@ LIQUID "--no-termination" @-}   -- TODO: assume
{-@ LIQUID "--no-totality" @-}      -- TODO: assume
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
freeBV (LambdaT a k e) = S.difference (freeBV e) (S.singleton a)  -- bound type variables are the same set 
freeBV (AppT e t)      = S.union (freeBV e)  (tfreeBV t)          --   TODO: revisit this decision
freeBV (Let x ex e)    = S.union (freeBV ex) (S.difference (freeBV e) (S.singleton x))
freeBV (Annot e t)     = S.union (freeBV e)  (tfreeBV t) 
freeBV Crash           = S.empty


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
{-@ reflect unbind @-} -- unbind converts (BV x) to (FV y) in e --TODO revisit refinment
{-@ unbind :: x:Vname -> y:Vname -> e:Expr 
                    -> { e':Expr | Set_sub (fv e) (fv e') && 
                                   Set_sub (fv e') (Set_cup (Set_sng y) (fv e)) &&
                                   ftv e == ftv e' &&
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
tfreeBV (BTV a)           = S.singleton a
tfreeBV (FTV a)           = S.empty
tfreeBV (TFunc x t_x t)   = S.union (tfreeBV t_x) (S.difference (tfreeBV t) (S.singleton x))
tfreeBV (TExists x t_x t) = S.union (tfreeBV t_x) (S.difference (tfreeBV t) (S.singleton x))
tfreeBV (TPoly a  k  t)   = S.difference (tfreeBV t) (S.singleton a)

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


--------------------------------------------------------------------------
----- | OPERATIONAL SEMANTICS (Small Step)
--------------------------------------------------------------------------

-- E-Prim c v -> delta(c,v)
-- E-App1 e e1 -> e' e1 if e->e'
-- E-App2 v e  -> v e'  if e->e'
-- E-AppAbs (\x. e) v -> e[v/x]
-- E-AppT
-- E-
-- E-Let  let x=e_x in e -> let x=e'_x in e if e_x->e'_x
-- E-LetV let x=v in e -> e[v/x]
-- E-Ann   e:t -> e':t  if e->e'
-- E-AnnV  v:t -> v

{-@ reflect delta @-}
{-@ delta :: p:Prim -> e:Value -> { e':Value | Set_emp (fv e') } @-}
delta :: Prim -> Expr -> Expr
delta And (Bc True)   = Lambda 1 (BV 1)
delta And (Bc False)  = Lambda 1 (Bc False)
delta Or  (Bc True)   = Lambda 1 (Bc True)
delta Or  (Bc False)  = Lambda 1 (BV 1)
delta Not (Bc True)   = Bc False
delta Not (Bc False)  = Bc True
delta Eqv (Bc True)   = Lambda 1 (BV 1)
delta Eqv (Bc False)  = Lambda 1 (App (Prim Not) (BV 1))
delta Leq      (Ic n) = Prim (Leqn n)
delta (Leqn n) (Ic m) = Bc (n <= m)
delta Eq       (Ic n) = Prim (Eqn n)
delta (Eqn n)  (Ic m) = Bc (n == m)
delta _ _             = Crash

data StepP where
    Step :: Expr -> Expr -> StepP

data Step where
    EPrim :: Prim -> Expr -> Step
    EApp1 :: Expr -> Expr -> Step -> Expr -> Step
    EApp2 :: Expr -> Expr -> Step -> Expr -> Step
    EAppAbs :: Vname -> Expr -> Expr -> Step
    EAppT :: Expr -> Expr -> Step -> Type -> Step
    EAppTAbs :: Vname -> Kind -> Expr -> Type -> Step
    ELet  :: Expr -> Expr -> Step -> Vname -> Expr -> Step
    ELetV :: Vname -> Expr -> Expr -> Step
    EAnn  :: Expr -> Expr -> Step -> Type -> Step
    EAnnV :: Expr -> Type -> Step

{-@ data Step where 
    EPrim :: c:Prim -> w:Value  
                 -> ProofOf( Step (App (Prim c) w) (delta c w) )
 |  EApp1 :: e:Expr -> e':Expr -> ProofOf( Step e e' ) 
                 -> e1:Expr -> ProofOf( Step (App e e1) (App e' e1))
 |  EApp2 :: e:Expr -> e':Expr -> ProofOf( Step e e' )
                 -> v:Value -> ProofOf( Step (App v e) (App v e'))
 |  EAppAbs :: x:Vname -> e:Expr -> v:Value  
                 -> ProofOf( Step (App (Lambda x e) v) (subBV x v e))
 |  EAppT :: e:Expr -> e':Expr -> ProofOf( Step e e' ) 
                 -> t:Type -> ProofOf( Step (AppT e t) (AppT e' t))
 |  EAppTAbs :: a:Vname -> k:Kind -> e:Expr -> t:Type
                 -> ProofOf( Step (AppT (LambdaT a k e) t) (subBTV a t e))
 |  ELet  :: e_x:Expr -> e_x':Expr -> ProofOf( Step e_x e_x' )
                 -> x:Vname -> e:Expr -> ProofOf( Step (Let x e_x e) (Let x e_x' e))
 |  ELetV :: x:Vname -> v:Value -> e:Expr
                 -> ProofOf( Step (Let x v e) (subBV x v e))
 |  EAnn  :: e:Expr -> e':Expr -> ProofOf(Step e e')
                 -> t:Type -> ProofOf(Step (Annot e t) (Annot e' t))
 |  EAnnV :: v:Value -> t:Type -> ProofOf(Step (Annot v t) v) @-} -- @-}

{- old versions with isValue only
 |  EApp2 :: e:Expr -> e':Expr -> ProofOf( Step e e' )
                 -> { v:Expr | isValue v } -> ProofOf( Step (App v e) (App v e'))
 |  EAnnV :: { v:Expr | isValue v } -> t:Type -> ProofOf( Step (Annot v t) v) @ -}

data EvalsToP where
    EvalsTo :: Expr -> Expr -> EvalsToP

data EvalsTo where
    Refl     :: Expr -> EvalsTo
    AddStep  :: Expr -> Expr -> Step -> Expr -> EvalsTo -> EvalsTo
{-@ data EvalsTo where 
    Refl     :: e:Expr -> ProofOf ( EvalsTo e e )
 |  AddStep  :: e1:Expr -> e2:Expr -> ProofOf( Step e1 e2 ) -> e3:Expr
               -> ProofOf ( EvalsTo e2 e3 ) -> ProofOf( EvalsTo e1 e3 ) @-} -- @-} 

-- TODO: If I need a `crashfree` measure, can restore it here  

-----------------------------------------------------------------------------
----- | JUDGEMENTS : the Bare-Typing Relation
-----------------------------------------------------------------------------

data HasFTypeP where
    HasFType :: FEnv -> Expr -> FType -> HasFTypeP 

data HasFType where
    FTBC   :: FEnv -> Bool -> HasFType
    FTIC   :: FEnv -> Int -> HasFType
    FTVar1 :: FEnv -> Vname -> FType -> HasFType 
    FTVar2 :: FEnv -> Vname -> FType -> HasFType -> Vname -> FType -> HasFType
    FTVar3 :: FEnv -> Vname -> FType -> HasFType -> Vname -> Kind -> HasFType
    FTPrm  :: FEnv -> Prim -> HasFType
    FTAbs  :: FEnv -> Vname -> FType -> Expr -> FType -> Vname -> HasFType -> HasFType
    FTApp  :: FEnv -> Expr -> FType -> FType -> HasFType 
                   -> Expr -> HasFType -> HasFType
    FTAbsT :: FEnv -> Vname -> Kind -> Expr -> FType -> Vname -> HasFType -> HasFType
    FTAppT :: FEnv -> Expr -> Vname -> Kind -> FType -> HasFType -> Type -> HasFType
    FTLet  :: FEnv -> Expr -> FType -> HasFType -> Vname -> Expr
                   -> FType -> Vname -> HasFType -> HasFType
    FTAnn  :: FEnv -> Expr -> FType -> Type -> HasFType -> HasFType

{-@ data HasFType where
    FTBC   :: g:FEnv -> b:Bool -> ProofOf(HasFType g (Bc b) (FTBasic TBool))
 |  FTIC   :: g:FEnv -> n:Int -> ProofOf(HasFType g (Ic n) (FTBasic TInt))
 |  FTVar1 :: g:FEnv -> { x:Vname | not (in_envF x g) } -> b:FType 
                -> ProofOf(HasFType (FCons x b g) (FV x) b)
 |  FTVar2 :: g:FEnv -> { x:Vname | in_envF x g } -> b:FType -> ProofOf(HasFType g (FV x) b)
                -> { y:Vname | y != x && not (in_envF y g) } -> b':FType 
                -> ProofOf(HasFType (FCons y b' g) (FV x) b)
 |  FTVar3 :: g:FEnv -> { x:Vname | in_envF x g } -> b:FType -> ProofOf(HasFType g (FV x) b)
                -> { y:Vname | y != x && not (in_envF y g) }  -> k:Kind
                -> ProofOf(HasFType (FConsT y k g) (FV x) b)
 |  FTPrm  :: g:FEnv -> c:Prim  -> ProofOf(HasFType g (Prim c) (erase (ty c)))
 |  FTAbs  :: g:FEnv -> x:Vname -> b:FType -> e:Expr -> b':FType
                -> { y:Vname | not (in_envF y g) && not (Set_mem y (fv e)) }
                -> ProofOf(HasFType (FCons y b g) (unbind x y e) b')
                -> ProofOf(HasFType g (Lambda x e) (FTFunc b b'))
 |  FTApp  :: g:FEnv -> e:Expr -> b:FType -> b':FType
                -> ProofOf(HasFType g e (FTFunc b b')) 
                -> e':Expr -> ProofOf(HasFType g e' b) 
                -> ProofOf(HasFType g (App e e') b')
 |  FTAbsT :: g:FEnv -> a:Vname -> k:Kind -> e:Expr -> b:FType
                -> { a':Vname | not (in_envF a' g) && not (Set_mem a' (fv e)) && not (Set_mem a' (ftv e)) }
                -> ProofOf(HasFType (FConsT a' k g) (unbind_tv a a' e) b)
                -> ProofOf(HasFType g (LambdaT a k e) (FTPoly a k b))
 |  FTAppT :: g:FEnv -> e:Expr -> a:Vname -> k:Kind -> t':FType
                -> ProofOf(HasFType g e (FTPoly a k t')) 
                -> t:Type -> ProofOf(HasFType g (AppT e t) (ftsubBV a (erase t) t'))
 |  FTLet  :: g:FEnv -> e_x:Expr -> b:FType -> ProofOf(HasFType g e_x b)
                -> x:Vname -> e:Expr -> b':FType 
                -> { y:Vname | not (in_envF y g) && not (Set_mem y (fv e)) }
                -> ProofOf(HasFType (FCons y b g) (unbind x y e) b')
                -> ProofOf(HasFType g (Let x e_x e) b')
 |  FTAnn  :: g:FEnv -> e:Expr -> b:FType 
                -> { t1:Type | (erase t1 == b) && Set_sub (free t1) (bindsF g)  }
                -> ProofOf(HasFType g e b) -> ProofOf(HasFType g (Annot e t1) b)  @-} 

-- old version : -> { t1:Type | (erase t1 == b) && Set_sub (free t1) (bindsF g) && Set_emp (tfreeBV t1) }
  
{-@ measure ftypSize @-}
{-@ ftypSize :: HasFType -> { v:Int | v >= 0 } @-}
ftypSize :: HasFType -> Int
ftypSize (FTBC {})                           = 1
ftypSize (FTIC {})                           = 1
ftypSize (FTVar1 {})                         = 1
ftypSize (FTVar2 _ _ _ p_x_b _ _)            = (ftypSize p_x_b)   + 1
ftypSize (FTPrm {})                          = 1
ftypSize (FTAbs _ _ _ _ _ _ p_e_b')          = (ftypSize p_e_b')  + 1
ftypSize (FTApp _ _ _ _ p_e_bb' _ p_e'_b)    = (ftypSize p_e_bb') + (ftypSize p_e'_b) + 1
ftypSize (FTAbsT _ _ _ _ _ _ p_e_b)          = (ftypSize p_e_b)  + 1
ftypSize (FTAppT _ _ _ _ _ p_e_at' _)        = (ftypSize p_e_at') + 1
ftypSize (FTLet _ _ _ p_ex_b _ _ _ _ p_e_b') = (ftypSize p_ex_b)  + (ftypSize p_e_b') + 1
ftypSize (FTAnn _ _ _ _ p_e_b)               = (ftypSize p_e_b)   + 1

{-@ simpleFTVar :: g:FEnv -> { x:Vname | in_envF x g} -> { t:FType | bound_inF x t g } 
                -> ProofOf(HasFType g (FV x) t) @-}
simpleFTVar :: FEnv -> Vname -> FType -> HasFType
simpleFTVar g x t = case g of
  (FCons y s g') ->  case (x == y, t == s) of   -- g = Empty is impossible
        (True, True) -> FTVar1 g' x t           -- x = y but t != s is impossible
        (False, _)   -> FTVar2 g' x t (simpleFTVar g' x t) y s
  (FConsT a k g') -> case (x == a) of
        False        -> FTVar3 g' x t (simpleFTVar g' x t) a k

------------------------------------------------------------
---- | Limited Bi-directional TYPE Checking and Synthesis --
------------------------------------------------------------
--
-- The only expressions fow which we are trying to automate the production of
--    are the refinements found in the types of the built in primitives, in ty(c)
--    These consist of constants, primitives, variables and function application only.

{-@ reflect noDefns @-}
noDefns :: Expr -> Bool
noDefns (Bc _)          = True
noDefns (Ic _)          = True
noDefns (BV _)          = True
noDefns (FV _)          = True
noDefns (Prim _)        = True
noDefns (Lambda _ _)    = False
noDefns (App e e')      = (noDefns e) && (noDefns e')
noDefns (LambdaT _ _ _) = False
noDefns (AppT e t)      = (noDefns e) -- && (noDefns e')
noDefns (Let _ _ _)     = False
noDefns (Annot e t)     = noDefns e
noDefns Crash           = True

{-@ reflect checkType @-}
{-@ checkType :: FEnv -> { e:Expr | noDefns e } -> t:FType -> Bool / [esize e] @-}
checkType :: FEnv -> Expr -> FType -> Bool
checkType g (Bc b) t         = ( t == FTBasic TBool )
checkType g (Ic n) t         = ( t == FTBasic TInt )
checkType g (Prim c) t       = ( t == erase (ty c) )
checkType g (BV x) t         = False
checkType g (FV x) t         = bound_inF x t g
checkType g (App e e') t     = case ( synthType g e' ) of
    (Just t')       -> checkType g e (FTFunc t' t)
    _               -> False
checkType g (AppT e t2) t    = case ( synthType g e ) of
    (Just (FTPoly a k t1))    -> ( t == ftsubBV a (erase t2) t1 )
    _                       -> False
checkType g (Annot e liqt) t   = ( checkType g e t ) && ( t == erase liqt ) &&
                                 ( S.isSubsetOf (free liqt) (bindsF g) ) {- &&
                                 ( S.null (tfreeBV liqt) ) -}
checkType g Crash t            = False -- Crash is untypable

{-@ reflect synthType @-}
{-@ synthType :: FEnv -> { e:Expr | noDefns e } -> Maybe FType / [esize e] @-}
synthType :: FEnv -> Expr -> Maybe FType
synthType g (Bc b)          = Just ( FTBasic TBool )
synthType g (Ic n)          = Just ( FTBasic TInt )
synthType g (Prim c)        = Just ( erase (ty c) )
synthType g (BV x)          = Nothing
synthType g (FV x)          = lookupF x g
synthType g (App e e')      = case ( synthType g e' ) of
    Nothing    -> Nothing
    (Just t')  -> case ( synthType g e ) of
        (Just (FTFunc t_x t)) -> if ( t_x == t' ) then Just t else Nothing
        _                     -> Nothing
synthType g (AppT e t2)     = case ( synthType g e ) of
    (Just (FTPoly a k t1))   -> Just (ftsubBV a (erase t2) t1)
    _                      -> Nothing
synthType g (Annot e liqt)  = case ( checkType g e (erase liqt) && -- S.null (tfreeBV liqt) &&
                                     S.isSubsetOf (free liqt) (bindsF g) ) of
    True  -> Just (erase liqt)
    False -> Nothing
synthType g Crash           = Nothing

{-@ lem_check_synth :: g:FEnv -> { e:Expr | noDefns e } -> { t:FType | synthType g e == Just t }
                              -> { pf:_ | checkType g e t } @-}
lem_check_synth :: FEnv -> Expr -> FType -> Proof
lem_check_synth g (Bc b) t         = case t of 
    (FTBasic TBool) -> ()
lem_check_synth g (Ic n) t         = case t of
    (FTBasic TInt)  -> () 
lem_check_synth g (Prim c) t       = ()
lem_check_synth g (FV x) t         = lem_lookup_boundinF x t g 
lem_check_synth g (App e e') t     = lem_check_synth g e (FTFunc t' t) 
  where
    (Just t') = synthType g e' 
lem_check_synth g (AppT e t2) t    = () -- TODO: recheck this
  where
    (Just (FTPoly a k t1)) = synthType g e
lem_check_synth g (Annot e liqt) t = ()

{-@ makeHasFType :: g:FEnv -> { e:Expr | noDefns e } -> { t:FType | checkType g e t }
        -> ProofOf(HasFType g e t) / [esize e] @-}
makeHasFType :: FEnv -> Expr -> FType -> HasFType
makeHasFType g (Bc b) t         = FTBC g b
makeHasFType g (Ic n) t         = FTIC g n
makeHasFType g (Prim c) t       = FTPrm g c
makeHasFType g (FV x) t         = simpleFTVar g (x? lem_boundin_inenvF x t g ) t
makeHasFType g (App e e') t     = FTApp g e t' t pf_e_t't e' pf_e'_t'
  where
    (Just t')  = synthType g e'
    pf_e_t't   = makeHasFType g e (FTFunc t' t)
    pf_e'_t'   = makeHasFType g e' (t' ? lem_check_synth g e' t')
makeHasFType g (AppT e t2) t    = FTAppT g e a k t1 pf_e_at1 t2
  where
    (Just (FTPoly a k t1)) = synthType g e 
    pf_e_at1               = makeHasFType g e (FTPoly a k t1)
makeHasFType g (Annot e liqt) t = FTAnn g e t liqt pf_e_t
  where
    pf_e_t = makeHasFType g e t

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

{-@ reflect refn_pred_freeBV @-}
refn_pred_freeBV :: Prim -> S.Set Vname
refn_pred_freeBV Not      = S.fromList [3,2]
refn_pred_freeBV (Leqn _) = S.fromList [3,2]
refn_pred_freeBV (Eqn _)  = S.fromList [3,2]
refn_pred_freeBV _        = S.fromList [3,2,1]

{- @ refn_pred :: c:Prim -> { p:Pred | noDefns p && yySet_sub (freeBV p) (refn_pred_freeBV c) -}
{-@ reflect refn_pred @-}
{-@ refn_pred :: c:Prim -> { p:Pred | noDefns p && Set_emp (fv p) } @-}
refn_pred :: Prim -> Pred
refn_pred And      = App (App (Prim Eqv) (BV 3)) 
                               (App (App (Prim And) (BV 1)) (BV 2)) 
refn_pred Or       = App (App (Prim Eqv) (BV 3)) 
                               (App (App (Prim Or) (BV 1)) (BV 2)) 
refn_pred Not      = App (App (Prim Eqv) (BV 3)) 
                           (App (Prim Not) (BV 2)) 
refn_pred Eqv      = App (App (Prim Eqv) (BV 3))
                               (App (App (Prim Or) 
                                    (App (App (Prim And) (BV 1)) (BV 2)))
                                    (App (App (Prim And) (App (Prim Not) (BV 1)))
                                         (App (Prim Not) (BV 2))))
refn_pred Leq      = App (App (Prim Eqv) (BV 3))
                               (App (App (Prim Leq) (BV 1)) (BV 2)) 
refn_pred (Leqn n) = App (App (Prim Eqv) (BV 3))
                           (App (App (Prim Leq) (Ic n)) (BV 2)) 
refn_pred Eq       = App (App (Prim Eqv) (BV 3))
                               (App (App (Prim Eq) (BV 1)) (BV 2))
refn_pred (Eqn n)  = App (App (Prim Eqv) (BV 3))
                           (App (App (Prim Eq) (Ic n)) (BV 2))

{-@ reflect un321_refn_pred @-}
{- @ un321_refn_pred :: c:Prim 
     -> { p:Pred | un321_refn_pred c == unbind 3 3 (un21_refn_pred c) } @-}
{- @ un321_refn_pred :: c:Prim -> { p:Pred | noDefns p } @-}
un321_refn_pred :: Prim -> Pred
un321_refn_pred And      = App (App (Prim Eqv) (FV 3)) 
                               (App (App (Prim And) (FV 1)) (FV 2)) 
un321_refn_pred Or       = App (App (Prim Eqv) (FV 3)) 
                               (App (App (Prim Or) (FV 1)) (FV 2)) 
un321_refn_pred Not      = App (App (Prim Eqv) (FV 3)) 
                               (App (Prim Not) (FV 2)) 
un321_refn_pred Eqv      = App (App (Prim Eqv) (FV 3))
                               (App (App (Prim Or) 
                                    (App (App (Prim And) (FV 1)) (FV 2)))
                                    (App (App (Prim And) (App (Prim Not) (FV 1)))
                                         (App (Prim Not) (FV 2))))
un321_refn_pred Leq      = App (App (Prim Eqv) (FV 3))
                               (App (App (Prim Leq) (FV 1)) (FV 2)) 
un321_refn_pred (Leqn n) = App (App (Prim Eqv) (FV 3))
                               (App (App (Prim Leq) (Ic n)) (FV 2)) 
un321_refn_pred Eq       = App (App (Prim Eqv) (FV 3))
                               (App (App (Prim Eq) (FV 1)) (FV 2))
un321_refn_pred (Eqn n)  = App (App (Prim Eqv) (FV 3))
                               (App (App (Prim Eq) (Ic n)) (FV 2))

{-@ reflect noDefnsInRefns @-}
noDefnsInRefns :: Env -> Type -> Bool
noDefnsInRefns g (TRefn b x p)      = noDefns (unbind x y p)
  where
    y = fresh_var g
noDefnsInRefns g (BTV a)            = True
noDefnsInRefns g (FTV a)            = True 
noDefnsInRefns g (TFunc x t_x t)    = noDefnsInRefns g t_x && noDefnsInRefns (Cons y t_x g) (unbindT x y t)
  where
    y = fresh_var g
noDefnsInRefns g (TExists x t_x t)  = noDefnsInRefns g t_x && noDefnsInRefns (Cons y t_x g) (unbindT x y t) 
  where
    y = fresh_var g
noDefnsInRefns g (TPoly   a  k  t)  = noDefnsInRefns (ConsT a' k g) (unbind_tvT a a' t)
  where
    a' = fresh_var g

{-@ reflect isWellFormed @-}
{-@ isWellFormed :: g:Env -> { t:Type| noDefnsInRefns g t } -> Bool  / [tsize t] @-}
isWellFormed :: Env -> Type -> Bool
isWellFormed g (TRefn b x p)     = checkType (FCons y (FTBasic b) (erase_env g)) (unbind x y p) (FTBasic TBool)
  where
    y = fresh_var g
isWellFormed g (BTV a)           = False
isWellFormed g (FTV a)           = case g of 
  Empty            -> False
  (Cons x t g')    -> isWellFormed g' (FTV a)
  (ConsT a' k g')  -> (a == a') || isWellFormed g' (FTV a)
isWellFormed g (TFunc x t_x t)   = isWellFormed g t_x && isWellFormed (Cons y t_x g) (unbindT x y t)
  where
    y = fresh_var g
isWellFormed g (TExists x t_x t) = isWellFormed g t_x && isWellFormed (Cons y t_x g) (unbindT x y t)
  where
    y = fresh_var g
isWellFormed g (TPoly a  k  t)   = isWellFormed (ConsT a' k g) (unbind_tvT a a' t)
  where
    a' = fresh_var g

{-@ reflect isKindCompat @-}
isKindCompat :: Env -> Type -> Kind -> Bool
isKindCompat g (TRefn b x p) k     = True
isKindCompat g (BTV a) k           = True
isKindCompat g (FTV a) k           = True
isKindCompat g (TFunc x t_x t) k   = k == Star
isKindCompat g (TExists x t_x t) k = isKindCompat g t k
isKindCompat g (TPoly a k'  t) k   = isKindCompat g t k


{-@ reflect ty @-} -- Primitive Typing            -- removed: && Set_emp (tfreeBV t)
{-@ ty :: c:Prim -> { t:Type | noDefnsInRefns Empty t && isWellFormed Empty t && Set_emp (free t) 
                                                      && t == TFunc (firstBV c) (inType c) (ty' c) } @-}
ty :: Prim -> Type
ty And      = TFunc 1 (TRefn TBool 1 (Bc True)) 
                  (TFunc 2 (TRefn TBool 2 (Bc True)) 
                      (TRefn TBool 3 (refn_pred And)))
ty Or       = TFunc 1 (TRefn TBool 1 (Bc True)) 
                  (TFunc 2 (TRefn TBool 2 (Bc True)) 
                      (TRefn TBool 3  (refn_pred Or)))
ty Not      = TFunc 2 (TRefn TBool 2 (Bc True)) 
                  (TRefn TBool 3 (refn_pred Not))
ty Eqv      = TFunc 1 (TRefn TBool 1 (Bc True))
                  (TFunc 2 (TRefn TBool 2 (Bc True))  
                      (TRefn TBool 3 (refn_pred Eqv)))
ty Leq      = TFunc 1 (TRefn TInt 1 (Bc True)) 
                  (TFunc 2 (TRefn TInt 2 (Bc True)) 
                      (TRefn TBool 3 (refn_pred Leq)))
ty (Leqn n) = TFunc 2 (TRefn TInt 2 (Bc True)) 
                  (TRefn TBool 3 (refn_pred (Leqn n)))
ty Eq       = TFunc 1 (TRefn TInt 1 (Bc True)) 
                  (TFunc 2 (TRefn TInt 2 (Bc True)) 
                      (TRefn TBool 3 (refn_pred Eq)))
ty (Eqn n)  = TFunc 2 (TRefn TInt 2 (Bc True)) 
                  (TRefn TBool 3 (refn_pred (Eqn n)))

{-@ reflect firstBV @-}
firstBV :: Prim -> Int
firstBV Not      = 2
firstBV (Leqn _) = 2
firstBV (Eqn _)  = 2
firstBV _        = 1

{-@ reflect inType @-}
inType :: Prim -> Type
inType And = TRefn TBool 1 (Bc True)
inType Or  = TRefn TBool 1 (Bc True)
inType Eqv = TRefn TBool 1 (Bc True)
inType Not = TRefn TBool 2 (Bc True)
inType Leq = TRefn TInt 1 (Bc True)
inType Eq  = TRefn TInt 1 (Bc True)
inType _   = TRefn TInt 2 (Bc True)

{-@ reflect ty' @-}
ty' :: Prim -> Type
ty' And      = TFunc 2 (TRefn TBool 2 (Bc True)) (TRefn TBool 3 (refn_pred And))
ty' Or       = TFunc 2 (TRefn TBool 2 (Bc True)) (TRefn TBool 3  (refn_pred Or))
ty' Not      = TRefn TBool 3 (refn_pred Not)
ty' Eqv      = TFunc 2 (TRefn TBool 2 (Bc True)) (TRefn TBool 3 (refn_pred Eqv))
ty' Leq      = TFunc 2 (TRefn TInt 2 (Bc True)) (TRefn TBool 3 (refn_pred Leq))
ty' (Leqn n) = TRefn TBool 3 (refn_pred (Leqn n))
ty' Eq       = TFunc 2 (TRefn TInt 2 (Bc True)) (TRefn TBool 3 (refn_pred Eq))
ty' (Eqn n)  = TRefn TBool 3 (refn_pred (Eqn n))


-----------------------------------------------------------------------------
----- | JUDGEMENTS : WELL-FORMEDNESS of TYPES and ENVIRONMENTS
-----------------------------------------------------------------------------

  --- Well-Formedness of Types

data WFTypeP where
    WFType :: Env -> Type -> Kind -> WFTypeP

data WFType where 
    WFRefn :: Env -> Vname -> Basic -> Pred -> Vname -> HasFType -> WFType
    WFVar1 :: Env -> Vname -> Kind -> WFType
    WFVar2 :: Env -> Vname -> Kind -> WFType -> Vname -> Type -> WFType
    WFVar3 :: Env -> Vname -> Kind -> WFType -> Vname -> Kind -> WFType
    WFFunc :: Env -> Vname -> Type -> Kind -> WFType -> Type -> Kind -> Vname -> WFType -> WFType
    WFExis :: Env -> Vname -> Type -> Kind -> WFType -> Type -> Kind -> Vname -> WFType -> WFType
    WFPoly :: Env -> Vname -> Kind -> Type -> Kind -> Vname -> WFType -> WFType
    WFKind :: Env -> Type -> WFType -> WFType

{-@ data WFType where
    WFRefn :: g:Env -> x:Vname -> b:Basic -> p:Pred 
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) }
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind x y p) (FTBasic TBool)) 
        -> ProofOf(WFType g (TRefn b x p) Base)
 |  WFVar1 :: g:Env -> { a:Vname | not (in_env a g) } -> k:Kind -> ProofOf(WFType (ConsT a k g) (FTV a) k)
 |  WFVar2 :: g:Env -> { a:Vname | in_env a g } -> k:Kind -> ProofOf(WFType g (FTV a) k)
        -> { y:Vname | y != a && not (in_env y g) } -> t:Type 
        -> ProofOf(WFType (Cons y t g) (FTV a) k)
 |  WFVar3 :: g:Env -> { a:Vname | in_env a g } -> k:Kind -> ProofOf(WFType g (FTV a) k)
        -> { a':Vname | a' != a && not (in_env a' g) } -> k':Kind -> ProofOf(WFType (ConsT a' k' g) (FTV a) k)
 |  WFFunc :: g:Env -> x:Vname -> t_x:Type -> k_x:Kind
        -> ProofOf(WFType g t_x k_x) -> t:Type -> k:Kind
        -> { y:Vname | not (in_env y g) && not (Set_mem y (free t)) }
        -> ProofOf(WFType (Cons y t_x g) (unbindT x y t) k) -> ProofOf(WFType g (TFunc x t_x t) Star)
 |  WFExis :: g:Env -> x:Vname -> t_x:Type -> k_x:Kind
        -> ProofOf(WFType g t_x k_x) -> t:Type -> k:Kind
        -> { y:Vname | not (in_env y g) && not (Set_mem y (free t)) }
        -> ProofOf(WFType (Cons y t_x g) (unbindT x y t) k) -> ProofOf(WFType g (TExists x t_x t) k) 
 |  WFPoly :: g:Env -> a:Vname -> k:Kind -> t:Type -> k_t:Kind
        -> { a':Vname | not (in_env a' g) && not (Set_mem a' (free t)) && not (Set_mem a' (freeTV t)) }
        -> ProofOf(WFType (ConsT a' k g) (unbind_tvT a a' t) k_t) -> ProofOf(WFType g (TPoly a k t) Star) 
 |  WFKind :: g:Env -> t:Type -> ProofOf(WFType g t Base) -> ProofOf(WFType g t Star) @-}

  -- TODO: what happened to k_t in WFPoly? why Star?

{-@ measure wftypSize @-}
{-@ wftypSize :: WFType -> { v:Int | v >= 0 } @-}
wftypSize :: WFType -> Int
wftypSize (WFRefn g x b p y p_yg_p_bl)            = 1
wftypSize (WFVar1 _ _ _)                          = 1
wftypSize (WFVar2 _ _ _ p_g_a _ _)                = (wftypSize p_g_a)  + 1
wftypSize (WFVar3 _ _ _ p_g_a _ _)                = (wftypSize p_g_a)  + 1
wftypSize (WFFunc g x t_x _ p_g_tx _ t y p_yg_t)  = (wftypSize p_g_tx) + (wftypSize p_yg_t) + 1
wftypSize (WFExis g x t_x _ p_g_tx _ t y p_yg_t)  = (wftypSize p_g_tx) + (wftypSize p_yg_t) + 1
wftypSize (WFPoly _ _ _ _ _ _ p_a'g_t)            = (wftypSize p_a'g_t) + 1
wftypSize (WFKind _ _ p_g_t)                      = (wftypSize p_g_t)  + 1

{-@ simpleWFVar :: g:Env -> { a:Vname | in_env a g } 
                -> ProofOf(WFType g (FTV a) Star) @-}
simpleWFVar :: Env -> Vname -> WFType
simpleWFVar g a   = case g of
  (Cons y s g')    -> case ( a == y ) of   -- g = Empty is impossible
        (False)    -> WFVar2 g' a Star (simpleWFVar g' a) y s
  (ConsT a' k' g') -> case ( a == a' ) of
        (True)     -> WFVar1 g' a Star          
        (False)    -> WFVar3 g' a Star (simpleWFVar g' a) a' k'

------------------------------------------------------------------------------------------
-- | AUTOMATING WELL-FORMEDNESS PROOF GENERATION for refinements that occur in practice --
------------------------------------------------------------------------------------------
{-
{-@ makeWFType :: g:Env -> { t:Type | noDefnsInRefns g t && isWellFormed g t && Set_sub (free t) (binds g) }
                        -> ProofOf(WFType g t Star) / [tsize t] @-}
makeWFType :: Env -> Type -> WFType
makeWFType g (TRefn b x p)     = WFKind g (TRefn b x p) p_g_t_base
  where
    y = fresh_var g
    p_g_t_base = WFRefn g x b p y (makeHasFType (FCons y (FTBasic b) (erase_env g)) 
                        (unbind x y p) (FTBasic TBool))
makeWFType g (FTV a)           = simpleWFVar g a 
makeWFType g (TFunc x t_x t)   = WFFunc g x t_x Star (makeWFType g t_x) t Star y
                                   (makeWFType (Cons y t_x g) (unbindT x y t))
  where
    y = fresh_var g
makeWFType g (TExists x t_x t) = WFExis g x t_x Star (makeWFType g t_x) t Star y
                                   (makeWFType (Cons y t_x g) (unbindT x y t))
  where
    y = fresh_var g
makeWFType g (TPoly a  k  t)   = WFPoly g a k t Star a' (makeWFType (ConsT a' k g) (unbind_tvT a a' t))
  where
    a' = fresh_var g
-}

  --- Well-formedness of Environments

data WFEnvP where
    WFEnv :: Env -> WFEnvP

data WFEnv where
    WFEEmpty :: WFEnv
    WFEBind  :: Env -> WFEnv -> Vname -> Type -> WFType -> WFEnv
    WFEBindT :: Env -> WFEnv -> Vname -> Kind -> WFEnv

{-@ data WFEnv where
    WFEEmpty :: ProofOf(WFEnv Empty)
 |  WFEBind  :: g:Env -> ProofOf(WFEnv g) -> { x:Vname | not (in_env x g) } -> t:Type 
                      -> ProofOf(WFType g t) -> ProofOf(WFEnv (Cons x t g)) 
 |  WFEBindT :: g:Env -> ProofOf(WFEnv g) -> { a:Vname | not (in_env a g) } -> k:Kind 
                                             -> ProofOf(WFEnv (ConsT a k g)) @-}

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

{-

-- Constant and Primitive Typing Lemmas
-- Lemma. Well-Formedness of Constant Types
{-@ lem_wf_tybc :: g:Env -> b:Bool -> ProofOf(WFType g (tybc b) Base) @-}
lem_wf_tybc :: Env -> Bool -> WFType
lem_wf_tybc g b = WFRefn g 1 TBool pred y pf_pr_bool
  where
     pred       = (App (App (Prim Eqv) (BV 1)) (Bc b)) 
     y          = (fresh_var g)
     g'         = (FCons y (FTBasic TBool) (erase_env g))
     pf_eqv_v   = FTApp g' (Prim Eqv) (FTBasic TBool) (FTFunc (FTBasic TBool) (FTBasic TBool)) 
                           (FTPrm g' Eqv) (FV y) (FTVar1 (erase_env g) y (FTBasic TBool))
     -- pf_pr_bool :: ProofOf(HasFType g' pred (FTBasic TBool)) @- }
     pf_pr_bool = FTApp g' (App (Prim Eqv) (FV y)) (FTBasic TBool) (FTBasic TBool) 
                           pf_eqv_v (Bc b) (FTBC g' b)

{-@ lem_wf_tyic :: g:Env -> n:Int -> ProofOf(WFType g (tyic n) Base) @-}
lem_wf_tyic :: Env -> Int -> WFType
lem_wf_tyic g n = WFRefn g 1 TInt pred y pf_pr_bool
  where
    pred        = (App (App (Prim Eq) (BV 1)) (Ic n))
    y           = fresh_var g
    g'          = (FCons y (FTBasic TInt) (erase_env g))
    pf_eq_v     = FTApp g' (Prim Eq) (FTBasic TInt) (FTFunc (FTBasic TInt) (FTBasic TBool)) 
                           (FTPrm g' Eq) (FV y) (FTVar1 (erase_env g) y (FTBasic TInt))
    pf_pr_bool  = FTApp g' (App (Prim Eq) (FV y)) (FTBasic TInt) (FTBasic TBool) 
                           pf_eq_v (Ic n) (FTIC g' n)

{-@ lem_wf_ty :: c:Prim -> ProofOf(WFType Empty (ty c) Star) @-}
lem_wf_ty :: Prim -> WFType
lem_wf_ty And      = makeWFType Empty (ty And) 
lem_wf_ty Or       = makeWFType Empty (ty Or) 
lem_wf_ty Not      = makeWFType Empty (ty Not) 
lem_wf_ty Eqv      = makeWFType Empty (ty Eqv) 
lem_wf_ty Leq      = makeWFType Empty (ty Leq) 
lem_wf_ty (Leqn n) = makeWFType Empty (ty (Leqn n)) 
lem_wf_ty Eq       = makeWFType Empty (ty Eq) 
lem_wf_ty (Eqn n)  = makeWFType Empty (ty (Eqn n))

-}

{-@ lem_bool_values :: { v:Expr | isValue v } -> ProofOf(HasFType FEmpty v (FTBasic TBool))
        -> { pf:_ | v == Bc True || v = Bc False } @-}
lem_bool_values :: Expr -> HasFType -> Proof
lem_bool_values v (FTBC _ _) = ()

{-@ reflect isInt @-}
isInt :: Expr -> Bool
isInt (Ic _ ) = True
isInt _       = False

{-@ lem_int_values :: v:Value -> ProofOf(HasFType FEmpty v (FTBasic TInt))
        -> { pf:_ | isInt v } @-}
lem_int_values :: Expr -> HasFType -> Proof
lem_int_values v (FTIC _ _) = ()

{-@ reflect isLambda @-}
isLambda :: Expr -> Bool
isLambda (Lambda _ _ ) = True
isLambda _             = False

{-@ reflect isPrim @-}
isPrim :: Expr -> Bool
isPrim (Prim _) = True
isPrim _        = False

{-@ lemma_function_values :: v:Value -> t:FType -> t':FType
        -> ProofOf(HasFType FEmpty v (FTFunc t t'))
        -> { pf:_ | isLambda v || isPrim v } @-}
lemma_function_values :: Expr -> FType -> FType -> HasFType -> Proof
lemma_function_values e t t' (FTPrm {})   = ()     
lemma_function_values e t t' (FTAbs {})   = ()    

{-
{-@ lem_delta_and_btyp :: v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim And) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta And v) t' } @-} -- &&
lem_delta_and_btyp :: Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_and_btyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty And) -> case v of
          (Bc True)  -> FTAbs FEmpty 1 (FTBasic TBool) (BV 1) (FTBasic TBool) 
                              1 (FTVar1 FEmpty 1 (FTBasic TBool) ) -- ? toProof ( unbind 1 1 (BV 1) === FV 1 ))
          (Bc False) -> FTAbs FEmpty 1 (FTBasic TBool) (Bc False) (FTBasic TBool) 
                              1 (FTBC (FCons 1 (FTBasic TBool) FEmpty) False)  
          _          -> impossible ("by lemma" ? lem_bool_values v p_v_tx) 


{-@ lem_delta_or_btyp :: v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim Or) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta Or v) t' } @-} 
lem_delta_or_btyp :: Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_or_btyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty Or) -> case v of
      (Bc True)  -> FTAbs FEmpty 1 (FTBasic TBool) (Bc True) (FTBasic TBool)
                          1 (FTBC (FCons 1 (FTBasic TBool) FEmpty) True)
      (Bc False) -> FTAbs FEmpty 1 (FTBasic TBool) (BV 1)    (FTBasic TBool) 
                          1 (FTVar1 FEmpty 1 (FTBasic TBool) ) -- ? toProof ( unbind 1 1 (BV 1) === FV 1 ))
      _          -> impossible ("by lemma" ? lem_bool_values v p_v_tx)


{-@ lem_delta_not_btyp :: v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim Not) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta Not v) t' } @-} 
lem_delta_not_btyp :: Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_not_btyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty Not) -> case v of
      (Bc True)  -> FTBC FEmpty False --    ? toProof ( t' === FTBasic TBool )
      (Bc False) -> FTBC FEmpty True  --    ? toProof ( t' === FTBasic TBool )
      _          -> impossible ("by lemma" ? lem_bool_values v p_v_tx)

{-@ lem_delta_eqv_btyp :: v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim Eqv) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta Eqv v) t' } @-} -- &&
lem_delta_eqv_btyp :: Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_eqv_btyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty Eqv) -> case v of
      (Bc True)  -> FTAbs FEmpty 1 (FTBasic TBool) (BV 1) (FTBasic TBool)
                          1 (FTVar1 FEmpty 1 (FTBasic TBool) ) -- ? toProof ( unbind 1 1 (BV 1) === FV 1 ))
      (Bc False) -> FTAbs FEmpty 1 (FTBasic TBool) not_x  (FTBasic TBool) 1 p_notx_bl
        where
          not_x     = App (Prim Not) (BV 1)
          g         = (FCons 1 (FTBasic TBool) FEmpty)
          p_notx_bl = FTApp g (Prim Not) (FTBasic TBool) (FTBasic TBool)
                            (FTPrm g Not) (FV 1) (FTVar1 FEmpty 1 (FTBasic TBool))
      _          -> impossible ("by lemma" ? lem_bool_values v p_v_tx)

{-@ lem_delta_leq_btyp :: v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim Leq) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta Leq v) t' } @-} 
lem_delta_leq_btyp :: Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_leq_btyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty Leq) -> case v of
      (Ic n) -> FTPrm FEmpty (Leqn n) --   ? toProof ( t' === (FTFunc (FTBasic TInt) (FTBasic TBool)) )
      _      -> impossible ("by lemma" ? lem_int_values v p_v_tx)

{-@ lem_delta_leqn_btyp :: n:Int -> v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim (Leqn n)) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta (Leqn n) v) t' } @-} 
lem_delta_leqn_btyp :: Int -> Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_leqn_btyp n v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty (Leqn _n)) -> case v of
      (Ic m) -> FTBC FEmpty ( n <= m ) --    ? toProof ( t' === FTBasic TBool)
      _      -> impossible ("by lemma" ? lem_int_values v p_v_tx)

{-@ lem_delta_eq_btyp :: v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim Eq) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta Eq v) t' } @-} -- &&
lem_delta_eq_btyp :: Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_eq_btyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty Eq) -> case v of
      (Ic n) -> FTPrm FEmpty (Eqn n) --    ? toProof ( t' === (FTFunc (FTBasic TInt) (FTBasic TBool)) )
      _      -> impossible ("by lemma" ? lem_int_values v p_v_tx)

{-@ lem_delta_eqn_btyp :: n:Int -> v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim (Eqn n)) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta (Eqn n) v) t' } @-} -- &&
lem_delta_eqn_btyp :: Int -> Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_eqn_btyp n v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty (Eqn _n)) -> case v of
      (Ic m) -> FTBC FEmpty ( n == m ) --    ? toProof ( t' === FTBasic TBool)
      _      -> impossible ("by lemma" ? lem_int_values v p_v_tx)

{-@ lem_delta_btyp :: c:Prim -> v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim c) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta c v) t' } @-} -- &&
--                    not ((delta c v) == Crash) } @- }
lem_delta_btyp :: Prim -> Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_btyp And      v t_x t' p_c_txt' p_v_tx = lem_delta_and_btyp    v t_x t' p_c_txt' p_v_tx
lem_delta_btyp Or       v t_x t' p_c_txt' p_v_tx = lem_delta_or_btyp     v t_x t' p_c_txt' p_v_tx
lem_delta_btyp Not      v t_x t' p_c_txt' p_v_tx = lem_delta_not_btyp    v t_x t' p_c_txt' p_v_tx
lem_delta_btyp Eqv      v t_x t' p_c_txt' p_v_tx = lem_delta_eqv_btyp    v t_x t' p_c_txt' p_v_tx
lem_delta_btyp Leq      v t_x t' p_c_txt' p_v_tx = lem_delta_leq_btyp    v t_x t' p_c_txt' p_v_tx
lem_delta_btyp (Leqn n) v t_x t' p_c_txt' p_v_tx = lem_delta_leqn_btyp n v t_x t' p_c_txt' p_v_tx
lem_delta_btyp Eq       v t_x t' p_c_txt' p_v_tx = lem_delta_eq_btyp     v t_x t' p_c_txt' p_v_tx
lem_delta_btyp (Eqn n)  v t_x t' p_c_txt' p_v_tx = lem_delta_eqn_btyp  n v t_x t' p_c_txt' p_v_tx
-}
