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

{-@ type Term = { e:Expr | isTerm e } @-}

{-@ reflect isTerm @-} -- a legal program term is an expression that does not contain Conj
isTerm :: Expr -> Bool --     (outside of refinements of course)
isTerm (Bc _)           = True
isTerm (Ic _)           = True
isTerm (Prim c)         = not ( c == Conj )
isTerm (BV _)           = True
isTerm (FV _)           = True
isTerm (Lambda _ e)     = isTerm e
isTerm (App e e')       = isTerm e && isTerm e'
isTerm (LambdaT _ _ e)  = isTerm e  
isTerm (AppT e t)       = isTerm e
isTerm (Let _ e_x e)    = isTerm e_x && isTerm e 
isTerm (Annot e t)      = isTerm e

{-@ type Value = { v:Term | isValue v } @-}
{-@ type PredValue = { v:Pred | isValue v } @-}

{-@ reflect isValue @-} -- meaning: is a syntactic value in normal expression
isValue :: Expr -> Bool
isValue (Bc _)          = True
isValue (Ic _)          = True
isValue (Prim c)        = True
isValue (FV _)          = True 
isValue (BV _)          = True -- Lambda 2.1: changed mind: now bound variables a legal value 
                               -- even though we want all values to be
isValue (Lambda x e)    = True --     well-formed as expressions
isValue (LambdaT a k e) = True
isValue _               = False

{-@ measure freeBV @-}
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

{-@ measure freeBTV @-}
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


  --- TERM-LEVEL SUBSTITUTION

--                                ( (noDefns v && noDefns e) => noDefns e' ) } / [esize e] @-}
{-@ reflect subFV @-} -- substitute a value for a term variable in a term 
{-@ subFV :: x:Vname -> v:Value -> e:Expr 
                     -> { e':Expr | (Set_mem x (fv e) || e == e') &&
                      ( Set_sub (fv e) (Set_cup (Set_sng x) (fv e')) ) &&
                      ( Set_sub (fv e') (Set_cup (fv v) (Set_dif (fv e) (Set_sng x)))) &&
                      ( (not (Set_mem x (fv v))) => not (Set_mem x (fv e')) ) && 
                        Set_sub (ftv e) (ftv e') &&
                        Set_sub (ftv e') (Set_cup (ftv e) (ftv v)) &&
                      ( Set_sub (freeBV e) (freeBV e') ) &&
                      ( Set_sub (freeBV e') (Set_cup (freeBV e) (freeBV v)) ) &&
                      ( Set_sub (freeBTV e) (freeBTV e') ) &&
                      ( Set_sub (freeBTV e') (Set_cup (freeBTV e) (freeBTV v)) ) &&
                      ( e == Bc True => e' == Bc True ) && ( isTerm e => isTerm e' ) &&
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
{-
                      ( (not (Set_mem a (freeTV t))) => not (Set_mem a (ftv e')) ) && 
 -}
--  removed for now:                           Set_sub (freeBV e)  (freeBV e') &&
--                      ( noDefns e => noDefns e' ) } / [esize e] @-}
--                      -- try without:
--                      ( Set_sub (ftv e) (Set_cup (Set_sng a) (ftv e')) ) &&
--                        Set_sub (fv e) (fv e') &&
{-@ reflect subFTV @-} -- substitute a type for a type variable in a term 
{-@ subFTV :: a:Vname -> t:UserType -> e:Expr 
                      -> { e':Expr | (Set_mem a (ftv e) || e == e') &&
                      ( Set_sub (ftv e') (Set_cup (freeTV t) (Set_dif (ftv e) (Set_sng a)))) &&
                        Set_sub (fv e') (Set_cup (fv e) (free t)) &&
                        Set_sub (freeBV e')  (Set_cup (tfreeBV t) (freeBV e)) &&
                        Set_sub (freeBTV e') (Set_cup (tfreeBTV t) (freeBTV e)) &&
                      ( isValue e => isValue e' ) && ( isTerm e => isTerm e' ) &&
                      ( e == Bc True => e' == Bc True )} / [esize e] @-}
subFTV :: Vname -> Type -> Expr -> Expr
subFTV a t_a (Bc b)                    = Bc b
subFTV a t_a (Ic n)                    = Ic n
subFTV a t_a (Prim p)                  = Prim p
subFTV a t_a (BV y)                    = BV y
subFTV a t_a (FV y)                    = FV y
subFTV a t_a (Lambda y e)              = Lambda  y  (subFTV a t_a e)
subFTV a t_a (App e e')                = App   (subFTV a t_a e)  (subFTV a t_a e')
subFTV a t_a (LambdaT a' k e)          = LambdaT a' k (subFTV a t_a e)
subFTV a t_a (AppT e t)                = AppT  (subFTV a t_a e) (tsubFTV a t_a t)
subFTV a t_a (Let y e1 e2)             = Let y (subFTV a t_a e1) (subFTV a t_a e2)
subFTV a t_a (Annot e t)               = Annot (subFTV a t_a e) (tsubFTV a t_a t) 

-- TODO removed for now: e' == (subBTV a (TRefn (FTV a') 1 (Bc True)) e) &&
--                            (not (Set_mem a (ftv e))) => not (Set_mem a (ftv e')) &&
--                                 (noDefns e => noDefns e') } / [esize e] @-}
{-@ reflect chgFTV @-}
{-@ chgFTV :: a:Vname -> a':Vname -> e:Expr
                  -> { e':Expr | (Set_mem a (ftv e) || e == e') &&
                                 Set_sub (ftv e)  (Set_cup (Set_sng a) (ftv e')) &&
                                 Set_sub (ftv e') (Set_cup (Set_sng a') (Set_dif (ftv e) (Set_sng a))) &&
                                 ( a != a'  => not (Set_mem a (ftv e'))) &&
                                 ( e == Bc True => e' == Bc True ) &&
                                 freeBV e == freeBV e' && freeBTV e == freeBTV e' &&
                                 fv e == fv e' && (isValue e => isValue e') } / [esize e] @-}
chgFTV :: Vname -> Vname -> Expr -> Expr
chgFTV a a' (Bc b)                = Bc b
chgFTV a a' (Ic n)                    = Ic n
chgFTV a a' (Prim p)                  = Prim p
chgFTV a a' (BV y)                    = BV y
chgFTV a a' (FV y)                    = FV y
chgFTV a a' (Lambda y e)              = Lambda  y  (chgFTV a a' e)
chgFTV a a' (App e e')                = App   (chgFTV a a' e)  (chgFTV a a' e')
chgFTV a a' (LambdaT a1 k e)          = LambdaT a1 k (chgFTV a a' e)
chgFTV a a' (AppT e bt)               = AppT  (chgFTV a a' e) (tchgFTV a a' bt)
chgFTV a a' (Let y e1 e2)             = Let y (chgFTV a a' e1) (chgFTV a a' e2)
chgFTV a a' (Annot e t)               = Annot (chgFTV a a' e) (tchgFTV a a' t) 

--                                    ( (noDefns v && noDefns e) => noDefns e' ) } / [esize e] @-}
{-@ reflect subBV @-} --substitute a value for x, which is a BOUND var
{-@ subBV :: x:Vname ->  v:Value -> e:Expr 
                     -> { e':Expr | Set_sub (fv e) (fv e') &&
                                    Set_sub (fv e') (Set_cup (fv e) (fv v)) &&
                                    Set_sub (ftv e) (ftv e') &&
                                    Set_sub (ftv e') (Set_cup (ftv e) (ftv v)) &&
                                    Set_sub (freeBV e')  (Set_cup (Set_dif (freeBV e) (Set_sng x)) (freeBV v)) &&
                                    Set_sub (Set_dif (freeBV e) (Set_sng x)) (freeBV e') &&
                                    Set_sub (freeBTV e') (Set_cup (freeBTV e) (freeBTV v)) &&
                                    Set_sub (freeBTV e) (freeBTV e') &&
                                    ( e == Bc True => e' == Bc True ) && ( isTerm e => isTerm e' ) &&
                                    ( esize v != 1  || esize e == esize e' ) } / [esize e] @-}
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

{-  TODO: work these back in!
                                    Set_sub (freeBV e) (freeBV e') &&
                                    Set_sub (freeBV e') (Set_cup (tfreeBV t) (freeBV e)) &&
                                    Set_sub (freeBTV e') (Set_cup (Set_dif (freeBTV e) (Set_sng a)) (tfreeBTV t)) &&
                                    Set_sub (Set_dif (freeBTV e) (Set_sng a)) (freeBTV e') &&
-}
--     ( isTrivial t =>  esize e == esize e' )        ( noDefns e => noDefns e' ) } / [esize e] @-}
--     try without:
--                                    Set_sub (fv e) (fv e') &&
--                                    Set_sub (ftv e) (ftv e') &&
{-@ reflect subBTV @-} -- substitute in a type for a BOUND TYPE var
{-@ subBTV :: a:Vname -> t:UserType -> e:Expr
                     -> { e':Expr | ( Set_mem a (freeBTV e) || e == e' ) &&
                                    Set_sub (fv e') (Set_cup (fv e) (free t)) &&
                                    Set_sub (ftv e') (Set_cup (ftv e) (freeTV t)) &&
                                    ( isTerm e => isTerm e' ) &&
                                    ( e == Bc True => e' == Bc True ) } / [esize e] @-}
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

--                                   esize e == esize e' && (noDefns e => noDefns e') } / [esize e] @-}
{-@ reflect unbind @-} -- unbind converts (BV x) to (FV y) in e 
{-@ unbind :: x:Vname -> y:Vname -> e:Expr 
                    -> { e':Expr | Set_sub (fv e) (fv e') && 
                                   Set_sub (fv e') (Set_cup (Set_sng y) (fv e)) &&
                                   Set_sub (ftv e) (ftv e') && Set_sub (ftv e') (ftv e) &&
                                   freeBV e' == Set_dif (freeBV e) (Set_sng x) &&
                                   freeBTV e' == freeBTV e && esize e == esize e' } / [esize e] @-}
unbind :: Vname -> Vname -> Expr -> Expr
unbind x y e = subBV x (FV y) e

--TODO not strictly true anymore:   e' == (subBTV a (TRefn (FTV a') 1 (Bc True)) e)
--                                   esize e == esize e' && (noDefns e => noDefns e') } / [esize e] @-} 
{-@ reflect unbind_tv @-} -- unbind converts (BTV a) to (FTV a') in e -- aka "chgBTV"
{-@ unbind_tv :: a:Vname -> a':Vname -> e:Expr 
                    -> { e':Expr | Set_sub (ftv e) (ftv e') && 
                                   Set_sub (ftv e') (Set_cup (Set_sng a') (ftv e)) &&
                                   Set_sub (fv e) (fv e') && Set_sub (fv e') (fv e) &&
                                   freeBV e' == freeBV e && esize e == esize e' &&
                                   freeBTV e' == Set_dif (freeBTV e) (Set_sng a) &&
                                   ( e == Bc True => e' == Bc True ) } / [esize e] @-}
unbind_tv :: Vname -> Vname -> Expr -> Expr
unbind_tv a a' (Bc b)                       = Bc b
unbind_tv a a' (Ic n)                       = Ic n
unbind_tv a a' (Prim p)                     = Prim p
unbind_tv a a' (BV y)                       = BV y -- looking for type vars
unbind_tv a a' (FV y)                       = FV y
unbind_tv a a' (Lambda y e)                 = Lambda y (unbind_tv a a' e)
unbind_tv a a' (App e e')                   = App   (unbind_tv a a' e)  (unbind_tv a a' e')
unbind_tv a a' (LambdaT a1 k e) | a == a1   = LambdaT a1 k e
                                | otherwise = LambdaT a1 k (unbind_tv a a' e)
unbind_tv a a' (AppT e t)                   = AppT  (unbind_tv a a' e) (unbind_tvT a a' t)
unbind_tv a a' (Let y e1 e2)                = Let y (unbind_tv a a' e1) (unbind_tv a a' e2)
unbind_tv a a' (Annot e t)                  = Annot (unbind_tv a a' e) (unbind_tvT a a' t)

  ---  Refinement Level: Names, Terms (in FO), FO Predicates, SMT Formulae

-- For now we'll allow refinements to have definitions in theory, but the ones we'll actually use won't,
--   so the issue of the incorrect substitution def'n w/ capture (TODO) can be avoided for now.
{- @ type Pred = { p:Expr | noDefns p } @-}
type Pred = Expr 

-- Assuming the binder in a refinement is always 0, so we don't have to worry about change of vars
-- new definition: we need this to be right-associate for the substitution properties to go through
{-@ reflect strengthen @-}
{-@ strengthen :: p:Pred -> r:Pred -> { q:Pred | Set_sub (fv q) (Set_cup (fv p) (fv r)) && 
                                                 Set_sub (Set_cup (fv p) (fv r)) (fv q) && 
                                                 Set_sub (ftv q) (Set_cup (ftv p) (ftv r)) && 
                                                 Set_sub (Set_cup (ftv p) (ftv r)) (ftv q) &&
                                                 freeBV q  == Set_cup (freeBV p) (freeBV r) &&
                                                 freeBTV q == Set_cup (freeBTV p) (freeBTV r) } @-} 
strengthen :: Pred -> Pred -> Pred
strengthen (App (App (Prim Conj) p) q) r = strengthen p (strengthen q r)
strengthen p                           r = App (App (Prim Conj) p) r

-- Star-kinded type variables may only be refined with a trivial predicate.
-- a trivial predicate is Bc True and its strengthenings by one more Trues:
--    i.e. True, True `And` True, True `And` True `And` True, and so on.
{-@ reflect isTrivial @-}
isTrivial :: Pred -> Bool
isTrivial (Bc True)         = True
isTrivial (App p r)         = (p == App (Prim Conj) (Bc True)) && isTrivial r
isTrivial _                 = False

{-@ lem_trivial_nofv :: { p:Pred | isTrivial p } 
        -> { pf:_ | Set_emp (fv p) && Set_emp (ftv p) } @-} 
lem_trivial_nofv :: Pred -> Proof
lem_trivial_nofv (Bc True) = ()
lem_trivial_nofv (App p r) = case p of
  (App (Prim Conj) (Bc True)) -> lem_trivial_nofv r

{-@ lem_trivial_nobv :: { p:Pred | isTrivial p } 
        -> { pf:_ | Set_emp (freeBV p) && Set_emp (freeBTV p) } @-}
lem_trivial_nobv :: Pred -> Proof
lem_trivial_nobv (Bc True) = ()
lem_trivial_nobv (App p r) = case p of
  (App (Prim Conj) (Bc True)) -> lem_trivial_nobv r

  ---   TYPES

data Basic = TBool         -- Bool
           | TInt          -- Int
           | BTV     Vname   -- a                    -- NEW!
           | FTV     Vname   -- a                    -- NEW!
  deriving (Eq, Show)

{-@ reflect isBTV @-}
isBTV :: Basic -> Bool
isBTV (BTV _) = True
isBTV _       = False

data Kind = Base         -- B, base kind
          | Star         -- *, star kind
  deriving (Eq, Show)

{-@ measure ksize @-}
{-@ ksize :: Kind -> { v:Int | v >= 0 } @-}
ksize :: Kind -> Int
ksize Base = 0
ksize Star = 1

{- @ type RVname =  { v:Int | v = 0 } @-} 
-- this stands in for the above b/c LH isn't inferring all refn binders are equal
data RVname = Z deriving (Eq, Show)

{-@ data Type [tsize] where 
        TRefn   :: Basic -> RVname -> Pred -> Type  
      | TFunc   :: Vname -> Type  -> Type -> Type 
      | TExists :: Vname -> Type  -> Type -> Type 
      | TPoly   :: Vname -> Kind  -> Type -> Type @-} -- @-}
data Type = TRefn   Basic RVname Pred     -- b{x0 : p}
          | TFunc   Vname Type Type      -- x:t_x -> t
          | TExists Vname Type Type      -- \exists x:t_x. t
          | TPoly   Vname Kind Type      -- \forall a:k. t
  deriving (Eq, Show)

  -- This will also avoid issues of capture in type variable substitution and refinement strengthening
{-@ type UserType = { t:Type | noExists t } @-}

{-@ reflect noExists @-}
noExists :: Type -> Bool          -- any types that appear in a well-typed refinement p will also necc.
noExists (TRefn b x p)     = True --   be UserTypes as well.
noExists (TFunc x t_x t)   = noExists t_x && noExists t
noExists (TExists x t_x t) = False
noExists (TPoly a k   t)   = noExists t

  -- ONLY types with Base Kind may have non-trivial refinements. Star kinded type variables 
  --     may only have the refinement { x : Bc True }.
{-
{-@ reflect isBare @-}
isBare :: Type -> Bool
isBare (TRefn b x p)     = p == Bc True
isBare (TFunc x t_x t)   = isBare t_x && isBare t
isBare (TExists x t_x t) = {-isBare t_x && isBare t-} False
isBare (TPoly a k   t)   = isBare t
-}

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

{-@ reflect isTFunc @-}
isTFunc :: Type -> Bool
isTFunc (TFunc {}) = True
isTFunc _          = False

{-@ reflect isTPoly @-}
isTPoly :: Type -> Bool
isTPoly (TPoly {}) = True
isTPoly _          = False

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

{-@ measure tfreeBV @-}
{-@ tfreeBV :: t:Type -> S.Set Vname / [tsize t] @-}
tfreeBV :: Type -> S.Set Vname
tfreeBV (TRefn b x r)     = S.difference (freeBV r) (S.singleton 0)
tfreeBV (TFunc x t_x t)   = S.union (tfreeBV t_x) (S.difference (tfreeBV t) (S.singleton x))
tfreeBV (TExists x t_x t) = S.union (tfreeBV t_x) (S.difference (tfreeBV t) (S.singleton x))
tfreeBV (TPoly a  k  t)   = (tfreeBV t)

{-@ measure tfreeBTV @-}
{-@ tfreeBTV :: t:Type -> S.Set Vname / [tsize t] @-}
tfreeBTV :: Type -> S.Set Vname
tfreeBTV (TRefn b x r)     = case b of --freeBTV r
  (BTV a)     -> S.union (S.singleton a) (freeBTV r)
  _           -> freeBTV r
tfreeBTV (TFunc x t_x t)   = S.union (tfreeBTV t_x) (tfreeBTV t) 
tfreeBTV (TExists x t_x t) = S.union (tfreeBTV t_x) (tfreeBTV t) 
tfreeBTV (TPoly a  k  t)   = S.difference (tfreeBTV t) (S.singleton a)

-- When substituting in for a type variable, say a{x:p}[t_a/a], where t_a is not a refined
--     basic type, then we need to express "t_a {x:p}" by pushing the refinement down into t_a.
--     For example a{x:p}[ ( \exists y:Int{y:q}. a'{z:r} )/a] becomes roughly speaking
--             \exists Int{y:q}. a'{z:r `And` p}
-- Assumption: x is the same as the binder of any refinement types
-- NO LONGER TRUE:     ( p != Bc True || t' == t) && ( isTrivial t => tsize t' == esize p + 1 ) } @-}
--   removed 12/21               Set_sub (Set_cup (free t) (fv p)) (free t') &&
--   removed 12/21               Set_sub (Set_cup (freeTV t) (ftv p)) (freeTV t') &&
--   try without these:
--                               Set_sub (free t) (free t') &&
--                               Set_sub (freeTV t) (freeTV t') &&
--                               Set_sub (tfreeBV t) (tfreeBV t') &&
--                               Set_sub (tfreeBTV t)  (tfreeBTV t') &&
{-@ reflect push @-}
{-@ push ::  p:Pred -> t:UserType 
                -> { t':UserType | Set_sub (free t') (Set_cup (free t) (fv p)) && 
                               Set_sub (freeTV t') (Set_cup (freeTV t) (ftv p)) &&
                               Set_sub (tfreeBV t') (Set_cup (tfreeBV t) (Set_dif (freeBV p) (Set_sng 0))) &&
                               Set_sub (tfreeBTV t') (Set_cup (tfreeBTV t) (freeBTV p)) &&
                               ( erase t' == erase t ) } @-}  
push :: Pred -> Type -> Type
push p (TRefn   b x   r) = TRefn   b x            (strengthen p r)
push p (TFunc   y t_y t) = TFunc   y t_y t -- TFunc   y (push p t_y) (push p t) -- remove this later? p must be trivial
--push p (TExists y t_y t) = TExists y t_y          (push p t)
push p (TPoly   a k   t) = TPoly   a k   t -- TPoly   a k            (push p t) -- remove this later? p must be trivial

-- Also note that non-trivially-refined Star types are unsound, so we cannot have t_a with Star
--     kind unless p == True, in which case there's nothing to push down. So this only really
--     affects the existential types.

--  removed for now:              (isBare t => isBare t')
{-@ reflect tsubFV @-}
{-@ tsubFV :: x:Vname -> e:Value -> t:Type  
         -> { t':Type | ( Set_mem x (free t) || t == t' ) && 
                        ( Set_sub (free t) (Set_cup (Set_sng x) (free t'))) &&
                ( Set_sub (free t') (Set_cup (fv e) (Set_dif (free t) (Set_sng x))) ) &&
                        Set_sub (freeTV t) (freeTV t') &&
                        Set_sub (freeTV t') (Set_cup (ftv e) (freeTV t)) &&
                        Set_sub (tfreeBV t) (tfreeBV t') &&
                        Set_sub (tfreeBV t') (Set_cup (tfreeBV t) (freeBV e)) &&
                        Set_sub (tfreeBTV t) (tfreeBTV t') &&
                        Set_sub (tfreeBTV t') (Set_cup (tfreeBTV t) (freeBTV e)) &&
                        ( (not (Set_mem x (fv e))) => not (Set_mem x (free t')) ) &&
                        ( noExists t => noExists t' ) } / [tsize t] @-}
tsubFV :: Vname -> Expr -> Type -> Type
tsubFV x v_x (TRefn b z r)     = TRefn b z  (subFV x v_x r)
tsubFV x v_x (TFunc z t_z t)   = TFunc   z (tsubFV x v_x t_z) (tsubFV x v_x t)
tsubFV x v_x (TExists z t_z t) = TExists z (tsubFV x v_x t_z) (tsubFV x v_x t)
tsubFV x v_x (TPoly a k   t)   = TPoly   a k                  (tsubFV x v_x t)

--  removed for now:     ((isBare t_a && isBare t) => isBare t') 
--  trywithout:
--                        ( Set_sub (freeTV t) (Set_cup (Set_sng a) (freeTV t'))) &&
--                        Set_sub (free t) (free t') &&
{-@ reflect tsubFTV @-}
{-@ tsubFTV :: a:Vname -> t_a:UserType -> t:Type 
         -> { t':Type | ( Set_mem a (freeTV t) || t == t' )  &&
                ( Set_sub (freeTV t') (Set_cup (freeTV t_a) (Set_dif (freeTV t) (Set_sng a))) ) &&
                        Set_sub (free t') (Set_cup (free t_a) (free t)) && 
                ( (not (Set_mem a (freeTV t_a))) => not (Set_mem a (freeTV t')) ) &&
                        Set_sub (tfreeBV t') (Set_cup (tfreeBV t_a) (tfreeBV t)) && 
                        Set_sub (tfreeBTV t') (Set_cup (tfreeBTV t_a) (tfreeBTV t)) &&
                        ( noExists t => noExists t' ) } / [tsize t] @-} 
tsubFTV :: Vname -> Type -> Type -> Type
tsubFTV a t_a (TRefn b x r)        = case b of
  (FTV a') | a == a' -> push  (subFTV a t_a r) t_a
  _                  -> TRefn b x (subFTV a t_a r)
tsubFTV a t_a (TFunc   z t_z t)    = TFunc   z  (tsubFTV a t_a t_z) (tsubFTV a t_a t)
tsubFTV a t_a (TExists z t_z t)    = TExists z  (tsubFTV a t_a t_z) (tsubFTV a t_a t)
tsubFTV a t_a (TPoly   a' k  t)    = TPoly   a' k                   (tsubFTV a t_a t)

-- removed for now        (isBare t => isBare t') &&    
--                        ( not (Set_mem a (freeTV t)) => not (Set_mem a (freeTV t')) ) } / [tsize t] @-}
{-@ reflect tchgFTV @-}
{-@ tchgFTV :: a:Vname -> a':Vname -> t:Type
                -> { t':Type | (Set_mem a (freeTV t) || t == t') && (free t' == free t) && 
                               Set_sub (freeTV t) (Set_cup (Set_sng a) (freeTV t')) &&
                               Set_sub (freeTV t') (Set_cup (Set_sng a') (Set_dif (freeTV t) (Set_sng a))) &&
                               tfreeBV t == tfreeBV t' && tfreeBTV t == tfreeBTV t' &&
                               ( a != a' => not (Set_mem a (freeTV t')) ) &&
                               ( noExists t => noExists t' ) } / [tsize t] @-}
tchgFTV :: Vname -> Vname -> Type -> Type
tchgFTV a a' (TRefn b x r)      = case b of
  (FTV a1) | a == a1 -> TRefn (FTV a') x (chgFTV a a' r)
  _                  -> TRefn b        x (chgFTV a a' r)
tchgFTV a a' (TFunc   x  t_x t) = TFunc   x (tchgFTV a a' t_x) (tchgFTV a a' t)
tchgFTV a a' (TExists x  t_x t) = TExists x (tchgFTV a a' t_x) (tchgFTV a a' t)
tchgFTV a a' (TPoly   a1 k   t) = TPoly   a1 k                 (tchgFTV a a' t)

{-@ reflect tsubBV @-}  --  (isBare t => isBare t') &&
{-@ tsubBV :: x:Vname -> v_x:Value -> t:Type  
                -> { t':Type | Set_sub (free t) (free t') &&
                               Set_sub (free t') (Set_cup (fv v_x) (free t)) &&
                               Set_sub (freeTV t) (freeTV t') &&
                               Set_sub (freeTV t') (Set_cup (ftv v_x) (freeTV t)) &&
                               Set_sub (tfreeBV t') (Set_cup (Set_dif (tfreeBV t) (Set_sng x)) (freeBV v_x)) &&
                               Set_sub (Set_dif (tfreeBV t) (Set_sng x)) (tfreeBV t') &&
                               Set_sub (tfreeBTV t') (Set_cup (tfreeBTV t) (freeBTV v_x)) &&
                               Set_sub (tfreeBTV t) (tfreeBTV t') && 
                               ( esize v_x != 1 || tsize t == tsize t' ) } / [tsize t] @-}
tsubBV :: Vname -> Expr -> Type -> Type
tsubBV x v_x (TRefn b y r)     
  | x == 0                     = TRefn b y r
  | otherwise                  = TRefn b y  (subBV x v_x r)
tsubBV x v_x (TFunc z t_z t)   
  | x == z                     = TFunc   z (tsubBV x v_x t_z) t
  | otherwise                  = TFunc   z (tsubBV x v_x t_z) (tsubBV x v_x t)
tsubBV x v_x (TExists z t_z t) 
  | x == z                     = TExists z (tsubBV x v_x t_z) t
  | otherwise                  = TExists z (tsubBV x v_x t_z) (tsubBV x v_x t)
tsubBV x v_x (TPoly a  k  t)   = TPoly   a k                  (tsubBV x v_x t)

{-  TODO: work these back in!
                               Set_sub (tfreeBV t) (tfreeBV t') &&
                               Set_sub (tfreeBV t') (Set_cup (tfreeBV t) (tfreeBV t_a)) &&
                               Set_sub (tfreeBTV t') (Set_cup (Set_dif (tfreeBTV t) (Set_sng a)) (tfreeBTV t_a)) &&
                               Set_sub (Set_dif (tfreeBTV t) (Set_sng a)) (tfreeBTV t') &&
 -} -- try without:
--                               Set_sub (free t) (free t') && 
--                               Set_sub (freeTV t) (freeTV t') && 
{-@ reflect tsubBTV @-}  --  (( isBare t_a && isBare t ) => isBare t') && ( isTrivial t_a => tsize t == tsize t' )
{-@ tsubBTV :: a:Vname -> t_a:UserType -> t:Type
                -> { t':Type | ( Set_mem a (tfreeBTV t) || t == t' ) &&
                               Set_sub (free t') (Set_cup (free t_a) (free t)) &&
                               Set_sub (freeTV t') (Set_cup (freeTV t_a) (freeTV t)) &&
                               ( noExists t => noExists t' ) } / [tsize t] @-}
tsubBTV :: Vname -> Type -> Type -> Type
tsubBTV a t_a (TRefn b x r)        = case b of 
  (BTV a') | a == a'  -> push  (subBTV a t_a r) t_a -- TExists y t_y (push x r[t_a/a] t')
  _                   -> TRefn b x   (subBTV a t_a r) -- looking for BTV, not BV
tsubBTV a t_a (TFunc z t_z t)      = TFunc   z  (tsubBTV a t_a t_z) (tsubBTV a t_a t)
tsubBTV a t_a (TExists z t_z t)    = TExists z  (tsubBTV a t_a t_z) (tsubBTV a t_a t)
tsubBTV a t_a (TPoly a' k  t)      
  | a == a'                        = TPoly   a' k t  -- not the same a' anymore
  | otherwise                      = TPoly   a' k (tsubBTV a t_a t)

{-@ reflect unbindT @-}         --   (isBare t => isBare t') &&
{-@ unbindT :: x:Vname -> y:Vname -> t:Type 
                       -> { t':Type | Set_sub (free t) (free t') &&
                                      Set_sub (free t') (Set_cup (Set_sng y) (free t)) &&
                                      freeTV t == freeTV t' &&
                                      tfreeBV t' == Set_dif (tfreeBV t) (Set_sng x) &&
                                      tfreeBTV t' == tfreeBTV t && tsize t == tsize t' } / [tsize t] @-} 
unbindT :: Vname -> Vname -> Type -> Type
unbindT x y t = tsubBV x (FV y) t

--TODO: not strictly true anymore:    t' == (tsubBTV a (TRefn (FTV a') 1 (Bc True)) t) &&
{-@ reflect unbind_tvT @-} -- aka: tchgBTV                --    (isBare t => isBare t') &&
{-@ unbind_tvT :: a:Vname -> a':Vname -> t:Type 
                       -> { t':Type | Set_sub (freeTV t) (freeTV t') &&
                                      Set_sub (freeTV t') (Set_cup (Set_sng a') (freeTV t)) &&
                                      Set_sub (free t) (free t') && Set_sub (free t') (free t) &&
                                      tfreeBV t' == tfreeBV t &&
                                      tfreeBTV t' == Set_dif (tfreeBTV t) (Set_sng a) &&
                                      tsize t == tsize t' } / [tsize t] @-} 
unbind_tvT :: Vname -> Vname -> Type -> Type
unbind_tvT a a' (TRefn b x r)        = case b of 
  (BTV a1) | a == a1  -> TRefn (FTV a') x (unbind_tv a a' r) -- (subBV x (BV 1) (unbind_tv a a' r))
  _                   -> TRefn b        x (unbind_tv a a' r) -- looking for BTV, not BV
unbind_tvT a a' (TFunc z t_z t)      = TFunc   z  (unbind_tvT a a' t_z) (unbind_tvT a a' t)
unbind_tvT a a' (TExists z t_z t)    = TExists z  (unbind_tvT a a' t_z) (unbind_tvT a a' t)
unbind_tvT a a' (TPoly a1 k  t)      
  | a == a1                        = TPoly   a1 k t  -- not the same a' anymore
  | otherwise                      = TPoly   a1 k (unbind_tvT a a' t)

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
      | Cons  :: x:Vname -> t:Type -> { g:Env | not (in_env x g) } 
                         -> { g':Env | Set_cup (vbinds g') (tvbinds g') == binds g' &&
                                       Set_emp (Set_cap (vbinds g') (tvbinds g')) } 
      | ConsT :: a:Vname -> k:Kind -> { g:Env | not (in_env a g) } 
                         -> { g':Env | Set_cup (vbinds g') (tvbinds g') == binds g' &&
                                       Set_emp (Set_cap (vbinds g') (tvbinds g')) }  @-}

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
                          else maxpList (Cons x (TRefn TBool Z (Bc True)) g)
 
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

{-@ reflect kind_for_tv @-}
{-@ kind_for_tv :: a:Vname -> { g:Env | Set_mem a (tvbinds g) } 
                           -> { k:Kind | tv_bound_in a k g } @-}
kind_for_tv :: Vname -> Env -> Kind
kind_for_tv a (Cons  x  t  g)             = kind_for_tv a g
kind_for_tv a (ConsT a' k' g) | (a == a') = k'
                              | otherwise = kind_for_tv a g

{-@ reflect binds @-}
binds :: Env -> S.Set Vname
binds Empty         = S.empty
binds (Cons x t g)  = S.union (S.singleton x) (binds g)
binds (ConsT a k g) = S.union (S.singleton a) (binds g)

{-@ reflect v_in_env @-}              -- (term) variables
v_in_env :: Vname -> Env -> Bool
v_in_env x g = S.member x (vbinds g) 

{-@ reflect vbinds @-}
{-@ vbinds :: g:Env -> { s:S.Set Vname | Set_sub s (binds g) } @-}
vbinds :: Env -> S.Set Vname
vbinds Empty         = S.empty
vbinds (Cons x t g)  = S.union (S.singleton x) (vbinds g)
vbinds (ConsT a k g) = vbinds g

{-@ reflect tv_in_env @-}              -- type variables
tv_in_env :: Vname -> Env -> Bool
tv_in_env x g = S.member x (tvbinds g) 

{-@ reflect tvbinds @-}
{-@ tvbinds :: g:Env -> { s:S.Set Vname | Set_sub s (binds g) } @-}
tvbinds :: Env -> S.Set Vname
tvbinds Empty         = S.empty
tvbinds (Cons x t g)  = tvbinds g
tvbinds (ConsT a k g) = S.union (S.singleton a) (tvbinds g)

  --- BARE TYPES: i.e. System F types. These still contain type polymorphism and type variables, 
  --    but all the refinements, dependent arrow binders, and existentials have been erased.

data FType = FTBasic Basic               -- b: Bool, Int, FTV a, BTV a
           | FTFunc FType FType          -- bt -> bt'
           | FTPoly Vname Kind FType     -- \forall a. bt 
  deriving (Eq, Show)

{-@ measure ftsize @-}
{-@ ftsize :: t:FType -> { v:Int | v >= 0 } @-} 
ftsize :: FType -> Int
ftsize (FTBasic b)      = 1
ftsize (FTFunc t_x   t) = (ftsize t_x) + (ftsize t) + 1
ftsize (FTPoly a  k  t) = (ftsize t)   + 1

{-@ measure isBaseF @-}
isBaseF :: FType -> Bool
isBaseF (FTBasic b)     = True
isBaseF _               = False

{-@ reflect erase @-}
erase :: Type -> FType
erase (TRefn b v r)     = FTBasic b
erase (TFunc x t_x t)   = FTFunc (erase t_x) (erase t)
erase (TExists x t_x t) = (erase t)
erase (TPoly a  k  t)   = FTPoly a k (erase t)

{-@ unerase :: ft:FType -> { t:UserType | erase t == ft } @-}
unerase :: FType -> Type
unerase (FTBasic b)      = TRefn b Z (Bc True)
unerase (FTFunc t_x   t) = TFunc   1 (unerase t_x) (unerase t)
unerase (FTPoly a  k  t) = TPoly a k (unerase t)

-- there are no term vars in a Bare Type, only type ones
{-@ reflect ffreeTV @-} 
{-@ ffreeTV :: t:FType -> S.Set Vname / [ftsize t] @-}
ffreeTV :: FType -> S.Set Vname
ffreeTV (FTBasic b)      = case b of
  (FTV a)                    -> S.singleton a
  _                          -> S.empty
ffreeTV (FTFunc t_x t)   = S.union (ffreeTV t_x) (ffreeTV t) 
ffreeTV (FTPoly a k t)   = ffreeTV t

{-@ reflect ffreeBV @-} 
{-@ ffreeBV :: t:FType -> S.Set Vname / [ftsize t] @-}
ffreeBV :: FType -> S.Set Vname
ffreeBV (FTBasic b)      = case b of
  (BTV a)                    -> S.singleton a
  _                          -> S.empty
ffreeBV (FTFunc t_x t)   = S.union (ffreeBV t_x) (ffreeBV t) 
ffreeBV (FTPoly a k t)   = S.difference (ffreeBV t) (S.singleton a)

-- System F substituion is simpler because there are no refinements to worry about, so we can just
--   do a single substitution instead of both a variable replacement t[a'/a] and a refinment-streng.
--   substitution t[a:=t_a]
{-@ reflect ftsubFV @-}
{-@ ftsubFV :: a:Vname -> t_a:FType -> t:FType  
         -> { t':FType | ( Set_mem a (ffreeTV t) || t == t' ) && 
                        ( Set_sub (ffreeTV t) (Set_cup (Set_sng a) (ffreeTV t'))) &&
                ( Set_sub (ffreeTV t') (Set_cup (ffreeTV t_a) (Set_dif (ffreeTV t) (Set_sng a))) ) &&
                Set_sub (ffreeBV t') (Set_cup (ffreeBV t) (ffreeBV t_a)) &&
                Set_sub (ffreeBV t) (ffreeBV t') &&
                ( (not (Set_mem a (ffreeTV t_a))) => not (Set_mem a (ffreeTV t')) ) } / [ftsize t] @-}
ftsubFV :: Vname -> FType -> FType -> FType
ftsubFV a t_a (FTBasic b)           = case b of 
  (FTV a') | a == a'                    -> t_a
  _                                     -> FTBasic b
ftsubFV a t_a (FTFunc t_z t)        = FTFunc (ftsubFV a t_a t_z) (ftsubFV a t_a t)
ftsubFV a t_a (FTPoly a' k t)       = FTPoly a' k (ftsubFV a t_a t)

{-@ reflect ftsubBV @-} 
{-@ ftsubBV :: a:Vname -> t_a:FType -> t:FType  
        -> { t':FType | Set_sub (ffreeTV t) (ffreeTV t') &&
                        Set_sub (ffreeTV t') (Set_cup (ffreeTV t_a) (ffreeTV t)) &&
                        Set_sub (ffreeBV t') (Set_cup (Set_dif (ffreeBV t) (Set_sng a)) (ffreeBV t_a)) && 
                        Set_sub (Set_dif (ffreeBV t) (Set_sng a)) (ffreeBV t') &&
                        ( ftsize t_a != 1 || ftsize t == ftsize t' ) } / [ftsize t] @-}
ftsubBV :: Vname -> FType -> FType -> FType
ftsubBV a t_a (FTBasic   b)         = case b of 
  (BTV a') | a == a'                    -> t_a
  _                                     -> FTBasic b
ftsubBV a t_a (FTFunc t_z t)        = FTFunc (ftsubBV a t_a t_z) (ftsubBV a t_a t)
ftsubBV a t_a (FTPoly a' k  t)      
  | a == a'                         = FTPoly a' k t  -- not the same a' anymore
  | otherwise                       = FTPoly a' k (ftsubBV a t_a t)

{-@ reflect unbindFT @-}
{-@ unbindFT :: a:Vname -> a':Vname -> t:FType 
                       -> { t':FType | Set_sub (ffreeTV t) (ffreeTV t') &&
                                       Set_sub (ffreeTV t') (Set_cup (Set_sng a') (ffreeTV t)) &&
                                       ffreeBV t' == Set_dif (ffreeBV t) (Set_sng a) &&
                                       ftsize t == ftsize t' } / [ftsize t] @-} 
unbindFT :: Vname -> Vname -> FType -> FType
unbindFT a a' t = ftsubBV a (FTBasic (FTV a')) t
 

  --- BARE-TYPING ENVIRONMENTS

data FEnv = FEmpty                       -- type FEnv = [(Vname, FType) or Vname]
          | FCons  Vname FType FEnv
          | FConsT Vname Kind  FEnv
  deriving (Show) 
{-@ data FEnv where
        FEmpty :: FEnv
      | FCons  :: x:Vname -> t:FType -> { g:FEnv | not (in_envF x g) } 
                          -> { g':FEnv | Set_cup (vbindsF g') (tvbindsF g') == bindsF g' &&
                                         Set_emp (Set_cap (vbindsF g') (tvbindsF g')) }
      | FConsT :: a:Vname -> k:Kind  -> { g:FEnv | not (in_envF a g) } 
                          -> { g':FEnv | Set_cup (vbindsF g') (tvbindsF g') == bindsF g' &&
                                         Set_emp (Set_cap (vbindsF g') (tvbindsF g')) } @-}

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

{-@ reflect tv_bound_inF @-}         -- type variables only
tv_bound_inF :: Vname -> Kind -> FEnv -> Bool
tv_bound_inF a k FEmpty                                   = False
tv_bound_inF a k (FCons x t g)    | (a == x)              = False
                                  | otherwise             = tv_bound_inF a k g
tv_bound_inF a k (FConsT a' k' g) | (a == a')             = (k == k')
                                  | otherwise             = tv_bound_inF a k g

{-@ reflect kind_for_tvF @-}
{-@ kind_for_tvF :: a:Vname -> { g:FEnv | Set_mem a (tvbindsF g) } 
                            -> { k:Kind | tv_bound_inF a k g } @-}
kind_for_tvF :: Vname -> FEnv -> Kind
kind_for_tvF a (FCons  x  t  g)             = kind_for_tvF a g
kind_for_tvF a (FConsT a' k' g) | (a == a') = k'
                                | otherwise = kind_for_tvF a g

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

{-@ lem_tvboundin_inenvF :: a:Vname -> k:Kind -> { g:FEnv | tv_bound_inF a k g}
        -> { pf:_ | in_envF a g } @-}
lem_tvboundin_inenvF :: Vname -> Kind -> FEnv -> Proof
lem_tvboundin_inenvF a k (FCons y s g)    | a == y    = impossible ""
                                          | otherwise = lem_tvboundin_inenvF a k g 
lem_tvboundin_inenvF a k (FConsT a' k' g) | a == a'   = ()
                                          | otherwise = lem_tvboundin_inenvF a k g 

{-@ reflect bindsF @-}
bindsF :: FEnv -> S.Set Vname
bindsF FEmpty         = S.empty
bindsF (FCons  x t g) = S.union (S.singleton x) (bindsF g)
bindsF (FConsT a k g) = S.union (S.singleton a) (bindsF g)

{-@ reflect vbindsF @-}
{-@ vbindsF :: g:FEnv -> { s:S.Set Vname | Set_sub s (bindsF g) } @-}
vbindsF :: FEnv -> S.Set Vname
vbindsF FEmpty         = S.empty
vbindsF (FCons x t g)  = S.union (S.singleton x) (vbindsF g)
vbindsF (FConsT a k g) = vbindsF g

{-@ reflect tvbindsF @-}
{-@ tvbindsF :: g:FEnv -> { s:S.Set Vname | Set_sub s (bindsF g) } @-}
tvbindsF :: FEnv -> S.Set Vname
tvbindsF FEmpty         = S.empty
tvbindsF (FCons x t g)  = tvbindsF g
tvbindsF (FConsT a k g) = S.union (S.singleton a) (tvbindsF g)

{-@ reflect erase_env @-}
{-@ erase_env :: g:Env -> { g':FEnv | binds g == bindsF g' && vbinds g == vbindsF g' 
                                                           && tvbinds g == tvbindsF g'} @-}
erase_env :: Env -> FEnv
erase_env Empty         = FEmpty
erase_env (Cons  x t g) = FCons  x (erase t) (erase_env g)
erase_env (ConsT a k g) = FConsT a k         (erase_env g)

{-@ lem_erase_freeTV :: t:Type -> { pf:_ | Set_sub (ffreeTV (erase t)) (freeTV t) } @-}
lem_erase_freeTV :: Type -> Proof
lem_erase_freeTV (TRefn   b   z p) = ()
lem_erase_freeTV (TFunc   z t_z t) = () ? lem_erase_freeTV t_z
                                        ? lem_erase_freeTV t
lem_erase_freeTV (TExists z t_z t) = () ? lem_erase_freeTV t
lem_erase_freeTV (TPoly   a' k' t) = () ? lem_erase_freeTV t

{-@ lem_erase_freeBV :: t:Type -> { pf:_ | Set_sub (ffreeBV (erase t)) (tfreeBTV t) } @-}
lem_erase_freeBV :: Type -> Proof
lem_erase_freeBV (TRefn   b   z p) = ()
lem_erase_freeBV (TFunc   z t_z t) = () ? lem_erase_freeBV t_z
                                        ? lem_erase_freeBV t
lem_erase_freeBV (TExists z t_z t) = () ? lem_erase_freeBV t
lem_erase_freeBV (TPoly   a' k' t) = () ? lem_erase_freeBV t
