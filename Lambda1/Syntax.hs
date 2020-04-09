{-# LANGUAGE GADTs #-}

--{-@ LIQUID "--higherorder" @-}
{- @ LIQUID "--diff"        @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Syntax where

--import Control.Exception (assert)
import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

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

--TODO: will classes and instances make anything easier or harder?
--class HasVars a where
--    free  :: a -> S.Set Vname
--    subst :: Vname -> 

---------------------------------------------------------------------------
----- | TERMS of our language
---------------------------------------------------------------------------
  ---   Term level expressions 
  ---   Locally named representations
  ---     "free" variables are ints because easier to pick fresh ones
  ---     "bound" ones also ints 

{- @ type Vname =  Nat @-} -- > 0 or not?
type Vname = Int

data Prim = And | Or | Not | Eqv
          | Leq | Leqn Int 
          | Eq  | Eqn Int
  deriving (Eq, Show)

data Expr = Bc Bool              -- True, False
          | Ic Int               -- 0, 1, 2, ...
          | Prim Prim            -- built-in primitive functions 
          | BV Vname             -- BOUND Variables: bound to a Lambda, Let or :t
          | FV Vname             -- FREE Variables: bound in an environment
          | Lambda Vname Expr    -- \x.e
          | App Expr Expr        -- e e'  TODO or does this become e v ??
          | Let Vname Expr Expr  -- let x = e1 in e2
          | Annot Expr Type      -- e : t
          | Crash
  deriving (Eq, Show)

{-@ measure esize @-}
{-@ esize :: Expr -> { v:Int | v >= 0 } @-}
esize :: Expr -> Int
esize (Bc _)	        = 0
esize (Ic _)		= 0
esize (Prim _)          = 0
esize (BV _)            = 0
esize (FV _)            = 0
esize (Lambda x e)      = (esize e) + 1
esize (App e e')        = (esize e) + (esize e') + 1
esize (Let x e_x e)     = (esize e_x) + (esize e) + 1
esize (Annot e t)       = (esize e) + 1
esize Crash             = 0

-- In a value, all BV must be bound to a binder within the expression
{-@ type Value = { v:Expr | isValue v && Set_emp (freeBV v) } @-}

{-@ reflect isValue @-}
{- @ isValue :: v:Expr -> { b:Bool | (isValue v) => Set_emp (freeBV v) } @-}
isValue :: Expr -> Bool
isValue (Bc _)         = True
isValue (Ic _)         = True
isValue (Prim _)       = True
isValue (FV _)         = True -- bound variables not a legal value because we 
isValue v@(Lambda x e) = True -- S.null (freeBV v)
  --     never reduce reduce under a lambda or let
isValue Crash          = True
isValue _              = False

{-@ reflect freeBV @-}
freeBV :: Expr -> S.Set Vname
freeBV (Bc _)       = S.empty
freeBV (Ic _)       = S.empty
freeBV (Prim _)     = S.empty
freeBV (FV x)       = S.empty
freeBV (BV x)       = S.singleton x
freeBV (Lambda x e) = S.difference (freeBV e) (S.singleton x)
freeBV (App e e')   = S.union (freeBV e) (freeBV e')
freeBV (Let x ex e) = S.union (freeBV ex) (S.difference (freeBV e) (S.singleton x))
freeBV (Annot e t)  = S.union (freeBV e)  (tfreeBV t) 
freeBV Crash        = S.empty

{-@ reflect fv @-}
fv :: Expr -> S.Set Vname
fv (Bc _)       = S.empty
fv (Ic _)       = S.empty
fv (Prim _)     = S.empty
fv (BV _)       = S.empty
fv (FV x)       = S.singleton x
fv (Lambda x e) = (fv e) -- S.difference (fv e) (S.singleton x)
fv (App e e')   = S.union (fv e) (fv e')
fv (Let x ex e) = S.union (fv ex) (fv e) -- (S.difference (fv e) (S.singleton x))
fv (Annot e t)  = S.union (fv e) (free t) -- fv e
fv (Crash)      = S.empty

--                      ( Set_sub (freeBV e') (Set_cup (freeBV v) (freeBV e)) ) &&
-- {-@ subFV :: x:Vname -> { v:Expr | isValue v } -> e:Expr 
{-@ reflect subFV @-} 
{-@ subFV :: x:Vname -> v:Value -> e:Expr 
                     -> { e':Expr | (Set_mem x (fv e) || e == e') &&
                      ( Set_sub (fv e) (Set_cup (Set_sng x) (fv e')) ) &&
                      ( Set_sub (fv e') (Set_cup (fv v) (Set_dif (fv e) (Set_sng x)))) &&
                      ( (freeBV e) == (freeBV e') ) &&
                      ( (not (Set_mem x (fv v))) => not (Set_mem x (fv e')) ) && 
                      ( (isValue v && isValue e) => isValue e' ) } @-}
subFV :: Vname -> Expr -> Expr -> Expr
subFV x e_x (Bc b)                    = Bc b
subFV x e_x (Ic n)                    = Ic n
subFV x e_x (Prim p)                  = Prim p
subFV x e_x (BV y)                    = BV y
subFV x e_x (FV y) | x == y           = e_x 
                   | otherwise        = FV y
subFV x e_x (Lambda y e)              = Lambda y (subFV x e_x e)
subFV x e_x (App e e')                = App (subFV x e_x e) (subFV x e_x e')
subFV x e_x (Let y e1 e2)             = Let y (subFV x e_x e1) (subFV x e_x e2)
subFV x e_x (Annot e t)               = Annot (subFV x e_x e) (tsubFV x e_x t) -- TODO not 100%
subFV x e_x Crash                     = Crash

--                                    Set_sub (freeBV e') (freeBV e) && 
--                                    Set_sub (freeBV e) (Set_cup (Set_sng x) (freeBV e')) } @-}
{-@ reflect subBV @-} -- x is a BOUND var  
{-@ subBV :: x:Vname ->  v:Value -> e:Expr 
                     -> { e':Expr | Set_sub (fv e) (fv e') &&
                                    Set_sub (fv e') (Set_cup (fv e) (fv v)) &&
                                    freeBV e' == Set_dif (freeBV e) (Set_sng x) } @-}
subBV :: Vname -> Expr -> Expr -> Expr
subBV x e_x (Bc b)                    = Bc b
subBV x e_x (Ic n)                    = Ic n
subBV x e_x (Prim p)                  = Prim p
subBV x e_x (BV y) | x == y           = e_x
                   | otherwise        = BV y
subBV x e_x (FV y)                    = FV y
subBV x e_x (Lambda y e) | x == y     = Lambda y e  -- not the same x anymore
                         | otherwise  = Lambda y (subBV x e_x e)
subBV x e_x (App e e')                = App (subBV x e_x e) (subBV x e_x e')
subBV x e_x (Let y e1 e2) | x == y    = Let y (subBV x e_x e1) e2 -- not the same x anymore
                          | otherwise = Let y (subBV x e_x e1) (subBV x e_x e2)
subBV x e_x (Annot e t)               = Annot (subBV x e_x e) (tsubBV x e_x t)
subBV x e_x Crash                     = Crash  -- I don't think lambdas can bind type vars

{-@ lem_subFV_value :: y:Vname -> v_y:Value -> v:Value  
                        -> { pf:_ | isValue (subFV y v_y v) && Set_emp (freeBV (subFV y v_y v)) } @-}
lem_subFV_value :: Vname -> Expr -> Expr -> Proof
lem_subFV_value y v_y (Bc _)       = ()
lem_subFV_value y v_y (Ic _)       = ()
lem_subFV_value y v_y (Prim _)     = ()
lem_subFV_value y v_y (FV x) 
    | x == y    = toProof ( subFV y v_y (FV x) === v_y ) 
    | otherwise = toProof ( subFV y v_y (FV x) === FV x)
lem_subFV_value y v_y (Lambda x e) 
    | x == y    = toProof ( subFV y v_y (Lambda x e) === Lambda x (subFV y v_y e) )
    | otherwise = toProof ( freeBV (subFV y v_y (Lambda x e))
                        === freeBV (Lambda x (subFV y v_y e))
                        === S.difference (freeBV (subFV y v_y e)) (S.singleton x)
                        === S.empty ) 
lem_subFV_value y v_y Crash        = ()  

{-@ lem_subBV_value :: x:Vname -> v_x:Value -> { v:Expr | not (Set_mem x (freeBV v)) }
                -> { pf:_ | subBV x v_x v == v } @-} -- TODO do i actually use this TODO ?
lem_subBV_value :: Vname -> Expr -> Expr -> Proof
lem_subBV_value x v_x (Bc _)       = ()
lem_subBV_value x v_x (Ic _)       = ()
lem_subBV_value x v_x (Prim _)     = ()
lem_subBV_value x v_x (BV w)       = ()
lem_subBV_value x v_x (FV _)       = ()
lem_subBV_value x v_x (Lambda w e)
    | x == w    = ()
    | otherwise = () ? lem_subBV_value x v_x e
lem_subBV_value x v_x (App e e')   = () ? lem_subBV_value x v_x e 
                                        ? lem_subBV_value x v_x e'
lem_subBV_value x v_x (Let w ew e)
    | x == w    = () ? lem_subBV_value x v_x ew
    | otherwise = () ? lem_subBV_value x v_x ew
                     ? lem_subBV_value x v_x e
lem_subBV_value x v_x (Annot e t)  = () ? lem_subBV_value x v_x e
                                        ? lem_tsubBV_inval x v_x t  
lem_subBV_value x v_x Crash        = ()


--                                   Set_sub (freeBV e') (freeBV e) &&
--                                   Set_sub (freeBV e) (Set_cup (Set_sng x) (freeBV e')) } @-}
{-@ reflect unbind @-} -- unbind converts (BV x) to (FV y) in e
{-@ unbind :: x:Vname -> y:Vname -> e:Expr 
                    -> { e':Expr | Set_sub (fv e) (fv e') && 
                                   Set_sub (fv e') (Set_cup (Set_sng y) (fv e)) &&
                                   freeBV e' == Set_dif (freeBV e) (Set_sng x) } @-}
unbind :: Vname -> Vname -> Expr -> Expr
unbind x y e = subBV x (FV y) e

{-@ lem_unbind_and_subFV :: x:Vname -> y:Vname -> z:Vname 
      -> { e:Expr | not (Set_mem y (fv e)) }
      -> { pf:_ | unbind x z e == subFV y (FV z) (unbind x y e) } @-}
lem_unbind_and_subFV :: Vname -> Vname -> Vname -> Expr -> Proof
lem_unbind_and_subFV x y z e = lem_subFV_unbind x y (FV z) e

{-@ lem_subFV_unbind :: x:Vname -> y:Vname -> v:Value
      -> { e:Expr | not (Set_mem y (fv e)) }
      -> { pf:_ | subBV x v e == subFV y v (unbind x y e) } @-}
lem_subFV_unbind :: Vname -> Vname -> Expr -> Expr -> Proof
lem_subFV_unbind x y v (Bc b)   = ()
lem_subFV_unbind x y v (Ic n)   = ()
lem_subFV_unbind x y v (Prim c) = ()
lem_subFV_unbind x y v (BV w)
    | x == w    = ()
    | otherwise = ()
lem_subFV_unbind x y v (FV w)   = ()
lem_subFV_unbind x y v e@(Lambda w e') 
    | x == w    = toProof ( subFV y v (unbind x y e)
                        === subFV y v (Lambda w e')
                        === Lambda w (subFV y v e')
                        === Lambda w e'
                        === subBV x v (Lambda w e') ) 
    | otherwise = () ? lem_subFV_unbind x y v e'
lem_subFV_unbind x y v (App e1 e2) 
                = () ? lem_subFV_unbind x y v e1
                     ? lem_subFV_unbind x y v e2
lem_subFV_unbind x y v e@(Let w ew e')
    | x == w    = () ? lem_subFV_unbind x y v ew
                     ? toProof ( subFV y v e' === e' )
    | otherwise = () ? lem_subFV_unbind x y v ew
                     ? lem_subFV_unbind x y v e'
lem_subFV_unbind x y v (Annot e' t)
                = () ? lem_subFV_unbind x y v e'
                     ? lem_tsubFV_unbindT x y v t
lem_subFV_unbind x y v (Crash)  = () 

{-@ lem_commute_subFV_unbind :: x:Vname -> y:Vname -> z:Vname 
        -> { z':Vname | z' != x } -> e:Expr
        -> {pf:_ | subFV x (FV y) (unbind z z' e) == unbind z z' (subFV x (FV y) e)} @-}
lem_commute_subFV_unbind :: Vname -> Vname -> Vname -> Vname -> Expr -> Proof
lem_commute_subFV_unbind x y z z' (Bc b)       = ()
lem_commute_subFV_unbind x y z z' (Ic n)       = ()
lem_commute_subFV_unbind x y z z' (Prim c)     = ()
lem_commute_subFV_unbind x y z z' (BV w)       
  | w == z    = ()
  | otherwise = ()
lem_commute_subFV_unbind x y z z' (FV w)       = ()
lem_commute_subFV_unbind x y z z' (Lambda w e) 
  | w == z    = ()
  | otherwise = () ? lem_commute_subFV_unbind x y z z' e
lem_commute_subFV_unbind x y z z' (App e e')     
              = () ? lem_commute_subFV_unbind x y z z' e
                   ? lem_commute_subFV_unbind x y z z' e'
lem_commute_subFV_unbind x y z z' (Let w ew e)     
  | w == z    = () ? lem_commute_subFV_unbind x y z z' ew
  | otherwise = () ? lem_commute_subFV_unbind x y z z' ew
                   ? lem_commute_subFV_unbind x y z z' e
lem_commute_subFV_unbind x y z z' (Annot e t)     
              = () ? lem_commute_subFV_unbind x y z z' e
                   ? lem_commute_tsubFV_unbindT x y z z' t
lem_commute_subFV_unbind x y z z' (Crash)      = ()

{-@ assume lem_commute_subBV_subFV :: x:Vname -> v:Value -> y:Vname ->  v_y:Value -> e:Expr
        -> { pf:_ | subBV x v (subFV y v_y e) == subFV y (subBV x v v_y) (subBV x v e) } @-}
lem_commute_subBV_subFV :: Vname -> Expr -> Vname -> Expr -> Expr -> Proof
lem_commute_subBV_subFV x v y v_y e = ()
{-                toProof ( subBV x v (subFV y v_y (BV w))
                      === subBV x v (BV w)
                      === 
                      === v
                      === subFV y v_y (BV w)
                      === subFV y v_y (subBV -}

{-@ lem_commute_subFV_subBV :: x:Vname -> v:Value -> y:Vname ->  v_y:Value -> e:Expr
        -> { pf:_ | subFV y v_y (subBV x v e) == subBV x (subFV y v_y v) (subFV y v_y e) } @-}
lem_commute_subFV_subBV :: Vname -> Expr -> Vname -> Expr -> Expr -> Proof
lem_commute_subFV_subBV x v y v_y (Bc b)       = ()
lem_commute_subFV_subBV x v y v_y (Ic n)       = ()
lem_commute_subFV_subBV x v y v_y (Prim p)     = ()
lem_commute_subFV_subBV x v y v_y (BV w) -- TODO TODO TODO here TODO TODO TODO
  | x == w    = toProof ( subFV y v_y (subBV x v (BV x))
                      === subFV y v_y v
                      === subBV x (subFV y v_y v) (BV x)
                      === subBV x (subFV y v_y v) (subFV y v_y (BV x)) ) --`withProof`
  | otherwise = ()
lem_commute_subFV_subBV x v y v_y (FV w)       
  | y == w    = toProof ( subFV y v_y (subBV x v (FV y))
                      === subFV y v_y (FV y)
                      === v_y ? lem_subBV_value x (subFV y v_y v) v_y
                      === subBV x (subFV y v_y v) v_y
                      === subBV x (subFV y v_y v) (subFV y v_y (FV y)) )
  | otherwise = ()
lem_commute_subFV_subBV x v y v_y (Lambda w e)
  | x == w    = () {- toProof ( subFV y v_y (subBV x v (Lambda w e))
                      === subFV y v_y (Lambda w e)
                      === Lambda w (subFV y v_y e)
                      === subBV x v (Lambda w (subFV y v_y e))
                      === subBV x v (subFV y v_y (Lambda w e)) ) -}
  | otherwise = () ? lem_commute_subFV_subBV x v y v_y e
lem_commute_subFV_subBV x v y v_y (App e e')
              = () ? lem_commute_subFV_subBV x v y v_y e
                   ? lem_commute_subFV_subBV x v y v_y e'
lem_commute_subFV_subBV x v y v_y (Let w ew e)
  | x == w    = () ? lem_commute_subFV_subBV x v y v_y ew
  | otherwise = () ? lem_commute_subFV_subBV x v y v_y ew
                   ? lem_commute_subFV_subBV x v y v_y e
lem_commute_subFV_subBV x v y v_y (Annot e t)
              = () ? lem_commute_subFV_subBV   x v y v_y e
                   ? lem_commute_tsubFV_tsubBV x v y v_y t
lem_commute_subFV_subBV x v y v_y Crash        = ()

{-@ assume lem_commute_subFV_subBV1 :: x:Vname -> v:Value 
        -> { y:Vname | not (Set_mem y (fv v)) } -> v_y:Value -> e:Expr
        -> { pf:_ | subFV y v_y (subBV x v e) == subBV x v (subFV y v_y e) } @-}
lem_commute_subFV_subBV1 :: Vname -> Expr -> Vname -> Expr -> Expr -> Proof
lem_commute_subFV_subBV1 x v y v_y e = undefined {- lem_commute_subFV_subBV x v y v_y e 
lem_commute_subFV_subBV x v y v_y (Bc b)       = ()
lem_commute_subFV_subBV x v y v_y (Ic n)       = ()
lem_commute_subFV_subBV x v y v_y (Prim p)     = ()
lem_commute_subFV_subBV x v y v_y (BV w)
  | x == w    = toProof ( subFV y v_y (subBV x v (BV x))
                      === subFV y v_y v
                      === v
                      === subBV x v (BV x)
                      === subBV x v (subFV y v_y (BV x)) ) 
  | otherwise = ()
lem_commute_subFV_subBV x v y v_y (FV w)       
  | y == w    = toProof ( subFV y v_y (subBV x v (FV y))
                      === subFV y v_y (FV y)
                      === v_y
                      === subBV x v v_y
                      === subBV x v (subFV y v_y (FV y)) )
  | otherwise = ()
lem_commute_subFV_subBV x v y v_y (Lambda w e)
  | x == w    = () {- toProof ( subFV y v_y (subBV x v (Lambda w e))
                      === subFV y v_y (Lambda w e)
                      === Lambda w (subFV y v_y e)
                      === subBV x v (Lambda w (subFV y v_y e))
                      === subBV x v (subFV y v_y (Lambda w e)) ) -}
  | otherwise = () ? lem_commute_subFV_subBV x v y v_y e
lem_commute_subFV_subBV x v y v_y (App e e')
              = () ? lem_commute_subFV_subBV x v y v_y e
                   ? lem_commute_subFV_subBV x v y v_y e'
lem_commute_subFV_subBV x v y v_y (Let w ew e)
  | x == w    = () ? lem_commute_subFV_subBV x v y v_y ew
  | otherwise = () ? lem_commute_subFV_subBV x v y v_y ew
                   ? lem_commute_subFV_subBV x v y v_y e
lem_commute_subFV_subBV x v y v_y (Annot e t)
              = () ? lem_commute_subFV_subBV   x v y v_y e
                   ? lem_commute_tsubFV_tsubBV x v y v_y t
lem_commute_subFV_subBV x v y v_y Crash        = ()
-}


  ---   Refinement Level: Names, Terms (in FO), FO Predicates, SMT Formulae
type Pred = Expr
--{-@ data Pred = Pred { pred  :: Expr,
--                       benv  :: Benv,
--                       btype :: ProofOf(HasBType benv pred (BTBase TBool)) } @-}
--data Pred = Pred { pred :: Expr,
--                   benv :: BEnv,
--                   btype :: HasBType }
--  deriving (Show)

data Form = P Pred                    -- p
          | FAnd Form Form            -- c1 ^ c2
          | Impl Vname Base Pred Form -- \forall x:b. p => c
  deriving (Show)



  ---   TYPES

data Base = TBool
          | TInt
  deriving (Eq, Show)

data Type = TRefn   Base Vname Pred      -- b{x : p}
          | TFunc   Vname Type Type      -- x:t_x -> t
          | TExists Vname Type Type      -- \exists x:t_x.t
  deriving (Eq, Show)
{-@ data Type where
    TRefn   :: Base -> Vname -> p:Pred -> { t:Type | free t == fv p }
  | TFunc   :: Vname -> t_x:Type -> t:Type 
                     -> { t':Type | free t' == Set_cup (free t_x) (free t) }
  | TExists :: Vname -> t_x:Type -> t:Type 
                     -> { t':Type | free t' == Set_cup (free t_x) (free t) } @-}

{-@ measure tsize @-}
{-@ tsize :: Type -> { v:Int | v >= 0 } @-}
tsize :: Type -> Int
--tsize (TBase b)	        = 0
tsize (TRefn b v r)     = (esize r) 
tsize (TFunc x t_x t)   = (tsize t_x) + (tsize t) + 1
tsize (TExists x t_x t) = (tsize t_x) + (tsize t) + 1

{-@ measure tlen @-}
{-@ tlen :: Type -> { v:Int | v >= 0 } @-}
tlen :: Type -> Int
--tsize (TBase b)	        = 0
tlen (TRefn b v r)     = 0
tlen (TFunc x t_x t)   = (tlen t) + 1
tlen (TExists x t_x t) = (tlen t) + 1

{-@ reflect free @-} 
free :: Type -> S.Set Vname
free (TRefn b v r)      = fv r
free (TFunc x t_x t)    = S.union (free t_x) (free t) 
free (TExists x t_x t)  = S.union (free t_x) (free t) 


{-@ reflect tfreeBV @-}
tfreeBV :: Type -> S.Set Vname
tfreeBV (TRefn b x r)     = S.difference (freeBV r) (S.singleton x)
tfreeBV (TFunc x t_x t)   = S.union (tfreeBV t_x) (S.difference (tfreeBV t) (S.singleton x))
tfreeBV (TExists x t_x t) = S.union (tfreeBV t_x) (S.difference (tfreeBV t) (S.singleton x))

{-@ reflect tsubFV @-}
{-@ tsubFV :: x:Vname -> e:Value -> t:Type  
         -> { t':Type | tlen t' <= tlen t && tlen t' >= 0 &&
                        ( Set_mem x (free t) || t == t' ) && 
                        ( Set_sub (free t) (Set_cup (Set_sng x) (free t'))) &&
                ( Set_sub (free t') (Set_cup (fv e) (Set_dif (free t) (Set_sng x))) ) &&
                ( tfreeBV t == tfreeBV t' ) &&
                ( (not (Set_mem x (fv e))) => not (Set_mem x (free t')) ) } @-}
                    -- -> { t':Type | tsize t' == tsize t } @-}
tsubFV :: Vname -> Expr -> Type -> Type
tsubFV x e_x (TRefn b z r)     = TRefn b z (subFV x e_x r)
tsubFV x e_x (TFunc z t_z t)   = TFunc   z (tsubFV x e_x t_z) (tsubFV x e_x t)
tsubFV x e_x (TExists z t_z t) = TExists z (tsubFV x e_x t_z) (tsubFV x e_x t)


--                                   Set_sub (tfreeBV t') (tfreeBV t) &&
--                                   Set_sub (tfreeBV t) (Set_cup (Set_sng x) (tfreeBV t'))  } @-}
{-@ reflect tsubBV @-}
{-@ tsubBV :: x:Vname -> v_x:Value -> t:Type  
                    -> { t':Type | tlen t' <= tlen t && tlen t' >= 0 &&
                                   Set_sub (free t) (free t') &&
                                   Set_sub (free t') (Set_cup (fv v_x) (free t)) &&
                                   tfreeBV t' == Set_dif (tfreeBV t) (Set_sng x) } @-}
tsubBV :: Vname -> Expr -> Type -> Type
tsubBV x e_x (TRefn b y r)     
  | x == y                     = TRefn b y r
  | otherwise                  = TRefn b y (subBV x e_x r)
tsubBV x e_x (TFunc z t_z t)   
  | x == z                     = TFunc z (tsubBV x e_x t_z) t
  | otherwise                  = TFunc z (tsubBV x e_x t_z) (tsubBV x e_x t)
tsubBV x e_x (TExists z t_z t) 
  | x == z                     = TExists z (tsubBV x e_x t_z) t
  | otherwise                  = TExists z (tsubBV x e_x t_z) (tsubBV x e_x t)

{-@ lem_tsubBV_inval :: x:Vname -> v_x:Value -> { t:Type | not (Set_mem x (tfreeBV t)) }
                -> { pf:_ | tsubBV x v_x t == t } @-} 
lem_tsubBV_inval :: Vname -> Expr -> Type -> Proof
lem_tsubBV_inval x v_x (TRefn b y r)       
    | x == y    = ()
    | otherwise = () ? lem_subBV_value x v_x r
lem_tsubBV_inval x v_x (TFunc z t_z t)       
    | x == z    = () ? lem_tsubBV_inval x v_x t_z
    | otherwise = () ? lem_tsubBV_inval x v_x t_z
                     ? lem_tsubBV_inval x v_x t
lem_tsubBV_inval x v_x (TExists z t_z t)       
    | x == z    = () ? lem_tsubBV_inval x v_x t_z
    | otherwise = () ? lem_tsubBV_inval x v_x t_z
                     ? lem_tsubBV_inval x v_x t

--                                      Set_sub (tfreeBV t') (tfreeBV t) &&
--                                     Set_sub (tfreeBV t) (Set_cup (Set_sng x) (tfreeBV t')) } @-}
{-@ reflect unbindT @-}
{-@ unbindT :: x:Vname -> y:Vname -> t:Type 
                       -> { t':Type | Set_sub (free t) (free t') &&
                                      Set_sub (free t') (Set_cup (Set_sng y) (free t)) &&
                                      tfreeBV t' == Set_dif (tfreeBV t) (Set_sng x) } @-} 
unbindT :: Vname -> Vname -> Type -> Type
unbindT x y t = tsubBV x (FV y) t

{-@ lem_unbindT_and_tsubFV :: x:Vname -> y:Vname -> z:Vname 
        -> { t:Type | not (Set_mem y (free t)) }
        -> { pf:_ | unbindT x z t == tsubFV y (FV z) (unbindT x y t) } @-}
lem_unbindT_and_tsubFV :: Vname -> Vname -> Vname -> Type -> Proof
lem_unbindT_and_tsubFV x y z t = lem_tsubFV_unbindT x y (FV z) t

{-@ lem_tsubFV_unbindT :: x:Vname -> y:Vname -> v:Value 
        -> { t:Type | not (Set_mem y (free t)) }
        -> { pf:_ | tsubBV x v t == tsubFV y v (unbindT x y t) } @-}
lem_tsubFV_unbindT :: Vname -> Vname -> Expr -> Type -> Proof
lem_tsubFV_unbindT x y v t@(TRefn b w p)     
  | x == w     = toProof ( tsubFV y v (unbindT x y t)
                       === tsubFV y v (TRefn b w p)
                       === TRefn b w (subFV y v p)
                       === TRefn b w p 
                       === tsubBV x v (TRefn b w p) )
  | otherwise  = () ? lem_subFV_unbind x y v p
lem_tsubFV_unbindT x y v t@(TFunc w t_w t')
  | x == w     = toProof ( tsubFV y v (unbindT x y t)
                       === tsubFV y v (TFunc w (unbindT x y t_w) t')
                       === TFunc w (tsubFV y v (unbindT x y t_w)) (tsubFV y v t')
                         ? lem_tsubFV_unbindT x y v t_w
                       === TFunc w (tsubBV x v t_w) (tsubFV y v t')
                       === TFunc w (tsubBV x v t_w) t'
                       === tsubBV x v (TFunc w t_w t') )
  | otherwise  = () ? lem_tsubFV_unbindT x y v t_w 
                    ? lem_tsubFV_unbindT x y v t' 
lem_tsubFV_unbindT x y v t@(TExists w t_w t') 
  | x == w     = toProof ( tsubFV y v (unbindT x y t)
                       === tsubFV y v (TExists w (unbindT x y t_w) t')
                       === TExists w (tsubFV y v (unbindT x y t_w)) (tsubFV y v t')
                         ? lem_tsubFV_unbindT x y v t_w 
                       === TExists w (tsubBV x v t_w) (tsubFV y v t')
                       === TExists w (tsubBV x v t_w) t'
                       === tsubBV x v (TExists w t_w t') )
  | otherwise  = () ? lem_tsubFV_unbindT x y v t_w
                    ? lem_tsubFV_unbindT x y v t'

{-@ lem_commute_tsubFV_unbindT :: x:Vname -> y:Vname -> z:Vname 
        -> { z':Vname | z' != x } -> t:Type
        -> {pf:_ | tsubFV x (FV y) (unbindT z z' t) == unbindT z z' (tsubFV x (FV y) t)} @-}
lem_commute_tsubFV_unbindT :: Vname -> Vname -> Vname -> Vname -> Type -> Proof
lem_commute_tsubFV_unbindT x y z z' (TRefn b w p)
  | z == w    = ()
  | otherwise = () ? lem_commute_subFV_unbind x y z z' p
lem_commute_tsubFV_unbindT x y z z' (TFunc w t_w t)
  | z == w    = () ? lem_commute_tsubFV_unbindT x y z z' t_w
  | otherwise = () ? lem_commute_tsubFV_unbindT x y z z' t_w
                   ? lem_commute_tsubFV_unbindT x y z z' t
lem_commute_tsubFV_unbindT x y z z' (TExists w t_w t)
  | z == w    = () ? lem_commute_tsubFV_unbindT x y z z' t_w
  | otherwise = () ? lem_commute_tsubFV_unbindT x y z z' t_w
                   ? lem_commute_tsubFV_unbindT x y z z' t

{-@ assume lem_commute_tsubBV_tsubFV :: x:Vname -> v:Value -> y:Vname -> v_y:Value -> t:Type
        -> { pf:_ | tsubBV x v (tsubFV y v_y t) == tsubFV y (subBV x v v_y) (tsubBV x v t) } @-}
lem_commute_tsubBV_tsubFV :: Vname -> Expr -> Vname -> Expr -> Type -> Proof
lem_commute_tsubBV_tsubFV x v y v_y t = undefined

{-@ lem_commute_tsubFV_tsubBV :: x:Vname -> v:Value -> y:Vname -> v_y:Value  -> t:Type
        -> { pf:_ | tsubFV y v_y (tsubBV x v t) == tsubBV x (subFV y v_y v) (tsubFV y v_y t) } @-}
lem_commute_tsubFV_tsubBV :: Vname -> Expr -> Vname -> Expr -> Type -> Proof
lem_commute_tsubFV_tsubBV x v y v_y (TRefn b w p)
  | x == w    = ()
  | otherwise = () ? lem_commute_subFV_subBV x v y v_y p
lem_commute_tsubFV_tsubBV x v y v_y (TFunc w t_w t)
  | x == w    = () ? lem_commute_tsubFV_tsubBV x v y v_y t_w
  | otherwise = () ? lem_commute_tsubFV_tsubBV x v y v_y t_w
                   ? lem_commute_tsubFV_tsubBV x v y v_y t
lem_commute_tsubFV_tsubBV x v y v_y (TExists w t_w t)
  | x == w    = () ? lem_commute_tsubFV_tsubBV x v y v_y t_w
  | otherwise = () ? lem_commute_tsubFV_tsubBV x v y v_y t_w
                   ? lem_commute_tsubFV_tsubBV x v y v_y t

{-@ lem_commute_tsubFV_tsubBV1 :: x:Vname -> v:Value 
        -> { y:Vname | not (Set_mem y (fv v)) } -> v_y:Value -> t:Type
        -> { pf:_ | tsubFV y v_y (tsubBV x v t) == tsubBV x v (tsubFV y v_y t) } @-}
lem_commute_tsubFV_tsubBV1 :: Vname -> Expr -> Vname -> Expr -> Type -> Proof
lem_commute_tsubFV_tsubBV1 x v y v_y (TRefn b w p)
  | x == w    = ()
  | otherwise = () ? lem_commute_subFV_subBV1 x v y v_y p
lem_commute_tsubFV_tsubBV1 x v y v_y (TFunc w t_w t)
  | x == w    = () ? lem_commute_tsubFV_tsubBV1 x v y v_y t_w
  | otherwise = () ? lem_commute_tsubFV_tsubBV1 x v y v_y t_w
                   ? lem_commute_tsubFV_tsubBV1 x v y v_y t
lem_commute_tsubFV_tsubBV1 x v y v_y (TExists w t_w t)
  | x == w    = () ? lem_commute_tsubFV_tsubBV1 x v y v_y t_w
  | otherwise = () ? lem_commute_tsubFV_tsubBV1 x v y v_y t_w
                   ? lem_commute_tsubFV_tsubBV1 x v y v_y t



  --- TYPING ENVIRONMENTS ---

data Env = Empty                         -- type Env = [(Vname, Type)]	
         | Cons Vname Type Env
  deriving (Show)
{-@ data Env where 
    Empty :: Env
  | Cons  :: x:Vname -> t:Type -> { g:Env | not (in_env x g) } -> Env @-}
--                               -> { g':Env | not (in_env x g) } @-} -- @-}
{-                     -> { g':Env | (binds g') == (Set_cup (binds g) (Set_sng x)) 
                                   && not (in_env x g) } @-}

{-@ measure unique @-}
unique :: Env -> Bool
unique Empty        = True
unique (Cons x t g) = (unique g) && not (in_env x g)

{-@ lem_env_unique :: g:Env -> { pf:_ | unique g } @-} 
lem_env_unique :: Env -> Proof
lem_env_unique Empty        = ()
lem_env_unique (Cons x t g) = () ? lem_env_unique g

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
maxpList Empty        = 1
maxpList (Cons n t g) = withProof (max (1+n) (maxpList g))
                              (lem_maxp_list1 (Cons n t g) (max (1+n) (maxpList g)))

{-@ reflect lem_maxp_list1 @-}
{-@ lem_maxp_list1 :: g:Env -> x:Vname -> { pf:_ | (in_env x g) => (x < maxpList g) } @-} 
lem_maxp_list1 :: Env -> Vname -> Bool
lem_maxp_list1 Empty             x = True
lem_maxp_list1 (Cons n t Empty)  x = True -- fresh_var [n] === n+1
lem_maxp_list1 (Cons n t g)      x 
    = case (x>n) of    
        True  -> True `withProof` (lem_maxp_list1 g x)
        False -> True   

-- we can only look at the most recent binding for x
{-@ reflect bound_in @-}
bound_in :: Vname -> Type -> Env -> Bool
bound_in x t Empty                                 = False
bound_in x t (Cons y t' g) | (x == y)              = (t == t')
                           | otherwise             = bound_in x t g

{-@ reflect binds @-}
binds :: Env -> S.Set Vname
binds Empty        = S.empty
binds (Cons x t g) = S.union (S.singleton x) (binds g)

{-@ reflect in_env @-}
in_env :: Vname -> Env -> Bool
in_env x g = S.member x (binds g) 

{-@ reflect concatE @-}
{-@ concatE :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
                     -> { h:Env | (binds h) == (Set_cup (binds g) (binds g')) } @-}
concatE :: Env -> Env -> Env
concatE g Empty         = g
concatE g (Cons x t g') = Cons x t (concatE g g')

{-@ lem_in_env_concat :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
    ->  x:Vname -> {pf:_ | (in_env x (concatE g g')) <=> ((in_env x g) || (in_env x g'))} @-}
lem_in_env_concat :: Env -> Env -> Vname -> Proof
lem_in_env_concat g Empty         x = ()
lem_in_env_concat g (Cons y s g') x = () ? lem_in_env_concat g g' x 

  --- BARE-TYPING ENVIRONMENTS

data BType = BTBase Base                 -- b
           | BTFunc BType BType          -- t -> t'
  deriving (Eq, Show)

{-@ reflect erase @-}
erase :: Type -> BType
erase (TRefn b v r)     = BTBase b
erase (TFunc x t_x t)   = BTFunc (erase t_x) (erase t)
erase (TExists x t_x t) = (erase t)

{-@ lem_erase_tsubFV :: x:Vname -> e:Expr -> t:Type 
                                -> { pf:_ | erase (tsubFV x e t) == erase t } @-}
lem_erase_tsubFV :: Vname -> Expr -> Type -> Proof
lem_erase_tsubFV x e (TRefn   b   z p) = ()
lem_erase_tsubFV x e (TFunc   z t_z t) = () ? lem_erase_tsubFV x e t_z
                                            ? lem_erase_tsubFV x e t
lem_erase_tsubFV x e (TExists z t_z t) = () ? lem_erase_tsubFV x e t

{-@ lem_erase_tsubBV :: x:Vname -> e:Expr -> t:Type 
                                -> { pf:_ | erase (tsubBV x e t) == erase t } @-}
lem_erase_tsubBV :: Vname -> Expr -> Type -> Proof
lem_erase_tsubBV x e (TRefn   b   z p) = ()
lem_erase_tsubBV x e (TFunc   z t_z t) = () ? lem_erase_tsubBV x e t_z
                                            ? lem_erase_tsubBV x e t
lem_erase_tsubBV x e (TExists z t_z t) = () ? lem_erase_tsubBV x e t

data BEnv = BEmpty                       -- type BEnv = [(Vname, BType)]
          | BCons Vname BType BEnv
  deriving (Show) 
{-@ data BEnv where
    BEmpty :: BEnv
  | BCons  :: x:Vname -> t:BType -> { g:BEnv | not (in_envB x g) } -> BEnv @-}
--                                 -> {g':BEnv | not (in_envB x g)} @-} 
--                           -> { g':BEnv | (bindsB g') == (Set_cup (bindsB g) (Set_sng x))

{-@ measure uniqueB @-}
uniqueB :: BEnv -> Bool
uniqueB BEmpty        = True
uniqueB (BCons x t g) = (uniqueB g) && not (in_envB x g)

{-@ lem_env_uniqueB :: g:BEnv -> { pf:_ | uniqueB g } @-} 
lem_env_uniqueB :: BEnv -> Proof
lem_env_uniqueB BEmpty        = ()
lem_env_uniqueB (BCons x t g) = () ? lem_env_uniqueB g

{-@ reflect fresh_varB @-}
{-@ fresh_varB :: g:BEnv -> { x:Vname | not (in_envB x g) } @-}
fresh_varB :: BEnv -> Vname
fresh_varB g = maxpListB g

{-@ reflect fresh_var_excludingB @-}
{-@ fresh_var_excludingB :: g:BEnv -> x:Vname 
                -> { y:Vname | not (in_envB y g) && y != x } @-}
fresh_var_excludingB :: BEnv -> Vname -> Vname
fresh_var_excludingB g x = if in_envB x g then maxpListB g
                           else maxpListB (BCons x (BTBase TBool) g)
 
{-@ reflect maxpListB @-}
{-@ maxpListB :: g:BEnv -> { x:Vname | (in_envB x g) => (x < maxpListB g) } @-}
maxpListB :: BEnv -> Int
maxpListB BEmpty        = 1
maxpListB (BCons n t g) = withProof (max (1+n) (maxpListB g))
                              (lem_maxp_listB (BCons n t g) (max (1+n) (maxpListB g)))

{-@ reflect lem_maxp_listB @-}
{-@ lem_maxp_listB :: g:BEnv -> x:Vname -> { pf:_ | (in_envB x g) => (x < maxpListB g) } @-} 
lem_maxp_listB :: BEnv -> Vname -> Bool
lem_maxp_listB BEmpty              x = True
lem_maxp_listB (BCons n t BEmpty)  x = True -- fresh_var [n] === n+1
lem_maxp_listB (BCons n t g)       x 
    = case (x>n) of    
        True  -> True `withProof` (lem_maxp_listB g x)
        False -> True   

{-@ reflect bound_inB @-}
bound_inB :: Vname -> BType -> BEnv -> Bool
bound_inB x t BEmpty                                 = False
bound_inB x t (BCons y t' g) | (x == y)              = (t == t')
                             | otherwise             = bound_inB x t g

{-@ reflect bindsB @-}
bindsB :: BEnv -> S.Set Vname
bindsB BEmpty        = S.empty
bindsB (BCons x t g) = S.union (S.singleton x) (bindsB g)

{-@ reflect in_envB @-}
in_envB :: Vname -> BEnv -> Bool
in_envB x g = S.member x (bindsB g) 

{-@ reflect concatB @-}
{-@ concatB :: g:BEnv -> { g':BEnv | Set_emp (Set_cap (bindsB g) (bindsB g')) } 
                      -> { h:BEnv  | bindsB h == Set_cup (bindsB g) (bindsB g') } @-}
concatB :: BEnv -> BEnv -> BEnv
concatB g BEmpty         = g
concatB g (BCons x t g') = BCons x t (concatB g g')

{-@ lem_in_env_concatB :: g:BEnv -> { g':BEnv | Set_emp (Set_cap (bindsB g) (bindsB g')) } 
    ->  x:Vname -> {pf:_ | (in_envB x (concatB g g')) <=> ((in_envB x g) || (in_envB x g'))} @-}
lem_in_env_concatB :: BEnv -> BEnv -> Vname -> Proof
lem_in_env_concatB g BEmpty         x = ()
lem_in_env_concatB g (BCons y s g') x = () ? lem_in_env_concatB g g' x 


{-@ lem_binds_cons_concatB :: g:BEnv -> g':BEnv -> x:Vname -> t_x:BType
  -> { pf:_ | Set_sub (bindsB (concatB g g')) (bindsB (concatB (BCons x t_x g) g')) && 
              bindsB (concatB (BCons x t_x g) g') == Set_cup (Set_cup (bindsB g) (Set_sng x)) (bindsB g') } @-}
lem_binds_cons_concatB :: BEnv -> BEnv -> Vname -> BType -> Proof
lem_binds_cons_concatB g BEmpty         x t = ()
lem_binds_cons_concatB g (BCons y s g') x t = () ? lem_binds_cons_concatB g g' x t


{-@ reflect erase_env @-}
{-@ erase_env :: g:Env -> { g':BEnv | binds g == bindsB g' } @-}
erase_env :: Env -> BEnv
erase_env Empty        = BEmpty
erase_env (Cons x t g) = BCons x (erase t) (erase_env g)

{-@ lem_erase_concat :: g:Env -> g':Env 
           -> { pf:_ |  erase_env (concatE g g') == concatB (erase_env g) (erase_env g') } @-}
lem_erase_concat :: Env -> Env -> Proof
lem_erase_concat g Empty         = ()
lem_erase_concat g (Cons x t g') = () ? lem_erase_concat g g'


-- -- -- -- -- -- -- -- -- -- -- --
-- Substitutions in Environments --
-- -- -- -- -- -- -- -- -- -- -- --

{-@ reflect esubFV @-}
{-@ esubFV :: x:Vname -> v:Value -> g:Env -> { g':Env | binds g == binds g' } @-}
esubFV :: Vname -> Expr -> Env -> Env
esubFV x e_x Empty          = Empty
esubFV x e_x (Cons z t_z g) = Cons z (tsubFV x e_x t_z) (esubFV x e_x g)

{-@ lem_in_env_esub :: g:Env -> x:Vname -> v_x:Value -> y:Vname
        -> { pf:_ | in_env y (esubFV x v_x g) <=> in_env y g } @-}
lem_in_env_esub :: Env -> Vname -> Expr -> Vname -> Proof
lem_in_env_esub g x v_x y = undefined  

{-@ lem_erase_esubFV :: x:Vname -> v:Expr -> g:Env
        -> { pf:_ | erase_env (esubFV x v g) == erase_env g } @-}
lem_erase_esubFV :: Vname -> Expr -> Env -> Proof
lem_erase_esubFV x e (Empty)      = ()
lem_erase_esubFV x e (Cons y t g) = () ? lem_erase_esubFV x e g
                                       ? lem_erase_tsubFV x e t


