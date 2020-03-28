{-# LANGUAGE GADTs #-}

--{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Lambda1Slow2 where

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

{-@ inline isValue @-}
{- @ isValue :: v:Expr -> { b:Bool | b => (unboundBV v == S.empty) } @-}
isValue :: Expr -> Bool
isValue (Bc _)         = True
isValue (Ic _)         = True
isValue (Prim _)       = True
isValue (FV _)         = True -- bound variables not a legal value because we 
isValue v@(Lambda _ _) = True -- (unboundBV v == S.empty)
  --     never reduce reduce under a lambda or let
isValue Crash          = True
isValue _              = False

{-@ reflect unboundBV @-}
unboundBV :: Expr -> S.Set Vname
unboundBV (Bc _)       = S.empty
unboundBV (Ic _)       = S.empty
unboundBV (Prim _)     = S.empty
unboundBV (FV x)       = S.empty
unboundBV (BV x)       = S.singleton x
unboundBV (Lambda x e) = S.difference (unboundBV e) (S.singleton x)
unboundBV (App e e')   = S.union (unboundBV e) (unboundBV e')
unboundBV (Let x ex e) = S.union (unboundBV ex) (S.difference (unboundBV e) (S.singleton x))
unboundBV (Annot e t)  = S.union (unboundBV e)  (tunboundBV t) 
unboundBV Crash        = S.empty

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

{-@ reflect subFV @-} 
{-@ subFV :: x:Vname -> v:Expr -> e:Expr -> { e':Expr | (Set_mem x (fv e) || e == e') &&
                      ( Set_sub (fv e) (Set_cup (Set_sng x) (fv e')) ) &&
                      ( Set_sub (fv e') (Set_cup (fv v) (Set_dif (fv e) (Set_sng x)))) &&
                      ( (not (Set_mem x (fv v))) => not (Set_mem x (fv e')) ) } @-}
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

{-@ reflect subBV @-} -- x is a BOUND var  -- TODO: should v be a value only?
{-@ subBV :: x:Vname -> v:Expr -> e:Expr 
                     -> { e':Expr | Set_sub (fv e) (fv e') &&
                                    Set_sub (fv e') (Set_cup (fv e) (fv v)) } @-}
--                                    (Set_mem x (fv e) || e == e') } @-}
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

{-@ assume lem_subBV_value :: x:Vname -> v_x:Expr -> { v:Expr | not (Set_mem x (unboundBV v)) }
                -> { pf:_ | subBV x v_x v == v } @-}
lem_subBV_value :: Vname -> Expr -> Expr -> Proof
lem_subBV_value x v_x v = undefined
{-lem_subBV_value x v_x (Bc _)       = ()
lem_subBV_value x v_x (Ic _)       = ()
lem_subBV_value x v_x (Prim _)     = ()
lem_subBV_value x v_x (FV _)       = ()
lem_subBV_value x v_x (Lambda w e)
    | x == w    = ()
    | otherwise = () ? lem_subBV_value x v_x e
lem_subBV_value x v_x Crash        = ()
lem_subBV_value x v_x (_)          = impossible "not a value"
-}

{-@ reflect unbind @-} -- unbind converts (BV x) to (FV y) in e
{-@ unbind :: Vname -> y:Vname -> e:Expr 
                    -> { e':Expr | Set_sub (fv e) (fv e') && 
                                   Set_sub (fv e') (Set_cup (Set_sng y) (fv e)) } @-}
unbind :: Vname -> Vname -> Expr -> Expr
unbind x y e = subBV x (FV y) e

{-@ lem_unbind_and_subFV :: x:Vname -> y:Vname -> z:Vname 
      -> { e:Expr | not (Set_mem y (fv e)) }
      -> { pf:_ | unbind x z e == subFV y (FV z) (unbind x y e) } @-}
lem_unbind_and_subFV :: Vname -> Vname -> Vname -> Expr -> Proof
lem_unbind_and_subFV x y z e = lem_subFV_unbind x y (FV z) e

{-@ lem_subFV_unbind :: x:Vname -> y:Vname -> v:Expr
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

{-@ assume lem_commute_subFV_subBV :: x:Vname -> { v:Expr | isValue v }
        -> { y:Vname | not (Set_mem y (fv v)) } -> { v_y:Expr | isValue v_y }
        -> e:Expr
        -> { pf:_ | subFV y v_y (subBV x v e) == subBV x v (subFV y v_y e) } @-}
lem_commute_subFV_subBV :: Vname -> Expr -> Vname -> Expr -> Expr -> Proof
lem_commute_subFV_subBV x v y v_y e = undefined {-
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


{-@ reflect tunboundBV @-}
tunboundBV :: Type -> S.Set Vname
tunboundBV (TRefn b x r)     = S.difference (unboundBV r) (S.singleton x)
tunboundBV (TFunc x t_x t)   = S.union (tunboundBV t_x) (S.difference (tunboundBV t) (S.singleton x))
tunboundBV (TExists x t_x t) = S.union (tunboundBV t_x) (S.difference (tunboundBV t) (S.singleton x))

{-@ reflect tsubFV @-}
{-@ tsubFV :: x:Vname -> e:Expr -> t:Type  
         -> { t':Type | tlen t' <= tlen t && tlen t' >= 0 &&
                        ( Set_mem x (free t) || t == t' ) && 
                        ( Set_sub (free t) (Set_cup (Set_sng x) (free t'))) &&
                ( Set_sub (free t') (Set_cup (fv e) (Set_dif (free t) (Set_sng x))) ) &&
                ( (not (Set_mem x (fv e))) => not (Set_mem x (free t')) ) } @-}
                    -- -> { t':Type | tsize t' == tsize t } @-}
tsubFV :: Vname -> Expr -> Type -> Type
tsubFV x e_x (TRefn b z r)     = TRefn b z (subFV x e_x r)
tsubFV x e_x (TFunc z t_z t)   = TFunc   z (tsubFV x e_x t_z) (tsubFV x e_x t)
tsubFV x e_x (TExists z t_z t) = TExists z (tsubFV x e_x t_z) (tsubFV x e_x t)


{-@ reflect tsubBV @-}
{-@ tsubBV :: Vname -> e_x:Expr -> t:Type  
                    -> { t':Type | tlen t' <= tlen t && tlen t' >= 0 &&
                                   Set_sub (free t) (free t') &&
                                   Set_sub (free t') (Set_cup (fv e_x) (free t))} @-}
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

{-@ reflect unbindT @-}
{-@ unbindT :: x:Vname -> y:Vname -> t:Type 
                       -> { t':Type | Set_sub (free t) (free t') &&
                                      Set_sub (free t') (Set_cup (Set_sng y) (free t)) } @-}
unbindT :: Vname -> Vname -> Type -> Type
unbindT x y t = tsubBV x (FV y) t

{-@ lem_unbindT_and_tsubFV :: x:Vname -> y:Vname -> z:Vname 
        -> { t:Type | not (Set_mem y (free t)) }
        -> { pf:_ | unbindT x z t == tsubFV y (FV z) (unbindT x y t) } @-}
lem_unbindT_and_tsubFV :: Vname -> Vname -> Vname -> Type -> Proof
lem_unbindT_and_tsubFV x y z t = lem_tsubFV_unbindT x y (FV z) t

{-@ lem_tsubFV_unbindT :: x:Vname -> y:Vname -> v:Expr
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

{-@ lem_commute_tsubFV_tsubBV :: x:Vname -> { v:Expr | isValue v }
        -> { y:Vname | not (Set_mem y (fv v)) } -> { v_y:Expr | isValue v_y }
        -> t:Type
        -> { pf:_ | tsubFV y v_y (tsubBV x v t) == tsubBV x v (tsubFV y v_y t) } @-}
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

data BEnv = BEmpty                       -- type BEnv = [(Vname, BType)]
          | BCons Vname BType BEnv
  deriving (Show) 
{-@ data BEnv where
    BEmpty :: BEnv
  | BCons  :: x:Vname -> t:BType -> { g:BEnv | not (in_envB x g)} -> BEnv @-}
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

{-@ reflect esubFV @-}
{-@ esubFV :: x:Vname -> Expr -> g:Env -> { g':Env | binds g == binds g' } @-}
esubFV :: Vname -> Expr -> Env -> Env
esubFV x e_x Empty          = Empty
esubFV x e_x (Cons z t_z g) = Cons z (tsubFV x e_x t_z) (esubFV x e_x g)

{-@ lem_erase_esubFV :: x:Vname -> e:Expr -> g:Env
        -> { pf:_ | erase_env (esubFV x e g) == erase_env g } @-}
lem_erase_esubFV :: Vname -> Expr -> Env -> Proof
lem_erase_esubFV x e (Empty)      = ()
lem_erase_esubFV x e (Cons y t g) = () ? lem_erase_esubFV x e g
                                       ? lem_erase_tsubFV x e t


--------------------------------------------------------------------------
----- | OPERATIONAL SEMANTICS (Small Step)
--------------------------------------------------------------------------

{-@ reflect delta @-}
{-@ delta :: p:Prim -> { e:Expr | isValue e } ->  e':Expr @-}
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

-- E-Prim c v -> delta(c,v)
-- E-App1 e e1 -> e' e1 if e->e'
-- E-App2 v e  -> v e'  if e->e'
-- E-AppAbs (\x. e) v -> e[v/x]
-- E-Let  let x=e_x in e -> let x=e'_x in e if e_x->e'_x
-- E-LetV let x=v in e -> e[v/x]
-- E-Ann   e:t -> e':t  if e->e'
-- E-AnnV  v:t -> v
--       Other possibilities: use contexts instead? E-Ctx 

data StepP where
    Step :: Expr -> Expr -> StepP

data Step where
    EPrim :: Prim -> Expr -> Step
    EApp1 :: Expr -> Expr -> Step -> Expr -> Step
    EApp2 :: Expr -> Expr -> Step -> Expr -> Step
    EAppAbs :: Vname -> Expr -> Expr -> Step
    ELet  :: Expr -> Expr -> Step -> Vname -> Expr -> Step
    ELetV :: Vname -> Expr -> Expr -> Step
    EAnn  :: Expr -> Expr -> Step -> Type -> Step
    EAnnV :: Expr -> Type -> Step

{-@ data Step where 
    EPrim :: c:Prim -> { w:Expr | isValue w } 
                 -> ProofOf( Step (App (Prim c) w) (delta c w) )
 |  EApp1 :: e:Expr -> e':Expr -> ProofOf( Step e e' ) 
                 -> e1:Expr -> ProofOf( Step (App e e1) (App e' e1))
 |  EApp2 :: e:Expr -> e':Expr -> ProofOf( Step e e' )
                 -> { v:Expr | isValue v } -> ProofOf( Step (App v e) (App v e'))
 |  EAppAbs :: x:Vname -> e:Expr -> { v:Expr | isValue v } 
                 -> ProofOf( Step (App (Lambda x e) v) (subBV x v e))
 |  ELet  :: e_x:Expr -> e_x':Expr -> ProofOf( Step e_x e_x' )
                 -> x:Vname -> e:Expr -> ProofOf( Step (Let x e_x e) (Let x e_x' e))
 |  ELetV :: x:Vname -> { v:Expr | isValue v } -> e:Expr
                 -> ProofOf( Step (Let x v e) (subBV x v e))
 |  EAnn  :: e:Expr -> e':Expr -> ProofOf( Step e e' )
                 -> t:Type -> ProofOf(Step (Annot e t) (Annot e' t))
 |  EAnnV :: { v:Expr | isValue v } -> t:Type -> ProofOf( Step (Annot v t) v) @-}


data EvalsToP where
    EvalsTo :: Expr -> Expr -> EvalsToP

data EvalsTo where
    Refl     :: Expr -> EvalsTo
    AddStep  :: Expr -> Expr -> Step -> Expr -> EvalsTo -> EvalsTo
{-@ data EvalsTo where 
    Refl     :: e:Expr -> ProofOf ( EvalsTo e e )
 |  AddStep  :: e1:Expr -> e2:Expr -> ProofOf( Step e1 e2 ) -> e3:Expr
               -> ProofOf ( EvalsTo e2 e3 ) -> ProofOf( EvalsTo e1 e3 ) @-} -- @-} 
  
-- EvalsToP is the transitive/reflexive closure of StepP:
{-@ lemma_evals_trans :: e1:Expr -> e2:Expr -> e3:Expr -> ProofOf( EvalsTo e1 e2)
                    -> ProofOf( EvalsTo e2 e3) -> ProofOf( EvalsTo e1 e3) @-} 
lemma_evals_trans :: Expr -> Expr -> Expr -> EvalsTo -> EvalsTo -> EvalsTo
lemma_evals_trans e1 e2 e3 (Refl _e1) p_e2e3 = p_e2e3
lemma_evals_trans e1 e2 e3 (AddStep _e1 e p_e1e _e2 p_ee2) p_e2e3 = p_e1e3
  where
    p_e1e3 = AddStep e1 e p_e1e e3 p_ee3
    p_ee3  = lemma_evals_trans e e2 e3 p_ee2 p_e2e3

{-@ lemma_app_many :: e:Expr -> e':Expr -> v':Expr -> ProofOf(EvalsTo e e')
                       -> ProofOf(EvalsTo (App e v') (App e' v')) @-}
lemma_app_many :: Expr -> Expr -> Expr -> EvalsTo -> EvalsTo
lemma_app_many e e' v (Refl _e) = Refl (App e v)
lemma_app_many e e' v (AddStep _e e1 s_ee1 _e' p_e1e') = p_ev_e'v
  where
    p_ev_e'v  = AddStep (App e v) (App e1 v) s_ev_e1v (App e' v) p_e1v_e'v
    s_ev_e1v  = EApp1 e e1 s_ee1 v 
    p_e1v_e'v = lemma_app_many e1 e' v p_e1e' 

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
                -> { t1:Type | (erase t1 == b) && Set_sub (free t1) (bindsB g) }
                -> ProofOf(HasBType g e b) -> ProofOf(HasBType g (Annot e t1) b)  @-} 

-- TODO: refactor without impossible
{-@ simpleBTVar :: g:BEnv -> { x:Vname | in_envB x g} -> { t:BType | bound_inB x t g } 
                -> ProofOf(HasBType g (FV x) t) @-}
simpleBTVar :: BEnv -> Vname -> BType -> HasBType
simpleBTVar BEmpty        x t = impossible "certainly"
simpleBTVar (BCons y s g) x t 
    = case (x == y, t == s) of
        (True, True) -> BTVar1 g x t
        (True, _)    -> impossible "again"
        (False, _)   -> BTVar2 g x t (simpleBTVar g x t) y s

-- Lemma. The underlying bare type system is sound. Omitting, for now, the textbook
--          soundness proof for the STLC.
{-@ assume lemma_soundness :: e:Expr -> e':Expr -> ProofOf(EvalsTo e e') -> b:BType
                   -> ProofOf(HasBType BEmpty e b) -> ProofOf(HasBType BEmpty e' b) @-}
lemma_soundness :: Expr -> Expr -> EvalsTo -> BType -> HasBType -> HasBType
lemma_soundness e e' p_ee' b p_eb = undefined

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


  --- Well-Formedness of Types

data WFTypeP where
    WFType :: Env -> Type -> WFTypeP

data WFType where 
    WFRefn :: Env -> Vname -> Base -> Pred -> Vname -> HasBType -> WFType
    WFFunc :: Env -> Vname -> Type -> WFType -> Type -> Vname -> WFType -> WFType
    WFExis :: Env -> Vname -> Type -> WFType -> Type -> Vname -> WFType -> WFType

{-@ data WFType where
    WFRefn :: g:Env -> x:Vname -> b:Base -> p:Pred 
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) }
        -> ProofOf(HasBType (BCons y (BTBase b) (erase_env g)) (unbind x y p) (BTBase TBool)) 
        -> ProofOf(WFType g (TRefn b x p))
 |  WFFunc :: g:Env -> x:Vname -> t_x:Type 
        -> ProofOf(WFType g t_x) -> t:Type 
        -> { y:Vname | not (in_env y g) && not (Set_mem y (free t)) }
        -> ProofOf(WFType (Cons y t_x g) (unbindT x y t)) -> ProofOf(WFType g (TFunc x t_x t))
 |  WFExis :: g:Env -> x:Vname -> t_x:Type 
        -> ProofOf(WFType g t_x) -> t:Type 
        -> { y:Vname | not (in_env y g) && not (Set_mem y (free t)) }
        -> ProofOf(WFType (Cons y t_x g) (unbindT x y t)) -> ProofOf(WFType g (TExists x t_x t)) @-} 


{-@ lem_free_bound_in_env :: g:Env -> t:Type -> ProofOf(WFType g t)
                -> { x:Vname | not (in_env x g) }
                -> { pf:_ | not (Set_mem x (free t)) } @-}
lem_free_bound_in_env :: Env -> Type -> WFType -> Vname -> Proof
lem_free_bound_in_env g t (WFRefn _g z b p z' p_z'_p_bl) x
    = case ( x == z' ) of
        (True)  -> ()
        (False) -> () ? lem_fv_bound_in_benv (BCons z' (BTBase b) (erase_env g)) 
                                             (unbind z z' p) (BTBase TBool) p_z'_p_bl x
lem_free_bound_in_env g t (WFFunc _g y t_y p_ty_wf t' y' p_y'_t'_wf) x
    = case ( x == y' ) of
        (True)  -> () ? lem_free_bound_in_env g t_y p_ty_wf x
        (False) -> () ? lem_free_bound_in_env g t_y p_ty_wf x
                      ? lem_free_bound_in_env (Cons y' t_y g) (unbindT y y' t') p_y'_t'_wf x
lem_free_bound_in_env g t (WFExis _g y t_y p_ty_wf t' y' p_y'_t'_wf) x
    = case ( x == y' ) of 
        (True)  -> () ? lem_free_bound_in_env g t_y p_ty_wf x
        (False) -> () ? lem_free_bound_in_env g t_y p_ty_wf x
                      ? lem_free_bound_in_env (Cons y' t_y g) (unbindT y y' t') p_y'_t'_wf x
 

  --- Well-formedness of Environments
data WFEnvP where
    WFEnv :: Env -> WFEnvP

data WFEnv where
    WFEEmpty :: WFEnv
    WFEBind  :: Env -> WFEnv -> Vname -> Type -> WFType -> WFEnv

{-@ data WFEnv where
    WFEEmpty :: ProofOf(WFEnv Empty)
 |  WFEBind  :: g:Env -> ProofOf(WFEnv g) -> { x:Vname | not (in_env x g) } -> t:Type 
                      -> ProofOf(WFType g t) -> ProofOf(WFEnv (Cons x t g)) @-}

  --- the Typing Judgement

data HasTypeP where
    HasType :: Env -> Expr -> Type -> HasTypeP -- HasType G e t means G |- e : t

data HasType where -- TODO: Indicate in notes/latex where well-formedness used
    TBC   :: Env -> Bool -> HasType
    TIC   :: Env -> Int -> HasType
    TVar1 :: Env -> Vname -> Type -> HasType
    TVar2 :: Env -> Vname -> Type -> HasType -> Vname -> Type -> HasType
    TPrm  :: Env -> Prim -> HasType
    TAbs  :: Env -> Vname -> Type -> WFType -> Expr -> Type 
              -> Vname -> HasType -> HasType
    TApp  :: Env -> Expr -> Vname -> Type -> Type -> HasType 
              -> Expr -> HasType -> HasType
    TLet  :: Env -> Expr -> Type -> HasType -> Vname -> Expr
              -> Type -> WFType -> Vname -> HasType -> HasType
    TAnn  :: Env -> Expr -> Type -> HasType -> HasType
    TSub  :: Env -> Expr -> Type -> HasType -> Type -> WFType -> Subtype -> HasType

{-@ data HasType where
    TBC   :: g:Env -> b:Bool -> ProofOf(HasType g (Bc b) (tybc b))
 |  TIC   :: g:Env -> n:Int -> ProofOf(HasType g (Ic n) (tyic n))
 |  TVar1 :: g:Env -> { x:Vname | not (in_env x g) } -> t:Type 
                -> ProofOf(HasType (Cons x t g) (FV x) t)
 |  TVar2 :: g:Env -> { x:Vname | in_env x g } -> t:Type -> ProofOf(HasType g (FV x) t)
                -> { y:Vname | y != x && not (in_env y g) } -> s:Type 
                -> ProofOf(HasType (Cons y s g) (FV x) t)
 |  TPrm  :: g:Env -> c:Prim -> ProofOf(HasType g (Prim c) (ty c))
 |  TAbs  :: g:Env -> x:Vname -> t_x:Type -> ProofOf(WFType g t_x) 
                -> e:Expr -> t:Type 
                -> { y:Vname | not (in_env y g) && not (Set_mem y (fv e)) &&
                                                   not (Set_mem y (free t)) } 
                -> ProofOf(HasType (Cons y t_x g) (unbind x y e) (unbindT x y t))
                -> ProofOf(HasType g (Lambda x e) (TFunc x t_x t))
 |  TApp  :: g:Env -> e:Expr -> x:Vname -> t_x:Type -> t:Type
                -> ProofOf(HasType g e (TFunc x t_x t)) 
                -> e':Expr -> ProofOf(HasType g e' t_x) 
                -> ProofOf(HasType g (App e e') (TExists x t_x t))
 |  TLet  :: g:Env -> e_x:Expr -> t_x:Type -> ProofOf(HasType g e_x t_x)
                -> x:Vname -> e:Expr -> t:Type -> ProofOf(WFType g t)
                -> { y:Vname | not (in_env y g) && not (Set_mem y (fv e)) &&
                                                   not (Set_mem y (free t)) }
                -> ProofOf(HasType (Cons y t_x g) (unbind x y e) (unbindT x y t))
                -> ProofOf(HasType g (Let x e_x e) t)
 |  TAnn  :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
                -> ProofOf(HasType g (Annot e t) t)
 |  TSub  :: g:Env -> e:Expr -> s:Type -> ProofOf(HasType g e s) -> t:Type 
                -> ProofOf(WFType g t) -> ProofOf(Subtype g s t) 
                -> ProofOf(HasType g e t) @-} -- @-}

-- TODO: refactor without impossible
{-@ simpleTVar :: g:Env -> { x:Vname | in_env x g } -> { t:Type | bound_in x t g } 
                -> ProofOf(HasType g (FV x) t) @-}
simpleTVar :: Env -> Vname -> Type -> HasType
simpleTVar Empty        x t = impossible "Clearly"
simpleTVar (Cons y s g) x t 
    = case (x == y, t == s) of
        (True, True) -> TVar1 g x t
        (True, _)    -> impossible "again"
        (False, _)   -> TVar2 g x t (simpleTVar g x t) y s


-------------------------------------------------------------------------
----- |
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

------------------------------------------------------------------------------
----- | SUBTYPING
------------------------------------------------------------------------------

data SubtypeP where
    Subtype :: Env -> Type -> Type -> SubtypeP

data Subtype where
    SBase :: Env -> Vname -> Base -> Pred -> Vname -> Pred -> Vname -> Entails -> Subtype
    SFunc :: Env -> Vname -> Type -> Vname -> Type -> Subtype
               -> Type -> Type -> Vname -> Subtype -> Subtype
    SWitn :: Env -> Expr -> Type -> HasType -> Type -> Vname -> Type
               -> Subtype -> Subtype
    SBind :: Env -> Vname -> Type -> Type -> Type -> Vname -> Subtype -> Subtype

{-@ data Subtype where
    SBase :: g:Env -> v1:Vname -> b:Base -> p1:Pred -> v2:Vname -> p2:Pred 
               -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p2)) }
               -> ProofOf(Entails ( Cons y (TRefn b v1 p1) g) (unbind v2 y p2))
               -> ProofOf(Subtype g (TRefn b v1 p1) (TRefn b v2 p2))
 |  SFunc :: g:Env -> x1:Vname -> s1:Type -> { x2:Vname | not (in_env x2 g) } -> s2:Type
               -> ProofOf(Subtype g s2 s1) -> t1:Type -> t2:Type
               -> { y:Vname | not (in_env y g) && not (Set_mem y (free t1)) 
                                               && not (Set_mem y (free t2)) }
               -> ProofOf(Subtype (Cons y s2 g) (unbindT x1 y t1) (unbindT x2 y t2))
               -> ProofOf(Subtype g (TFunc x1 s1 t1) (TFunc x2 s2 t2))
 |  SWitn :: g:Env -> { e:Expr | isValue e } -> t_x:Type -> ProofOf(HasType g e t_x) 
               -> t:Type -> x:Vname -> t':Type -> ProofOf(Subtype g t (tsubBV x e t'))
               -> ProofOf(Subtype g t (TExists x t_x t'))
 |  SBind :: g:Env -> x:Vname -> t_x:Type -> t:Type -> {t':Type | not Set_mem x (free t')} 
               -> { y:Vname | not (in_env y g) }
               -> ProofOf(Subtype (Cons y t_x g) (unbindT x y t) t')
               -> ProofOf(Subtype g (TExists x t_x t) t')
@-}

{-@ assume lem_erase_subtype :: g:Env -> t1:Type -> t2:Type -> ProofOf(Subtype g t1 t2)
               -> { pf:_ | erase t1 == erase t2 } @-}
lem_erase_subtype :: Env -> Type -> Type -> Subtype -> Proof
lem_erase_subtype g t1 t2 p_t1_t2 = undefined
{-lem_erase_subtype g t1 t2 (SBase _g x1 b p1 x2 p2 y _) = ()
lem_erase_subtype g t1 t2 (SFunc _g x1 s1 x2 s2 p_s2_s1 t1' t2' y p_t1'_t2')
    = () ? lem_erase_subtype g s2 s1 p_s2_s1
         ? lem_erase_subtype (Cons y s2 g) t1' t2' p_t1'_t2'
lem_erase_subtype g t1 t2 (SWitn _g v t_x p_v_tx _t1 x t' p_t1_t'v)
    = toProof ( erase t1 ? lem_erase_subtype g t1 (tsubBV x v t') p_t1_t'v
            === erase (tsubBV x v t')
            === erase t' === erase t2 )
--    = () ? lem_erase_subtype g t1 (tsubBV x v t') p_t1_t'v
lem_erase_subtype g t1 t2 (SBind _g x t_x t _t2 y p_t_t')
    = () ? lem_erase_subtype (Cons y t_x g) (unbindT x y t) t2 p_t_t'
-}


-------------------------------------------------------------------------
----- | CLOSING SUBSTITUTIONS and DENOTATIONAL SEMANTICS 
-------------------------------------------------------------------------

-- closing substitutions (i.e. th(x), th(e), th(t)) proceed from the top/right of
--   the typing env downwards/leftwards

data CSubst = CEmpty
            | CCons Vname Expr CSubst
{-@ data CSubst  where
    CEmpty :: CSubst
  | CCons  :: x:Vname -> {v:Expr | isValue v} -> th:CSubst -> CSubst @-}

{-@ reflect bindsC @-}
bindsC :: CSubst -> S.Set Vname
bindsC CEmpty         = S.empty
bindsC (CCons x v th) = S.union (S.singleton x) (bindsC th)

{-@ measure uniqueC @-}
uniqueC :: CSubst -> Bool
uniqueC CEmpty         = True
uniqueC (CCons x v th) = (uniqueC th) && not (S.member x (bindsC th))

{-@ reflect csubst @-}
csubst :: CSubst -> Expr -> Expr
csubst CEmpty         e = e
csubst (CCons x v th) e = csubst th (subFV x v e)

-- Idea: ctsubst th t = foldr (\(x,e) t' -> tsubFV x e t') t th 
{-@ reflect ctsubst @-}
ctsubst :: CSubst -> Type -> Type
ctsubst CEmpty         t = t
ctsubst (CCons x v th) t = ctsubst th (tsubFV x v t)

  --- various distributive properties of csubst and ctsubst

{-@ lem_ctsubst_refn :: th:CSubst -> b:Base -> x:Vname -> p:Expr
               -> { pf:_ | ctsubst th (TRefn b x p) == TRefn b x (csubst th p) } @-}
lem_ctsubst_refn :: CSubst -> Base -> Vname -> Expr -> Proof
lem_ctsubst_refn (CEmpty)       b x p = ()
lem_ctsubst_refn (CCons y v th) b x p = toProof ( ctsubst (CCons y v th) (TRefn b x p)
                                              === ctsubst th (tsubFV y v (TRefn b x p))
                                              === ctsubst th (TRefn b x (subFV y v p))
                                                ? lem_ctsubst_refn th b x (subFV y v p)
                                              === TRefn b x (csubst th (subFV y v p)) 
                                              === TRefn b x (csubst (CCons y v th) p) )

{-@ lem_ctsubst_func :: th:CSubst -> x:Vname -> t_x:Type -> t:Type
        -> { pf:_ | ctsubst th (TFunc x t_x t) == TFunc x (ctsubst th t_x) (ctsubst th t) } @-}  
lem_ctsubst_func :: CSubst -> Vname -> Type -> Type -> Proof
lem_ctsubst_func (CEmpty)       x t_x t = ()
lem_ctsubst_func (CCons y v th) x t_x t 
    = () ? lem_ctsubst_func th x (tsubFV y v t_x) (tsubFV y v t) 

{-@ lem_ctsubst_exis :: th:CSubst -> x:Vname -> t_x:Type -> t:Type
        -> {pf:_ | ctsubst th (TExists x t_x t) == TExists x (ctsubst th t_x) (ctsubst th t)} @-}  
lem_ctsubst_exis :: CSubst -> Vname -> Type -> Type -> Proof
lem_ctsubst_exis (CEmpty)       x t_x t = ()
lem_ctsubst_exis (CCons y v th) x t_x t 
    = () ? lem_ctsubst_exis th x (tsubFV y v t_x) (tsubFV y v t) 

{-@ lem_csubst_subBV :: x:Vname -> { v:Expr | isValue v } -> b:Base 
           -> ProofOf(HasBType BEmpty v (BTBase b)) -> th:CSubst -> p:Expr
           -> { pf:_ | csubst th (subBV x v p) == subBV x v (csubst th p) } @-}
lem_csubst_subBV :: Vname -> Expr -> Base -> HasBType -> CSubst -> Expr -> Proof
lem_csubst_subBV x v b pf_v_b (CEmpty)         p = ()
lem_csubst_subBV x v b pf_v_b (CCons y v_y th) p 
    = () ? lem_commute_subFV_subBV x v 
                   (y `withProof` lem_fv_bound_in_benv BEmpty v (BTBase b) pf_v_b y) v_y p
         ? lem_csubst_subBV x v b pf_v_b th (subFV y v_y p)

{-@ lem_ctsubst_tsubBV :: x:Vname -> { v:Expr | isValue v } -> bt:BType
           -> ProofOf(HasBType BEmpty v bt) -> th:CSubst -> t:Type
           -> { pf:_ | ctsubst th (tsubBV x v t) == tsubBV x v (ctsubst th t) } @-}
lem_ctsubst_tsubBV :: Vname -> Expr -> BType -> HasBType -> CSubst -> Type -> Proof
lem_ctsubst_tsubBV x v bt pf_v_b (CEmpty)         t = ()
lem_ctsubst_tsubBV x v bt pf_v_b (CCons y v_y th) t 
    = () ? lem_commute_tsubFV_tsubBV x v 
                   (y `withProof` lem_fv_bound_in_benv BEmpty v bt pf_v_b y) v_y t
         ? lem_ctsubst_tsubBV x v bt pf_v_b th (tsubFV y v_y t)

{-@ lem_csubst_and_unbind :: x:Vname -> y:Vname 
           -> { v:Expr | isValue v } -> b:Base -> ProofOf(HasBType BEmpty v (BTBase b))
           -> th:CSubst -> { p:Expr | not (Set_mem y (fv p)) }
           -> { pf:_ | csubst (CCons y v th) (unbind x y p) == subBV x v (csubst th p) } @-}
lem_csubst_and_unbind :: Vname -> Vname -> Expr -> Base -> HasBType -> CSubst -> Expr -> Proof
lem_csubst_and_unbind x y v b pf_v_b th p = toProof ( csubst (CCons y v th) (unbind x y p)
                                                  === csubst th (subFV y v (unbind x y p))
                                                    ? lem_subFV_unbind x y v p
                                                  === csubst th (subBV x v p)
                                                    ? lem_csubst_subBV x v b pf_v_b th p
                                                  === subBV x v (csubst th p) )

{-@ lem_ctsubst_and_unbindT :: x:Vname -> y:Vname
           -> { v:Expr | isValue v } -> bt:BType -> ProofOf(HasBType BEmpty v bt)
           -> th:CSubst -> { t:Type | not (Set_mem y (free t)) }
           -> { pf:_ | ctsubst (CCons y v th) (unbindT x y t) == tsubBV x v (ctsubst th t) } @-}
lem_ctsubst_and_unbindT :: Vname -> Vname -> Expr -> BType -> HasBType 
           -> CSubst -> Type -> Proof
lem_ctsubst_and_unbindT x y v bt pf_v_b th t = toProof ( ctsubst (CCons y v th) (unbindT x y t)
                                                   === ctsubst th (tsubFV y v (unbindT x y t))
                                                     ? lem_tsubFV_unbindT x y v t
                                                   === ctsubst th (tsubBV x v t)
                                                     ? lem_ctsubst_tsubBV x v bt pf_v_b th t
                                                   === tsubBV x v (ctsubst th t) )


{-@ lem_erase_ctsubst :: th:CSubst -> t:Type 
               -> { pf:_ | erase (ctsubst th t) == erase t } @-}
lem_erase_ctsubst :: CSubst -> Type -> Proof
lem_erase_ctsubst (CEmpty)       t = ()
lem_erase_ctsubst (CCons y v th) t = toProof ( erase (ctsubst (CCons y v th) t)
                                           === erase (ctsubst th (tsubFV y v t))
                                             ? lem_erase_ctsubst th (tsubFV y v t)
                                           === erase (tsubFV y v t)
                                             ? lem_erase_tsubFV y v t
                                           === erase t )

{-@ lem_erase_th_sub :: g:Env -> t1:Type -> t2:Type -> ProofOf(Subtype g t1 t2)
               -> th:CSubst -> { pf:_ | erase (ctsubst th t1) == erase (ctsubst th t2) } @-}
lem_erase_th_sub :: Env -> Type -> Type -> Subtype -> CSubst -> Proof
lem_erase_th_sub g t1 t2 p_t1_t2 th = toProof ( erase (ctsubst th t1) 
                                              ? lem_erase_ctsubst th t1
                                            === erase t1 ? lem_erase_subtype g t1 t2 p_t1_t2
                                            === erase t2 ? lem_erase_ctsubst th t2
                                            === erase (ctsubst th t2) )
                      
data EntailsP where
    Entails :: Env -> Pred -> EntailsP

data Entails where
    EntPred :: Env -> Pred -> (CSubst -> DenotesEnv -> EvalsTo) -> Entails

{-@ data Entails where
    EntPred :: g:Env -> p:Pred 
               -> (th:CSubst -> ProofOf(DenotesEnv g th) 
                             -> ProofOf(EvalsTo (csubst th p) (Bc True)) )
               -> ProofOf(Entails g p) @-} 

data DenotesP where 
    Denotes :: Type -> Expr -> DenotesP    -- e \in [[t]]

data Denotes where
    DRefn :: Base -> Vname -> Pred -> Expr -> HasBType -> EvalsTo -> Denotes
    DFunc :: Vname -> Type -> Type -> Expr -> HasBType
              -> (Expr -> Denotes -> (Expr, (EvalsTo, Denotes))) -> Denotes
    DExis :: Vname -> Type -> Type -> Expr -> HasBType
              -> Expr -> Denotes -> Denotes -> Denotes
{-@ data Denotes where
    DRefn :: b:Base -> x:Vname -> p:Pred -> { v:Expr | isValue v } 
              -> ProofOf(HasBType BEmpty v (BTBase b))
              -> ProofOf(EvalsTo (subBV x v p) (Bc True)) 
              -> ProofOf(Denotes (TRefn b x p) v)
  | DFunc :: x:Vname -> t_x:Type -> t:Type -> { v:Expr | isValue v } 
              -> ProofOf(HasBType BEmpty v (erase (TFunc x t_x t)))
              -> ({ v_x:Expr | isValue v_x } -> ProofOf(Denotes t_x v_x)
                    -> (Expr, (EvalsTo, Denotes))
                       <{\v' pfs -> (isValue v') 
                                       && (propOf (fst pfs) == EvalsTo (App v v_x) v')
                                       && (propOf (snd pfs) == Denotes (tsubBV x v_x t) v')}>)
              -> ProofOf(Denotes (TFunc x t_x t) v)
  | DExis :: x:Vname -> t_x:Type -> t:Type -> { v:Expr | isValue v }
              -> ProofOf(HasBType BEmpty v (erase t)) 
              -> { v_x:Expr | isValue v_x } -> ProofOf(Denotes t_x v_x)
              -> ProofOf(Denotes (tsubBV x v_x t) v)
              -> ProofOf(Denotes (TExists x t_x t) v)  @-} 

  --- helper functions to avoid deeply nested pattern matching

{-@ get_btyp_from_den :: t:Type -> { v:Expr | isValue v } -> ProofOf(Denotes t v)
              -> ProofOf(HasBType BEmpty v (erase t)) @-}
get_btyp_from_den :: Type -> Expr -> Denotes -> HasBType    
get_btyp_from_den t v (DRefn _ _ _ _ pf_v_b _)     = pf_v_b
get_btyp_from_den t v (DFunc _ _ _ _ pf_v_b _)     = pf_v_b
get_btyp_from_den t v (DExis _ _ _ _ pf_v_b _ _ _) = pf_v_b

{-@ get_obj_from_dfunc :: x:Vname -> s:Type -> t:Type -> { v:Expr | isValue v }
        -> ProofOf(Denotes (TFunc x s t) v) -> { v':Expr | isValue v' }
        -> ProofOf(Denotes s v')   
        -> (Expr, (EvalsTo, Denotes))<{\v'' pfs -> (isValue v'') 
                && (propOf (fst pfs) == EvalsTo (App v v') v'')
                && (propOf (snd pfs) == Denotes (tsubBV x v' t) v'') }> @-}
get_obj_from_dfunc :: Vname -> Type -> Type -> Expr -> Denotes -> Expr 
                                            -> Denotes -> (Expr, (EvalsTo, Denotes))
get_obj_from_dfunc x s t v (DFunc _ _ _ _ _ prover) v' den_s_v' = prover v' den_s_v' 



-- Denotations of Environments, [[g]]. There are two cases:
--   1. [[ Empty ]] = { CEmpty }.
--   2. [[ Cons x t g ]] = { CCons x v_x th | Denotes th(t) v_x && th \in [[ g ]] }
data DenotesEnvP where 
    DenotesEnv :: Env -> CSubst -> DenotesEnvP 

data DenotesEnv where
    DEmp :: DenotesEnv
    DExt :: Env -> CSubst -> DenotesEnv -> Vname -> Type -> Expr 
               -> Denotes -> DenotesEnv
{-@ data DenotesEnv where 
    DEmp :: ProofOf(DenotesEnv Empty CEmpty)
 |  DExt :: g:Env -> th:CSubst -> ProofOf(DenotesEnv g th) 
               -> { x:Vname | not (in_env x g) } -> t:Type 
               -> { v:Expr | isValue v } -> ProofOf(Denotes (ctsubst th t) v)
               -> ProofOf(DenotesEnv (Cons x t g) (CCons x v th)) @-}

------------------------------------------------------------------------------
----- | METATHEORY Development
------------------------------------------------------------------------------

-- -- -- -- -- -- -- -- ---
-- Basic Facts and Lemmas -
-- -- -- -- -- -- -- -- ---

-- Determinism of the Operational Semantics
{-@ lem_value_stuck :: e:Expr -> e':Expr -> ProofOf(Step e e') 
                   -> { proof:_ | not (isValue e) } @-}
lem_value_stuck :: Expr -> Expr -> Step -> Proof
lem_value_stuck e  e' (EPrim _ _)      
    = case e of 
        (App _ _)    -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (EApp1 _ _ _ _)  
    = case e of 
        (App _ _)    -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (EApp2 _ _ _ _)  
    = case e of 
        (App _ _)    -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (EAppAbs _ _ _)  
    = case e of 
        (App _ _)    -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (ELet _ _ _ _ _) 
    = case e of 
        (Let _ _ _)  -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (ELetV _ _ _)    
    = case e of 
        (Let _ _ _)  -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (EAnn _ _ _ _)   
    = case e of 
        (Annot _ _)  -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (EAnnV _ _)      
    = case e of 
        (Annot _ _)  -> ()
        (_)          -> impossible ""


{-@ lem_sem_det :: e:Expr -> e1:Expr -> ProofOf(Step e e1)
                   -> e2:Expr -> ProofOf(Step e e2) -> { x:_ | e1 == e2 } @-}
lem_sem_det :: Expr -> Expr -> Step -> Expr -> Step -> Proof
lem_sem_det e e1 p1@(EPrim _ _) e2 p2  -- e = App (Prim c) w
    = case p2 of    
        (EPrim _ _)            -> ()            
        (EApp1 f f' p_f_f' f1) -> impossible ("by lem" ? lem_value_stuck f f' p_f_f')
        (EApp2 f f' p_f_f' v)  -> impossible ("by lem" ? lem_value_stuck f f' p_f_f')
        (EAppAbs {})           -> impossible "OK"
        (_)                    -> impossible ""
lem_sem_det e e' (EApp1 e1 e1' p_e1e1' e2) e'' pf_e_e''
    = case pf_e_e'' of
        (EPrim _ _)                 -> impossible ("by lem" ? lem_value_stuck e1 e1' p_e1e1')
        (EApp1 _e1 e1'' p_e1e1'' _) -> () ? lem_sem_det e1 e1' p_e1e1' e1'' p_e1e1''  
        (EApp2 g g' p_g_g' v)       -> impossible ("by lem" ? lem_value_stuck e1 e1' p_e1e1')
        (EAppAbs {})                -> impossible ("by lem" ? lem_value_stuck e1 e1' p_e1e1')
        (_)                         -> impossible "" 
    -- e = e1 e2, e' = e1' e2, e'' = e1'' e2
lem_sem_det e e' (EApp2 e1 e1' p_e1e1' v1) e'' pf_e_e''
    = case pf_e_e'' of
        (EPrim _ _)                 -> impossible ("by lem" ? lem_value_stuck e1 e1' p_e1e1')
        (EApp1 _v1 v1' p_v1v1' _)   -> impossible ("by lem" ? lem_value_stuck _v1 v1' p_v1v1')
        (EApp2 _ e1'' p_e1e1'' _)   -> () ? lem_sem_det e1 e1' p_e1e1' e1'' p_e1e1''
        (EAppAbs {})                -> impossible ("by lem" ? lem_value_stuck e1 e1' p_e1e1')
        (_)                         -> impossible ""
    -- e = v1 e1, e' = v1 e1', e'' = v1 e1''
lem_sem_det e e1 (EAppAbs x e' v) e2 pf_e_e2
    = case pf_e_e2 of 
        (EPrim {})                  -> impossible ""
        (EApp1 f f' p_f_f' _)       -> impossible ("by lem" ? lem_value_stuck f f' p_f_f')
        (EApp2 f f' p_f_f' _)       -> impossible ("by lem" ? lem_value_stuck f f' p_f_f')
        (EAppAbs _x _e' _v)         -> ()
        (_)                         -> impossible ""
lem_sem_det e e1 (ELet e_x e_x' p_ex_ex' x e1') e2 pf_e_e2
    = case pf_e_e2 of 
        (ELet _ e_x'' p_ex_ex'' _x _) -> () ? lem_sem_det e_x e_x' p_ex_ex' e_x'' p_ex_ex''
        (ELetV _ _ _)                 -> impossible ("by" ? lem_value_stuck e_x e_x' p_ex_ex')
        (_)                           -> impossible ""
lem_sem_det e e1 (ELetV x v e') e2 pf_e_e2
    = case pf_e_e2 of 
        (ELet e_x e_x' p_ex_ex' _x _) -> impossible ("by" ? lem_value_stuck e_x e_x' p_ex_ex')
        (ELetV _ _ _)                 -> ()
        (_)                           -> impossible ""
lem_sem_det e e1 (EAnn e' e1' p_e_e1' t) e2 pf_e_e2
    = case pf_e_e2 of
        (EAnn _e' e2' p_e_e2' _t) -> () ? lem_sem_det e' e1' p_e_e1' e2' p_e_e2'
        (EAnnV {})                -> impossible ("by lem" ? lem_value_stuck e' e1' p_e_e1')
        (_)                       -> impossible ""
lem_sem_det e e1 (EAnnV v t) e2 pf_e_e2
    = case pf_e_e2 of 
        (EAnn e' e1' p_e_e1' t)   -> impossible ("by lem" ? lem_value_stuck e' e1' p_e_e1')
        (EAnnV _v _t)             -> ()
        (_)                       -> impossible "" 

-- We can alpha-rename a variable anywhere in the environment and recursively alter the type
--   derivation tree. NB this is the base type judgement so there are no variables in the 
--   types to worry about
{-@ lem_change_var_btyp :: g:BEnv -> { x:Vname | not (in_envB x g) } -> t_x:BType
        -> { g':BEnv | not (in_envB x g') && Set_emp (Set_cap (bindsB g) (bindsB g')) }
        -> e:Expr -> t:BType -> ProofOf(HasBType (concatB (BCons x t_x g) g') e t)
        -> { y:Vname | not (in_envB y g) && not (in_envB y g') }
        -> ProofOf(HasBType (concatB (BCons y t_x g) g') (subFV x (FV y) e) t) @-}
lem_change_var_btyp :: BEnv -> Vname -> BType -> BEnv -> Expr -> BType 
                -> HasBType ->  Vname -> HasBType
lem_change_var_btyp g x t_x g' e t (BTBC _ b) y
    = BTBC (concatB (BCons y t_x g) g') b
lem_change_var_btyp g x t_x g' e t (BTIC _ n) y
    = BTIC (concatB (BCons y t_x g) g') n 
lem_change_var_btyp g x t_x g' e t p_z_t@(BTVar1 _ z _t) y
    = case g' of 
        (BEmpty)           -> BTVar1 g y t_x 
        (BCons _z _ g'')   -> BTVar1 (concatB (BCons y t_x g) g'') z t
lem_change_var_btyp g x t_x g' e t (BTVar2 _ z _t p_z_t w t_w) y
    = case g' of             -- g''=Emp so x=w and p_z_t :: HasBType(g (FV z) t)
        (BEmpty)           -> case (x == z) of
                                (True)  -> impossible "it is"
                                (False) -> BTVar2 g z t p_z_t y t_x 
        (BCons _w _tw g'') -> case (x == z) of
                    (True)  -> BTVar2 (concatB (BCons y t_x g) g'') 
                                 (y `withProof` lem_in_env_concatB (BCons y t_x g) g'' y)
                                 t (lem_change_var_btyp g x t_x g'' (FV z) t p_z_t y) w t_w
                    (False) -> BTVar2 (concatB (BCons y t_x g) g'')
                                 (z `withProof` lem_in_env_concatB (BCons y t_x g) g'' z
                                    `withProof` lem_in_env_concatB (BCons x t_x g) g'' z)
                                 t (lem_change_var_btyp g x t_x g'' (FV z) t p_z_t y) w t_w
lem_change_var_btyp g x t_x g' e t (BTPrm _ c) y
    = BTPrm (concatB (BCons y t_x g) g') c
lem_change_var_btyp g x t_x g' e t p_e_t@(BTAbs gg z b e' b' z' p_z'_e'_b') y
    = BTAbs (concatB (BCons y t_x g) g') z b (subFV x (FV y) e') b' 
            (z'' `withProof` lem_fv_bound_in_benv (concatB (BCons x t_x g) g') e t p_e_t z'')
            (lem_change_var_btyp g x t_x (BCons z'' b g') (unbind z z'' e') b' 
                (p_z''_e'_b' `withProof` lem_unbind_and_subFV z z' z''
--                      ((e' `withProof` lem_fv_subset e' e)
                        (e' `withProof` lem_fv_bound_in_benv (concatB (BCons x t_x g) g')
                                                          e t p_e_t z'))
                y `withProof` lem_commute_subFV_unbind x y z z'' e')
        where
            z''         = fresh_var_excludingB (concatB (BCons x t_x g) g') y
            p_z''_e'_b' = lem_change_var_btyp  (concatB (BCons x t_x g) g') z' b BEmpty 
                                    (unbind z z' e') b' p_z'_e'_b' 
                                    (z'' `withProof` lem_in_env_concatB g g' z''
                                         `withProof` lem_in_env_concatB (BCons x t_x g) g' z'')
lem_change_var_btyp g x t_x g' e t (BTApp _ e1 t1 t2 p_e1_t1t2 e2 p_e2_t1) y
    = BTApp (concatB (BCons y t_x g) g') (subFV x (FV y) e1) t1 t2 
            (lem_change_var_btyp g x t_x g' e1 (BTFunc t1 t2) p_e1_t1t2 y)
            (subFV x (FV y) e2) (lem_change_var_btyp g x t_x g' e2 t1 p_e2_t1 y)
lem_change_var_btyp g x t_x g' e t p_e_t@(BTLet gg e_z t_z p_ez_tz z e' t' z' p_z'_e'_t') y
    = BTLet (concatB (BCons y t_x g) g') (subFV x (FV y) e_z) t_z
            (lem_change_var_btyp g x t_x g' e_z t_z p_ez_tz y) z (subFV x (FV y) e') t' 
            (z'' `withProof` lem_fv_bound_in_benv (concatB (BCons x t_x g) g') e t p_e_t z'')
            (lem_change_var_btyp g x t_x (BCons z'' t_z g') (unbind z z'' e') t' 
                (p_z''_e'_t' `withProof` lem_unbind_and_subFV z z' z'' 
                        (e' `withProof` lem_fv_bound_in_benv (concatB (BCons x t_x g) g')
                                                          e t p_e_t z'))
                y `withProof` lem_commute_subFV_unbind x y z z'' e')
        where
            z''         = fresh_var_excludingB (concatB (BCons x t_x g) g') y
            p_z''_e'_t' = lem_change_var_btyp  (concatB (BCons x t_x g) g') z' t_z BEmpty 
                                    (unbind z z' e') t' p_z'_e'_t' 
                                    (z'' `withProof` lem_in_env_concatB g g' z''
                                         `withProof` lem_in_env_concatB (BCons x t_x g) g' z'')
lem_change_var_btyp g x t_x g' e t (BTAnn _ e' _t t' p_e'_t) y
    = BTAnn (concatB (BCons y t_x g) g') (subFV x (FV y) e') t 
            (tsubFV x (FV y) t' `withProof` lem_erase_tsubFV x (FV y) t'
                                `withProof` lem_binds_cons_concatB g g' x t_x)
            (lem_change_var_btyp g x t_x g' e' t p_e'_t y)

{-@ lem_change_var_wf :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> t:Type -> ProofOf(WFType (concatE (Cons x t_x g) g') t)
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> ProofOf(WFType (concatE (Cons y t_x g) (esubFV x (FV y) g')) (tsubFV x (FV y) t)) @-}
lem_change_var_wf :: Env -> Vname -> Type -> Env -> Type -> WFType -> Vname -> WFType
lem_change_var_wf g x t_x g' t p_t_wf@(WFRefn gg z b p z' p_z'_p_b) y
    = WFRefn (concatE (Cons y t_x g) (esubFV x (FV y) g')) z b (subFV x (FV y) p) 
             (z'' `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') t p_t_wf z'')
             (lem_change_var_btyp (erase_env g) x (erase t_x) 
                  (BCons z'' (BTBase b) (erase_env g')) (unbind z z'' p) (BTBase TBool) 
                  (p_z''_p_b `withProof` lem_unbind_and_subFV z z' z''
                       (p `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') 
                                                            t p_t_wf z'))
                  y `withProof` lem_commute_subFV_unbind x y z z'' p
                    `withProof` lem_erase_concat (Cons y t_x g) (esubFV x (FV y) g')
                    `withProof` lem_erase_esubFV x (FV y) g')
        where
            z''       = fresh_var_excluding (concatE (Cons x t_x g) g') y
            p_z''_p_b = lem_change_var_btyp (erase_env (concatE (Cons x t_x g) g')) 
                                  z' (BTBase b) BEmpty 
                                  (unbind z z' p) (BTBase TBool) p_z'_p_b  
                                  (z'' `withProof` lem_erase_concat (Cons x t_x g) g'
                                       `withProof` lem_erase_concat g g')
lem_change_var_wf g x t_x g' t p_t_wf@(WFFunc gg z t_z p_tz_wf t' z' p_z'_t'_wf) y
    = WFFunc (concatE (Cons y t_x g) (esubFV x (FV y) g')) z (tsubFV x (FV y) t_z)
             (lem_change_var_wf g x t_x g' t_z p_tz_wf y) (tsubFV x (FV y) t') 
             (z'' `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') t p_t_wf z'')
             (lem_change_var_wf g x t_x (Cons z'' t_z g') (unbindT z z'' t') 
                 (p_z''_t'_wf `withProof` lem_unbindT_and_tsubFV z z' z'' 
                      (t' `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') 
                                                        t p_t_wf z'))
                 y `withProof` lem_commute_tsubFV_unbindT x y z z'' t')
--             `withProof` lem_esubFV_tsubFV x (FV y) z'' t_z g'
        where
            z''         = fresh_var_excluding (concatE (Cons x t_x g) g') y
            p_z''_t'_wf = lem_change_var_wf (concatE (Cons x t_x g) g') z' t_z Empty 
                                    (unbindT z z' t') p_z'_t'_wf --z''
                                    (z'' `withProof` lem_in_env_concat g g' z''
                                         `withProof` lem_in_env_concat (Cons x t_x g) g' z'')
lem_change_var_wf g x t_x g' t p_t_wf@(WFExis gg z t_z p_tz_wf t' z' p_z'_t'_wf) y
    = WFExis (concatE (Cons y t_x g) (esubFV x (FV y) g')) z (tsubFV x (FV y) t_z)
             (lem_change_var_wf g x t_x g' t_z p_tz_wf y) (tsubFV x (FV y) t') 
             (z'' `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') t p_t_wf z'')
             ((lem_change_var_wf g x t_x (Cons z'' t_z g') (unbindT z z'' t') 
                  (p_z''_t'_wf `withProof` lem_unbindT_and_tsubFV z z' z'' 
                      (t' `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') 
                                                        t p_t_wf z'))
                  y `withProof` lem_commute_tsubFV_unbindT x y z z'' t') -- this the key
             )--     `withProof` lem_esubFV_tsubFV x (FV y) z'' t_z g')
        where
            z''         = fresh_var_excluding (concatE (Cons x t_x g) g') y
            p_z''_t'_wf = lem_change_var_wf (concatE (Cons x t_x g) g') z' t_z Empty 
                                    (unbindT z z' t') p_z'_t'_wf 
                                    (z'' `withProof` lem_in_env_concat g g' z''
                                         `withProof` lem_in_env_concat (Cons x t_x g) g' z'')

--                   e' (t' `withProof` lem_bound_concatB g g' y t_y) p_e'_t' x t_x) 
{-@ lem_weaken_btyp :: g:BEnv -> { g':BEnv | Set_emp (Set_cap (bindsB g) (bindsB g')) }
                -> e:Expr -> bt:BType -> ProofOf(HasBType (concatB g g') e bt) 
                -> { x:Vname | (not (in_envB x g)) && (not (in_envB x g')) }
                -> t_x:BType -> ProofOf(HasBType (concatB (BCons x t_x g) g') e bt) @-}
lem_weaken_btyp :: BEnv -> BEnv -> Expr -> BType -> HasBType -> Vname -> BType -> HasBType
lem_weaken_btyp g g' e t (BTBC _g b)      x t_x = BTBC  (concatB (BCons x t_x g) g') b
lem_weaken_btyp g g' e t (BTIC _g n)      x t_x = BTIC  (concatB (BCons x t_x g) g') n
lem_weaken_btyp g g' e t p_y_ty@(BTVar1 _g y t_y) x t_x 
    = case g' of 
        (BEmpty)           -> BTVar2 (BCons y t_y _g) y t_y p_y_ty x t_x
        (BCons _y _ty g'') -> BTVar1 (concatB (BCons x t_x g) g'') y t_y 
-- (g; g' == _g, z:t_z) |- y : t_y
lem_weaken_btyp g g' e t p_y_ty@(BTVar2 _g y t_y p_gg'_y_ty z t_z) x t_x
    = case g' of
        (BEmpty)           -> BTVar2 (BCons z t_z _g) y t_y p_y_ty x t_x
        (BCons _z _tz g'') -> BTVar2 (concatB (BCons x t_x g) g'') 
                                  (y `withProof` lem_in_env_concatB g g'' y
                                     `withProof` lem_in_env_concatB (BCons x t_x g) g'' y) t_y
                                     (lem_weaken_btyp g g'' e t p_gg'_y_ty x t_x)
                                     z t_z
lem_weaken_btyp g g' e t (BTPrm _g c)     x t_x = BTPrm (concatB (BCons x t_x g) g') c
lem_weaken_btyp g g' e t p_e_t@(BTAbs gg y t_y e' t' y' p_y'_e'_t') x t_x
    = BTAbs (concatB (BCons x t_x g) g') y t_y e' t' 
               (y'' `withProof` lem_fv_bound_in_benv (concatB g g') e t p_e_t y'')
               (lem_weaken_btyp g (BCons y'' t_y g') (unbind y y'' e') t' 
                       (p_y''_e'_t' `withProof` lem_unbind_and_subFV y y' y'' e')
--                       (e' `withProof` lem_fv_bound_in_benv (concatB g g') e t p_e_t y'))
                       x t_x) 
        where
            y''         = fresh_varB (concatB (BCons x t_x g) g')
            p_y''_e'_t' = lem_change_var_btyp (concatB g g') y' t_y BEmpty (unbind y y' e') 
                                   t' p_y'_e'_t' 
                                   (y'' `withProof` lem_in_env_concatB g g' y''
                                        `withProof` lem_in_env_concatB (BCons x t_x g) g' y'')
lem_weaken_btyp g g' e t (BTApp _g e1 s s' p_e1_ss' e2 p_e2_s) x t_x 
    = BTApp (concatB (BCons x t_x g) g') e1 s s' 
               (lem_weaken_btyp g g' e1 (BTFunc s s') p_e1_ss' x t_x)
                e2 (lem_weaken_btyp g g' e2 s p_e2_s x t_x)
lem_weaken_btyp g g' e t p_e_t@(BTLet gg e_y t_y p_ey_ty y e' t' y' p_y'_e'_t') x t_x
    = BTLet (concatB (BCons x t_x g) g') e_y t_y 
               (lem_weaken_btyp g g' e_y t_y p_ey_ty x t_x) y e' t' 
               (y'' `withProof` lem_fv_bound_in_benv (concatB g g') e t p_e_t y'')
               (lem_weaken_btyp g (BCons y'' t_y g') (unbind y y'' e') t' 
                       (p_y''_e'_t' `withProof` lem_unbind_and_subFV y y' y'' e')
--                        (e' `withProof` lem_fv_bound_in_benv (concatB g g') e t p_e_t y'))
                       x t_x)
        where
            y''         = fresh_varB (concatB (BCons x t_x g) g')
            p_y''_e'_t' = lem_change_var_btyp (concatB g g') y' t_y BEmpty (unbind y y' e') 
                              t' p_y'_e'_t' (y'' `withProof` lem_in_env_concatB g g' y''
                                        `withProof` lem_in_env_concatB (BCons x t_x g) g' y'')
--               (y `withProof` lem_binds_bv_distinctB (concatB g g') e t p_e_t)
lem_weaken_btyp g g' e bt (BTAnn _g e' _bt lt p_e'_bt) x t_x
    = BTAnn (concatB (BCons x t_x g) g') e' bt 
            (lt `withProof` lem_binds_cons_concatB g g' x t_x)
            (lem_weaken_btyp g g' e' bt p_e'_bt x t_x)

{-@ lem_weaken_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
            -> t:Type -> ProofOf(WFType (concatE g g') t)
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } 
            -> t_x:Type -> ProofOf(WFType g t_x)
            -> ProofOf(WFType (concatE (Cons x t_x g) g') t) @-}
lem_weaken_wf :: Env -> Env -> Type -> WFType -> Vname -> Type -> WFType -> WFType
lem_weaken_wf g g' t p_t_wf@(WFRefn _g y b p y' pf_p_bl) x t_x p_tx
    = WFRefn (concatE (Cons x t_x g) g') y b p
                           (y'' `withProof` lem_in_env_concat g g' y''
                                `withProof` lem_in_env_concat (Cons x t_x g) g' y''
                                `withProof` lem_free_bound_in_env (concatE g g') t p_t_wf y'') 
          (lem_weaken_btyp (erase_env g) (BCons y'' (BTBase b) (erase_env g')) 
               (unbind y y'' p) (BTBase TBool) 
               (pf_y''_p_bl `withProof` lem_unbind_and_subFV y y' y'' p) 
                           x (erase t_x))
        where
          y''         = fresh_var (concatE (Cons x t_x g) g')
          pf_y''_p_bl = lem_change_var_btyp (erase_env (concatE g g')) y' (BTBase b) BEmpty
                             (unbind y y' p) (BTBase TBool) pf_p_bl
                             (y'' `withProof` lem_erase_concat (Cons x t_x g) g'
                                  `withProof` lem_erase_concat g g')
lem_weaken_wf g g' t p_t_wf@(WFFunc _g y t_y p_ty_wf t' y' p_y'_t'_wf) x t_x p_tx
    = WFFunc (concatE (Cons x t_x g) g') y
             t_y (lem_weaken_wf g g' t_y p_ty_wf x t_x p_tx)
             t' (y'' `withProof` lem_free_bound_in_env (concatE g g') t p_t_wf y'')
             (lem_weaken_wf g (Cons y'' t_y g') (unbindT y y'' t') 
                         (p_y''_t'_wf `withProof` lem_unbindT_and_tsubFV y y' y'' t')
                         x t_x p_tx)
        where
          y''         = fresh_var(concatE (Cons x t_x g) g')
          p_y''_t'_wf = lem_change_var_wf (concatE g g') y' t_y Empty
                             (unbindT y y' t') p_y'_t'_wf
                             (y'' `withProof` lem_in_env_concat g g' y''
                                  `withProof` lem_in_env_concat (Cons x t_x g) g' y'')
lem_weaken_wf g g' t p_t_wf@(WFExis gg y t_y p_ty_wf t' y' p_y'_t'_wf) x t_x p_tx
    = WFExis (concatE (Cons x t_x g) g') y 
             t_y (lem_weaken_wf g g' t_y p_ty_wf x t_x p_tx)
             t' (y'' `withProof` lem_free_bound_in_env (concatE g g') t p_t_wf y'')
             (lem_weaken_wf g (Cons y'' t_y g') (unbindT y y'' t')
                         (p_y''_t'_wf `withProof` lem_unbindT_and_tsubFV y y' y''  t')
                         x t_x p_tx)
        where
          y''         = fresh_var (concatE (Cons x t_x g) g')
          p_y''_t'_wf = lem_change_var_wf (concatE g g') y' t_y Empty 
                             (unbindT y y' t') p_y'_t'_wf 
                             (y'' `withProof` lem_in_env_concat g g' y''
                                  `withProof` lem_in_env_concat (Cons x t_x g) g' y'')

{-
{-@ lem_denote_sound_sub :: g:Env -> t1:Type -> t2:Type -> ProofOf(Subtype g t1 t2)
                -> th:CSubst -> ProofOf(DenotesEnv g th) -> { v:Expr | isValue v}
                -> ProofOf(Denotes (ctsubst th t1) v) 
                -> ProofOf(Denotes (ctsubst th t2) v) @-}
lem_denote_sound_sub :: Env -> Type -> Type -> Subtype -> CSubst -> DenotesEnv
                            -> Expr -> Denotes -> Denotes 
lem_denote_sound_sub g t1@(TRefn _ _ _) t2@(TRefn _ _ _) (SBase _g x1 b p1 x2 p2 y pf_ent_p2)
                    -- t1 = b{x1:p1}, t2 = b{x2:p2}  -- Pf(Entails g' p2[y/x2])
                       th den_g_th val den_t1_v@(DRefn _b _ _ _val pf_v_b pf_th_p1v_tt)
    = case (pf_ent_p2) of                                        -- EvalsTo th(p1[v/x1]) tt
        (EntPred y_g _p2 ev_thp2_tt) 
                       -- forall th' in [[x1,g]]. EvalsTo th'(p2[x1/x2]) tt 
            -> DRefn b x2 (csubst th p2) _val pf_v_b' pf_th'_p2v_tt
                     `withProof` lem_ctsubst_refn th b x2 p2
                where
                  pf_v_b'       = pf_v_b `withProof`  lem_ctsubst_refn th b x1 p1 
                  th'           = CCons y val th -- y is fresh repl. x1
                                 -- th' = (y |-> v, th) \in [[ Cons y t1 g ]]
                  den_g'_th'    = DExt g th den_g_th y t1 val den_t1_v
                  pf_th'_p2v_tt = ev_thp2_tt th' den_g'_th' 
                                    `withProof` lem_csubst_and_unbind x2 y val b pf_v_b' th p2
lem_denote_sound_sub g t1@(TFunc _ _ _) t2@(TFunc _ _ _)  -----------------------------------
             p_t1_t2@(SFunc _g x1 s1 x2 s2 p_g_s2_s1 t1' t2' y p_g'_t1_t2)
                                                -- Subtype (Cons y s2 g) t1'[y/x1] t2'[y/x2]
             th den_g_th _v den_tht1_v@(DFunc _x1 ths1 tht1' val pf_v_er_t1 _pf_den_tht1'_vv')
   =   DFunc x2 (ctsubst th s2) (ctsubst th t2') val pf_v_er_t2 (pf_den_tht2'_vv')
            `withProof` lem_ctsubst_func th x1 s1 t1'
            `withProof` lem_ctsubst_func th x2 s2 t2'
        where
          pf_v_er_t2   = pf_v_er_t1 `withProof` lem_erase_th_sub g t1 t2 p_t1_t2 th
                                    `withProof` lem_ctsubst_func th x1 s1 t1'
                                    `withProof` lem_ctsubst_func th x2 s2 t2'
          g'           = Cons y s2 g
          ths2_ths1    = lem_denote_sound_sub g s2 s1 p_g_s2_s1 th den_g_th 
          tht1'_tht2'  = lem_denote_sound_sub g' (unbindT x1 y t1') (unbindT x2 y t2')
                                              p_g'_t1_t2 
          {-@ pf_den_tht2'_vv' :: ({ v':Expr | isValue v' } 
               -> ProofOf(Denotes (ctsubst th s2) v') -> (Expr, (EvalsTo, Denotes))
                 <{\v'' pfs -> (isValue v'')
                    && (propOf (fst pfs) == EvalsTo (App val v') v'')
                    && (propOf (snd pfs) == Denotes (tsubBV x2 v' (ctsubst th t2')) v'')}>) @-}
          pf_den_tht2'_vv' v' den_ths2_v' = (v'', (fst pfs, den_t2'v'_v'')) 
              where
                pf_v'_er_s2    = get_btyp_from_den (ctsubst th s2)  v' den_ths2_v' 
                                         `withProof` lem_erase_th_sub g s2 s1 p_g_s2_s1 th 
                th'            = CCons y v' th -- (y |-> v', th) in [[y:s2,g]]
                den_g'_th'     = DExt g th den_g_th y s2 v' den_ths2_v' 
                (v'', pfs)     = get_obj_from_dfunc x1 (ctsubst th s1) (ctsubst th t1') 
                         val den_tht1_v v' 
                         (ths2_ths1 v' (den_ths2_v' `withProof` lem_ctsubst_func th x2 s2 t2')
                         `withProof` lem_ctsubst_func th x1 s1 t1')
                pf_vv'_er_t1'  = BTApp BEmpty val (erase (ctsubst th s1)) 
                                       (erase (ctsubst th t1')) pf_v_er_t1
                                       v' (get_btyp_from_den (ctsubst th s2) v' den_ths2_v')
                pf_v''_er_t1'  = lemma_soundness (App val v') v'' (fst pfs)
                                                 (erase t1') pf_vv'_er_t1'
                {-@ den_t2'v'_v'' :: ProofOf(Denotes (tsubBV x2 v' (ctsubst th t2')) v'') @-}
                den_t2'v'_v''  = tht1'_tht2' th' den_g'_th' v'' 
                                      (snd pfs `withProof` lem_ctsubst_and_unbindT 
                                                            x1 y v' (erase (ctsubst th s1)) 
                                                            pf_v'_er_s2 th t1')
                                      `withProof` lem_ctsubst_func th x2 s2 t2'
                                      `withProof` lem_ctsubst_func th x1 s1 t1'
                                      `withProof` lem_ctsubst_and_unbindT x2 y v' 
                                          (erase (ctsubst th s2)) 
                                          (get_btyp_from_den (ctsubst th s2) v' den_ths2_v') 
                                          th t2'


{-@ lem_denote_sound_typ :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
                -> th:CSubst -> ProofOf(DenotesEnv g th)  
                -> (Expr, (EvalsTo, Denotes))<{\v' pfs ->
                     (isValue v') && 
                     (propOf (fst pfs) == EvalsTo (csubst th e) v') &&
                     (propOf (snd pfs) == Denotes (ctsubst th t) v')}> @-}
lem_denote_sound_typ :: Env -> Expr -> Type -> HasType -> CSubst -> DenotesEnv
                            -> (Expr, (EvalsTo, Denotes))
lem_denote_sound_typ g e t p_e_t th den = undefined 
-}

{-@ lem_typing_wf :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
                      -> ProofOf(WFEnv g) -> ProofOf(WFType g t) @-} 
lem_typing_wf :: Env -> Expr -> Type -> HasType -> WFEnv -> WFType
--lem_typing_wf g e t (TBC _g b) p_wf_g  = lem_wf_tybc g b
--lem_typing_wf g e t (TIC _g n) p_wf_g  = lem_wf_tyic g n
lem_typing_wf g e t (TVar1 _g' x _t) p_wf_g
    = case p_wf_g of
        (WFEEmpty)                     -> impossible "surely"
        (WFEBind g' p_g' _x _t p_g'_t) -> lem_weaken_wf g' Empty t p_g'_t x t p_g'_t
lem_typing_wf g e t (TVar2 g' x _t p_g'_x_t y s) p_wf_g
    = case p_wf_g of
        (WFEEmpty)                     -> impossible "Surely"
        (WFEBind g' p_g' _y _s p_g'_s) -> lem_weaken_wf g' Empty t 
                                              (lem_typing_wf g' e t p_g'_x_t p_g')
                                              y s p_g'_s
--TODO: refactor lem_wf_ty: adds five minutes to typechecking
--lem_typing_wf g e t (TPrm _g c) p_wf_g = lem_wf_ty g c
lem_typing_wf g e t (TAbs _g x t_x p_tx_wf e' t' y p_e'_t') p_wf_g
    = WFFunc g x t_x p_tx_wf t' y (lem_typing_wf (Cons y t_x g) (unbind x y e') 
                                               (unbindT x y t') p_e'_t'
                                               (WFEBind g p_wf_g y t_x p_tx_wf))
lem_typing_wf g e t (TApp _g e1 x t_x t' p_e1_txt' e2 p_e2_tx) p_wf_g
    = case (lem_typing_wf g e1 (TFunc x t_x t') p_e1_txt' p_wf_g) of
        (WFFunc _ _ _ p_g_tx _ y p_gx_t') -> WFExis g x t_x 
                                                    (lem_typing_wf g e2 t_x p_e2_tx p_wf_g)
                                                    t' y p_gx_t'
        (_)                               -> impossible "clearly"
lem_typing_wf g e t (TLet _g e_x t_x p_ex_tx x e' _t p_g_t y p_e'_t) p_wf_g = p_g_t 
lem_typing_wf g e t (TAnn _g e' _t p_e'_t) p_wf_g
    = lem_typing_wf g e' t p_e'_t p_wf_g
lem_typing_wf g e t (TSub _g _e s p_e_s _t p_g_t p_s_t) p_wf_g = p_g_t


-- the big theorems 
{-@ thm_progress :: e:Expr -> t:Type -> ProofOf(HasType Empty e t)  
           -> Either { v:_ | isValue e } (Expr, Step)<{\e' pf -> propOf pf == Step e e'}> @-}
thm_progress :: Expr -> Type -> HasType -> Either Proof (Expr,Step) 
thm_progress c _b (TBC Empty _)           = Left ()
thm_progress c _b (TIC Empty _)           = Left ()
thm_progress x _t (TVar1 Empty _ _)       = Left ()
thm_progress x _t (TVar2 Empty _ _ _ _ _) = Left ()
thm_progress c _t (TPrm Empty _)          = Left ()
thm_progress e t  (TAbs {})               = Left ()
thm_progress _e _t (TApp Empty (Prim p) x t_x t p_e1_txt e2 p_e2_tx) 
      = case (thm_progress e2 t_x p_e2_tx) of
          Left ()               -> Right (delta p e2, EPrim p e2)
          Right (e2', p_e2_e2') -> Right (App (Prim p) e2', EApp2 e2 e2' p_e2_e2' (Prim p))
thm_progress _e _t (TApp Empty (Lambda x e') _x t_x t p_e1_txt e2 p_e2_tx) 
      = case (thm_progress e2 t_x p_e2_tx) of
          Left ()               -> Right (subBV x e2 e', EAppAbs x e' e2)
          Right (e2', p_e2_e2') -> Right (App (Lambda x e') e2', EApp2 e2 e2' p_e2_e2' (Lambda x e'))
thm_progress _e _t (TApp Empty e1 x t_x t p_e1_txt e2 p_e2_tx) 
      = Right (App e1' e2, EApp1 e1 e1' p_e1_e1' e2)
        where
          Right (e1', p_e1_e1') = thm_progress e1 (TFunc x t_x t) p_e1_txt
thm_progress _e _t (TLet Empty e1 tx p_e1_tx x e2 t p_t y p_e2_t)
      = case (thm_progress e1 tx p_e1_tx) of
          Left ()               -> Right (subBV x e1 e2, ELetV x e1 e2)
          Right (e1', p_e1_e1') -> Right (Let x e1' e2, ELet e1 e1' p_e1_e1' x e2) 
thm_progress _e _t (TAnn Empty e1 t p_e1_t)
      = case (thm_progress e1 t p_e1_t) of
          Left ()               -> Right (e1, EAnnV e1 t)
          Right (e1', p_e1_e1') -> Right (Annot e1' t, EAnn e1 e1' p_e1_e1' t)
thm_progress _e _t (TSub Empty e s p_e_s t p_t p_s_t)
      = case (thm_progress e s p_e_s) of
          Left ()               -> Left ()
          Right (e', p_e_e')    -> Right (e', p_e_e') 

