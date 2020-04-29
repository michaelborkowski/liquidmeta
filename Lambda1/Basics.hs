{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-}
{- @ LIQUID "--no-totality" @-}
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
  ---   Locally named representations
  ---     "free" variables are ints because easier to pick fresh ones
  ---     "bound" ones also ints 

{- @ type Vname =  Nat @-} -- > 0 or not?
type Vname = Int

data Prim = And | Or | Not | Eqv
          | Leq | Leqn Int 
          | Eq  | Eqn Int
  deriving (Eq, Show)

{-@ data Expr [esize] @-}
data Expr = Bc Bool              -- True, False
          | Ic Int               -- 0, 1, 2, ...
          | Prim Prim            -- built-in primitive functions 
          | BV Vname             -- BOUND Variables: bound to a Lambda, Let or :t
          | FV Vname             -- FREE Variables: bound in an environment
          | Lambda Vname Expr    -- \x.e
          | App Expr Expr        -- e e' 
          | Let Vname Expr Expr  -- let x = e1 in e2
          | Annot Expr Type      -- e : t
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
esize (Let x e_x e)     = (esize e_x) + (esize e) + 1
esize (Annot e t)       = (esize e)   + (tsize t) + 1
esize Crash             = 1

-- In a value, all BV must be bound to a binder within the expression
{-@ type Value = { v:Expr | isValue v && Set_emp (freeBV v) } @-}

{-@ reflect isValue @-} -- meaning: is a syntactic value
{- @ isValue :: v:Expr -> { b:Bool | (isValue v) => Set_emp (freeBV v) } @-}
isValue :: Expr -> Bool
isValue (Bc _)         = True
isValue (Ic _)         = True
isValue (Prim _)       = True
isValue (FV _)         = True -- bound variables not a legal value because we 
isValue v@(Lambda x e) = True -- S.null (freeBV v)
isValue Crash          = True
isValue _              = False

{-@ reflect freeBV @-}
{-@ freeBV :: e:Expr -> S.Set Vname / [esize e] @-}
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
{-@ fv :: e:Expr -> S.Set Vname / [esize e] @-}
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

  --- TERM-LEVEL SUBSTITUTION

{-@ reflect subFV @-} 
{-@ subFV :: x:Vname -> v:Value -> e:Expr 
                     -> { e':Expr | (Set_mem x (fv e) || e == e') &&
                      ( Set_sub (fv e) (Set_cup (Set_sng x) (fv e')) ) &&
                      ( Set_sub (fv e') (Set_cup (fv v) (Set_dif (fv e) (Set_sng x)))) &&
                      ( (freeBV e) == (freeBV e') ) &&
                      ( (not (Set_mem x (fv v))) => not (Set_mem x (fv e')) ) && 
                      ( (isValue v && isValue e) => isValue e' ) } / [esize e] @-}
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

{-@ reflect subBV @-} -- x is a BOUND var  
{-@ subBV :: x:Vname ->  v:Value -> e:Expr 
                     -> { e':Expr | Set_sub (fv e) (fv e') &&
                                    Set_sub (fv e') (Set_cup (fv e) (fv v)) &&
                                    freeBV e' == Set_dif (freeBV e) (Set_sng x) &&
                                    ( esize v != 1  || esize e == esize e' )} / [esize e] @-}
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


{-@ reflect unbind @-} -- unbind converts (BV x) to (FV y) in e
{-@ unbind :: x:Vname -> y:Vname -> e:Expr 
                    -> { e':Expr | Set_sub (fv e) (fv e') && 
                                   Set_sub (fv e') (Set_cup (Set_sng y) (fv e)) &&
                                   freeBV e' == Set_dif (freeBV e) (Set_sng x) &&
                                   (unbind x y e == subBV x (FV y) e) &&
                                   esize e == esize e' } / [esize e] @-}
unbind :: Vname -> Vname -> Expr -> Expr
unbind x y e = subBV x (FV y) e


  ---   Refinement Level: Names, Terms (in FO), FO Predicates, SMT Formulae
type Pred = Expr

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
{-@ data Type [tsize] @-}
{- @ data Type [tsize] where
    TRefn   :: Base -> Vname -> p:Pred -> { t:Type | free t == fv p }
  | TFunc   :: Vname -> t_x:Type -> t:Type 
                     -> { t':Type | free t' == Set_cup (free t_x) (free t) }
  | TExists :: Vname -> t_x:Type -> t:Type 
                     -> { t':Type | free t' == Set_cup (free t_x) (free t) } @-}

{-@ lazy tsize @-}
{-@ measure tsize @-}
{-@ tsize :: t:Type -> { v:Int | v >= 0 } @-} 
tsize :: Type -> Int
tsize (TRefn b v r)     = (esize r) + 1
tsize (TFunc x t_x t)   = (tsize t_x) + (tsize t) + 1
tsize (TExists x t_x t) = (tsize t_x) + (tsize t) + 1


{-@ measure tlen @-}
{-@ tlen :: Type -> { v:Int | v >= 0 } @-}
tlen :: Type -> Int
tlen (TRefn b v r)     = 0
tlen (TFunc x t_x t)   = (tlen t) + 1
tlen (TExists x t_x t) = (tlen t) + 1

{-@ reflect free @-} 
{-@ free :: t:Type -> S.Set Vname / [tsize t] @-}
free :: Type -> S.Set Vname
free (TRefn b v r)      = fv r
free (TFunc x t_x t)    = S.union (free t_x) (free t) 
free (TExists x t_x t)  = S.union (free t_x) (free t) 


{-@ reflect tfreeBV @-}
{-@ tfreeBV :: t:Type -> S.Set Vname / [tsize t] @-}
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
                ( (not (Set_mem x (fv e))) => not (Set_mem x (free t')) ) } / [tsize t] @-}
tsubFV :: Vname -> Expr -> Type -> Type
tsubFV x e_x (TRefn b z r)     = TRefn b z (subFV x e_x r)
tsubFV x e_x (TFunc z t_z t)   = TFunc   z (tsubFV x e_x t_z) (tsubFV x e_x t)
tsubFV x e_x (TExists z t_z t) = TExists z (tsubFV x e_x t_z) (tsubFV x e_x t)


{-@ reflect tsubBV @-}
{-@ tsubBV :: x:Vname -> v_x:Value -> t:Type  
                    -> { t':Type | tlen t' <= tlen t && tlen t' >= 0 &&
                                   Set_sub (free t) (free t') &&
                                   Set_sub (free t') (Set_cup (fv v_x) (free t)) &&
                                   tfreeBV t' == Set_dif (tfreeBV t) (Set_sng x) &&
                                   ( esize v_x != 1 || tsize t == tsize t' ) } / [tsize t] @-}
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
                                      Set_sub (free t') (Set_cup (Set_sng y) (free t)) &&
                                      tfreeBV t' == Set_dif (tfreeBV t) (Set_sng x) &&
                                      (unbindT x y t == tsubBV x (FV y) t) &&
                                      tsize t == tsize t' } / [tsize t] @-} 
unbindT :: Vname -> Vname -> Type -> Type
unbindT x y t = tsubBV x (FV y) t


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

data Env = Empty                         -- type Env = [(Vname, Type)]	
         | Cons Vname Type Env
  deriving (Show)
{-@ data Env where 
    Empty :: Env
  | Cons  :: x:Vname -> t:Type -> { g:Env | not (in_env x g) } -> Env @-}

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

{-@ reflect in_env @-}
in_env :: Vname -> Env -> Bool
in_env x g = S.member x (binds g) 

{- @ reflect lookup @- }
lookup :: Vname -> Env -> Maybe Type
lookup x Empty                     = Nothing
lookup x (Cons y t g) | (x == y)   = Just t
                      | otherwise  = lookup x g -}

{-@ reflect bound_in @-}
bound_in :: Vname -> Type -> Env -> Bool
bound_in x t Empty                                 = False
bound_in x t (Cons y t' g) | (x == y)              = (t == t')
                           | otherwise             = bound_in x t g

{-@ reflect binds @-}
binds :: Env -> S.Set Vname
binds Empty        = S.empty
binds (Cons x t g) = S.union (S.singleton x) (binds g)

  --- BARE-TYPING ENVIRONMENTS

data BType = BTBase Base                 -- b
           | BTFunc BType BType          -- t -> t'
  deriving (Eq, Show)

{-@ reflect erase @-}
erase :: Type -> BType
erase (TRefn b v r)     = BTBase b
erase (TFunc x t_x t)   = BTFunc (erase t_x) (erase t)
erase (TExists x t_x t) = (erase t)

data BEnv = BEmpty                       -- type BEnv = [(Vname, BType)]
          | BCons Vname BType BEnv
  deriving (Show) 
{-@ data BEnv where
    BEmpty :: BEnv
  | BCons  :: x:Vname -> t:BType -> { g:BEnv | not (in_envB x g) } -> BEnv @-}

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

{-@ reflect in_envB @-}
in_envB :: Vname -> BEnv -> Bool
in_envB x g = S.member x (bindsB g) 

{-@ reflect lookupB @-}
{- @ lookupB :: x:Vname -> g:BEnv -> { mt:Maybe BType | (mt == Just t) => bound_inB x t g } @-}
lookupB :: Vname -> BEnv -> Maybe BType
lookupB x BEmpty                     = Nothing
lookupB x (BCons y t g) | x == y     = Just t
                        | otherwise  = lookupB x g

{-@ reflect bound_inB @-}
{- @ bound_inB :: x:Vname -> t:BType -> g:BEnv 
        -> { b:Bool | (not b || in_envB x g) && (lookupB x g == Just t => bound_inB x t g)} @-}
bound_inB :: Vname -> BType -> BEnv -> Bool
bound_inB x t BEmpty                                 = False
bound_inB x t (BCons y t' g) | (x == y)              = (t == t')
                             | otherwise             = bound_inB x t g

{-@ lem_lookup_boundinB :: x:Vname -> t:BType -> { g:BEnv | lookupB x g == Just t }
        -> { pf:_ | bound_inB x t g } @-}
lem_lookup_boundinB :: Vname -> BType -> BEnv -> Proof
lem_lookup_boundinB x t (BCons y s g) | x == y    = ()
                                      | otherwise = lem_lookup_boundinB x t g

{-@ lem_boundin_inenvB :: x:Vname -> t:BType -> { g:BEnv | bound_inB x t g}
        -> { pf:_ | in_envB x g } @-}
lem_boundin_inenvB :: Vname -> BType -> BEnv -> Proof
lem_boundin_inenvB x t (BCons y s g) | x == y    = ()
                                     | otherwise = lem_boundin_inenvB x t g 

{-@ reflect bindsB @-}
bindsB :: BEnv -> S.Set Vname
bindsB BEmpty        = S.empty
bindsB (BCons x t g) = S.union (S.singleton x) (bindsB g)


{-@ reflect erase_env @-}
{-@ erase_env :: g:Env -> { g':BEnv | binds g == bindsB g' } @-}
erase_env :: Env -> BEnv
erase_env Empty        = BEmpty
erase_env (Cons x t g) = BCons x (erase t) (erase_env g)


--------------------------------------------------------------------------
----- | OPERATIONAL SEMANTICS (Small Step)
--------------------------------------------------------------------------

-- E-Prim c v -> delta(c,v)
-- E-App1 e e1 -> e' e1 if e->e'
-- E-App2 v e  -> v e'  if e->e'
-- E-AppAbs (\x. e) v -> e[v/x]
-- E-Let  let x=e_x in e -> let x=e'_x in e if e_x->e'_x
-- E-LetV let x=v in e -> e[v/x]
-- E-Ann   e:t -> e':t  if e->e'
-- E-AnnV  v:t -> v

{-@ reflect delta @-}
{-@ delta :: p:Prim -> e:Value ->  e':Expr @-}
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
                 -> { v:Expr | isValue v } -> ProofOf( Step (App v e) (App v e'))
 |  EAppAbs :: x:Vname -> e:Expr -> v:Value  
                 -> ProofOf( Step (App (Lambda x e) v) (subBV x v e))
 |  ELet  :: e_x:Expr -> e_x':Expr -> ProofOf( Step e_x e_x' )
                 -> x:Vname -> e:Expr -> ProofOf( Step (Let x e_x e) (Let x e_x' e))
 |  ELetV :: x:Vname -> v:Value -> e:Expr
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
  

-----------------------------------------------------------------------------
----- | JUDGEMENTS : the Bare-Typing Relation
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
                -> { t1:Type | (erase t1 == b) && Set_sub (free t1) (bindsB g) && Set_emp (tfreeBV t1) }
                -> ProofOf(HasBType g e b) -> ProofOf(HasBType g (Annot e t1) b)  @-} 

{-@ measure btypSize @-}
{-@ btypSize :: HasBType -> { v:Int | v >= 0 } @-}
btypSize :: HasBType -> Int
btypSize (BTBC {})                           = 1
btypSize (BTIC {})                           = 1
btypSize (BTVar1 {})                         = 1
btypSize (BTVar2 _ _ _ p_x_b _ _)            = (btypSize p_x_b)   + 1
btypSize (BTPrm {})                          = 1
btypSize (BTAbs _ _ _ _ _ _ p_e_b')          = (btypSize p_e_b')  + 1
btypSize (BTApp _ _ _ _ p_e_bb' _ p_e'_b)    = (btypSize p_e_bb') + (btypSize p_e'_b) + 1
btypSize (BTLet _ _ _ p_ex_b _ _ _ _ p_e_b') = (btypSize p_ex_b)  + (btypSize p_e_b') + 1
btypSize (BTAnn _ _ _ _ p_e_b)               = (btypSize p_e_b)   + 1

{-@ simpleBTVar :: g:BEnv -> { x:Vname | in_envB x g} -> { t:BType | bound_inB x t g } 
                -> ProofOf(HasBType g (FV x) t) @-}
simpleBTVar :: BEnv -> Vname -> BType -> HasBType
simpleBTVar g x t = case g of
  (BCons y s g') ->  case (x == y, t == s) of   -- g = Empty is impossible
        (True, True) -> BTVar1 g' x t           -- x = y but t != s is impossible
        (False, _)   -> BTVar2 g' x t (simpleBTVar g' x t) y s


------------------------------------------------------------
---- | Limited Bi-directional TYPE Checking and Synthesis --
------------------------------------------------------------
--
-- The only expressions fow which we are trying to automate the production of
--    are the refinements found in the types of the built in primitives, in ty(c)
--    These consist of constants, primitives, variables and function application only.

{-@ reflect noDefns @-}
noDefns :: Expr -> Bool
noDefns (Bc _)        = True
noDefns (Ic _)        = True
noDefns (BV _)        = True
noDefns (FV _)        = True
noDefns (Prim _)      = True
noDefns (Lambda _ _ ) = False
noDefns (App e e')    = (noDefns e) && (noDefns e')
noDefns (Let _ _ _)   = False
noDefns (Annot e t)   = noDefns e
noDefns Crash         = True

{-@ reflect checkType @-}
{-@ checkType :: BEnv -> { e:Expr | noDefns e } -> t:BType -> Bool / [esize e] @-}
checkType :: BEnv -> Expr -> BType -> Bool
checkType g (Bc b) t         = ( t == BTBase TBool )
checkType g (Ic n) t         = ( t == BTBase TInt )
checkType g (Prim c) t       = ( t == erase (ty c) )
checkType g (BV x) t         = False
checkType g (FV x) t         = bound_inB x t g
checkType g (App e e') t     = case ( synthType g e' ) of
    (Just t')       -> checkType g e (BTFunc t' t)
    _               -> False
checkType g (Annot e liqt) t   = ( checkType g e t ) && ( t == erase liqt ) &&
                                 ( S.isSubsetOf (free liqt) (bindsB g) ) &&
                                 ( S.null (tfreeBV liqt) )
checkType g Crash t            = False -- Crash is untypable

{-@ reflect synthType @-}
{-@ synthType :: BEnv -> { e:Expr | noDefns e } -> Maybe BType / [esize e] @-}
synthType :: BEnv -> Expr -> Maybe BType
synthType g (Bc b)          = Just ( BTBase TBool )
synthType g (Ic n)          = Just ( BTBase TInt )
synthType g (Prim c)        = Just ( erase (ty c) )
synthType g (BV x)          = Nothing
synthType g (FV x)          = lookupB x g
synthType g (App e e')      = case ( synthType g e' ) of
    Nothing    -> Nothing
    (Just t')  -> case ( synthType g e ) of
        (Just (BTFunc t_x t)) -> if ( t_x == t' ) then Just t else Nothing
        _                     -> Nothing
synthType g (Annot e liqt)  = case ( checkType g e (erase liqt) && S.null (tfreeBV liqt) &&
                                     S.isSubsetOf (free liqt) (bindsB g) ) of
    True  -> Just (erase liqt)
    False -> Nothing
synthType g Crash           = Nothing

{-@ lem_check_synth :: g:BEnv -> { e:Expr | noDefns e } -> { t:BType | synthType g e == Just t }
                              -> { pf:_ | checkType g e t } @-}
lem_check_synth :: BEnv -> Expr -> BType -> Proof
lem_check_synth g (Bc b) t         = case t of 
    (BTBase TBool) -> ()
lem_check_synth g (Ic n) t         = case t of
    (BTBase TInt)  -> () 
lem_check_synth g (Prim c) t       = ()
lem_check_synth g (FV x) t         = lem_lookup_boundinB x t g 
lem_check_synth g (App e e') t     = lem_check_synth g e (BTFunc t' t) 
  where
    (Just t') = synthType g e' 
lem_check_synth g (Annot e liqt) t = ()

{-@ makeHasBType :: g:BEnv -> { e:Expr | noDefns e } -> { t:BType | checkType g e t }
        -> ProofOf(HasBType g e t) / [esize e] @-}
makeHasBType :: BEnv -> Expr -> BType -> HasBType
makeHasBType g (Bc b) t         = BTBC g b
makeHasBType g (Ic n) t         = BTIC g n
makeHasBType g (Prim c) t       = BTPrm g c
makeHasBType g (FV x) t         = simpleBTVar g (x? lem_boundin_inenvB x t g ) t
makeHasBType g (App e e') t     = BTApp g e t' t pf_e_t't e' pf_e'_t'
  where
    (Just t')  = synthType g e'
    pf_e_t't   = makeHasBType g e (BTFunc t' t)
    pf_e'_t'   = makeHasBType g e' (t' ? lem_check_synth g e' t')
makeHasBType g (Annot e liqt) t = BTAnn g e t liqt pf_e_t
  where
    pf_e_t = makeHasBType g e t

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

{-@ reflect refn_pred @-}
{- @ refn_pred :: c:Prim -> { p:Pred | noDefns p } @-}
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
noDefnsInRefns g (TFunc x t_x t)    = noDefnsInRefns g t_x && noDefnsInRefns (Cons y t_x g) (unbindT x y t)
  where
    y = fresh_var g
noDefnsInRefns g (TExists x t_x t)  = noDefnsInRefns g t_x && noDefnsInRefns (Cons y t_x g) (unbindT x y t) 
  where
    y = fresh_var g

{-@ reflect isWellFormed @-}
{-@ isWellFormed :: g:Env -> { t:Type| noDefnsInRefns g t } -> Bool  / [tsize t] @-}
isWellFormed :: Env -> Type -> Bool
isWellFormed g (TRefn b x p)     = checkType (BCons y (BTBase b) (erase_env g)) (unbind x y p) (BTBase TBool)
  where
    y = fresh_var g
isWellFormed g (TFunc x t_x t)   = isWellFormed g t_x && isWellFormed (Cons y t_x g) (unbindT x y t)
  where
    y = fresh_var g
isWellFormed g (TExists x t_x t) = isWellFormed g t_x && isWellFormed (Cons y t_x g) (unbindT x y t)
  where
    y = fresh_var g

{-@ reflect ty @-} -- Primitive Typing
{- @ ty :: c:Prim -> { t:Type | noDefnsInRefns Empty t && isWellFormed Empty t } @-}
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
ty Not      = TFunc 2 (TRefn TBool 5 (Bc True)) 
                  (TRefn TBool 3
                      (App (App (Prim Eqv) (BV 3)) 
                           (App (Prim Not) (BV 2)) ))
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
{-

{-@ reflect ty @-} -- Primitive Typing
{- @ ty :: c:Prim -> { t:Type | noDefnsInRefns Empty t && isWellFormed Empty t } @-}
ty :: Prim -> Type
ty And      = TFunc 1 (TRefn TBool 4 (Bc True)) 
                  (TFunc 2 (TRefn TBool 5 (Bc True)) 
                      (TRefn TBool 3 (refn_pred And)))
ty Or       = TFunc 1 (TRefn TBool 4 (Bc True)) 
                  (TFunc 2 (TRefn TBool 5 (Bc True)) 
                      (TRefn TBool 3  (refn_pred Or)))
ty Not      = TFunc 2 (TRefn TBool 5 (Bc True)) 
                  (TRefn TBool 3 (refn_pred Not))
ty Eqv      = TFunc 1 (TRefn TBool 4 (Bc True))
                  (TFunc 2 (TRefn TBool 5 (Bc True))  
                      (TRefn TBool 3 (refn_pred Eqv)))
ty Leq      = TFunc 1 (TRefn TInt 4 (Bc True)) 
                  (TFunc 2 (TRefn TInt 5 (Bc True)) 
                      (TRefn TBool 3 (refn_pred Leq)))
ty (Leqn n) = TFunc 2 (TRefn TInt 5 (Bc True)) 
                  (TRefn TBool 3 (refn_pred (Leqn n)))
ty Eq       = TFunc 1 (TRefn TInt 4 (Bc True)) 
                  (TFunc 2 (TRefn TInt 5 (Bc True)) 
                      (TRefn TBool 3 (refn_pred Eq)))
ty (Eqn n)  = TFunc 2 (TRefn TInt 5 (Bc True)) 
                  (TRefn TBool 3 (refn_pred (Eqn n)))

{-@ reflect isCmpn @-}
isCmpn :: Prim -> Bool
isCmpn (Leqn _) = True
isCmpn (Eqn _)  = True
isCmpn _        = False

{-@ reflect un1_refn_pred @-}
{-@ un1_refn_pred :: c:Prim 
     -> { p:Pred | un1_refn_pred c == unbind 1 1 (refn_pred c) } @-}
un1_refn_pred :: Prim -> Pred
un1_refn_pred And      = App (App (Prim Eqv) (BV 3)) 
                               (App (App (Prim And) (FV 1)) (BV 2)) 
un1_refn_pred Or       = App (App (Prim Eqv) (BV 3)) 
                               (App (App (Prim Or) (FV 1)) (BV 2)) 
un1_refn_pred Not      = App (App (Prim Eqv) (BV 3)) 
                               (App (Prim Not) (BV 2)) 
un1_refn_pred Eqv      = App (App (Prim Eqv) (BV 3))
                               (App (App (Prim Or) 
                                    (App (App (Prim And) (FV 1)) (BV 2)))
                                    (App (App (Prim And) (App (Prim Not) (FV 1)))
                                         (App (Prim Not) (BV 2))))
un1_refn_pred Leq      = App (App (Prim Eqv) (BV 3))
                               (App (App (Prim Leq) (FV 1)) (BV 2)) 
un1_refn_pred (Leqn n) = App (App (Prim Eqv) (BV 3))
                               (App (App (Prim Leq) (Ic n)) (BV 2)) 
un1_refn_pred Eq       = App (App (Prim Eqv) (BV 3))
                               (App (App (Prim Eq) (FV 1)) (BV 2))
un1_refn_pred (Eqn n)  = App (App (Prim Eqv) (BV 3))
                               (App (App (Prim Eq) (Ic n)) (BV 2))


{-@ reflect un21_refn_pred @-}
{-@ un21_refn_pred :: c:Prim 
     -> { p:Pred | un21_refn_pred c == unbind 2 2 (un1_refn_pred c) } @-}
un21_refn_pred :: Prim -> Pred
un21_refn_pred And      = App (App (Prim Eqv) (BV 3)) 
                               (App (App (Prim And) (FV 1)) (FV 2)) 
un21_refn_pred Or       = App (App (Prim Eqv) (BV 3)) 
                               (App (App (Prim Or) (FV 1)) (FV 2)) 
un21_refn_pred Not      = App (App (Prim Eqv) (BV 3)) 
                               (App (Prim Not) (FV 2)) 
un21_refn_pred Eqv      = App (App (Prim Eqv) (BV 3))
                               (App (App (Prim Or) 
                                    (App (App (Prim And) (FV 1)) (FV 2)))
                                    (App (App (Prim And) (App (Prim Not) (FV 1)))
                                         (App (Prim Not) (FV 2))))
un21_refn_pred Leq      = App (App (Prim Eqv) (BV 3))
                               (App (App (Prim Leq) (FV 1)) (FV 2)) 
un21_refn_pred (Leqn n) = App (App (Prim Eqv) (BV 3))
                               (App (App (Prim Leq) (Ic n)) (FV 2)) 
un21_refn_pred Eq       = App (App (Prim Eqv) (BV 3))
                               (App (App (Prim Eq) (FV 1)) (FV 2))
un21_refn_pred (Eqn n)  = App (App (Prim Eqv) (BV 3))
                               (App (App (Prim Eq) (Ic n)) (FV 2))
-}

-----------------------------------------------------------------------------
----- | JUDGEMENTS : WELL-FORMEDNESS of TYPES and ENVIRONMENTS
-----------------------------------------------------------------------------

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

{-@ measure wftypSize @-}
{-@ wftypSize :: WFType -> { v:Int | v >= 0 } @-}
wftypSize :: WFType -> Int
wftypSize (WFRefn g x b p y p_yg_p_bl)        = 1
wftypSize (WFFunc g x t_x p_g_tx t y p_yg_t)  = (wftypSize p_g_tx) + (wftypSize p_yg_t) + 1
wftypSize (WFExis g x t_x p_g_tx t y p_yg_t)  = (wftypSize p_g_tx) + (wftypSize p_yg_t) + 1

------------------------------------------------------------------------------------------
-- | AUTOMATING WELL-FORMEDNESS PROOF GENERATION for refinements that occur in practice --
------------------------------------------------------------------------------------------

{-@ makeWFType :: g:Env -> { t:Type | noDefnsInRefns g t && isWellFormed g t && Set_sub (free t) (binds g) }
                        -> ProofOf(WFType g t) / [tsize t] @-}
makeWFType :: Env -> Type -> WFType
makeWFType g (TRefn b x p)     = WFRefn g x b p y (makeHasBType (BCons y (BTBase b) (erase_env g))
                                        (unbind x y p) (BTBase TBool))
  where
    y = fresh_var g
makeWFType g (TFunc x t_x t)   = WFFunc g x t_x (makeWFType g t_x) t y
                                   (makeWFType (Cons y t_x g) (unbindT x y t))
  where
    y = fresh_var g
makeWFType g (TExists x t_x t) = WFExis g x t_x (makeWFType g t_x) t y
                                   (makeWFType (Cons y t_x g) (unbindT x y t))
  where
    y = fresh_var g

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

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------


-- Constant and Primitive Typing Lemmas
-- Lemma. Well-Formedness of Constant Types
{-@ lem_wf_tybc :: g:Env -> b:Bool -> ProofOf(WFType g (tybc b)) @-}
lem_wf_tybc :: Env -> Bool -> WFType
lem_wf_tybc g b = WFRefn g 1 TBool pred y pf_pr_bool
  where
     pred       = (App (App (Prim Eqv) (BV 1)) (Bc b)) 
     y          = (fresh_var g)
     g'         = (BCons y (BTBase TBool) (erase_env g))
     pf_eqv_v   = BTApp g' (Prim Eqv) (BTBase TBool) (BTFunc (BTBase TBool) (BTBase TBool)) 
                           (BTPrm g' Eqv) (FV y) (BTVar1 (erase_env g) y (BTBase TBool))
     -- pf_pr_bool :: ProofOf(HasBType g' pred (BTBase TBool)) @- }
     pf_pr_bool = BTApp g' (App (Prim Eqv) (FV y)) (BTBase TBool) (BTBase TBool) 
                           pf_eqv_v (Bc b) (BTBC g' b)

{-@ lem_wf_tyic :: g:Env -> n:Int -> ProofOf(WFType g (tyic n)) @-}
lem_wf_tyic :: Env -> Int -> WFType
lem_wf_tyic g n = WFRefn g 1 TInt pred y pf_pr_bool
  where
    pred        = (App (App (Prim Eq) (BV 1)) (Ic n))
    y           = fresh_var g
    g'          = (BCons y (BTBase TInt) (erase_env g))
    pf_eq_v     = BTApp g' (Prim Eq) (BTBase TInt) (BTFunc (BTBase TInt) (BTBase TBool)) 
                           (BTPrm g' Eq) (FV y) (BTVar1 (erase_env g) y (BTBase TInt))
    pf_pr_bool  = BTApp g' (App (Prim Eq) (FV y)) (BTBase TInt) (BTBase TBool) 
                           pf_eq_v (Ic n) (BTIC g' n)

{-
{-@ lem_ty_isWellFormed :: c:Prim -> { pf:_ | noDefnsInRefns Empty (ty c) && isWellFormed Empty (ty c) } @-}
lem_ty_isWellFormed :: Prim -> Proof
lem_ty_isWellFormed And      = ()
lem_ty_isWellFormed Or       = ()
lem_ty_isWellFormed Not      = ()
lem_ty_isWellFormed Eqv      = ()
lem_ty_isWellFormed Leq      = ()
lem_ty_isWellFormed (Leqn n) = ()
lem_ty_isWellFormed Eq       = ()
lem_ty_isWellFormed (Eqn n)  = ()


{-@ lem_wf_ty :: c:Prim -> ProofOf(WFType Empty (ty c)) @-}
lem_wf_ty :: Prim -> WFType
lem_wf_ty And      = makeWFType Empty (ty And) ? lem_ty_isWellFormed And 
lem_wf_ty Or       = makeWFType Empty (ty Or) ? lem_ty_isWellFormed Or
lem_wf_ty Not      = makeWFType Empty (ty Not) ? lem_ty_isWellFormed Not
lem_wf_ty Eqv      = makeWFType Empty (ty Eqv) ? lem_ty_isWellFormed Eqv
lem_wf_ty Leq      = makeWFType Empty (ty Leq) ? lem_ty_isWellFormed Leq
lem_wf_ty (Leqn n) = makeWFType Empty (ty (Leqn n)) ? lem_ty_isWellFormed (Leqn n)
lem_wf_ty Eq       = makeWFType Empty (ty Eq) ? lem_ty_isWellFormed Eq
lem_wf_ty (Eqn n)  = makeWFType Empty (ty (Eqn n)) ? lem_ty_isWellFormed (Eqn n)
-}

{-@ lem_wf_ty :: c:Prim -> ProofOf(WFType Empty (ty c)) @-}
lem_wf_ty :: Prim -> WFType
lem_wf_ty And      = makeWFType Empty (ty And) 
lem_wf_ty Or       = makeWFType Empty (ty Or) 
lem_wf_ty Not      = makeWFType Empty (ty Not) 
lem_wf_ty Eqv      = makeWFType Empty (ty Eqv) 
lem_wf_ty Leq      = makeWFType Empty (ty Leq) 
lem_wf_ty (Leqn n) = makeWFType Empty (ty (Leqn n)) 
lem_wf_ty Eq       = makeWFType Empty (ty Eq) 
lem_wf_ty (Eqn n)  = makeWFType Empty (ty (Eqn n))



{-@ lem_bool_values :: v:Value -> ProofOf(HasBType BEmpty v (BTBase TBool))
        -> { pf:_ | v == Bc True || v = Bc False } @-}
lem_bool_values :: Expr -> HasBType -> Proof
lem_bool_values v (BTBC _ _) = ()

{-@ reflect isInt @-}
isInt :: Expr -> Bool
isInt (Ic _ ) = True
isInt _       = False

{-@ lem_int_values :: v:Value -> ProofOf(HasBType BEmpty v (BTBase TInt))
        -> { pf:_ | isInt v } @-}
lem_int_values :: Expr -> HasBType -> Proof
lem_int_values v (BTIC _ _) = ()

{-@ reflect isLambda @-}
isLambda :: Expr -> Bool
isLambda (Lambda _ _ ) = True
isLambda _             = False

{-@ reflect isPrim @-}
isPrim :: Expr -> Bool
isPrim (Prim _) = True
isPrim _        = False

{-@ lemma_function_values :: v:Value -> t:BType -> t':BType
        -> ProofOf(HasBType BEmpty v (BTFunc t t'))
        -> { pf:_ | isLambda v || isPrim v } @-}
lemma_function_values :: Expr -> BType -> BType -> HasBType -> Proof
lemma_function_values e t t' (BTPrm {})   = ()     
lemma_function_values e t t' (BTAbs {})   = ()    

{-@ lem_delta_and_btyp :: v:Value -> t_x:BType -> t':BType
        -> ProofOf(HasBType BEmpty (Prim And) (BTFunc t_x t')) -> ProofOf(HasBType BEmpty v t_x)
        -> { pf:_ | propOf pf == HasBType BEmpty (delta And v) t' } @-} -- &&
lem_delta_and_btyp :: Expr -> BType -> BType -> HasBType -> HasBType -> HasBType
lem_delta_and_btyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (BTPrm BEmpty And) -> case v of
          (Bc True)  -> BTAbs BEmpty 1 (BTBase TBool) (BV 1) (BTBase TBool) 
                              1 (BTVar1 BEmpty 1 (BTBase TBool) ) -- ? toProof ( unbind 1 1 (BV 1) === FV 1 ))
          (Bc False) -> BTAbs BEmpty 1 (BTBase TBool) (Bc False) (BTBase TBool) 
                              1 (BTBC (BCons 1 (BTBase TBool) BEmpty) False)  
          _          -> impossible ("by lemma" ? lem_bool_values v p_v_tx) 


{-@ lem_delta_or_btyp :: v:Value -> t_x:BType -> t':BType
        -> ProofOf(HasBType BEmpty (Prim Or) (BTFunc t_x t')) -> ProofOf(HasBType BEmpty v t_x)
        -> { pf:_ | propOf pf == HasBType BEmpty (delta Or v) t' } @-} 
lem_delta_or_btyp :: Expr -> BType -> BType -> HasBType -> HasBType -> HasBType
lem_delta_or_btyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (BTPrm BEmpty Or) -> case v of
      (Bc True)  -> BTAbs BEmpty 1 (BTBase TBool) (Bc True) (BTBase TBool)
                          1 (BTBC (BCons 1 (BTBase TBool) BEmpty) True)
      (Bc False) -> BTAbs BEmpty 1 (BTBase TBool) (BV 1)    (BTBase TBool) 
                          1 (BTVar1 BEmpty 1 (BTBase TBool) ) -- ? toProof ( unbind 1 1 (BV 1) === FV 1 ))
      _          -> impossible ("by lemma" ? lem_bool_values v p_v_tx)


{-@ lem_delta_not_btyp :: v:Value -> t_x:BType -> t':BType
        -> ProofOf(HasBType BEmpty (Prim Not) (BTFunc t_x t')) -> ProofOf(HasBType BEmpty v t_x)
        -> { pf:_ | propOf pf == HasBType BEmpty (delta Not v) t' } @-} 
lem_delta_not_btyp :: Expr -> BType -> BType -> HasBType -> HasBType -> HasBType
lem_delta_not_btyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (BTPrm BEmpty Not) -> case v of
      (Bc True)  -> BTBC BEmpty False --    ? toProof ( t' === BTBase TBool )
      (Bc False) -> BTBC BEmpty True  --    ? toProof ( t' === BTBase TBool )
      _          -> impossible ("by lemma" ? lem_bool_values v p_v_tx)

{-@ lem_delta_eqv_btyp :: v:Value -> t_x:BType -> t':BType
        -> ProofOf(HasBType BEmpty (Prim Eqv) (BTFunc t_x t')) -> ProofOf(HasBType BEmpty v t_x)
        -> { pf:_ | propOf pf == HasBType BEmpty (delta Eqv v) t' } @-} -- &&
lem_delta_eqv_btyp :: Expr -> BType -> BType -> HasBType -> HasBType -> HasBType
lem_delta_eqv_btyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (BTPrm BEmpty Eqv) -> case v of
      (Bc True)  -> BTAbs BEmpty 1 (BTBase TBool) (BV 1) (BTBase TBool)
                          1 (BTVar1 BEmpty 1 (BTBase TBool) ) -- ? toProof ( unbind 1 1 (BV 1) === FV 1 ))
      (Bc False) -> BTAbs BEmpty 1 (BTBase TBool) not_x  (BTBase TBool) 1 p_notx_bl
        where
          not_x     = App (Prim Not) (BV 1)
          g         = (BCons 1 (BTBase TBool) BEmpty)
          p_notx_bl = BTApp g (Prim Not) (BTBase TBool) (BTBase TBool)
                            (BTPrm g Not) (FV 1) (BTVar1 BEmpty 1 (BTBase TBool))
      _          -> impossible ("by lemma" ? lem_bool_values v p_v_tx)

{-@ lem_delta_leq_btyp :: v:Value -> t_x:BType -> t':BType
        -> ProofOf(HasBType BEmpty (Prim Leq) (BTFunc t_x t')) -> ProofOf(HasBType BEmpty v t_x)
        -> { pf:_ | propOf pf == HasBType BEmpty (delta Leq v) t' } @-} 
lem_delta_leq_btyp :: Expr -> BType -> BType -> HasBType -> HasBType -> HasBType
lem_delta_leq_btyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (BTPrm BEmpty Leq) -> case v of
      (Ic n) -> BTPrm BEmpty (Leqn n) --   ? toProof ( t' === (BTFunc (BTBase TInt) (BTBase TBool)) )
      _      -> impossible ("by lemma" ? lem_int_values v p_v_tx)

{-@ lem_delta_leqn_btyp :: n:Int -> v:Value -> t_x:BType -> t':BType
        -> ProofOf(HasBType BEmpty (Prim (Leqn n)) (BTFunc t_x t')) -> ProofOf(HasBType BEmpty v t_x)
        -> { pf:_ | propOf pf == HasBType BEmpty (delta (Leqn n) v) t' } @-} 
lem_delta_leqn_btyp :: Int -> Expr -> BType -> BType -> HasBType -> HasBType -> HasBType
lem_delta_leqn_btyp n v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (BTPrm BEmpty (Leqn _n)) -> case v of
      (Ic m) -> BTBC BEmpty ( n <= m ) --    ? toProof ( t' === BTBase TBool)
      _      -> impossible ("by lemma" ? lem_int_values v p_v_tx)

{-@ lem_delta_eq_btyp :: v:Value -> t_x:BType -> t':BType
        -> ProofOf(HasBType BEmpty (Prim Eq) (BTFunc t_x t')) -> ProofOf(HasBType BEmpty v t_x)
        -> { pf:_ | propOf pf == HasBType BEmpty (delta Eq v) t' } @-} -- &&
lem_delta_eq_btyp :: Expr -> BType -> BType -> HasBType -> HasBType -> HasBType
lem_delta_eq_btyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (BTPrm BEmpty Eq) -> case v of
      (Ic n) -> BTPrm BEmpty (Eqn n) --    ? toProof ( t' === (BTFunc (BTBase TInt) (BTBase TBool)) )
      _      -> impossible ("by lemma" ? lem_int_values v p_v_tx)

{-@ lem_delta_eqn_btyp :: n:Int -> v:Value -> t_x:BType -> t':BType
        -> ProofOf(HasBType BEmpty (Prim (Eqn n)) (BTFunc t_x t')) -> ProofOf(HasBType BEmpty v t_x)
        -> { pf:_ | propOf pf == HasBType BEmpty (delta (Eqn n) v) t' } @-} -- &&
lem_delta_eqn_btyp :: Int -> Expr -> BType -> BType -> HasBType -> HasBType -> HasBType
lem_delta_eqn_btyp n v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (BTPrm BEmpty (Eqn _n)) -> case v of
      (Ic m) -> BTBC BEmpty ( n == m ) --    ? toProof ( t' === BTBase TBool)
      _      -> impossible ("by lemma" ? lem_int_values v p_v_tx)

{-@ lem_delta_btyp :: c:Prim -> v:Value -> t_x:BType -> t':BType
        -> ProofOf(HasBType BEmpty (Prim c) (BTFunc t_x t')) -> ProofOf(HasBType BEmpty v t_x)
        -> { pf:_ | propOf pf == HasBType BEmpty (delta c v) t' } @-} -- &&
--                    not ((delta c v) == Crash) } @- }
lem_delta_btyp :: Prim -> Expr -> BType -> BType -> HasBType -> HasBType -> HasBType
lem_delta_btyp And      v t_x t' p_c_txt' p_v_tx = lem_delta_and_btyp    v t_x t' p_c_txt' p_v_tx
lem_delta_btyp Or       v t_x t' p_c_txt' p_v_tx = lem_delta_or_btyp     v t_x t' p_c_txt' p_v_tx
lem_delta_btyp Not      v t_x t' p_c_txt' p_v_tx = lem_delta_not_btyp    v t_x t' p_c_txt' p_v_tx
lem_delta_btyp Eqv      v t_x t' p_c_txt' p_v_tx = lem_delta_eqv_btyp    v t_x t' p_c_txt' p_v_tx
lem_delta_btyp Leq      v t_x t' p_c_txt' p_v_tx = lem_delta_leq_btyp    v t_x t' p_c_txt' p_v_tx
lem_delta_btyp (Leqn n) v t_x t' p_c_txt' p_v_tx = lem_delta_leqn_btyp n v t_x t' p_c_txt' p_v_tx
lem_delta_btyp Eq       v t_x t' p_c_txt' p_v_tx = lem_delta_eq_btyp     v t_x t' p_c_txt' p_v_tx
lem_delta_btyp (Eqn n)  v t_x t' p_c_txt' p_v_tx = lem_delta_eqn_btyp  n v t_x t' p_c_txt' p_v_tx

