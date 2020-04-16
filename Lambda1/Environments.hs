{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-}
{- @ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Environments where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Syntax

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

{-@ lem_union_subset :: a:S.Set Vname -> b:S.Set Vname 
        -> { c:S.Set Vname | Set_sub a c && Set_sub b c }
        -> { pf:_ | Set_sub (Set_cup a b) c } @-}
lem_union_subset :: S.Set Vname -> S.Set Vname -> S.Set Vname -> Proof
lem_union_subset a b c = ()

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


