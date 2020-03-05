{-# LANGUAGE GADTs #-}

--{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Lambda1 where

import Control.Exception (assert)
import Prelude hiding (max, foldr)
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
{-
{-@ reflect foldr @-}
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f i []     = i
foldr f i (x:xs) = f x (foldr f i xs)
-}

--TODO: will classes and instances make anything easier or harder?
--class HasVars a where
--    free  :: a -> S.Set Vname
--    subst :: Vname -> 

---------------------------------------------------------------------------
----- | TERMS of our language
---------------------------------------------------------------------------
  ---   Term level expressions 
{- @ type Vname =  n:Int  @-} -- > 0 or not?
type Vname = String

data Prim = And | Or | Not | Eqv
          | Leq | Leqn Int 
          | Eq  | Eqn Int
  deriving (Eq, Show)

data Expr = Bc Bool              -- True, False
          | Ic Int               -- 0, 1, 2, ...
          | Prim Prim            -- built-in primitive functions 
          | V Vname              -- (V 1) etc
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
esize (V _)             = 0
esize (Lambda x e)      = (esize e) + 1
esize (App e e')        = (esize e) + (esize e') + 1
esize (Let x e_x e)     = (esize e_x) + (esize e) + 1
esize (Annot e t)       = (esize e) + 1
esize Crash             = 0

{-@ inline isValue @-}
isValue :: Expr -> Bool
isValue (Bc _)       = True
isValue (Ic _)       = True
isValue (Prim _)     = True
isValue (V _)        = True
isValue (Lambda _ _) = True
isValue Crash        = True
isValue _            = False
{-
{-@ inline isBc @-}
isBc :: Expr -> Bool
isBc (Bc _) = True
isBc _      = False

{-@ inline isIc @-}
isIc :: Expr -> Bool
isIc (Ic _) = True
isIc _      = False
-}
{-@ reflect subst @-} -- TODO: should v be a value only?
{-@ subst :: Vname -> v:Expr -> e:Expr -> e':Expr @-} -- @-}
subst :: Vname -> Expr -> Expr -> Expr
subst x e_x (Bc b)                    = Bc b
subst x e_x (Ic n)                    = Ic n
subst x e_x (Prim p)                  = Prim p
subst x e_x (V y) | x == y            = e_x
                  | otherwise         = V y
subst x e_x (Lambda y e) | x == y     = Lambda y e -- not the same x anymore
                         | otherwise  = Lambda y (subst x e_x e)
subst x e_x (App e e')                = App (subst x e_x e) (subst x e_x e')
subst x e_x (Let y e1 e2) | x == y    = Let y e1 e2 -- not the same x anymore
                          | otherwise = Let y (subst x e_x e1) (subst x e_x e2)
subst x e_x (Annot e t)               = Annot (subst x e_x e) t
subst x e_x Crash                     = Crash
{-
{-@ reflect subv @-} 
{-@ subv :: Vname -> Vname -> e:Expr -> { e':Expr | esize e == esize e' } @-}
subv :: Vname -> Vname -> Expr -> Expr
subv x x' (Bc b)                    = Bc b
subv x x' (Ic n)                    = Ic n
subv x x' (Prim p)                  = Prim p
subv x x' (V y) | x == y            = V x'
                | otherwise         = V y
subv x x' (Lambda y e) | x == y     = Lambda y e -- shouldn't happen
                       | otherwise  = Lambda y (subv x x' e)
subv x x' (App e e')                = App (subv x x' e) (subv x x' e')
subv x x' (Let y e1 e2) | x == y    = Let y e1 e2 -- shouldn't happen
                        | otherwise = Let y (subv x x' e1) (subv x x' e2)
subv x x' (Annot e t)               = Annot (subv x x' e) t
subv x x' Crash                     = Crash
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

{-@ reflect fv @-}
fv :: Expr -> S.Set Vname
fv (Bc _)       = S.empty
fv (Ic _)       = S.empty
fv (Prim _)     = S.empty
fv (V x)        = S.singleton x
fv (Lambda x e) = S.difference (fv e) (S.singleton x)
fv (App e e')   = S.union (fv e) (fv e')
fv (Let x ex e) = S.union (fv ex) (S.difference (fv e) (S.singleton x))
fv (Annot e t)  = fv e
fv (Crash)      = S.empty

{-
{-@ reflect bv @-}
bv :: Expr -> S.Set Vname
bv (Bc _)       = S.empty
bv (Ic _)       = S.empty
bv (Prim _)     = S.empty
bv (V x)        = S.empty
bv (Lambda x e) = S.union (bv e) (S.singleton x)
bv (App e e')   = S.union (bv e) (bv e')
bv (Let x ex e) = S.union (S.singleton x) (S.union (bv ex) (bv e))
bv (Annot e t)  = (bv e)  -- S.union (bv e) (bound t) -- TODO TODO which should it be?
bv Crash        = S.empty
-}
  ---   TYPES

data Base = TBool
          | TInt
  deriving (Eq, Show)

data Type = {-TBase   Base                 -- b
        |-} TRefn   Base Vname Pred      -- b{x : p}
          | TFunc   Vname Type Type      -- x:t_x -> t
          | TExists Vname Type Type      -- \exists x:t_x.t
  deriving (Eq, Show)

data Env = Empty                         -- type Env = [(Vname, Type)]	
         | Cons Vname Type Env
  deriving (Show)
{- @ data Env where 
    Empty :: Env
  | Cons  :: Vname -> Type -> Env -> Env @-} -- @-}
{-                     -> { g':Env | (binds g') == (Set_cup (binds g) (Set_sng x)) 
                                   && not (in_env x g) } @-}

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
{-
{-@ reflect bindList @-}
bindList :: Env -> [Vname]
bindList Empty        = []
bindList (Cons x t g) = x:(bindList g) 

{-@ lem_binds_bindList :: g:Env -> {pf:_ | binds g == fromList (bindList g) } @-}
lem_binds_bindList :: Env -> Proof
lem_binds_bindList Empty        = () 
lem_binds_bindList (Cons x t g) = () ? lem_binds_bindList g
-}
{-@ reflect in_env @-}
in_env :: Vname -> Env -> Bool
in_env x g = S.member x (binds g) 

{-@ reflect concatE @-}
{- @ concatE :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
                     -> { h:Env | (binds h) == (Set_cup (binds g) (binds g')) } @-}
concatE :: Env -> Env -> Env
concatE g Empty         = g
concatE g (Cons x t g') = Cons x t (concatE g g')
{-
{-@ lem_bound_concat :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
    ->  x:Vname  -> t:Type
    -> { pf:_ | (bound_in x t (concatE g g')) <=> ((bound_in x t g) || (bound_in x t g'))} @-}
lem_bound_concat :: Env -> Env -> Vname -> Type -> Proof
lem_bound_concat g Empty         x t = ()
lem_bound_concat g (Cons y s g') x t = () ? lem_bound_concat g g' x t

{-@ lem_in_env_concat :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
    ->  x:Vname -> {pf:_ | (in_env x (concatE g g')) <=> ((in_env x g) || (in_env x g'))} @-}
lem_in_env_concat :: Env -> Env -> Vname -> Proof
lem_in_env_concat g Empty         x = ()
lem_in_env_concat g (Cons y s g') x = () ? lem_in_env_concat g g' x 
-}

-- do we really want a separate Bare Type datatype?
data BType = BTBase Base                 -- b
           | BTFunc BType BType          -- t -> t'
  deriving (Eq, Show)

data BEnv = BEmpty                       -- type BEnv = [(Vname, BType)]
          | BCons Vname BType BEnv
  deriving (Show) 
{- @ data BEnv where
    BEmpty :: BEnv
  | BCons  :: x:Vname -> t:BType -> g:BEnv ->  g':BEnv  @-} 

{-@ reflect bound_inB @-}
bound_inB :: Vname -> BType -> BEnv -> Bool
bound_inB x t BEmpty                                 = False
bound_inB x t (BCons y t' g) | (x == y)              = (t == t')
                             | otherwise             = bound_inB x t g

{-{-@ reflect lookup_inB @-}
lookup_inB :: Vname -> BEnv -> Maybe BType
lookup_inB x BEmpty                    = Nothing
lookup_inB x (BCons y t g) | x == y    = Just t
                           | otherwise = lookup_inB x g -}

{-@ reflect bindsB @-}
bindsB :: BEnv -> S.Set Vname
bindsB BEmpty        = S.empty
bindsB (BCons x t g) = S.union (S.singleton x) (bindsB g)
{-
{-@ reflect bindListB @-}
bindListB :: BEnv -> [Vname]
bindListB BEmpty        = []
bindListB (BCons x t g) = x:(bindListB g) 
-}
{-@ reflect in_envB @-}
in_envB :: Vname -> BEnv -> Bool
in_envB x g = S.member x (bindsB g) 

{-@ reflect concatB @-}
{-@ concatB :: g:BEnv -> g':BEnv 
                      -> { h:BEnv | bindsB h == Set_cup (bindsB g) (bindsB g') } @-}
concatB :: BEnv -> BEnv -> BEnv
concatB g BEmpty         = g
concatB g (BCons x t g') = BCons x t (concatB g g')
{-
{-@ lem_bound_concatB :: g:BEnv -> g':BEnv -> x:Vname -> t:BType
  -> { pf:_ | (bound_inB x t (concatB g g')) <=> ((bound_inB x t g) || (bound_inB x t g')) } @-}
lem_bound_concatB :: BEnv -> BEnv -> Vname -> BType -> Proof
lem_bound_concatB g BEmpty         x t = ()
lem_bound_concatB g (BCons y s g') x t = () ? lem_bound_concatB g g' x t
-}

{-
{-@ lem_bound_consB :: g:BEnv -> x:Vname -> t:BType -> y:Vname 
  -> { s:BType | bound_inB y s g} -> { pf:_ | bound_inB y s (BCons x t g) } @-}
lem_bound_consB :: BEnv -> Vname -> BType -> Vname -> BType -> Proof
lem_bound_consB g x t y s = bound_inB y s (BCons x t g)
                        === (((x == y) && (t == s)) || (bound_inB y s g))
                        === True *** QED 
-}                        

{-@ reflect erase @-}
erase :: Type -> BType
--erase (TBase b)         = BTBase b
erase (TRefn b v r)     = BTBase b
erase (TFunc x t_x t)   = BTFunc (erase t_x) (erase t)
erase (TExists x t_x t) = (erase t)

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
{-
{-@ lem_in_env_erase :: g:Env -> x:Vname 
           -> { pf:_ | in_env x g <=> in_envB x (erase_env g) } @-}
lem_in_env_erase :: Env -> Vname -> Proof
lem_in_env_erase Empty        x = ()
lem_in_env_erase (Cons y s g) x = () ? lem_in_env_erase g x

{-@ lem_erase_cons :: g:Env -> { x:Vname | not (in_env x g) } -> t:Type
           -> { pf:_ | erase_env (Cons x t g) == BCons x (erase t) (erase_env g) } @-}
lem_erase_cons :: Env -> Vname -> Type -> Proof
lem_erase_cons g x t = ()
-}
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

{-@ reflect free @-} -- TODO: verify this
free :: Type -> S.Set Vname
--free (TBase b)          = S.empty
free (TRefn b v r)      = S.difference (fv r) (S.singleton v)
free (TFunc x t_x t)    = S.union (free t_x) (S.difference (free t) (S.singleton x))
free (TExists x t_x t)  = S.union (free t_x) (S.difference (free t) (S.singleton x))
{-
{-@ reflect bound @-} -- TODO: delete me
bound :: Type -> S.Set Vname
bound (TRefn b x r)     = S.union (S.singleton x) (bv r)
bound (TFunc x t_x t)   = S.union (S.singleton x) (S.union (bound t_x) (bound t))
bound (TExists x t_x t) = S.union (S.singleton x) (S.union (bound t_x) (bound t))

{-@ reflect bvt @-}
bvt :: Type -> S.Set Vname
bvt (TRefn b x r)     = S.union (S.singleton x) (bv r)
bvt (TFunc x t_x t)   = S.union (S.singleton x) (S.union (bvt t_x) (bvt t))
bvt (TExists x t_x t) = S.union (S.singleton x) (S.union (bvt t_x) (bvt t))
-}

-- TODO: doublecheck that this is capture avoiding
{-@ reflect tsubst @-}
{-@ tsubst :: Vname -> Expr -> t:Type  
                    -> { t':Type | tlen t' <= tlen t && tlen t' >= 0 } @-}
tsubst :: Vname -> Expr -> Type -> Type
--tsubst x _   (TBase b)         = TBase b
tsubst x e_x (TRefn b v r)     = TRefn b v (subst x e_x r)
tsubst x e_x (TFunc z t_z t)   
  | x == z                     = TFunc z t_z t
  | otherwise                  = TFunc z (tsubst x e_x t_z) (tsubst x e_x t)
tsubst x e_x (TExists z t_z t) 
  | x == z                     = TExists z t_z t
  | otherwise                  = TExists z (tsubst x e_x t_z) (tsubst x e_x t)

{-
{-@ reflect tsubv @-}
{-@ tsubv :: Vname -> Vname -> t:Type  
                    -> { t':Type | tsize t' == tsize t } @-}
tsubv :: Vname -> Vname -> Type -> Type
tsubv x x' (TRefn b v r)     = TRefn b v (subv x x' r)
tsubv x x' (TFunc z t_z t)   
  | x == z                   = TFunc z t_z t
  | otherwise                = TFunc z (tsubv x x' t_z) (tsubv x x' t)
tsubv x x' (TExists z t_z t) 
  | x == z                   = TExists z t_z t
  | otherwise                = TExists z (tsubv x x' t_z) (tsubv x x' t)
-}

----- OPERATIONAL SEMANTICS (Small Step)

{-@ reflect delta @-}
{-@ delta :: p:Prim -> { e:Expr | isValue e } ->  e':Expr @-}
delta :: Prim -> Expr -> Expr
delta And (Bc True)   = Lambda "y" (V "y")
delta And (Bc False)  = Lambda "y" (Bc False)
delta Or  (Bc True)   = Lambda "y" (Bc True)
delta Or  (Bc False)  = Lambda "y" (V "y")
delta Not (Bc True)   = Bc False
delta Not (Bc False)  = Bc True
delta Eqv (Bc True)   = Lambda "y" (V "y")
delta Eqv (Bc False)  = Lambda "y" (App (Prim Not) (V "y"))
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
--       Do I want to use contexts instead? E-Ctx ?? does this replace App1/Let1

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
                 -> ProofOf( Step (App (Lambda x e) v) (subst x v e))
 |  ELet  :: e_x:Expr -> e_x':Expr -> ProofOf( Step e_x e_x' )
                 -> x:Vname -> e:Expr -> ProofOf( Step (Let x e_x e) (Let x e_x' e))
 |  ELetV :: x:Vname -> { v:Expr | isValue v } -> e:Expr
                 -> ProofOf( Step (Let x v e) (subst x v e))
 |  EAnn  :: e:Expr -> e':Expr -> ProofOf( Step e e' )
                 -> t:Type -> ProofOf(Step (Annot e t) (Annot e' t))
 |  EAnnV :: { v:Expr | isValue v } -> t:Type -> ProofOf( Step (Annot v t) v) @-}
{-
{-@ inline isEPrim @-}
isEPrim :: Step -> Bool
isEPrim (EPrim {}) = True
isEPrim _          = False
-}
data EvalsToP where
    EvalsTo :: Expr -> Expr -> EvalsToP

data EvalsTo where
    Refl     :: Expr -> EvalsTo
    AddStep  :: Expr -> Expr -> Step -> Expr -> EvalsTo -> EvalsTo
{-@ data EvalsTo where 
    Refl     :: e:Expr -> ProofOf ( EvalsTo e e )
 |  AddStep  :: e1:Expr -> e2:Expr -> ProofOf( Step e1 e2 ) -> e3:Expr
               -> ProofOf ( EvalsTo e2 e3 ) -> ProofOf( EvalsTo e1 e3 ) @-} -- @-} 
{-  
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
-}
----- the Bare-Typing Relation and the Typing Relation

data HasBTypeP where
    HasBType :: BEnv -> Expr -> BType -> HasBTypeP 

data HasBType where
    BTBC   :: BEnv -> Bool -> HasBType
    BTIC   :: BEnv -> Int -> HasBType
    BTVar1 :: BEnv -> Vname -> BType -> HasBType 
    BTVar2 :: BEnv -> Vname -> BType -> HasBType -> Vname -> BType -> HasBType
    BTPrm  :: BEnv -> Prim -> HasBType
    BTAbs  :: BEnv -> Vname -> BType -> Expr -> BType -> HasBType -> HasBType
    BTApp  :: BEnv -> Expr -> BType -> BType -> HasBType 
              -> Expr -> HasBType -> HasBType
    BTLet  :: BEnv -> Expr -> BType -> HasBType -> Vname -> Expr
              -> BType -> HasBType -> HasBType
    BTAnn  :: BEnv -> Expr -> BType -> Type -> HasBType -> HasBType

{-@ data HasBType where
    BTBC   :: g:BEnv -> b:Bool -> ProofOf(HasBType g (Bc b) (BTBase TBool))
 |  BTIC   :: g:BEnv -> n:Int -> ProofOf(HasBType g (Ic n) (BTBase TInt))
 |  BTVar1 :: g:BEnv -> x:Vname -> b:BType -> ProofOf(HasBType (BCons x b g) (V x) b)
 |  BTVar2 :: g:BEnv -> x:Vname -> b:BType -> ProofOf(HasBType g (V x) b)
                -> {y:Vname | (y != x)} -> b':BType 
                -> ProofOf(HasBType (BCons y b' g) (V x) b)
 |  BTPrm  :: g:BEnv -> c:Prim  -> ProofOf(HasBType g (Prim c) (erase (ty c)))
 |  BTAbs  :: g:BEnv -> x:Vname -> b:BType -> e:Expr -> b':BType
                -> ProofOf(HasBType (BCons x b g) e b')
                -> ProofOf(HasBType g (Lambda x e) (BTFunc b b'))
 |  BTApp  :: g:BEnv -> e:Expr -> b:BType -> b':BType
                -> ProofOf(HasBType g e (BTFunc b b')) 
                -> e':Expr -> ProofOf(HasBType g e' b) 
                -> ProofOf(HasBType g (App e e') b')
 |  BTLet  :: g:BEnv -> e_x:Expr -> b:BType -> ProofOf(HasBType g e_x b)
                -> x:Vname -> e:Expr -> b':BType 
                -> ProofOf(HasBType (BCons x b g) e b')
                -> ProofOf(HasBType g (Let x e_x e) b')
 |  BTAnn  :: g:BEnv -> e:Expr -> b:BType -> { t:Type | erase(t) == b }
                -> ProofOf(HasBType g e b)-> ProofOf(HasBType g (Annot e t) b)  @-} 

-- TODO: refactor without impossible
{-@ simpleBTVar :: g:BEnv -> x:Vname -> { t:BType | bound_inB x t g } 
                -> ProofOf(HasBType g (V x) t) @-}
simpleBTVar :: BEnv -> Vname -> BType -> HasBType
simpleBTVar BEmpty        x t = impossible "Clearly"
simpleBTVar (BCons y s g) x t 
    = case (x == y, t == s) of
        (True, True) -> BTVar1 g x t
        (True, _)    -> impossible "again"
        (False, _)   -> BTVar2 g x t (simpleBTVar g x t) y s

{-
{-@ assume lemma_soundness :: e:Expr -> e':Expr -> ProofOf(EvalsTo e e') -> b:BType
                   -> ProofOf(HasBType BEmpty e b) -> ProofOf(HasBType BEmpty e' b) @-}
lemma_soundness :: Expr -> Expr -> EvalsTo -> BType -> HasBType -> HasBType
lemma_soundness e e' p_ee' b p_eb = undefined
-}

data WFTypeP where
    WFType :: Env -> Type -> WFTypeP

data WFType where 
    --WFBase :: Env -> Base -> WFType
    WFRefn :: Env -> Vname -> Base -> Pred -> HasBType -> WFType
    WFFunc :: Env -> Vname -> Type -> WFType -> Type -> WFType -> WFType
    WFExis :: Env -> Vname -> Type -> WFType -> Type -> WFType -> WFType

{-@ data WFType where
    WFRefn :: g:Env -> x:Vname -> b:Base -> p:Pred 
               -> ProofOf(HasBType (BCons x (BTBase b) (erase_env g)) p (BTBase TBool)) 
               -> ProofOf(WFType g (TRefn b x p))
 |  WFFunc :: g:Env -> x:Vname -> t_x:Type 
               -> ProofOf(WFType g t_x) -> t:Type
               -> ProofOf(WFType (Cons x t_x g) t) -> ProofOf(WFType g (TFunc x t_x t))
 |  WFExis :: g:Env -> x:Vname -> t_x:Type 
               -> ProofOf(WFType g t_x) -> t:Type
               -> ProofOf(WFType (Cons x t_x g) t) -> ProofOf(WFType g (TExists x t_x t)) @-} 
-- @-} 
    -- WFBase :: g:Env -> b:Base -> ProofOf(WFType g (TBase b))
 
-- TODO: Well-formedness of Environments

data WFEnvP where
    WFEnv :: Env -> WFEnvP

data WFEnv where
    WFEEmpty :: WFEnv
    WFEBind  :: Env -> WFEnv -> Vname -> Type -> WFType -> WFEnv

{-@ data WFEnv where
    WFEEmpty :: ProofOf(WFEnv Empty)
 |  WFEBind  :: g:Env -> ProofOf(WFEnv g) -> x:Vname -> {t:Type | not (Set_mem x (free t))}
                      -> ProofOf(WFType g t) -> ProofOf(WFEnv (Cons x t g)) @-}

data HasTypeP where
    HasType :: Env -> Expr -> Type -> HasTypeP -- HasType G e t means G |- e : t

data HasType where -- TODO: Indicate in notes/latex where well-formedness used
    TBC   :: Env -> Bool -> HasType
    TIC   :: Env -> Int -> HasType
    TVar1 :: Env -> Vname -> Type -> HasType
    TVar2 :: Env -> Vname -> Type -> HasType -> Vname -> Type -> HasType
    TPrm  :: Env -> Prim -> HasType
    TAbs  :: Env -> Vname -> Type -> WFType -> Expr -> Type -> HasType -> HasType
    TApp  :: Env -> Expr -> Vname -> Type -> Type -> HasType 
              -> Expr -> HasType -> HasType
    TLet  :: Env -> Expr -> Type -> HasType -> Vname -> Expr
              -> Type -> WFType -> HasType -> HasType
    TAnn  :: Env -> Expr -> Type -> HasType -> HasType
    TSub  :: Env -> Expr -> Type -> HasType -> Type -> WFType -> Subtype -> HasType

--   TBC  :: g:Env -> b:Bool -> ProofOf(HasType g (Bc b) (TBase TBool))
--   TIC  :: g:Env -> n:Int -> ProofOf(HasType g (Ic n) (TBase TInt))
{-@ data HasType where
    TBC   :: g:Env -> b:Bool -> ProofOf(HasType g (Bc b) (tybc b))
 |  TIC   :: g:Env -> n:Int -> ProofOf(HasType g (Ic n) (tyic n))
 |  TVar1 :: g:Env -> x:Vname -> t:Type -> ProofOf(HasType (Cons x t g) (V x) t)
 |  TVar2 :: g:Env -> x:Vname -> t:Type -> ProofOf(HasType g (V x) t)
                -> { y:Vname | (y != x) && not (Set_mem y (free t)) } -> s:Type 
                -> ProofOf(HasType (Cons y s g) (V x) t)
 |  TPrm  :: g:Env -> c:Prim -> ProofOf(HasType g (Prim c) (ty c))
 |  TAbs  :: g:Env -> x:Vname -> { t_x:Type | not (Set_mem x (free t_x)) } 
                -> ProofOf(WFType g t_x) 
                -> e:Expr -> t:Type -> ProofOf(HasType (Cons x t_x g) e t)
                -> ProofOf(HasType g (Lambda x e) (TFunc x t_x t))
 |  TApp  :: g:Env -> e:Expr -> x:Vname -> t_x:Type -> t:Type
                -> ProofOf(HasType g e (TFunc x t_x t)) 
                -> e':Expr -> ProofOf(HasType g e' t_x) 
                -> ProofOf(HasType g (App e e') (TExists x t_x t))
 |  TLet  :: g:Env -> e_x:Expr -> t_x:Type -> ProofOf(HasType g e_x t_x)
                -> x:Vname -> e:Expr -> t:Type -> ProofOf(WFType g t)
                -> ProofOf(HasType (Cons x t_x g) e t)
                -> ProofOf(HasType g (Let x e_x e) t)
 |  TAnn  :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
                -> ProofOf(HasType g (Annot e t) t)
 |  TSub  :: g:Env -> e:Expr -> s:Type -> ProofOf(HasType g e s) -> t:Type 
                -> ProofOf(WFType g t) -> ProofOf(Subtype g s t) 
                -> ProofOf(HasType g e t) @-} -- @-}

{-
-- TODO: refactor without impossible
{-@ simpleTVar :: g:Env -> x:Vname -> { t:Type | bound_in x t g } 
                -> ProofOf(HasType g (V x) t) @-}
simpleTVar :: Env -> Vname -> Type -> HasType
simpleTVar Empty        x t = impossible "Clearly"
simpleTVar (Cons y s g) x t 
    = case (x == y, t == s) of
        (True, True) -> TVar1 g x t
        (True, _)    -> impossible "again"
        (False, _)   -> TVar2 g x t (simpleTVar g x t) y s
-}

{-@ reflect tybc @-} -- Refined Constant Typing
tybc :: Bool -> Type
tybc True  = TRefn TBool "v" (App (App (Prim Eqv) (V "v")) (Bc True))
tybc False = TRefn TBool "v" (App (App (Prim Eqv) (V "v")) (Bc False))

{-@ reflect tyic @-}
tyic :: Int -> Type
tyic n = TRefn TInt "v" (App (App (Prim Eq) (V "v")) (Ic n))

{-@ reflect refn_pred @-} -- Primitive Typing
refn_pred :: Prim -> Pred
refn_pred And      = App (App (Prim Eqv) (V "z")) 
                               (App (App (Prim And) (V "x")) (V "y")) 
refn_pred Or       = App (App (Prim Eqv) (V "z")) 
                               (App (App (Prim Or) (V "x")) (V "y")) 
refn_pred Not      = App (App (Prim Eqv) (V "z")) 
                           (App (Prim Not) (V "x")) 
refn_pred Eqv      = App (App (Prim Eqv) (V "z"))
                               (App (App (Prim Or) 
                                    (App (App (Prim And) (V "x")) (V "y")))
                                    (App (App (Prim And) (App (Prim Not) (V "x")))
                                         (App (Prim Not) (V "y"))))
refn_pred Leq      = App (App (Prim Eqv) (V "z"))
                               (App (App (Prim Leq) (V "x")) (V "y")) 
refn_pred (Leqn n) = App (App (Prim Eqv) (V "z"))
                           (App (App (Prim Leq) (Ic n)) (V "y")) 
refn_pred Eq       = App (App (Prim Eqv) (V "z"))
                               (App (App (Prim Eq) (V "x")) (V "y"))
refn_pred (Eqn n)  = App (App (Prim Eqv) (V "z"))
                           (App (App (Prim Eq) (Ic n)) (V "y"))

{-@ reflect ty @-} -- Primitive Typing
ty :: Prim -> Type
ty And      = TFunc "x" (TRefn TBool "x'" (Bc True)) 
                  (TFunc "y" (TRefn TBool "y'" (Bc True)) 
                      (TRefn TBool "z" 
                          (App (App (Prim Eqv) (V "z")) 
                               (App (App (Prim And) (V "x")) (V "y")) )))
ty Or       = TFunc "x" (TRefn TBool "x'" (Bc True)) 
                  (TFunc "y" (TRefn TBool "y'" (Bc True)) 
                      (TRefn TBool "z" 
                          (App (App (Prim Eqv) (V "z")) 
                               (App (App (Prim Or) (V "x")) (V "y")) )))
ty Not      = TFunc "x" (TRefn TBool "x'" (Bc True)) 
                  (TRefn TBool "z"
                      (App (App (Prim Eqv) (V "z")) 
                           (App (Prim Not) (V "x")) ))
ty Eqv      = TFunc "x" (TRefn TBool "x'" (Bc True))
                  (TFunc "y" (TRefn TBool "y'" (Bc True))  
                      (TRefn TBool "z"
                          (App (App (Prim Eqv) (V "z"))
                               (App (App (Prim Or) 
                                    (App (App (Prim And) (V "x")) (V "y")))
                                    (App (App (Prim And) (App (Prim Not) (V "x")))
                                         (App (Prim Not) (V "y")))))))
ty Leq      = TFunc "x" (TRefn TInt "x'" (Bc True)) 
                  (TFunc "y" (TRefn TInt "y'" (Bc True)) 
                      (TRefn TBool "z"
                          (App (App (Prim Eqv) (V "z"))
                               (App (App (Prim Leq) (V "x")) (V "y")) )))
ty (Leqn n) = TFunc "y" (TRefn TInt "y'" (Bc True)) 
                  (TRefn TBool "z"
                      (App (App (Prim Eqv) (V "z"))
                           (App (App (Prim Leq) (Ic n)) (V "y")) )) 
ty Eq       = TFunc "x" (TRefn TInt "x'" (Bc True)) 
                  (TFunc "y" (TRefn TInt "y'" (Bc True)) 
                      (TRefn TBool "z"
                          (App (App (Prim Eqv) (V "z"))
                               (App (App (Prim Eq) (V "x")) (V "y")) )))
ty (Eqn n)  = TFunc "y" (TRefn TInt "y'" (Bc True)) 
                  (TRefn TBool "z"
                      (App (App (Prim Eqv) (V "z"))
                           (App (App (Prim Eq) (Ic n)) (V "y")) ))

-- Constant and Primitive Typing Lemmas
-- Lemma. Well-Formedness of Primitive/Constant Types
{-@ lem_wf_tybc :: g:Env -> b:Bool -> ProofOf(WFType g (tybc b)) @-}
lem_wf_tybc :: Env -> Bool -> WFType
lem_wf_tybc g b = WFRefn g "v" TBool pred pf_pr_bool
  where
     pred       = (App (App (Prim Eqv) (V "v")) (Bc b)) 
     g'         = (BCons "v" (BTBase TBool) (erase_env g))
     pf_eqv_v   = BTApp g' (Prim Eqv) (BTBase TBool) (BTFunc (BTBase TBool) (BTBase TBool)) 
                           (BTPrm g' Eqv) (V "v") (BTVar1 (erase_env g) "v" (BTBase TBool))
     -- pf_pr_bool :: ProofOf(HasBType g' pred (BTBase TBool)) @- }
     pf_pr_bool = BTApp g' (App (Prim Eqv) (V "v")) (BTBase TBool) (BTBase TBool) 
                           pf_eqv_v (Bc b) (BTBC g' b)

{-@ lem_wf_tyic :: g:Env -> n:Int -> ProofOf(WFType g (tyic n)) @-}
lem_wf_tyic :: Env -> Int -> WFType
lem_wf_tyic g n = WFRefn g "v" TInt pred pf_pr_bool
  where
    pred        = (App (App (Prim Eq) (V "v")) (Ic n))
    g'          = (BCons "v" (BTBase TInt) (erase_env g))
    pf_eq_v     = BTApp g' (Prim Eq) (BTBase TInt) (BTFunc (BTBase TInt) (BTBase TBool)) 
                           (BTPrm g' Eq) (V "v") (BTVar1 (erase_env g) "v" (BTBase TInt))
    pf_pr_bool  = BTApp g' (App (Prim Eq) (V "v")) (BTBase TInt) (BTBase TBool) 
                           pf_eq_v (Ic n) (BTIC g' n)
{-
-- these are various helpers to show ty(c) always well-formed
{-@ pf_base_wf :: g:Env -> b:Base -> x:Vname 
                            -> ProofOf(WFType g (TRefn b x (Bc True))) @-}
pf_base_wf :: Env -> Base -> Vname -> WFType
pf_base_wf g b x = WFRefn g x b (Bc True) (BTBC (BCons x (BTBase b) (erase_env g)) True) 

{-@ pf_app_prim_wf :: g:BEnv -> c:Prim 
      -> {b:Base | erase (ty c) == (BTFunc (BTBase b) (BTFunc (BTBase b) (BTBase TBool)))}
      -> { v:Vname | bound_inB v (BTBase b) g }
      -> ProofOf(HasBType g (App (Prim c) (V v)) (BTFunc (BTBase b) (BTBase TBool))) @-}
pf_app_prim_wf :: BEnv -> Prim -> Base -> Vname -> HasBType
pf_app_prim_wf g c b v = BTApp g (Prim c) (BTBase b) (BTFunc (BTBase b) (BTBase TBool))
                           (BTPrm g c) (V v) (simpleBTVar g v (BTBase b))

{-@ pf_app_app_prim_wf :: g:BEnv -> c:Prim 
      -> { b:Base | erase (ty c) == BTFunc (BTBase b) (BTFunc (BTBase b) (BTBase TBool)) }
      -> { x:Vname | bound_inB x (BTBase b) g} -> { y:Vname | bound_inB y (BTBase b) g }
      -> ProofOf(HasBType g (App (App (Prim c) (V x)) (V y)) (BTBase TBool)) @-}
pf_app_app_prim_wf :: BEnv -> Prim -> Base -> Vname -> Vname -> HasBType
pf_app_app_prim_wf g c b x y = BTApp g (App (Prim c) (V x)) (BTBase b) (BTBase TBool)
                               (pf_app_prim_wf g c b x) (V y) (simpleBTVar g y (BTBase b)) 

{-@ lem_wf_ty :: g:Env -> c:Prim -> ProofOf(WFType g (ty c)) @-}
lem_wf_ty :: Env -> Prim -> WFType
lem_wf_ty g' And   = WFFunc g' "x" (TRefn TBool "x'" (Bc True)) (pf_base_wf g' TBool "x'")
                                      middle_type pf_middle_wf
  where
    g            = BCons "z" (BTBase TBool) (BCons "y" (BTBase TBool) 
                                            (BCons "x" (BTBase TBool) (erase_env g')))
    pf_eqv_v     = pf_app_prim_wf g Eqv TBool "z"
    pf_and_xy    = pf_app_app_prim_wf g And TBool "x" "y"
    pf_refn_and  = BTApp g (App (Prim Eqv) (V "z")) (BTBase TBool) (BTBase TBool) pf_eqv_v
                        (App (App (Prim And) (V "x")) (V "y")) pf_and_xy
    g1           = Cons "y" (TRefn TBool "y'" (Bc True))
                                            (Cons "x" (TRefn TBool "x'" (Bc True)) g')
    g2           = Cons "x" (TRefn TBool "x'" (Bc True)) g'
    inner_type   = TRefn TBool "z" (refn_pred And)
    pf_inner_wf  = WFRefn g1 "z" TBool (refn_pred And) pf_refn_and
    middle_type  = TFunc "y" (TRefn TBool "y'" (Bc True)) inner_type 
    pf_middle_wf = WFFunc g2 "y" (TRefn TBool "y'" (Bc True)) (pf_base_wf g2 TBool "y'")
                                 inner_type pf_inner_wf 
lem_wf_ty g' Or     = WFFunc g' "x" (TRefn TBool "x'" (Bc True)) (pf_base_wf g' TBool "x'")
                                      middle_type  pf_middle_wf
  where
    g            = BCons "z" (BTBase TBool) (BCons "y" (BTBase TBool) 
                                            (BCons "x" (BTBase TBool) (erase_env g')))
    pf_eqv_v     = pf_app_prim_wf g Eqv TBool "z"
    pf_or_xy     = pf_app_app_prim_wf g Or TBool "x" "y"
    pf_refn_or   = BTApp g (App (Prim Eqv) (V "z")) (BTBase TBool) (BTBase TBool) pf_eqv_v
                        (App (App (Prim Or) (V "x")) (V "y")) pf_or_xy
    g1           = Cons "y" (TRefn TBool "y'" (Bc True))
                                            (Cons "x" (TRefn TBool "x'" (Bc True)) g')
    g2           = Cons "x" (TRefn TBool "x'" (Bc True)) g'
    inner_type   = TRefn TBool "z" (refn_pred Or)
    pf_inner_wf  = WFRefn g1 "z" TBool (refn_pred Or) pf_refn_or
    middle_type  = TFunc "y" (TRefn TBool "y'" (Bc True)) inner_type 
    pf_middle_wf = WFFunc g2 "y" (TRefn TBool "y'" (Bc True)) (pf_base_wf g2 TBool "y'")
                                 inner_type pf_inner_wf 
lem_wf_ty g' Not    = WFFunc g' "x" (TRefn TBool "x'" (Bc True)) (pf_base_wf g' TBool "x'")
                                      inner_type pf_inner_wf
  where
    g            = BCons "z" (BTBase TBool) (BCons "x" (BTBase TBool) (erase_env g'))
    pf_eqv_v     = pf_app_prim_wf g Eqv TBool "z"
    pf_not_x     = BTApp g (Prim Not) (BTBase TBool) (BTBase TBool)
                           (BTPrm g Not) (V "x") (simpleBTVar g "x" (BTBase TBool))
    pf_refn_not  = BTApp g (App (Prim Eqv) (V "z")) (BTBase TBool) (BTBase TBool) pf_eqv_v
                        (App (Prim Not) (V "x")) pf_not_x
    g1           = Cons "x" (TRefn TBool "x'" (Bc True)) g'
    inner_type   = TRefn TBool "z" (refn_pred Not)
    pf_inner_wf  = WFRefn g1 "z" TBool (refn_pred Not) pf_refn_not
lem_wf_ty g' Eqv    = WFFunc g' "x" (TRefn TBool "x'" (Bc True)) (pf_base_wf g' TBool "x'")
                                      middle_type pf_middle_wf
  where
    g            = BCons "z" (BTBase TBool) (BCons "y" (BTBase TBool) 
                                            (BCons "x" (BTBase TBool) (erase_env g')))
    pf_eqv_v     = pf_app_prim_wf g Eqv TBool "z"
    pf_and_xy    = pf_app_app_prim_wf g And TBool "x" "y"
    pf_not_x     = BTApp g (Prim Not) (BTBase TBool) (BTBase TBool)
                           (BTPrm g Not) (V "x") (simpleBTVar g "x" (BTBase TBool))
    pf_not_y     = BTApp g (Prim Not) (BTBase TBool) (BTBase TBool)
                           (BTPrm g Not) (V "y") (simpleBTVar g "y" (BTBase TBool))
    pf_and_nx    = BTApp g (Prim And) (BTBase TBool) (BTFunc (BTBase TBool) (BTBase TBool))
                               (BTPrm g And) (App (Prim Not) (V "x")) pf_not_x
    pf_and_nxny  = BTApp g (App (Prim And) (App (Prim Not) (V "x"))) 
                               (BTBase TBool) (BTBase TBool) pf_and_nx
                               (App (Prim Not) (V "y")) pf_not_y
    pf_iff_xy1   = BTApp g (Prim Or) (BTBase TBool) (BTFunc (BTBase TBool) (BTBase TBool))
                               (BTPrm g Or) (App (App (Prim And) (V "x")) (V "y")) pf_and_xy 
    pf_iff_xy2   = BTApp g (App (Prim Or) (App (App (Prim And) (V "x")) (V "y")))
                               (BTBase TBool) (BTBase TBool) pf_iff_xy1
                               (App (App (Prim And) (App (Prim Not) (V "x")))
                                    (App (Prim Not) (V "y"))) pf_and_nxny
    pf_refn_eqv  = BTApp g (App (Prim Eqv) (V "z")) (BTBase TBool) (BTBase TBool) pf_eqv_v
                        (App (App (Prim Or) (App (App (Prim And) (V "x")) (V "y")))
                                            (App (App (Prim And) (App (Prim Not) (V "x")))
                                                 (App (Prim Not) (V "y")))) pf_iff_xy2
    g1           = Cons "y" (TRefn TBool "y'" (Bc True))
                                            (Cons "x" (TRefn TBool "x'" (Bc True)) g')
    g2           = Cons "x" (TRefn TBool "x'" (Bc True)) g'
    inner_type   = TRefn TBool "z" (refn_pred Eqv)
    pf_inner_wf  = WFRefn g1 "z" TBool (refn_pred Eqv) pf_refn_eqv
    middle_type  = TFunc "y" (TRefn TBool "y'" (Bc True)) inner_type 
    pf_middle_wf = WFFunc g2 "y" (TRefn TBool "y'" (Bc True)) (pf_base_wf g2 TBool "y'")
                                 inner_type pf_inner_wf 
lem_wf_ty g' Leq    = WFFunc g' "x" (TRefn TInt "x'" (Bc True)) (pf_base_wf g' TInt "x'")
                                      middle_type pf_middle_wf
  where
    g            = BCons "z" (BTBase TBool) (BCons "y" (BTBase TInt) 
                                            (BCons "x" (BTBase TInt) (erase_env g')))
    pf_eqv_v     = pf_app_prim_wf g Eqv TBool "z"
    pf_leq_xy    = pf_app_app_prim_wf g Leq TInt "x" "y"
    pf_refn_leq  = BTApp g (App (Prim Eqv) (V "z")) (BTBase TBool) (BTBase TBool) pf_eqv_v
                        (App (App (Prim Leq) (V "x")) (V "y")) pf_leq_xy
    g1           = Cons "y" (TRefn TInt "y'" (Bc True))
                                            (Cons "x" (TRefn TInt "x'" (Bc True)) g')
    g2           = Cons "x" (TRefn TInt "x'" (Bc True)) g'
    inner_type   = TRefn TBool "z" (refn_pred Leq)
    pf_inner_wf  = WFRefn g1 "z" TBool (refn_pred Leq) pf_refn_leq
    middle_type  = TFunc "y" (TRefn TInt "y'" (Bc True)) inner_type 
    pf_middle_wf = WFFunc g2 "y" (TRefn TInt "y'" (Bc True)) (pf_base_wf g2 TInt "y'")
                                 inner_type pf_inner_wf 
lem_wf_ty g' (Leqn n) = WFFunc g' "y" (TRefn TInt "y'" (Bc True)) (pf_base_wf g' TInt "y'")
                                      inner_type pf_inner_wf
  where
    g            = BCons "z" (BTBase TBool) (BCons "y" (BTBase TInt) (erase_env g'))
    pf_eqv_v     = pf_app_prim_wf g Eqv TBool "z"
    pf_leqn_n    = BTApp g (Prim Leq) (BTBase TInt) (BTFunc (BTBase TInt) (BTBase TBool))
                      (BTPrm g Leq) (Ic n) (BTIC g n)
    pf_leqn_ny   = BTApp g (App (Prim Leq) (Ic n)) (BTBase TInt) (BTBase TBool)
                      pf_leqn_n (V "y") (simpleBTVar g "y" (BTBase TInt))
    pf_refn_leqn = BTApp g (App (Prim Eqv) (V "z")) (BTBase TBool) (BTBase TBool) pf_eqv_v
                        (App (App (Prim Leq) (Ic n)) (V "y")) pf_leqn_ny
    g1           = Cons "y" (TRefn TInt "y'" (Bc True)) g'
    inner_type   = TRefn TBool "z" (refn_pred (Leqn n))
    pf_inner_wf  = WFRefn g1 "z" TBool (refn_pred (Leqn n)) pf_refn_leqn
lem_wf_ty g' Eq     = WFFunc g' "x" (TRefn TInt "x'" (Bc True)) (pf_base_wf g' TInt "x'")
                                      middle_type pf_middle_wf
  where
    g            = BCons "z" (BTBase TBool) (BCons "y" (BTBase TInt) 
                                            (BCons "x" (BTBase TInt) (erase_env g')))
    pf_eqv_v     = pf_app_prim_wf g Eqv TBool "z"
    pf_eq_xy     = pf_app_app_prim_wf g Eq TInt "x" "y"
    pf_refn_eq   = BTApp g (App (Prim Eqv) (V "z")) (BTBase TBool) (BTBase TBool) pf_eqv_v
                        (App (App (Prim Eq) (V "x")) (V "y")) pf_eq_xy
    g1           = Cons "y" (TRefn TInt "y'" (Bc True))
                                            (Cons "x" (TRefn TInt "x'" (Bc True)) g')
    g2           = Cons "x" (TRefn TInt "x'" (Bc True)) g'
    inner_type   = TRefn TBool "z" (refn_pred Eq)
    pf_inner_wf  = WFRefn g1 "z" TBool (refn_pred Eq) pf_refn_eq
    middle_type  = TFunc "y" (TRefn TInt "y'" (Bc True)) inner_type 
    pf_middle_wf = WFFunc g2 "y" (TRefn TInt "y'" (Bc True)) (pf_base_wf g2 TInt "y'")
                                 inner_type pf_inner_wf 
lem_wf_ty g' (Eqn n) = WFFunc g' "y" (TRefn TInt "y'" (Bc True)) (pf_base_wf g' TInt "y'")
                                      inner_type pf_inner_wf
  where
    g            = BCons "z" (BTBase TBool) (BCons "y" (BTBase TInt) (erase_env g'))
    pf_eqv_v     = pf_app_prim_wf g Eqv TBool "z"
    pf_eqn_n     = BTApp g (Prim Eq) (BTBase TInt) (BTFunc (BTBase TInt) (BTBase TBool))
                      (BTPrm g Eq) (Ic n) (BTIC g n)
    pf_eqn_ny    = BTApp g (App (Prim Eq) (Ic n)) (BTBase TInt) (BTBase TBool)
                      pf_eqn_n (V "y") (simpleBTVar g "y" (BTBase TInt))
    pf_refn_eqn  = BTApp g (App (Prim Eqv) (V "z")) (BTBase TBool) (BTBase TBool) pf_eqv_v
                        (App (App (Prim Eq) (Ic n)) (V "y")) pf_eqn_ny
    g1           = Cons "y" (TRefn TInt "y'" (Bc True)) g'
    inner_type   = TRefn TBool "z" (refn_pred (Eqn n))
    pf_inner_wf  = WFRefn g1 "z" TBool (refn_pred (Eqn n)) pf_refn_eqn
-}

data SubtypeP where
    Subtype :: Env -> Type -> Type -> SubtypeP

data Subtype where
    SBase :: Env -> Vname -> Base -> Pred -> Vname -> Pred -> Entails -> Subtype
    SFunc :: Env -> Vname -> Type -> Vname -> Type -> Subtype
               -> Type -> Type -> Subtype -> Subtype
    SWitn :: Env -> Expr -> Type -> HasType -> Type -> Vname -> Type
               -> Subtype -> Subtype
    SBind :: Env -> Vname -> Type -> Type -> Type -> Subtype -> Subtype

{-@ data Subtype where
    SBase :: g:Env -> v1:Vname -> b:Base -> p1:Pred -> v2:Vname -> p2:Pred 
               -> ProofOf(Entails ( Cons v1 (TRefn b v1 p1) g) (subst v2 (V v1) p2))
               -> ProofOf(Subtype g (TRefn b v1 p1) (TRefn b v2 p2))
 |  SFunc :: g:Env -> x1:Vname -> s1:Type -> { x2:Vname | not (in_env x2 g) } -> s2:Type
               -> ProofOf(Subtype g s2 s1) -> t1:Type -> t2:Type
               -> ProofOf(Subtype (Cons x2 s2 g) (tsubst x1 (V x2) t1) t2)
               -> ProofOf(Subtype g (TFunc x1 s1 t1) (TFunc x2 s2 t2))
 |  SWitn :: g:Env -> { e:Expr | isValue e } -> t_x:Type -> ProofOf(HasType g e t_x) 
               -> t:Type -> x:Vname -> t':Type -> ProofOf(Subtype g t (tsubst x e t'))
               -> ProofOf(Subtype g t (TExists x t_x t'))
 |  SBind :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type 
               -> t:Type -> {t':Type | not Set_mem x (free t')} 
               -> ProofOf(Subtype (Cons x t_x g) t t')
               -> ProofOf(Subtype g (TExists x t_x t) t')
@-}

{-
{-@ lem_simple_type_app :: g:Env -> e:Expr -> x:Vname -> t_x:Type -> t:Type
               -> ProofOf(HasType g e (TFunc x t_x t))
               -> e':Expr -> ProofOf(HasType g e t_x)
               -> { t':Type | not Set_mem x (free t') } -> ProofOf(WFType g t') 
               -> ProofOf(Subtype (Cons x t_x g) t t') 
               -> ProofOf(HasType g (App e e') t') @-}
lem_simple_type_app :: Env -> Expr -> Vname -> Type -> Type -> HasType
               -> Expr -> HasType -> Type -> WFType -> Subtype -> HasType
lem_simple_type_app g e x t_x t p_e_txt e' p_e'_tx t' p_g_t' p_t_t'
    = TSub g (App e e') (TExists x t_x t) p_ee'_txt t' p_g_t' p_t_t'
      where
        p_ee'_txt = TApp g e x t_x t p_e_txt e' p_e'_tx
-}
--data SMTValidP where --dummy SMT Validity certificates
--    SMTValid :: Form -> SMTValidP
--
--data SMTValid where
--    SMTProp :: Pred -> EvalsTo -> SMTValid
--{-@ data SMTValid where
--    SMTProp :: { p:Pred | fv p == S.empty } -> ProofOf(EvalsTo p (Bc True))
--               -> ProofOf(SMTValid (P p)) @-}
--    EntEmpP :: Pred -> EvalsTo -> Entails
--    EntEmpI :: Base -> Vname -> Pred -> Form  
--                -> (CSubst -> DenotesEnv -> Entails) -> Entails
--    EntEmpC :: Env -> Form -> Entails -> Form -> Entails -> Entails
--    EntEmpP :: p:Pred -> ProofOf(EvalsTo p (Bc True)) -> ProofOf(Entails Empty p)
-- |  EntEmpI :: b:Base -> x:Vname -> p:Pred -> c:Form 
--               -> (th:CSubst -> ProofOf(DenotesEnv (Cons x (TRefn b x p) Empty) th)
--                       -> ProofOf(Entails Empty (cfsubst th c)) )
--               -> ProofOf(Entails Empty (Impl x b p c))
-- |  EntEmpC :: g:Env -> c1:Form -> ProofOf(Entails g c1) -> c2: Form -> ProofOf(Entails g c2)
--               -> ProofOf(Entails g (FAnd c1 c2))

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
--    DBase :: Base -> Expr -> HasBType -> Denotes
    DRefn :: Base -> Vname -> Pred -> Expr -> HasBType -> EvalsTo -> Denotes
    DFunc :: Vname -> Type -> Type -> Expr -> HasBType
              -> (Expr -> Denotes -> (Expr, (EvalsTo, Denotes))) -> Denotes
    DExis :: Vname -> Type -> Type -> Expr -> HasBType
              -> Expr -> Denotes -> Denotes -> Denotes
{-@ data Denotes where
    DRefn :: b:Base -> x:Vname -> p:Pred -> { v:Expr | isValue v } 
              -> ProofOf(HasBType BEmpty v (BTBase b))
              -> ProofOf(EvalsTo (subst x v p) (Bc True)) 
              -> ProofOf(Denotes (TRefn b x p) v)
  | DFunc :: x:Vname -> t_x:Type -> t:Type -> { v:Expr | isValue v } 
              -> ProofOf(HasBType BEmpty v (erase (TFunc x t_x t)))
              -> ({ v_x:Expr | isValue v_x } -> ProofOf(Denotes t_x v_x)
                    -> (Expr, (EvalsTo, Denotes))
                       <{\v' pfs -> (isValue v') 
                                       && (propOf (fst pfs) == EvalsTo (App v v_x) v')
                                       && (propOf (snd pfs) == Denotes (tsubst x v_x t) v')}>)
              -> ProofOf(Denotes (TFunc x t_x t) v)
  | DExis :: x:Vname -> t_x:Type -> t:Type -> { v:Expr | isValue v }
              -> ProofOf(HasBType BEmpty v (erase t)) 
              -> { v_x:Expr | isValue v_x } -> ProofOf(Denotes t_x v_x)
              -> ProofOf(Denotes (tsubst x v_x t) v)
              -> ProofOf(Denotes (TExists x t_x t) v)  @-} 

    --DBase :: b:Base -> e:Expr -> ProofOf(HasBType BEmpty e (BTBase b)) 
    --          -> ProofOf(Denotes (TBase b) e)
-- TODO: Still need closing substitutions -- rethink this!
data CSubst = CEmpty
            | CCons Vname Expr CSubst
{-@ data CSubst  where
    CEmpty :: CSubst
  | CCons  :: x:Vname -> {v:Expr | isValue v} -> th:CSubst -> CSubst @-}

-- closing substitutions (i.e. th(x), th(e), th(t)) proceed from the top/right of
--   the typing env downwards/leftwards

{-@ reflect csubst_var @-}
csubst_var :: CSubst -> Vname -> Expr
csubst_var CEmpty            x             = (V x)
csubst_var (CCons y e binds) x | x == y    = e
                               | otherwise = csubst_var binds x

{-@ reflect remove @-}
--{-@ remove :: Vname -> th:CSubst -> { th':CSubst | len th' <= len th } @-}
remove :: Vname -> CSubst -> CSubst
remove x CEmpty                         = CEmpty
remove x (CCons y e binds) | x == y     = binds
                           | otherwise  = CCons y e (remove x binds)

{-@ reflect csubst @-}
csubst :: CSubst -> Expr -> Expr
csubst th               (Bc b)             = Bc b
csubst th               (Ic n)             = Ic n
csubst th               (Prim p)           = Prim p
csubst th               (V x)              = csubst_var th x
csubst th               (Lambda x e')      = Lambda x (csubst (remove x th) e')
csubst th               (App e e')         = App (csubst th e) (csubst th e')
csubst th               (Let y e1 e2)      = Let y (csubst th' e1) (csubst th' e2)
  where
    th' = remove y th
csubst th               (Annot e t)        = Annot (csubst th e) (ctsubst th t)
csubst th               Crash              = Crash

{-@ reflect ctsubst @-}
ctsubst :: CSubst -> Type -> Type
--ctsubst th t = foldr (\(x,e) t' -> tsubst x e t') t th 
ctsubst CEmpty         t = t
ctsubst (CCons x v th) t = ctsubst th (tsubst x v t)

-- TODO: Still need denotations of environments
data DenotesEnvP where 
    DenotesEnv :: Env -> CSubst -> DenotesEnvP 

data DenotesEnv where
    DEmp :: DenotesEnv
    DExt :: Env -> CSubst -> DenotesEnv -> Vname -> Type -> Expr 
               -> Denotes -> DenotesEnv
{-@ data DenotesEnv where 
    DEmp :: ProofOf(DenotesEnv Empty CEmpty)
 |  DExt :: g:Env -> th:CSubst -> ProofOf(DenotesEnv g th) 
               -> x:Vname -> t:Type -> { v:Expr | isValue v }
               -> ProofOf(Denotes (ctsubst th t) v)
               -> ProofOf(DenotesEnv (Cons x t g) (CCons x v th)) @-}
{-
    DEnv :: Env -> CSubst -> (Vname -> Type -> Denotes) -> DenotesEnv
    DEnv :: g:Env -> th:CSubst ->     
      (x:Vname -> {t:Type | bound_in x t g} 
               -> ProofOf(Denotes (ctsubst th t) (csubst th (V x))))
         -> ProofOf(DenotesEnv g th) 
-}
-- -- -- -- -- -- -- -- ---
-- Basic Facts and Lemmas -
-- -- -- -- -- -- -- -- ---

-- Determinism of the Operational Semantics
{-
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
-}
{-
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
-}

--                   e' (t' `withProof` lem_bound_concatB g g' y t_y) p_e'_t' x t_x) 
--                -> { x:Vname | not (Set_mem x (bindsB g')) } -> t_x:BType  
{-@ lem_weaken_btyp :: g:BEnv -> g':BEnv -> e:Expr -> t:BType 
                -> ProofOf(HasBType (concatB g g') e t) 
                -> { x:Vname | (Set_mem x (bindsB g')) || not (Set_mem x (fv e)) } 
                -> t_x:BType -> ProofOf(HasBType (concatB (BCons x t_x g) g') e t) @-}
lem_weaken_btyp :: BEnv -> BEnv -> Expr -> BType -> HasBType -> Vname -> BType -> HasBType
lem_weaken_btyp g g' e t (BTBC _g b)      x t_x = BTBC  (concatB (BCons x t_x g) g') b
lem_weaken_btyp g g' e t (BTIC _g n)      x t_x = BTIC  (concatB (BCons x t_x g) g') n
lem_weaken_btyp g g' e t p_y_ty@(BTVar1 _g y t_y) x t_x 
    = case g' of 
        (BEmpty)           -> BTVar2 g y t_y p_y_ty x t_x
        (BCons _y _ty g'') -> BTVar1 (concatB (BCons x t_x g) g'') y t_y 
--               `withProof` (lem_bound_concatB g g' y t_y)
--               `withProof` (lem_bound_concatB (BCons x t_x g) g' y t_y)
-- (g; g' == _g, z:t_z) |- y : t_y
lem_weaken_btyp g g' e t p_y_ty@(BTVar2 _g y t_y p_gg'_y_ty z t_z) x t_x
    = case g' of
        (BEmpty)           -> BTVar2 g y t_y p_y_ty x t_x
        (BCons _z _tz g'') -> BTVar2 (concatB (BCons x t_x g) g'') y t_y 
                                     (lem_weaken_btyp g g'' e t p_gg'_y_ty x t_x)
                                     z t_z
lem_weaken_btyp g g' e t (BTPrm _g c)     x t_x = BTPrm (concatB (BCons x t_x g) g') c
lem_weaken_btyp g g' e t (BTAbs _g y t_y e' t' p_e'_t') x t_x
    = BTAbs (concatB (BCons x t_x g) g') y t_y e' t' 
               (lem_weaken_btyp g (BCons y t_y g') e' t' p_e'_t' x t_x) 
--               (y `withProof` lem_binds_bv_distinctB (concatB g g') e t p_e_t) t_y e' t' 
--                   e' (t' `withProof` lem_bound_concatB g g' y t_y) p_e'_t' x t_x) 
lem_weaken_btyp g g' e t (BTApp _g e1 s s' p_e1_ss' e2 p_e2_s) x t_x 
    = BTApp (concatB (BCons x t_x g) g') e1 s s' 
               (lem_weaken_btyp g g' e1 (BTFunc s s') p_e1_ss' x t_x)
                e2 (lem_weaken_btyp g g' e2 s p_e2_s x t_x)
lem_weaken_btyp g g' e t p_e_t@(BTLet _g e_y t_y p_ey_ty y e' t' p_e'_t') x t_x
    = BTLet (concatB (BCons x t_x g) g') e_y t_y 
               (lem_weaken_btyp g g' e_y t_y p_ey_ty x t_x)
               y e' t' (lem_weaken_btyp g (BCons y t_y g') e' t' p_e'_t' x t_x)
--               (y `withProof` lem_binds_bv_distinctB (concatB g g') e t p_e_t)
lem_weaken_btyp g g' e bt (BTAnn _g e' _bt t p_e'_bt) x t_x
    = BTAnn (concatB (BCons x t_x g) g') e' bt t (lem_weaken_btyp g g' e' bt p_e'_bt x t_x)


{-@ lem_weaken_wf :: g:Env -> g':Env -> t:Type -> ProofOf(WFType (concatE g g') t)
            -> { x:Vname | (Set_mem x (binds g')) || not (Set_mem x (free t))} 
            -> t_x:Type -> ProofOf(WFType g t_x)
            -> ProofOf(WFType (concatE (Cons x t_x g) g') t) @-}
lem_weaken_wf :: Env -> Env -> Type -> WFType -> Vname -> Type -> WFType -> WFType
lem_weaken_wf g g' t (WFRefn _g y b p pf_p_bl) x t_x p_tx
    = WFRefn (concatE (Cons x t_x g) g') y b p
--                           (y `withProof` lem_in_env_concat g g' y
--                              `withProof` lem_in_env_concat (Cons x t_x g) g' y) b p 
          (lem_weaken_btyp (erase_env g) (BCons y (BTBase b) (erase_env g')) p (BTBase TBool) 
                           (pf_p_bl `withProof` lem_erase_concat (Cons x t_x g) g'
                                    `withProof` lem_erase_concat g g') 
--                           (x `withProof` lem_in_env_erase g x
--                              `withProof` lem_in_env_erase g' x)
                           x (erase t_x))
lem_weaken_wf g g' t (WFFunc _g y t_y p_ty_wf t' p_t'_wf) x t_x p_tx
    = WFFunc (concatE (Cons x t_x g) g') y
--                           (y `withProof` lem_in_env_concat g g' y
--                              `withProof` lem_in_env_concat (Cons x t_x g) g' y) 
                           t_y (lem_weaken_wf g g' t_y p_ty_wf x t_x p_tx)
                           t' (lem_weaken_wf g (Cons y t_y g') t' p_t'_wf x t_x p_tx)
lem_weaken_wf g g' t (WFExis _g y t_y p_ty_wf t' p_t'_wf) x t_x p_tx
    = WFExis (concatE (Cons x t_x g) g') y
--                           (y `withProof` lem_in_env_concat g g' y
--                              `withProof` lem_in_env_concat (Cons x t_x g) g' y) 
                           t_y (lem_weaken_wf g g' t_y p_ty_wf x t_x p_tx)
                           t' (lem_weaken_wf g (Cons y t_y g') t' p_t'_wf x t_x p_tx)
{-
{-@ lem_sub_refl :: g:Env -> t:Type -> ProofOf(WFType g t) -> ProofOf(Subtype g t t) @-}
lem_sub_refl :: Env -> Type -> WFType -> Subtype
lem_sub_refl g t (WFRefn _g x b p p_p_bl) -- t = b{x:p}
    = SBase g x b p x p (EntExt (Cons x (TRefn b x p) g) (subst x (V x) p) eval_thp)
        where
    -- need eval_thp :: th:CSubst -> ProofOf(DenotesEnv (Cons x (TRefn b x p) g) th)
    --                            -> ProofOf(EvalsTo (csubst th p) (True))
            eval_thp th pf_den_gx_th = Refl (csubst th p)
                where
                    (DRefn _ _ _ _ _ pf_pxx_tt) = 
-}
{-
    = case ( ? ) of
        (DRefn _ _ _ _v p_v_b eval_pvx_tt) - >
                     -- ProofOf(Entails (Cons v1 (TRefn b v1 p1) g) (subst v2 (V v1) p2))
    = SBase g x b p x p (EntExt (Cons x (TRefn b x p) g) (subst x (V x) p) eval_thp)
        where -- need :: ProofOf(EvalsTo (csubst th p) (Bc True))
            eval_thp th pf_den_gx_th =  
  -} 
{-lem_sub_refl g t (WFFunc _g x t_x p_g_tx t' p_gx_t') 
    = ? -- TODO
lem_sub_refl g t (WFExis _g x t_x p_g_tx t' p_gx_t') 
    = ? -- TODO
-}
{-
{-@ lem_extend_denotes_env :: g:Env -> th:CSubst -> ProofOf(DenotesEnv g th)
                -> x:Vname -> { t:Type | not (Set_mem x (free t)) } 
                -> { v:Expr | isValue v } -> ProofOf(Denotes (ctsubst th t) v)
                -> ProofOf(DenotesEnv (Cons x t g) (CCons x v th)) @-}
lem_extend_denotes_env :: Env -> CSubst -> DenotesEnv -> Vname -> Type -> Expr
                              -> Denotes -> DenotesEnv
lem_extend_denotes_env g th (DEnv _g _th mk_pf_den_tht_thx) x t v den_tht_v 
    = DEnv (Cons x t g) (CCons x v th) mk_pf_den_th't_th'x
      where
        {-@ mk_pf_den_th't_th'x :: y:Vname -> {s:Type | bound_in y s (Cons x t g)}           
              -> ProofOf(Denotes (ctsubst (CCons x v th) s) (csubst (CCons x v th) (V y))) @-}
        mk_pf_den_th't_th'x  y s = case (x == y, t == s) of 
          (True, True)   -> den_tht_v
          (False, _)     -> mk_pf_den_tht_thx y s
          (_, _)         -> impossible "definitely"
  -}        
{- 
{-@ lem_denote_sound_sub :: g:Env -> t1:Type -> t2:Type -> ProofOf(Subtype g t1 t2)
                -> th:CSubst -> ProofOf(DenotesEnv g th) -> { v:Expr | isValue v}
                -> ProofOf(Denotes (ctsubst th t1) v) 
                -> ProofOf(Denotes (ctsubst th t2) v) @-}
lem_denote_sound_sub :: Env -> Type -> Type -> Subtype -> CSubst -> DenotesEnv
                            -> Expr -> Denotes -> Denotes 
lem_denote_sound_sub g t1 t2 (SBase _g x1 b p1 x2 p2 pf_ent_p2)
                                                  -- Pf(Entails g' p2[x1/x2])
                       th den_g_th v den_t1_v
    = case (pf_ent_p2, den_t1_v) of 
        (EntPred _g' _p2 ev_thp2_tt, DRefn _ _ _ _v pf_v_b pf_p1v_tt) 
            -> DRefn b x2 p2 v pf_v_b (ev_thp2_tt th' den_g'_th')
               where
                 th'        = CCons x1 v th
                 den_g'_th' = DExt g th den_g_th x1 t1 v den_t1_v
        --- need th'(p2[x1/x2]) = th(p[x1/x2][v/x1]) peeling lemma
        (_, _) -> impossible "certainly"
-}
{-
{-@ lem_denote_sound_typ :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
                -> th:CSubst -> ProofOf(DenotesEnv g th)  
                -> (Expr, (EvalsTo, Denotes))<{\v pfs ->
                     (isValue v') && 
                     (propOf (fst pfs) == EvalsTo (csubst th e) v') &&
                     (propOf (snd pfs) == Denotes (ctsubst th t) v')}> @-}
lem_denote_sound_typ :: Env -> Expr -> Type -> HasType -> CSubst -> DenotesEnv
                            -> (Expr, (EvalsTo, Denotes))
-}
{-
-- Lemma 1 in the Pen and Paper version (Preservation of Denotations)
-- If e ->* e' then e in [[t]] iff e' in [[t]]
{-@ lemma1_fwd :: e:Expr -> e':Expr -> ProofOf(EvalsTo e e') -> t:Type
                -> ProofOf(Denotes t e) -> ProofOf(Denotes t e') / [tsize t] @-}
lemma1_fwd :: Expr -> Expr -> EvalsTo -> Type -> Denotes -> Denotes
{-lemma1_fwd e e' p_ee' (TBase _b) (DBase b _e p_eb) = DBase b e' p_e'b
  where 
    p_e'b              = lemma_soundness e e' p_ee' (BTBase b) p_eb-}
lemma1_fwd e e' p_ee' (TRefn _b _x _p) (DRefn b x p _e p_eb predicate) = den_te'
  where
    den_te'            = DRefn b x p e' p_e'b predicate2
    p_e'b              = lemma_soundness e e' p_ee' (BTBase b) p_eb
    {-@ predicate2 :: {w:Expr | isValue w} -> ProofOf(EvalsTo e' w)
                            -> ProofOf( EvalsTo (subst x w p) (Bc True)) @-}
    predicate2 :: Expr -> EvalsTo -> EvalsTo
    predicate2 v p_e'v = predicate v (lemma_evals_trans e e' v p_ee' p_e'v)
lemma1_fwd e e' p_ee' (TFunc _x _tx _t) (DFunc x t_x t _e p_ebt app_den) = den_te'
  where
    den_te'          = DFunc x t_x t e' p_e'bt app_den'
    p_e'bt           = lemma_soundness e e' p_ee' (erase (TFunc x t_x t)) p_ebt
    app_den' v d_txv = lemma1_fwd (App e v) (App e' v) p_ev_e'v (tsubst x v t) dtev
      where
        p_ev_e'v     = (lemma_app_many e e' v p_ee')
        dtev         = app_den v d_txv 
lemma1_fwd e e' p_ee' (TExists _x _tx _t) (DExis x t_x t _e p_ebt v d_txv d_te) = d_te'
  where
    d_te'     = DExis x t_x t e' p_e'bt v d_txv den_te'
    p_e'bt    = lemma_soundness e e' p_ee' (erase (TExists x t_x t)) p_ebt
    den_te'   = lemma1_fwd e e' p_ee' (tsubst x v t) d_te

--{-@ lemma1_bck :: e:Expr -> e':Expr -> ProofOf(EvalsTo e e') -> t:Type
--                   -> ProofOf(Denotes t e') -> ProofOf(Denotes t e) @-}
--lemma1_bck :: Expr -> Expr -> EvalsTo -> Type -> Denotes -> Denotes
--lemma1_bck = undefined
-}



{-@ lem_typing_wf :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
                      -> ProofOf(WFEnv g) -> ProofOf(WFType g t) @-} 
lem_typing_wf :: Env -> Expr -> Type -> HasType -> WFEnv -> WFType
lem_typing_wf g e t (TBC _g b) p_wf_g  = lem_wf_tybc g b
lem_typing_wf g e t (TIC _g n) p_wf_g  = lem_wf_tyic g n
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
lem_typing_wf g e t (TAbs _g x t_x p_tx_wf e' t' p_e'_t') p_wf_g
    = WFFunc g x t_x p_tx_wf t' (lem_typing_wf (Cons x t_x g) e' t' p_e'_t'
                                               (WFEBind g p_wf_g x t_x p_tx_wf))
lem_typing_wf g e t (TApp _g e1 x t_x t' p_e1_txt' e2 p_e2_tx) p_wf_g
    = case (lem_typing_wf g e1 (TFunc x t_x t') p_e1_txt' p_wf_g) of
        (WFFunc _ _ _ p_g_tx _ p_gx_t') -> WFExis g x t_x (lem_typing_wf g e2 t_x p_e2_tx p_wf_g)
                                                      t'  p_gx_t'
        (_)                             -> impossible "clearly"
lem_typing_wf g e t (TLet _g e_x t_x p_ex_tx x e' _t p_g_t p_e'_t) p_wf_g = p_g_t 
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
          Left ()               -> Right (subst x e2 e', EAppAbs x e' e2)
          Right (e2', p_e2_e2') -> Right (App (Lambda x e') e2', EApp2 e2 e2' p_e2_e2' (Lambda x e'))
thm_progress _e _t (TApp Empty e1 x t_x t p_e1_txt e2 p_e2_tx) 
      = Right (App e1' e2, EApp1 e1 e1' p_e1_e1' e2)
        where
          Right (e1', p_e1_e1') = thm_progress e1 (TFunc x t_x t) p_e1_txt
thm_progress _e _t (TLet Empty e1 tx p_e1_tx x e2 t p_t p_e2_t)
      = case (thm_progress e1 tx p_e1_tx) of
          Left ()               -> Right (subst x e1 e2, ELetV x e1 e2)
          Right (e1', p_e1_e1') -> Right (Let x e1' e2, ELet e1 e1' p_e1_e1' x e2) 
thm_progress _e _t (TAnn Empty e1 t p_e1_t)
      = case (thm_progress e1 t p_e1_t) of
          Left ()               -> Right (e1, EAnnV e1 t)
          Right (e1', p_e1_e1') -> Right (Annot e1' t, EAnn e1 e1' p_e1_e1' t)
thm_progress _e _t (TSub Empty e s p_e_s t p_t p_s_t)
      = case (thm_progress e s p_e_s) of
          Left ()               -> Left ()
          Right (e', p_e_e')    -> Right (e', p_e_e') 
