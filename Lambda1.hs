{-# LANGUAGE GADTs #-}

--{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
--{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--short-names" @-}

module Lambda1 where

import Prelude hiding (foldr,max)
import Language.Haskell.Liquid.ProofCombinators
import qualified Data.Set as S

---------------------------------------------------------------------------
----- | PRELIMINARIES
---------------------------------------------------------------------------

{-@ measure propOf :: a -> b @-}
{-@ type ProofOf E = { proofObj:_ | propOf proofObj = E } @-}

{-@ inline max @-}
max :: Int -> Int -> Int
max x y = if x >= y then x else y

{-@ reflect foldr @-}
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f i []     = i
foldr f i (x:xs) = f x (foldr f i xs)

--TODO: will classes and instances make anything easier or harder?
--class HasVars a where
--    free  :: a -> S.Set Vname
--    subst :: Vname -> 

---------------------------------------------------------------------------
----- | TERMS of our language
---------------------------------------------------------------------------
  ---   Term level expressions 

type Vname = String

data Prim = And | Or | Not | Eqv
          | Leq | Leqn Int 
          | Eq  | Eqn Int
  deriving (Eq, Show)

data Expr = Bc Bool              -- True, False
          | Ic Int               -- 0, 1, 2, ...
          | Prim Prim            -- built-in primitive functions 
          | V Vname              -- x
          | Lambda Vname Expr    -- \x.e
          | App Expr Expr        -- e e'  TODO or does this become e v ??
          | Let Vname Expr Expr  -- let x = e1 in e2
          | Annot Expr Type      -- e : t
          | Crash
  deriving (Eq, Show)

{-@ inline isValue @-}
isValue :: Expr -> Bool
isValue (Bc _)       = True
isValue (Ic _)       = True
isValue (Prim _)     = True
isValue (V _)        = True
isValue (Lambda _ _) = True
isValue Crash        = True
isValue _            = False

{-@ inline isBc @-}
isBc :: Expr -> Bool
isBc (Bc _) = True
isBc _      = False

{-@ inline isIc @-}
isIc :: Expr -> Bool
isIc (Ic _) = True
isIc _      = False

{-@ reflect subst @-} -- TODO: should v be a value only?
{-@ subst :: Vname -> v:Expr -> e:Expr -> e':Expr @-} -- @-}
subst :: Vname -> Expr -> Expr -> Expr
subst x e_x (Bc b)                    = Bc b
subst x e_x (Ic n)                    = Ic n
subst x e_x (Prim p)                  = Prim p
subst x e_x (V y) | x == y            = e_x
                  | otherwise         = V y
subst x e_x (Lambda y e) | x == y     = Lambda y e
                         | otherwise  = Lambda y (subst x e_x e)
subst x e_x (App e e')                = App (subst x e_x e) (subst x e_x e')
subst x e_x (Let y e1 e2) | x == y    = Let y e1 e2 
                          | otherwise = Let y (subst x e_x e1) (subst x e_x e2)
subst x e_x (Annot e t)               = Annot (subst x e_x e) t
subst x e_x Crash                     = Crash

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

{-@ reflect in_env @-}
in_env :: Vname -> Env -> Bool
in_env x Empty                    = False
in_env x (Cons y t g) | x == y    = True
                      | otherwise = in_env x g

{-@ reflect bound_in @-}
bound_in :: Vname -> Type -> Env -> Bool
bound_in x t Empty                     = False
bound_in x t (Cons y t' g) | x == y    = (t == t')
                           | otherwise = bound_in x t g

{-@ reflect lookup_in @-}
lookup_in :: Vname -> Env -> Maybe Type
lookup_in x Empty                    = Nothing
lookup_in x (Cons y t g) | x == y    = Just t
                         | otherwise = lookup_in x g

-- do we really want a separate Bare Type datatype?
data BType = BTBase Base                 -- b
           | BTFunc BType BType          -- t -> t'
  deriving (Eq, Show)

data BEnv = BEmpty                       -- type BEnv = [(Vname, BType)]
          | BCons Vname BType BEnv
  deriving (Show) 

{-@ reflect bound_inB @-}
bound_inB :: Vname -> BType -> BEnv -> Bool
bound_inB x t BEmpty                     = False
bound_inB x t (BCons y t' g) | x == y    = (t == t')
                             | otherwise = bound_inB x t g

{-@ measure tsize @-}
{-@ tsize :: Type -> { v:Int | v >= 0 } @-}
tsize :: Type -> Int
--tsize (TBase b)	        = 0
tsize (TRefn b v r)     = 0
tsize (TFunc x t_x t)   = (tsize t) + 1
tsize (TExists x t_x t) = (tsize t) + 1

{-@ reflect erase @-}
erase :: Type -> BType
--erase (TBase b)         = BTBase b
erase (TRefn b v r)     = BTBase b
erase (TFunc x t_x t)   = BTFunc (erase t_x) (erase t)
erase (TExists x t_x t) = (erase t)

{-@ reflect erase_env @-}
erase_env :: Env -> BEnv
erase_env Empty        = BEmpty
erase_env (Cons x t g) = BCons x (erase t) (erase_env g)

{-@ reflect free @-} -- TODO: verify this
free :: Type -> S.Set Vname
--free (TBase b)          = S.empty
free (TRefn b v r)      = S.difference (fv r) (S.singleton v)
free (TFunc x t_x t)    = S.union (free t_x) (S.difference (free t) (S.singleton x))
free (TExists x t_x t)  = S.union (free t_x) (S.difference (free t) (S.singleton x))

-- TODO: doublecheck that this is capture avoiding
{-@ reflect tsubst @-}
{-@ tsubst :: Vname -> Expr -> t:Type  
                    -> { t':Type | tsize t' <= tsize t && tsize t' >= 0 } @-}
tsubst :: Vname -> Expr -> Type -> Type
--tsubst x _   (TBase b)         = TBase b
tsubst x e_x (TRefn b v r)     = TRefn b v (subst x e_x r)
tsubst x e_x (TFunc z t_z t)   
  | x == z                     = TFunc z t_z t
  | otherwise                  = TFunc z (tsubst x e_x t_z) (tsubst x e_x t)
tsubst x e_x (TExists z t_z t) 
  | x == z                     = TExists z t_z t
  | otherwise                  = TExists z (tsubst x e_x t_z) (tsubst x e_x t)

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

{-@ inline isEPrim @-}
isEPrim :: Step -> Bool
isEPrim (EPrim {}) = True
isEPrim _          = False

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

----- the Bare-Typing Relation and the Typing Relation

data HasBTypeP where
    HasBType :: BEnv -> Expr -> BType -> HasBTypeP 

data HasBType where
    BTBC  :: BEnv -> Bool -> HasBType
    BTIC  :: BEnv -> Int -> HasBType
    BTVar :: BEnv -> Vname -> BType -> HasBType
    BTPrm :: BEnv -> Prim -> HasBType
    BTAbs :: BEnv -> Vname -> BType -> Expr -> BType -> HasBType -> HasBType
    BTApp :: BEnv -> Expr -> BType -> BType -> HasBType 
              -> Expr -> HasBType -> HasBType
    BTLet :: BEnv -> Expr -> BType -> HasBType -> Vname -> Expr
              -> BType -> HasBType -> HasBType
    BTAnn :: BEnv -> Expr -> BType -> Type -> HasBType -> HasBType

{-@ data HasBType where
    BTBC  :: g:BEnv -> b:Bool -> ProofOf(HasBType g (Bc b) (BTBase TBool))
 |  BTIC  :: g:BEnv -> n:Int -> ProofOf(HasBType g (Ic n) (BTBase TInt))
 |  BTVar :: g:BEnv -> x:Vname -> {b:BType | bound_inB x b g} -> ProofOf(HasBType g (V x) b)
 |  BTPrm :: g:BEnv -> c:Prim -> ProofOf(HasBType g (Prim c) (erase (ty c)))
 |  BTAbs :: g:BEnv -> x:Vname -> b:BType -> e:Expr -> b':BType
                -> ProofOf(HasBType (BCons x b g) e b')
                -> ProofOf(HasBType g (Lambda x e) (BTFunc b b'))
 |  BTApp :: g:BEnv -> e:Expr -> b:BType -> b':BType
                -> ProofOf(HasBType g e (BTFunc b b')) 
                -> e':Expr -> ProofOf(HasBType g e' b) 
                -> ProofOf(HasBType g (App e e') b')
 |  BTLet :: g:BEnv -> e_x:Expr -> b:BType -> ProofOf(HasBType g e_x b)
                -> x:Vname -> e:Expr -> b':BType 
                -> ProofOf(HasBType (BCons x b g) e b')
                -> ProofOf(HasBType g (Let x e_x e) b')
 |  BTAnn :: g:BEnv -> e:Expr -> b:BType -> t:Type -> ProofOf(HasBType g e b)
                -> ProofOf(HasBType g (Annot e t) b)            @-} -- @-}

{-@ assume lemma_soundness :: e:Expr -> e':Expr -> ProofOf(EvalsTo e e') -> b:BType
                   -> ProofOf(HasBType BEmpty e b) -> ProofOf(HasBType BEmpty e' b) @-}
lemma_soundness :: Expr -> Expr -> EvalsTo -> BType -> HasBType -> HasBType
lemma_soundness e e' p_ee' b p_eb = undefined

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
 |  WFFunc :: g:Env -> x:Vname -> t_x:Type -> ProofOf(WFType g t_x) -> t:Type
               -> ProofOf(WFType (Cons x t_x g) t) -> ProofOf(WFType g (TFunc x t_x t))
 |  WFExis :: g:Env -> x:Vname -> t_x:Type -> ProofOf(WFType g t_x) -> t:Type
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
 |  WFEBind  :: g:Env -> ProofOf(WFEnv g) -> x:Vname -> t:Type -> ProofOf(WFType g t)
                -> ProofOf(WFEnv (Cons x t g)) @-} -- @-}

data HasTypeP where
    HasType :: Env -> Expr -> Type -> HasTypeP -- HasType G e t means G |- e : t

data HasType where -- TODO: Indicate in notes/latex where well-formedness used
    TBC  :: Env -> Bool -> HasType
    TIC  :: Env -> Int -> HasType
    TVar :: Env -> Vname -> Type -> HasType
    TPrm :: Env -> Prim -> HasType
    TAbs :: Env -> Vname -> Type -> WFType -> Expr -> Type -> HasType -> HasType
    TApp :: Env -> Expr -> Vname -> Type -> Type -> HasType 
              -> Expr -> HasType -> HasType
    TLet :: Env -> Expr -> Type -> HasType -> Vname -> Expr
              -> Type -> WFType -> HasType -> HasType
    TAnn :: Env -> Expr -> Type -> HasType -> HasType
    TSub :: Env -> Expr -> Type -> HasType -> Type -> WFType -> Subtype -> HasType

--   TBC  :: g:Env -> b:Bool -> ProofOf(HasType g (Bc b) (TBase TBool))
--   TIC  :: g:Env -> n:Int -> ProofOf(HasType g (Ic n) (TBase TInt))
{-@ data HasType where
    TBC  :: g:Env -> b:Bool -> ProofOf(HasType g (Bc b) (tybc b))
 |  TIC  :: g:Env -> n:Int -> ProofOf(HasType g (Ic n) (tyic n))
 |  TVar :: g:Env -> x:Vname -> { t:Type | bound_in x t g } -> ProofOf(HasType g (V x) t)
 |  TPrm :: g:Env -> c:Prim -> ProofOf(HasType g (Prim c) (ty c))
 |  TAbs :: g:Env -> x:Vname -> t_x:Type -> ProofOf(WFType g t_x) -> e:Expr -> t:Type
                -> ProofOf(HasType (Cons x t_x g) e t)
                -> ProofOf(HasType g (Lambda x e) (TFunc x t_x t))
 |  TApp :: g:Env -> e:Expr -> x:Vname -> t_x:Type -> t:Type
                -> ProofOf(HasType g e (TFunc x t_x t)) 
                -> e':Expr -> ProofOf(HasType g e' t_x) 
                -> ProofOf(HasType g (App e e') (TExists x t_x t))
 |  TLet :: g:Env -> e_x:Expr -> t_x:Type -> ProofOf(HasType g e_x t_x)
                -> x:Vname -> e:Expr -> t:Type -> ProofOf(WFType g t)
                -> ProofOf(HasType (Cons x t_x g) e t)
                -> ProofOf(HasType g (Let x e_x e) t)
 |  TAnn :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
                -> ProofOf(HasType g (Annot e t) t)
 |  TSub :: g:Env -> e:Expr -> s:Type -> ProofOf(HasType g e s) -> t:Type 
                -> ProofOf(WFType g t)-> ProofOf(Subtype g s t) -> ProofOf(HasType g e t) @-}

{-@ reflect tybc @-} -- Refined Constant Typing
tybc :: Bool -> Type
tybc True  = TRefn TBool "v" (App (App (Prim Eqv) (V "v")) (Bc True))
tybc False = TRefn TBool "v" (App (App (Prim Eqv) (V "v")) (Bc False))

{-@ reflect tyic @-}
tyic :: Int -> Type
tyic n = TRefn TInt "v" (App (App (Prim Eq) (V "v")) (Ic n))

{-@ reflect ty @-} -- Primitive Typing
ty :: Prim -> Type
ty And      = TFunc "x" (TRefn TBool "x" (Bc True)) 
                  (TFunc "y" (TRefn TBool "y" (Bc True)) 
                      (TRefn TBool "z" 
                          (App (App (Prim Eqv) (V "z")) 
                               (App (App (Prim And) (V "x")) (V "y")) )))
ty Or       = TFunc "x" (TRefn TBool "x" (Bc True)) 
                  (TFunc "y" (TRefn TBool "y" (Bc True)) 
                      (TRefn TBool "z" 
                          (App (App (Prim Eqv) (V "z")) 
                               (App (App (Prim Or) (V "x")) (V "y")) )))
ty Not      = TFunc "x" (TRefn TBool "x" (Bc True)) 
                  (TRefn TBool "z"
                      (App (App (Prim Eqv) (V "z")) 
                           (App (Prim Not) (V "x")) ))
ty Eqv      = TFunc "x" (TRefn TBool "x" (Bc True))
                  (TFunc "y" (TRefn TBool "y" (Bc True))  
                      (TRefn TBool "z"
                          (App (App (Prim Eqv) (V "z"))
                               (App (App (Prim Or) 
                                    (App (App (Prim And) (V "x")) (V "y")))
                                    (App (App (Prim And) (App (Prim Not) (V "x")))
                                         (App (Prim Not) (V "y")))))))
ty Leq      = TFunc "x" (TRefn TInt "x" (Bc True)) 
                  (TFunc "y" (TRefn TInt "y" (Bc True)) 
                      (TRefn TBool "z"
                          (App (App (Prim Eqv) (V "z"))
                               (App (App (Prim Leq) (V "x")) (V "y")) )))
ty (Leqn n) = TFunc "y" (TRefn TInt "y" (Bc True)) 
                  (TRefn TBool "z"
                      (App (App (Prim Eqv) (V "z"))
                           (App (App (Prim Leq) (Ic n)) (V "y")) )) 
ty Eq       = TFunc "x" (TRefn TInt "x" (Bc True)) 
                  (TFunc "y" (TRefn TInt "y" (Bc True)) 
                      (TRefn TBool "z"
                          (App (App (Prim Eqv) (V "z"))
                               (App (App (Prim Eq) (V "x")) (V "y")) )))
ty (Eqn n)  = TFunc "y" (TRefn TInt "y" (Bc True)) 
                  (TRefn TBool "z"
                      (App (App (Prim Eqv) (V "z"))
                           (App (App (Prim Eq) (Ic n)) (V "y")) ))

-- Constant and Primitive Typing Lemmas
-- Lemma. Well-Formedness of Primitive/Constant Types
{-@ lem_wf_tybc :: b:Bool -> ProofOf(WFType Empty (tybc b)) @-}
lem_wf_tybc :: Bool -> WFType
lem_wf_tybc True  = WFRefn Empty "v" TBool pred pf_pr_bool
  where
     pred       = (App (App (Prim Eqv) (V "v")) (Bc True))
     g          = (BCons "v" (BTBase TBool) BEmpty)
     --{-@ pf_pr_bool :: ProofOf(HasBType (BCons "v" (BTBase TBool) BEmpty) pred (BTBase TBool)) @-}
     pf_eqv_v   = BTApp g (Prim Eqv) (BTBase TBool) (BTFunc (BTBase TBool) (BTBase TBool)) (BTPrm g Eqv) (V "v") (BTVar g "v" (BTBase TBool))
     pf_pr_bool = BTApp g (App (Prim Eqv) (V "v")) (BTBase TBool) (BTBase TBool) pf_eqv_v (Bc True) (BTBC g True)
lem_wf_tybc False  = WFRefn Empty "v" TBool pred pf_pr_bool
  where
     pred       = (App (App (Prim Eqv) (V "v")) (Bc False))
     g          = (BCons "v" (BTBase TBool) BEmpty)
     --{-@ pf_pr_bool :: ProofOf(HasBType (BCons "v" (BTBase TBool) BEmpty) pred (BTBase TBool)) @-}
     pf_eqv_v   = BTApp g (Prim Eqv) (BTBase TBool) (BTFunc (BTBase TBool) (BTBase TBool)) (BTPrm g Eqv) (V "v") (BTVar g "v" (BTBase TBool))
     pf_pr_bool = BTApp g (App (Prim Eqv) (V "v")) (BTBase TBool) (BTBase TBool) pf_eqv_v (Bc False) (BTBC g False)

{-@ lem_wf_tyic :: n:Int -> ProofOf(WFType Empty (tyic n)) @-}
lem_wf_tyic :: Int -> WFType
lem_wf_tyic n = WFRefn Empty "v" TInt pred pf_pr_bool
  where
    pred        = (App (App (Prim Eq) (V "v")) (Ic n))
    g           = (BCons "v" (BTBase TInt) BEmpty)
    pf_eq_v     = BTApp g (Prim Eq) (BTBase TInt) (BTFunc (BTBase TInt) (BTBase TBool)) (BTPrm g Eq) (V "v") (BTVar g "v" (BTBase TInt))
    pf_pr_bool  = BTApp g (App (Prim Eq) (V "v")) (BTBase TInt) (BTBase TBool) pf_eq_v (Ic n) (BTIC g n)

{-@ pf_base_wf :: g:Env -> b:Base -> x:Vname -> ProofOf(WFType g (TRefn b x (Bc True))) @-}
pf_base_wf :: Env -> Base -> Vname -> WFType
pf_base_wf g b x = WFRefn g x b (Bc True) (BTBC (BCons x (BTBase b) (erase_env g)) True) 

{-@ lem_wf_ty :: c:Prim -> ProofOf(WFType Empty (ty c)) @-}
lem_wf_ty :: Prim -> WFType
lem_wf_ty And      = WFFunc Empty "x" (TRefn TBool "x" (Bc True)) (pf_base_wf Empty TBool "x")
                                      middle_type pf_middle_wf
  where
    pred         = (App (App (Prim Eqv) (V "z")) (App (App (Prim And) (V "x")) (V "y")) )
    g            = BCons "z" (BTBase TBool) (BCons "y" (BTBase TBool) 
                                            (BCons "x" (BTBase TBool) BEmpty))
    pf_eqv_v     = BTApp g (Prim Eqv) (BTBase TBool) (BTFunc (BTBase TBool) (BTBase TBool))
                        (BTPrm g Eqv) (V "z") (BTVar g "z" (BTBase TBool))
    pf_and_x     = BTApp g (Prim And) (BTBase TBool) (BTFunc (BTBase TBool) (BTBase TBool))
                        (BTPrm g And) (V "x") (BTVar g "x" (BTBase TBool))
    pf_and_xy    = BTApp g (App (Prim And) (V "x")) (BTBase TBool) (BTBase TBool)
                        pf_and_x (V "y") (BTVar g "y" (BTBase TBool))
    pf_pred_bool = BTApp g (App (Prim Eqv) (V "z")) (BTBase TBool) (BTBase TBool) pf_eqv_v
                        (App (App (Prim And) (V "x")) (V "y")) pf_and_xy
  --g1           = Cons "z" (TRefn TBool "z" (Bc True)) (Cons "y" (TRefn TBool "y" (Bc True))
  --                                                (Cons "x" (TRefn TBool "x" (Bc True))))   
    g1           = Cons "y" (TRefn TBool "y" (Bc True))
                                                 (Cons "x" (TRefn TBool "x" (Bc True)) Empty)
    g2           = Cons "x" (TRefn TBool "x" (Bc True)) Empty
    inner_type   = TRefn TBool "z" pred
    pf_inner_wf  = WFRefn g1 "z" TBool pred pf_pred_bool
    middle_type  = TFunc "y" (TRefn TBool "y" (Bc True)) inner_type 
    pf_middle_wf = WFFunc g2 "y" (TRefn TBool "y" (Bc True)) (pf_base_wf g2 TBool "y")
                                 inner_type pf_inner_wf 
{-
ty Or       = TFunc "x" (TRefn TBool "x" (Bc True)) 
                  (TFunc "y" (TRefn TBool "y" (Bc True)) 
                      (TRefn TBool "z" 
                          (App (App (Prim Eqv) (V "z")) 
                               (App (App (Prim Or) (V "x")) (V "y")) )))
ty Not      = TFunc "x" (TRefn TBool "x" (Bc True)) 
                  (TRefn TBool "z"
                      (App (App (Prim Eqv) (V "z")) 
                           (App (Prim Not) (V "x")) ))
ty Eqv      = TFunc "x" (TRefn TBool "x" (Bc True))
                  (TFunc "y" (TRefn TBool "y" (Bc True))  
                      (TRefn TBool "z"
                          (App (App (Prim Eqv) (V "z"))
                               (App (App (Prim Or) 
                                    (App (App (Prim And) (V "x")) (V "y")))
                                    (App (App (Prim And) (App (Prim Not) (V "x")))
                                         (App (Prim Not) (V "y")))))))
ty Leq      = TFunc "x" (TRefn TInt "x" (Bc True)) 
                  (TFunc "y" (TRefn TInt "y" (Bc True)) 
                      (TRefn TBool "z"
                          (App (App (Prim Eqv) (V "z"))
                               (App (App (Prim Leq) (V "x")) (V "y")) )))
ty (Leqn n) = TFunc "y" (TRefn TInt "y" (Bc True)) 
                  (TRefn TBool "z"
                      (App (App (Prim Eqv) (V "z"))
                           (App (App (Prim Leq) (Ic n)) (V "y")) )) 
ty Eq       = TFunc "x" (TRefn TInt "x" (Bc True)) 
                  (TFunc "y" (TRefn TInt "y" (Bc True)) 
                      (TRefn TBool "z"
                          (App (App (Prim Eqv) (V "z"))
                               (App (App (Prim Eq) (V "x")) (V "y")) )))
ty (Eqn n)  = TFunc "y" (TRefn TInt "y" (Bc True)) 
                  (TRefn TBool "z"
                      (App (App (Prim Eqv) (V "z"))
                           (App (App (Prim Eq) (Ic n)) (V "y")) ))

 |  TLet :: g:Env -> e_x:Expr -> t_x:Type -> ProofOf(HasType g e_x t_x)
                -> x:Vname -> e:Expr -> t:Type -> ProofOf(WFType g t)
                -> ProofOf(HasType (Cons x t_x g) e t)
                -> ProofOf(HasType g (Let x e_x e) t)
 |  TAnn :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
                -> ProofOf(HasType g (Annot e t) t)
 |  TSub :: g:Env -> e:Expr -> s:Type -> ProofOf(HasType g e s) -> t:Type 
                -> ProofOf(WFType g t)-> ProofOf(Subtype g s t) -> ProofOf(HasType g e t) -}

{-{-@ reflect ty_simple @-} -- TODO: this conflicts with the current metatheory
ty_simple :: Prim -> Type
ty_simple And      = TFunc "x" (TBase TBool) (TFunc "y" (TBase TBool) (TBase TBool))
ty_simple Or       = TFunc "x" (TBase TBool) (TFunc "y" (TBase TBool) (TBase TBool))
ty_simple Not      = TFunc "x" (TBase TBool) (TBase TBool)
ty_simple Eqv      = TFunc "x" (TBase TBool) (TFunc "y" (TBase TBool) (TBase TBool))
ty_simple Leq      = TFunc "x" (TBase TInt) (TFunc "y" (TBase TInt) (TBase TInt))
ty_simple (Leqn _) = TFunc "x" (TBase TInt) (TBase TBool)
ty_simple Eq       = TFunc "x" (TBase TInt) (TFunc "y" (TBase TInt) (TBase TInt))
ty_simple (Eqn _)  = TFunc "x" (TBase TInt) (TBase TBool)

{-@ lem_ty_simple :: g:Env -> c:Prim -> ProofOf(HasType g (Prim c) (ty_simple c)) @-}
lem_typ_simple :: Env -> Prim -> HasType-}

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
 |  SFunc :: g:Env -> x1:Vname -> s1:Type -> x2:Vname -> s2:Type
               -> ProofOf(Subtype g s2 s1) -> t1:Type -> t2:Type
               -> ProofOf(Subtype (Cons x2 s2 g) (tsubst x1 (V x2) t1) t2)
               -> ProofOf(Subtype g (TFunc x1 s1 t1) (TFunc x2 s2 t2))
 |  SWitn :: g:Env -> e:Expr -> t_x:Type -> ProofOf(HasType g e t_x) -> t:Type 
               -> x:Vname -> t':Type -> ProofOf(Subtype g t (tsubst x e t'))
               -> ProofOf(Subtype g t (TExists x t_x t'))
 |  SBind :: g:Env -> x:Vname -> t_x:Type -> t:Type -> { t':Type | not Set_mem x (free t') } 
               -> ProofOf(Subtype (Cons x t_x g) t t')
               -> ProofOf(Subtype g (TExists x t_x t) t')
@-}

-- Lemma. Subtyping is reflexive TODO TODO TODO

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
    EntExt  :: Env -> Pred -> (CSubst -> DenotesEnv -> EvalsTo) -> Entails

{-@ data Entails where
    EntExt :: g:Env -> p:Pred 
               -> (th:CSubst -> ProofOf(DenotesEnv g th) 
                             -> ProofOf(EvalsTo (csubst th p) (Bc True)) )
               -> ProofOf(Entails g p) @-} 

data DenotesP where 
    Denotes :: Type -> Expr -> DenotesP    -- e \in [[t]]

data Denotes where
--    DBase :: Base -> Expr -> HasBType -> Denotes
    DRefn :: Base -> Vname -> Pred -> Expr -> HasBType 
              -> (Expr -> EvalsTo -> EvalsTo) -> Denotes
    DFunc :: Vname -> Type -> Type -> Expr -> HasBType
              -> (Expr -> Denotes -> Denotes) -> Denotes
    DExis :: Vname -> Type -> Type -> Expr -> HasBType
              -> Expr -> Denotes -> Denotes -> Denotes
{-@ data Denotes where
    DRefn :: b:Base -> x:Vname -> p:Pred -> e:Expr 
              -> ProofOf(HasBType BEmpty e (BTBase b))
              -> ({v':Expr | isValue v'} -> ProofOf(EvalsTo e v') 
                        -> ProofOf(EvalsTo (subst x v' p) (Bc True))) 
              -> ProofOf(Denotes (TRefn b x p) e)
  | DFunc :: x:Vname -> t_x:Type -> t:Type -> e:Expr 
              -> ProofOf(HasBType BEmpty e (erase (TFunc x t_x t)))
              -> ({ v':Expr | isValue v' } -> ProofOf(Denotes t_x v')
                        -> ProofOf(Denotes (tsubst x v' t) (App e v')) )
              -> ProofOf(Denotes (TFunc x t_x t) e)
  | DExis :: x:Vname -> t_x:Type -> t:Type -> e:Expr 
              -> ProofOf(HasBType BEmpty e (erase t)) 
              -> { v':Expr | isValue v' } -> ProofOf(Denotes t_x v')
              -> ProofOf(Denotes (tsubst x v' t) e)
              -> ProofOf(Denotes (TExists x t_x t) e)  @-} 

    --DBase :: b:Base -> e:Expr -> ProofOf(HasBType BEmpty e (BTBase b)) 
    --          -> ProofOf(Denotes (TBase b) e)
-- TODO: Still need closing substitutions
type CSubst = [(Vname, Expr)]

{-@ reflect csubst_var @-}
csubst_var :: CSubst -> Vname -> Expr
csubst_var []              x             = (V x)
csubst_var ((y,e) : binds) x | x == y    = e
                             | otherwise = csubst_var binds x

{-@ reflect remove @-}
{-@ remove :: Vname -> th:CSubst -> { th':CSubst | len th' <= len th } @-}
remove :: Vname -> CSubst -> CSubst
remove x []                           = []
remove x ((y,e) : binds) | x == y     = binds
                       | otherwise  = (y,e) : (remove x binds)

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

--{-@ reflect cfsubst @-}


{-@ reflect ctsubst @-}
ctsubst :: CSubst -> Type -> Type
ctsubst th t = foldr (\(x,e) t' -> tsubst x e t') t th 


--{-@ reflect theta @-}

-- TODO: Still need denotations of environments
data DenotesEnvP where 
    DenotesEnv :: Env -> CSubst -> DenotesEnvP 

data DenotesEnv where
    DEnv :: Env -> CSubst -> [Denotes] -> DenotesEnv
--{-@ data DenotesEnv where 
--    DEnv :: g:Env -> th:CSubst ->     Denotes (theta t th) (csubst x th)

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


-- the big theorems
{-@ thm_progress :: e:Expr -> t:Type -> ProofOf(HasType Empty e t)  
           -> Either { v:_ | isValue e } (Expr, Step)<{\e' pf -> propOf pf == Step e e'}> @-}
thm_progress :: Expr -> Type -> HasType -> Either Proof (Expr,Step) 
thm_progress c _b (TBC Empty _)    = Left ()
thm_progress c _b (TIC Empty _)    = Left ()
thm_progress x _t (TVar Empty _ _) = Left ()
thm_progress c _t (TPrm Empty _)   = Left ()
thm_progress e t  (TAbs {})        = Left ()
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

