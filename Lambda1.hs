{-# LANGUAGE GADTs #-}

--{-@ LIQUID "--counter-examples" @-}
--{-@ LIQUID "--exact-data-cons" @-}
--{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--short-names" @-}

module Lambda1 where

import Data.Foldable
import Language.Haskell.Liquid.ProofCombinators
import qualified Data.Set as S

---------------------------------------------------------------------------
----- | PRELIMINARIES
---------------------------------------------------------------------------

{-@ measure proposition :: a -> b @-}
{-@ type ProofOf E = { v:_ | proposition v = E } @-}

--TODO: will classes and instances make anything easier or harder?
--class HasVars a where
--    free  :: a -> S.Set Vname
--    subst :: Vname -> 

---------------------------------------------------------------------------
----- | TERMS of our language
---------------------------------------------------------------------------
  ---   Term level expressions 

type Vname = String

data Prim = And | Or | Not
          | Leq | Leqn Int 
          | Eq  | Eqn Int
  deriving (Eq, Show)

{-@ inline expects_bool @-}
expects_bool :: Prim -> Bool
expects_bool And = True
expects_bool Or  = True
expects_bool Not = True
expects_bool _   = False

{-@ inline expects_int @-}
expects_int :: Prim -> Bool
expects_int Leq      = True    
expects_int (Leqn _) = True
expects_int Eq       = True
expects_int (Eqn _)  = True
expects_int _        = False

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

{-@ reflect isValue @-}
isValue :: Expr -> Bool
isValue (Bc _)       = True
isValue (Ic _)       = True
isValue (Prim _)     = True
isValue (V _)        = True
isValue (Lambda _ _) = True
isValue Crash        = True
isValue _            = False

{-@ inline is_bc @-}
is_bc :: Expr -> Bool
is_bc (Bc _) = True
is_bc _      = False

{-@ inline is_ic @-}
is_ic :: Expr -> Bool
is_ic (Ic _) = True
is_ic _      = False

{-@ reflect subst @-}
--{-@ subst :: Vname -> { v:Expr | isValue v } -> Expr -> Expr @-}
subst :: Vname -> Expr -> Expr -> Expr
subst x e_x (Bc b)             = Bc b
subst x e_x (Ic n)             = Ic n
subst x e_x (Prim p)           = Prim p
subst x e_x (V y) | x == y     = e_x
                  | otherwise  = V y -- TODO ensure no clashes with bound var names
subst x e_x (Lambda y e)       = Lambda y (subst x e_x e)
subst x e_x (App e e')         = App (subst x e_x e) (subst x e_x e')
subst x e_x (Let y e1 e2)      = Let y (subst x e_x e1) (subst x e_x e2)
subst x e_x (Annot e t)        = Annot (subst x e_x e) t
subst x e_x Crash              = Crash

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

data Type = TBase   Base                 -- b
          | TRefn   Base Vname Pred      -- b{x : p}
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

-- do we really want a separate Bare Type datatype?
data BType = BTBase Base                 -- b
           | BTFunc BType BType          -- t -> t'
  deriving (Show)

data BEnv = BEmpty                       -- type BEnv = [(Vname, BType)]
          | BCons Vname BType BEnv
  deriving (Show) 

{-@ measure tsize @-}
tsize :: Type -> Int
tsize (TBase b)	        = 0
tsize (TRefn b v r)     = 0
tsize (TFunc x t_x t)   = (tsize t_x) + (tsize t) + 1
tsize (TExists x t_x t) = (tsize t_x) + (tsize t) + 1

{-@ reflect erase @-}
erase :: Type -> BType
erase (TBase b)         = BTBase b
erase (TRefn b v r)     = BTBase b
erase (TFunc x t_x t)   = BTFunc (erase t_x) (erase t)
erase (TExists x t_x t) = (erase t)

{-@ reflect free @-} -- TODO: verify this
free :: Type -> S.Set Vname
free (TBase b)          = S.empty
free (TRefn b v r)      = S.difference (fv r) (S.singleton v)
free (TFunc x t_x t)    = S.union (free t_x) (S.difference (free t) (S.singleton x))
free (TExists x t_x t)  = S.union (free t_x) (S.difference (free t) (S.singleton x))

-- assuming no collisions with bound vars - TODO fix this
{-@ reflect tsubst @-}
{-@ tsubst :: Vname -> Expr -> t:Type  
                    -> { t':Type | tsize t' <= tsize t && tsize t' >= 0 } @-}
tsubst :: Vname -> Expr -> Type -> Type
tsubst x _   (TBase b)         = TBase b
tsubst x e_x (TRefn b v r)     = TRefn b v (subst x e_x r)
tsubst x e_x (TFunc z t_z t)   = TFunc z (tsubst x e_x t_z) (tsubst x e_x t)
tsubst x e_x (TExists z t_z t) = TExists z (tsubst x e_x t_z) (tsubst x e_x t)

----- OPERATIONAL SEMANTICS (Small Step)

{-@ reflect delta @-}
--{-@ delta :: p:Prim -> { e:Expr | (is_bc e && expects_bool p) || (is_ic e && expects_int p) } -> Expr @-}
delta :: Prim -> Expr -> Expr
delta And (Bc True)   = Lambda "x" (V "x")
delta And (Bc False)  = Lambda "x" (Bc False)
delta Or  (Bc True)   = Lambda "x" (Bc True)
delta Or  (Bc False)  = Lambda "x" (V "x")
delta Not (Bc True)   = Bc False
delta Not (Bc False)  = Bc True
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
    EPrim :: c:Prim -> { v:Expr | isValue v } 
                 -> ProofOf( Step (App (Prim c) v) (delta c v) )
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

{-@ reflect ty @-}
ty :: Prim -> Type
ty And      = TFunc "x" (TBase TBool) (TFunc "y" (TBase TBool) (TBase TBool))
ty Or       = TFunc "x" (TBase TBool) (TFunc "y" (TBase TBool) (TBase TBool))
ty Not      = TFunc "x" (TBase TBool) (TBase TBool)
ty Leq      = TFunc "x" (TBase TInt) (TFunc "y" (TBase TInt) (TBase TInt))
ty (Leqn _) = TFunc "x" (TBase TInt) (TBase TBool)
ty Eq       = TFunc "x" (TBase TInt) (TFunc "y" (TBase TInt) (TBase TInt))
ty (Eqn _)  = TFunc "x" (TBase TInt) (TBase TBool)

data HasBTypeP where
    HasBType :: BEnv -> Expr -> BType -> HasBTypeP 

data HasBType where
    BTBC  :: BEnv -> Bool -> HasBType
    BTIC  :: BEnv -> Int -> HasBType
    BTVar :: BEnv -> Vname -> BType -> HasBType
    BTPrm :: BEnv -> Prim -> HasBType
    BTAbs :: BEnv -> Vname -> BType -> Expr -> BType -> HasBType -> HasBType
    BTApp :: BEnv -> Expr -> Vname -> BType -> BType -> HasBType 
              -> Expr -> HasBType -> HasBType
    BTLet :: BEnv -> Expr -> BType -> HasBType -> Vname -> Expr
              -> BType -> HasBType -> HasBType
    BTAnn :: BEnv -> Expr -> BType -> Type -> HasBType -> HasBType

{-@ data HasBType where
    BTBC  :: g:BEnv -> b:Bool -> ProofOf(HasBType g (Bc b) (BTBase TBool))
 |  BTIC  :: g:BEnv -> n:Int -> ProofOf(HasBType g (Ic n) (BTBase TInt))
 |  BTVar :: g:BEnv -> x:Vname -> {b:BType | elem (x,b) g} -> ProofOf(HasBType g e b)
 |  BTPrm :: g:BEnv -> c:Prim -> ProofOf(HasBType g (Prim c) (erase (ty c)))
 |  BTAbs :: g:BEnv -> x:Vname -> b:BType -> e:Expr -> b':BType
                -> ProofOf(HasBType (BCons x b g) e b')
                -> ProofOf(HasBType g (Lambda x e) (BTFunc b b'))
 |  BTApp :: g:BEnv -> e:Expr -> x:Vname -> b:BType -> b':BType
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
    WFBase :: Env -> Base -> WFType
    WFRefn :: Env -> Vname -> Base -> Pred -> HasType -> WFType
    WFFunc :: Env -> Vname -> Type -> WFType -> Type -> WFType -> WFType
    WFExis :: Env -> Vname -> Type -> WFType -> Type -> WFType -> WFType

{-@ data WFType where
    WFBase :: g:Env -> b:Base -> ProofOf(WFType g (TBase b))
 |  WFRefn :: g:Env -> x:Vname -> b:Base -> p:Pred 
               -> ProofOf(HasType (Cons x b g) p (TBase TBool)) 
               -> ProofOf(WFType g (TRefn v b p))
 |  WFFunc :: g:Env -> x:Vname -> t_x:Type -> ProofOf(WFType g t_x) -> t:Type
               -> ProofOf(WFType (Cons x t_x g) t) -> ProofOf(WFType g (TFunc x t_x t))
 |  WFExis :: g:Env -> x:Vname -> t_x:Type -> ProofOf(WFType g t_x) -> t:Type
               -> ProofOf(WFType (Cons x t_x g) t) -> ProofOf(WFType g (TExists x t_x t)) @-} 
-- @-}
 
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

{-@ data HasType where
    TBC  :: g:Env -> b:Bool -> ProofOf(HasType g (Bc b) (TBase TBool))
 |  TIC  :: g:Env -> n:Int -> ProofOf(HasType g (Ic n) (TBase TInt))
 |  TVar :: g:Env -> x:Vname -> { t:Type | elem (x,t) g } -> ProofOf(HasType g e t)
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
-- @-}

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
 |  SBind :: g:Env -> x:Vname -> t_x:Type -> t:Type -> { t':Type | not S.elem x (free t') } 
               -> ProofOf(Subtype (Cons x t_x g) t t')
               -> ProofOf(Subtype g (TExists x t_x t) t')
@-}

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
    DBase :: Base -> Expr -> HasBType -> Denotes
    DRefn :: Base -> Vname -> Pred -> Expr -> HasBType 
              -> (Expr -> EvalsTo -> EvalsTo) -> Denotes
    DFunc :: Vname -> Type -> Type -> Expr -> HasBType
              -> (Expr -> Denotes -> Denotes) -> Denotes
    DExis :: Vname -> Type -> Type -> Expr -> HasBType
              -> Expr -> Denotes -> Denotes -> Denotes
{-@ data Denotes where
    DBase :: b:Base -> e:Expr -> ProofOf(HasBType BEmpty e (BTBase b)) 
              -> ProofOf(Denotes (TBase b) e)
  | DRefn :: b:Base -> x:Vname -> p:Pred -> e:Expr 
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

-- TODO: Still need closing substitutions
type CSubst = [(Vname, Expr)]

--{-@ reflect csubst @-}
--csubst :: CSubst -> Expr -> Expr
--csubst x []                           = (V x)
--csubst x ((y, e) : binds) | x == y    = e
--                          | otherwise = csubst x binds


--- reflect cfsubst @-}

--- reflect ctsubst @-}

--{-@ reflect theta @-}
--theta :: Type -> CSubst -> Type
--theta t th = foldr (\(x,e) t' -> tsubst x e t') t th 

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
--    helping lemma?
{-@ lem_sem_det :: e:Expr -> e1:Expr -> ProofOf(Step e e1)
                   -> e2:Expr -> ProofOf(Step e e2) -> { x:_ | e1 == e2 } @-}
lem_sem_det :: Expr -> Expr -> Step -> Expr -> Step -> Proof
lem_sem_det e@(App (Prim c) w) e1 (EPrim c1 w1) e2 (EPrim c2 w2) 
    = () ? (e1 === (delta c1 w1)) ? (e2 === (delta c2 w2)) ? ((App (Prim c1) w1) === e)
--lem_sem_det (App (Prim _) _) e1 p1@(EPrim _ _)  e2 p2@(EPrim _ _) = () 
--lem_sem_det e e1 p1@(EPrim And (Bc False)) e2 p2@(EPrim And (Bc False)) = () 
--lem_sem_det e e1 p1@(EPrim Or (Bc True))   e2 p2@(EPrim Or (Bc True)) = () 
--lem_sem_det e e1 p1@(EPrim Or (Bc False))  e2 p2@(EPrim Or (Bc False)) = () 
--lem_sem_det e e1 p1@(EPrim Not (Bc True))  e2 p2@(EPrim Not (Bc True)) = () 
--lem_sem_det e e1 p1@(EPrim Not (Bc False)) e2 p2@(EPrim Not (Bc False)) = () 
--lem_sem_det e e1 p1@(EPrim Leq (Ic n))     e2 p2@(EPrim Leq (Ic _n)) 
--  = () ? ((App (Prim Leq) (Ic n)) === e === (App (Prim Leq) (Ic _n))) 
--lem_sem_det e e1 p1@(EPrim (Leqn n) (Ic m)) e2 p2@(EPrim (Leqn _n) (Ic _m)) = () 
--lem_sem_det e e1 p1@(EPrim Eq (Ic n))      e2 p2@(EPrim Eq (Ic _n)) = () 
--lem_sem_det e e1 p1@(EPrim (Eqn n) (Ic m))  e2 p2@(EPrim (Eqn _n) (Ic _m)) = () 
--lem_sem_det e e1 p1@(EPrim _ _) e2 p2@(EPrim _ _) = () 

lem_sem_det e e' (EApp1 e1 e1' p_e1e1' e2) e'' (EApp1 _e1 e1'' p_e1e1'' _e2)
      = () ? lem_sem_det e1 e1' p_e1e1' e1'' p_e1e1''  

  -- e = e1 e2, e' = e1' e2, e'' = e1'' e2

-- Lemma 1 in the Pen and Paper version (Preservation of Denotations)
-- If e ->* e' then e in [[t]] iff e' in [[t]]
{-@ lemma1_fwd :: e:Expr -> e':Expr -> ProofOf(EvalsTo e e') -> t:Type
                   -> ProofOf(Denotes t e) -> ProofOf(Denotes t e') / [tsize t] @-}
lemma1_fwd :: Expr -> Expr -> EvalsTo -> Type -> Denotes -> Denotes
lemma1_fwd e e' p_ee' (TBase _b) (DBase b _e p_eb) = DBase b e' p_e'b
  where 
    p_e'b              = lemma_soundness e e' p_ee' (BTBase b) p_eb
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
{-@ thm_progress :: { e:Expr | not (isValue e) } -> t:Type 
                   -> ProofOf(HasType Empty e t)  
                   -> { p:_ | proposition(snd p) == Step e (fst p) } @-}
thm_progress :: Expr -> Type -> HasType -> (Expr,Step) 
thm_progress _c _b (TBC Empty _) = undefined
thm_progress _c _b (TIC Empty _) = undefined
thm_progress _x _t (TVar Empty _ _) = undefined
thm_progress _c _t (TPrm Empty _) = undefined
--thm_progress _e _t (TApp BEmpty e1 x t_x t _proof e2 _proof2) = 
