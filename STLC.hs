module STLC where

import qualified Data.Set as S

{-@ LIQUID "--reflection" @-}

{-# LANGUAGE GADTs #-}

----- PRELIMINARIES

{-@ measure prop : a -> b @-}
{-@ type ProofOf E = { v:_ | prop v = E } @-}

--class HasVars a where
--    free  :: a -> S.Set Vname
--    subst :: Vname -> 

----- TERMS

type Vname = String

data Pred = Bc Bool                   -- True, False
          | Bv Vname                  -- x, y, z; interpreted over Z?
          | Ic Int                    -- 0, 1, ...
          | And Pred Pred
          | Or Pred Pred
          | Not Pred
          -- and uninterpreted functions?
          -- and anything else eneeded?
  deriving (Show)

data Form = P Pred                    -- p
          | FAnd Form Form            -- c1 ^ c2
          | Impl Vname Base Pred Form -- \forall x:b. p => c
  deriving (Show)

{-@ reflect fv @-}
fv :: Pred -> S.Set Vname
fv (Bc _)      = S.empty
fv (Bv x)      = S.singleton x
fv (Ic _)      = S.empty
fv (And p1 p2) = S.union (fv p1) (fv p2)
fv (Or p1 p2)  = S.union (fv p1) (fv p2)
fv (Not p1)    = fv p1

{-@ refelct isTermValue @-}
isTermValue :: Pred -> Bool
isTermValue (Bv _) = True
isTermValue (Ic _) = True
isTermValue _      = False

{-@ reflect bsubst @-}
bsubst :: Vname -> Vname -> Pred -> Pred
bsubst x y (Bc b)             = Bc b
bsubst x y (Bv z) | z == x    = Bv y
                  | otherwise = Bv z
bsubst x y (Ic c)             = Ic c
bsubst x y (And p1 p2)        = And (bsubst x y p1) (bsubst x y p2)
bsubst x y (Or p1 p2)         = Or  (bsubst x y p1) (bsubst x y p2)
bsubst x y (Not p)            = Not (bsubst x y p)

{-@ reflect bsubstc @-}
bsubstc :: Vname -> Int -> Pred -> Pred
bsubstc x c (Bc b)             = Bc b
bsubstc x c (Bv z) | z == x    = Ic c
                  | otherwise  = Bv z
bsubstc x c (Ic c')            = Ic c'
bsubstc x c (And p1 p2)        = And (bsubstc x y p1) (bsubstc x y p2)
bsubstc x c (Or p1 p2)         = Or  (bsubstc x y p1) (bsubstc x y p2)
bsubstc x c (Not p)            = Not (bsubstc x y p)


-- TODO: do i need operational semantics for boolean predicates?

--data Val  = VC Int                -- Constant c
--          | VV Vname              -- x
--          | VLambda Vname Expr    -- \x.e

data Expr = C Int                -- Constant c
          | V Vname              -- x
          | Lambda Vname Expr    -- \x.e
          | App Expr Expr        -- e e'  TODO or does this become e v ??
          | Let Vname Expr Expr  -- let x = e1 in e2
          | Annot Expr Type      -- e : t
  deriving (Show)

{-@ reflect isValue @-}
isValue :: Expr -> Bool
isValue (C _)        = True
isValue (V _)        = True
isValue (Lambda _ _) = True
isValue _            = False

{-@ reflect subst @-}
{-@ subst :: Vname -> { v:Expr | isValue v } -> Expr -> Expr @-}
subst :: Vname -> Expr -> Expr -> Expr
subst x v (C n)              = C n
subst x v (V y) | x == y     = v
                | otherwise  = V y -- TODO ensure no clashes with bound var names
subst x v (Lambda y e)       = Lambda y (subst x e_x e)
subst x v (App e v')         = App (subst x v e) (subst x v v')
subst x v (Let y e1 e2)      = Let y (subst x v e1) (subst x v e2)
subst x v (Annot e t)        = Annot (subst x v e) t

----- TYPES

data Base = TInt

data Type = TBase   Base                 -- b
          | TRefn   Base Vname Pred      -- b{v : r}
          | TFunc   Vname Type Type      -- x:t_x -> t
          | TExists Vname Type Type      -- \exists x:t_x.t
  deriving (Show)

type Env = [(Vname, Type)]	

-- do we really want a separate Bare Type datatype?
data BType = BTBase Base                 -- b
           | BTFunc BType BType          -- t -> t'
  deriving (Show)

type BEnv = [(Vname, BType)]

{-@ reflect erase @-}
erase :: Type -> BType
erase (TBase b)         = BTBase b
erase (TRefn b v r)     = BTBase b
erase (TFunc x t_x t)   = BTFunc (erase t_x) (erase t)
erase (TExists x t_x t) = (erase t)

{-@ reflect free @-} -- TODO: verify this
free :: Type -> S.Set Vname
free (TBase b)          = S.empty
free (TRefn b v r)      = S.delete v (fv r) 
free (TFunc x t_x t)    = S.union (free t_x) (S.delete x (free t))
free (TExists x t_x t)  = S.union (free t_x) (S.delete x (free t))

-- assuming no collisions with bound vars - TODO fix this
{-@ reflect tsubst @-}
tsubst :: Vname -> Vname -> Type -> Type
tsubst x y (TBase b)         = TBase b
tsubst x y (TRefn b v r)     = TRefn b v (bsubst x y r)
tsubst x y (TFunc z t_z t)   = TFunc z (tsubst x y t_z) (tsubst x y t)
tsubst x y (TExists z t_Z t) = TExists z (tsubst x y t_z) (tsubst x y t)

----- OPERATIONAL SEMANTICS (Small Step)
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
    EApp1 :: Expr -> Expr -> Step -> Expr -> Step
    EApp2 :: Expr -> Expr -> Step -> Expr -> Step
    EAppAbs :: Vname -> Expr -> Expr -> Step
    ELet  :: Expr -> Expr -> Step -> Vname -> Expr -> Step
    ELetV :: Vname -> Expr -> Expr -> Step
    EAnn  :: Expr -> Expr -> Step -> Type -> Step
    EAnnV :: Expr -> Type -> Step

{-@ data Step where 
    EApp1 :: e:Expr -> e':Expr -> ProofOf( Step e e' ) 
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
{-@ lemma_evals_trans :: e1:Expr -> e2:Expr -> e3:Expr -> ProofOf( EvalsToP e1 e2)
                    -> ProofOf( EvalsToP e2 e3) -> ProofOf( EvalsToP e1 e3) @-} 
lemma_evals_trans :: Expr -> Expr -> Expr -> EvalsTo -> EvalsTo -> EvalsTo
lemma_evals_trans e1 e2 e3 (Refl _e1) p_e2e3 = p_e2e3
lemma_evals_trans e1 e2 e3 (AddStep _e1 e p_e1e _e2 p_ee2) p_e2e3 = p_e1e3
  where
    p_e1e3 = AddStep e1 e p_e1e e3 p_ee3
    p_ee3  = lemma_evals_trans e e2 e3 p_ee2 pe2e3

{-@ lemma_app_many :: e:Expr -> e':Expr -> v:Expr -> ProofOf(EvalsTo e e')
                       -> ProofOf(EvalsTo (App e v) (App e' v)) @-}
lemma_app_many :: Expr -> Expr -> Expr -> EvalsTo -> EvalsTo
lemma_app_many e e' v (Refl _e) = Refl (App e v)
lemma_app_many e e' v (AddStep _e e1 s_ee1 _e' p_e1e') = p_ev_e'v
  where
    p_ev_e'v  = AddStep (App e v) (App e1 v) s_ev_e1v (App e' v) p_e1v_e'v
    s_ev_e1v  = EApp1 e e' s_ee1 v 
    p_e1v_e'v = lemma_app_many e1 e' v p_e1e' 

----- the Bare-Typing Relation and the Typing Relation

data HasBTypeP where
    HasBType :: BEnv -> Expr -> BType -> HasBTypeP 

data HasBType where
    BTVar :: BEnv -> Vname -> BType -> HasBType
    BTCon :: BEnv -> Int -> HasBType
    BTAbs :: BEnv -> Vname -> BType -> Expr -> BType -> HasBType -> HasBType
    BTApp :: BEnv -> Expr -> Vname -> BType -> BType -> HasBType 
              -> Expr -> HasBType -> HasBType
    BTLet :: BEnv -> Expr -> BType -> HasBType -> Vname -> Expr
              -> BType -> HasBType -> HasBType
    BTAnn :: BEnv -> Expr -> BType -> Type -> HasBType -> HasBType

{-@ data HasBType where
    BTVar :: g:BEnv -> x:Vname -> {b:BType | elem (x,b) g} -> ProofOf(HasBType g e b)
 |  BTCon :: g:BEnv -> c:Int -> ProofOf(HasBType g c (BTBase TInt))
 |  BTAbs :: g:BEnv -> x:Vname -> b:BType -> e:Expr -> b':BType
                -> ProofOf(HasBType (g ++ (x,b)) e b')
                -> ProofOf(HasBType g (Lambda x e) (BTFunc b b'))
 |  BTApp :: g:BEnv -> e:Expr -> x:Vname -> b:BType -> b':BType
                -> ProofOf(HasBType g e (BTFunc b b')) 
                -> e':Expr -> ProofOf(HasBType g e' b) 
                -> ProofOf(HasBType g (App e e') b')
 |  BTLet :: g:BEnv -> e_x:Expr -> b:BType -> ProofOf(HasBType g e_x b)
                -> x:Vname -> e:Expr -> b':BType 
                -> ProofOf(HasBType (g ++ (x,b)) e b')
                -> ProofOf(HasBType g (Let x e_x e) b')
 |  BTAnn :: g:BEnv -> e:Expr -> b:BType -> t:Type -> ProofOf(HasBType g e b)
                -> ProofOf(HasBType g (Annot e t) b)            @-} -- @-}

{-@ assume lemma_soundness :: e:Expr -> e':Expr -> ProofOf(EvalsTo e e') -> b:BType
                        -> ProofOf(HasBType [] e b) -> ProofOf(HasBType [] e' b) @-}
lemma_soundness :: Expr -> Expr -> EvalsTo -> BType -> HasBType -> HasBType
lemma_soundness e e' p_ee' b p_eb = undefined

data HasTypeP where
    HasType :: Env -> Expr -> Type -> HasTypeP -- HasType G e t means G |- e : t

data HasType where
    TVar :: Env -> Vname -> Type -> HasType
    TCon :: Env -> Int -> HasType
    TAbs :: Env -> Vname -> Type -> Expr -> Type -> HasType -> HasType
    TApp :: Env -> Expr -> Vname -> Type -> Type -> HasType 
              -> Expr -> HasType -> HasType
    TLet :: Env -> Expr -> Type -> HasType -> Vname -> Expr
              -> Type -> HasType -> HasType
    TAnn :: Env -> Expr -> Type -> HasType -> HasType
    TSub :: Env -> Expr -> Type -> HasType -> Type -> Subtype -> HasType

{-@ data HasType where
    TVar :: g:Env -> x:Vname -> { t:Type | elem (x,t) g } -> ProofOf(HasType g e t)
 |  TCon :: g:Env -> c:Int -> ProofOf(HasType g c (TBase TInt))
 |  TAbs :: g:Env -> x:Vname -> t_x:Type -> e:Expr -> t:Type
                -> ProofOf(HasType (g ++ (x,t_x)) e t)
                -> ProofOf(HasType g (Lambda x e) (TFunc x t_x t))
 |  TApp :: g:Env -> e:Expr -> x:Vname -> t_x:Type -> t:Type
                -> ProofOf(HasType g e (TFunc x t_x t)) 
                -> e':Expr -> ProofOf(HasType g e' t_x) 
                -> ProofOf(HasType g (App e e') (TExists x t_x t))
 |  TLet :: g:Env -> e_x:Expr -> t_x:Type -> ProofOf(HasType g e_x t_x)
                -> x:Vname -> e:Expr -> t:Type 
                -> ProofOf(HasType (g ++ (x,t_x)) e t)
                -> ProofOf(HasType g (Let x e_x e) t)
 |  TAnn :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
                -> ProofOf(HasType g (Annot e t) t)
 |  TSub :: g:Env -> e:Expr -> s:Type -> ProofOf(HasType g e s) -> t:Type
                -> ProofOf(Subtype g s t) -> ProofOf(HasType g e t) @-} -- @-}

data SubtypeP where
    Subtype :: Env -> Type -> Type -> Subtype

data Subtype where
    SBase :: Env -> Vname -> Base -> Pred -> Vname -> Pred -> Entails -> Subtype
    SFunc :: Env -> Vname -> Type -> Vname -> Type -> Subtype
               -> Type -> Type -> Subtype -> Subtype
    -- TODO: Is this the form of [S-WITN] that we need?
    SWitn :: Env -> Vname -> Type -> HasType -> Type -> Vname -> Type
               -> Subtype -> Subtype
    SBind :: Env -> Vname -> Type -> Type -> Type -> Subtype -> Subtype

{-@ data Subtype where
    SBase :: g:Env -> v1:Vname -> b:Base -> p1:Pred -> v2:Vname -> p2:Pred
               -> ProofOf(Entails (g ++ (v1, TRefn b v1 p)) (bsubst v2 v1 p2))
               -> ProofOf(Subtype g (TRefn b v1 p1) (TRefn b v2 p2))
 |  SFunc :: g:Env -> x1:Vname -> s1:Type -> x2:Vname -> s2:Type
               -> ProofOf(Subtype g s2 s1) -> t1:Type -> t2:Type
               -> ProofOf(Subtype (g ++ (x2,s2)) (subst x1 x2 t1) t2)
 |  SWitn :: g:Env -> y:Vname -> t_x:Type -> ProofOf(HasType g y t_x) -> t:Type 
               -> x:Vname -> t':Type -> ProofOf(Subtype g t (tsubst x y t'))
               -> ProofOf(Subtype g t (TExists x t_x t'))
 |  SBind :: g:Env -> x:Vname -> t_x:Type -> ProofOf(HasType g x t_x) -> t:Type
               -> { t':Type | not S.elem x (free t') } 
               -> ProofOf(Subtype (g ++ (x,t_x)) t t')
               -> ProofOf(Subtype g (TExists x t_x t) t')
@-}

--TODO: How do I add ENT-EMP: |- c if SMTValid(c) ?
data EntailsP where
    Entails :: Env -> Form -> EntailsP

data Entails where
    -- EntEmp ::
    EntExt :: Env -> Vname -> Base -> Pred -> Form -> Entails -> Entails

{-@ data Entails where
    EntExt :: g:Env -> v:Vname -> b:Base -> p:Pred -> c:Form
               -> ProofOf(Entails g (Impl v b p c))
               -> ProofOf(Entails (g ++ (x, TRefn b v p)) c)  @-}

data DenotesP where 
    Denotes :: Type -> Expr -> DenotesP    -- e \in [[t]]

data Denotes where
    DBase :: Base -> Expr -> HasBType -> Denotes
    DRefn :: Base -> Vname -> Pred -> Expr -> HasBType 
              -> (Int -> EvalsTo -> BEvalsTo) -> Denotes
    DFunc :: Vname -> Type -> Type -> Expr -> HasBType
              -> (Expr -> Denotes -> Denotes) -> Denotes
    DExis :: Vname -> Type -> Type -> Expr -> HasBType
              -> Expr -> Denotes -> Denotes -> Denotes
{-@ data Denotes where
    DBase :: b:Base -> e:Expr -> ProofOf(HasBType [] e b) 
              -> ProofOf(Denotes (TBase b) e)
  | DRefn :: b:Base -> x:Vname -> p:Pred -> e:Expr -> ProofOf(HasBType [] e b)
              -> (v:Int -> ProofOf(EvalsTo e (C v)) 
                        -> ProofOf(BEvalsTo (bsubstc x v p) (Bc True)) )
              -> ProofOf(Denotes (TRefn b x p) e)
  | DFunc :: x:Vname -> t_x:Type -> t:Type -> e:Expr 
              -> ProofOf(HasBType [] e (erase (TFunc x t_x t)))
              -> ({ v:Expr | isValue v } -> ProofOf(Denotes t_x v)
                        -> ProofOf(Denotes (tsubst x v t) (App e v)) )
              -> ProofOf(Denotes (TFunc x t_x t) e)
  | DExis :: x:Vname -> t_x:Type -> t:Type -> e:Expr 
              -> ProofOf(HasBType [] e (erase t)) 
              -> { v:Expr | isValue v } -> ProofOf(Denotes t_x v)
              -> ProofOf(Denotes (tsubst x v t) e)
              -> ProofOf(Denotes (TExists x t_x t) e)  @-} 

-- TODO: Still need closing substitutions
-- TODO: Still need denotations of environments

-- Lemma 1 in the Pen and Paper version (Preservation of Denotations)
-- If e ->* e' then e in [[t]] iff e' in [[t]]
{-@ lemma1_fwd :: e:Expr -> e':Expr -> ProofOf(EvalsTo e e') -> t:Type
                   -> ProofOf(Denotes t e) -> ProofOf(Denotes t e') @-}
lemma1_fwd :: Expr -> Expr -> EvalsTo -> Type -> Denotes -> Denotes
lemma1_fwd e e' p_ee' (TBase b) (DBase _b _e p_eb) = DBase b e p_e'b
  where 
    p_e'b              = lemma_soundness e e' p_ee' b p_eb
lemma1_fwd e e' p_ee' (TRefn b x p) (DRefn _b _x _p _e p_eb predicate) = den_te'
  where
    den_te'            = DRefn b x p e' p_e'b predicate'
    p_e'b              = lemma_soundness e e' p_ee' b p_eb
    predicate' v p_e'v = predicate v (lemma_evals_trans e e' v p_ee' e_e'v)
lemma1_fwd e e' p_ee' (TFunc x t_x t) (DFunc _x _tx _t _e p_ebt app_den) = den_te'
  where
    den_te'          = DFunc x t_x t e' p_e'bt app_den'
    p_e'bt           = lemma_soundness e e' p_ee' (erase (TFunc x t_x t))
    app_den' v d_txv = lemma1_fwd (App e v) (App e' v) p_ev_e'v (tsubst x v t) dtev
    p_ev_e'v         = (lemma_app_many e e' v p_ee')
    dtev             = app_den v d_txv 
lemma1_fwd e e' p_ee' (TExists x t_x t) (DExis _x _tx _t _e p_ebt v d_txv d_te) = d_te'
  where
    d_te'     = DExis x t_x t e' p_e'bt v d_txv den_te'
    p_e'bt    = lemma_soundness e e' p_ee' (erase (TExists x t_x t))
    den_te'   = lemma1_fwd e e' p_ee' (tsubst x v t) d_te

{-@ lemma1_bck :: e:Expr -> e':Expr -> ProofOf(EvalsTo e e') -> t:Type
                   -> ProofOf(Denotes t e') -> ProofOf(Denotes t e) @-}
lemma1_bck :: Expr -> Expr -> EvalsTo -> Type -> Denotes -> Denotes
lemma1_bck = undefined
