{-# LANGUAGE GADTs #-}

{-@ LIQUID "--counter-examples" @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--short-names" @-}

module STLC where

import qualified Data.Set as S

---------------------------------------------------------------------------
----- | PRELIMINARIES
---------------------------------------------------------------------------

{-@ measure prop :: a -> b @-}
{-@ type ProofOf E = { v:_ | prop v = E } @-}

type Proof = ()

--TODO: will classes and instances make anything easier or harder?
--class HasVars a where
--    free  :: a -> S.Set Vname
--    subst :: Vname -> 

---------------------------------------------------------------------------
----- | TERMS of our language
---------------------------------------------------------------------------
  ---   Refinement Level: Names, Terms (in FO), FO Predicates, SMT Formulae

type Vname = String

data Term = Ic Int                    -- 0, 1, ...
          | Iv Vname                  -- x, y, z; interpreted over Z
  deriving (Show)

data Pred = Bc Bool                   -- True, False
          | And Pred Pred
          | Or Pred Pred
          | Not Pred
          | Leq Term Term
          | Eq Term Term
          -- and uninterpreted functions?
          -- and anything else eneeded? don't seem to need Boolean vars
  deriving (Show)

data Form = P Pred                    -- p
          | FAnd Form Form            -- c1 ^ c2
          | Impl Vname Base Pred Form -- \forall x:b. p => c
  deriving (Show)

{-@ reflect isTermValue @-}
isTermValue :: Term -> Bool
isTermValue (Ic _) = True
isTermValue _      = False

{-@ reflect vars @-}
vars :: Term -> S.Set Vname
vars (Iv x) = S.singleton x
vars _      = S.empty

{-@ reflect fv @-}
fv :: Pred -> S.Set Vname
fv (Bc _)      = S.empty
fv (And p1 p2) = S.union (fv p1) (fv p2)
fv (Or p1 p2)  = S.union (fv p1) (fv p2)
fv (Not p1)    = fv p1
fv (Leq t1 t2) = S.union (vars t1) (vars t2)
fv (Eq  t1 t2) = S.union (vars t1) (vars t2)

{-@ reflect bval @-} -- only defined if no free vars
{-@ bval :: { p:Pred | fv p = S.empty } -> Bool @-}
bval :: Pred -> Bool
bval (Bc b)                = b
bval (And p1 p2)           = (bval p1) && (bval p2)
bval (Or  p1 p2)           = (bval p1) || (bval p2)
bval (Not p1)              = not (bval p1)
bval (Leq (Ic n1) (Ic n2)) = n1 <= n2
bval (Eq  (Ic n1) (Ic n2)) = n1 == n2

{-@ reflect bsubst @-}
bsubst :: Vname -> Term -> Pred -> Pred
bsubst x t (Bc b)             = Bc b
bsubst x t (And p1 p2)        = And (bsubst x t p1) (bsubst x t p2)
bsubst x t (Or p1 p2)         = Or  (bsubst x t p1) (bsubst x t p2)
bsubst x t (Not p)            = Not (bsubst x t p)
bsubst x t (Leq t1 t2)        = Leq (tmsubst x t t1) (tmsubst x t t2)
bsubst x t (Eq  t1 t2)        = Eq  (tmsubst x t t1) (tmsubst x t t2)

{-@ reflect tmsubst @-}
tmsubst :: Vname -> Term -> Term -> Term
tmsubst x (Iv y) (Iv z) | z == x    = Iv y
                        | otherwise = Iv z
tmsubst x (Ic n) (Iv z)             = Ic n
tmsubst x _      (Ic c)             = Ic c

-- TODO: do i need BEvalsTo in addition to just bval?
  
  ---   Term level expressions 

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
subst x v (Lambda y e)       = Lambda y (subst x v e)
subst x v (App e v')         = App (subst x v e) (subst x v v')
subst x v (Let y e1 e2)      = Let y (subst x v e1) (subst x v e2)
subst x v (Annot e t)        = Annot (subst x v e) t

  ---   TYPES

data Base = TInt
  deriving (Show)

data Type = TBase   Base                 -- b
          | TRefn   Base Vname Pred      -- b{v : r}
          | TFunc   Vname Type Type      -- x:t_x -> t
          | TExists Vname Type Type      -- \exists x:t_x.t
  deriving (Show)

data Env = Empty                         -- type Env = [(Vname, Type)]	
         | Cons Vname Type Env
  deriving (Show)

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
tsize (TFunc x t_x t)   = (tsize t) + 1
tsize (TExists x t_x t) = (tsize t) + 1

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
{-@ tsubst :: Vname -> { v:Expr | isValue v } -> t:Type  
                    -> { t':Type | tsize t' <= tsize t && tsize t' >= 0 } @-}
tsubst :: Vname -> Expr -> Type -> Type
tsubst x _ (TBase b)         = TBase b
tsubst x (C n) (TRefn b v r) = TRefn b v (bsubst x (Ic n) r)
tsubst x (V y) (TRefn b v r) = TRefn b v (bsubst x (Iv y) r)
tsubst x _     (TRefn b v r) = TRefn b v r
tsubst x v (TFunc z t_z t)   = TFunc z (tsubst x v t_z) (tsubst x v t)
tsubst x v (TExists z t_z t) = TExists z (tsubst x v t_z) (tsubst x v t)

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

data BEvalsToP where
    BEvalsTo :: Pred -> Pred -> BEvalsToP

data BEvalsTo where
    BvalTo :: Pred -> BEvalsTo
{-@ data BEvalsTo where
    BvalTo :: { p:Pred | bval p } -> ProofOf( BEvalsTo p (Bc True)) @-}

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
                -> ProofOf(HasType (Cons x t_x g) e t)
                -> ProofOf(HasType g (Lambda x e) (TFunc x t_x t))
 |  TApp :: g:Env -> e:Expr -> x:Vname -> t_x:Type -> t:Type
                -> ProofOf(HasType g e (TFunc x t_x t)) 
                -> e':Expr -> ProofOf(HasType g e' t_x) 
                -> ProofOf(HasType g (App e e') (TExists x t_x t))
 |  TLet :: g:Env -> e_x:Expr -> t_x:Type -> ProofOf(HasType g e_x t_x)
                -> x:Vname -> e:Expr -> t:Type 
                -> ProofOf(HasType (Cons x t_x g) e t)
                -> ProofOf(HasType g (Let x e_x e) t)
 |  TAnn :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
                -> ProofOf(HasType g (Annot e t) t)
 |  TSub :: g:Env -> e:Expr -> s:Type -> ProofOf(HasType g e s) -> t:Type
                -> ProofOf(Subtype g s t) -> ProofOf(HasType g e t) @-} -- @-}

data SubtypeP where
    Subtype :: Env -> Type -> Type -> SubtypeP

data Subtype where
    SBase :: Env -> Vname -> Base -> Pred -> Vname -> Pred -> Entails -> Subtype
    SFunc :: Env -> Vname -> Type -> Vname -> Type -> Subtype
               -> Type -> Type -> Subtype -> Subtype
    -- TODO: Is this the form of [S-WITN] that we need?
    SWitn :: Env -> Vname -> Type -> HasType -> Type -> Vname -> Type
               -> Subtype -> Subtype
    SBind :: Env -> Vname -> Type -> HasType -> Type -> Type -> Subtype -> Subtype

{-@ data Subtype where
    SBase :: g:Env -> v1:Vname -> b:Base -> p1:Pred -> v2:Vname -> p2:Pred
               -> ProofOf(Entails ( Cons v1 (TRefn b v1 p1) g) (bsubst v2 (Iv v1) p2))
               -> ProofOf(Subtype g (TRefn b v1 p1) (TRefn b v2 p2))
 |  SFunc :: g:Env -> x1:Vname -> s1:Type -> x2:Vname -> s2:Type
               -> ProofOf(Subtype g s2 s1) -> t1:Type -> t2:Type
               -> ProofOf(Subtype (Cons x2 s2 g) (tsubst x1 x2 t1) t2)
               -> ProofOf(Subtype g (TFunc x1 s1 t1) (TFunc x2 s2 t2))
 |  SWitn :: g:Env -> y:Vname -> t_x:Type -> ProofOf(HasType g y t_x) -> t:Type 
               -> x:Vname -> t':Type -> ProofOf(Subtype g t (tsubst x y t'))
               -> ProofOf(Subtype g t (TExists x t_x t'))
 |  SBind :: g:Env -> x:Vname -> t_x:Type -> ProofOf(HasType g x t_x) -> t:Type
               -> { t':Type | not S.elem x (free t') } 
               -> ProofOf(Subtype (Cons x t_x g) t t')
               -> ProofOf(Subtype g (TExists x t_x t) t')
@-}

data SMTValidP where --dummy SMT Validity certificates
    SMTValid :: Form -> SMTValidP

data SMTValid where
    SMTProp :: Pred -> SMTValid
{-@ data SMTValid where
    SMTProp :: { p:Pred | fv p == S.empty && bval p } -> ProofOf(SMTValid (P p)) @-}

data EntailsP where
    Entails :: Env -> Form -> EntailsP

data Entails where
    EntEmp :: Form -> SMTValid -> Entails
    EntExt :: Env -> Vname -> Base -> Pred -> Form -> Entails -> Entails

{-@ data Entails where
    EntEmp :: c:Form -> ProofOf(SMTValid c) -> ProofOf(Entails BEmpty c)
 |  EntExt :: g:Env -> v:Vname -> b:Base -> p:Pred -> c:Form
               -> ProofOf(Entails g (Impl v b p c))
               -> ProofOf(Entails (Cons x (TRefn b v p) g) c)  @-} -- @-}

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
    DBase :: b:Base -> e:Expr -> ProofOf(HasBType BEmpty e (BTBase b)) 
              -> ProofOf(Denotes (TBase b) e)
  | DRefn :: b:Base -> x:Vname -> p:Pred -> e:Expr 
              -> ProofOf(HasBType BEmpty e (BTBase b))
              -> (v':Int -> ProofOf(EvalsTo e (C v')) 
                        -> ProofOf(BEvalsTo (bsubst x (Ic v') p) (Bc True))) 
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

-- old version of DRefn, in case I want to bring back BEvalsTo
-- | DRefn :: b:Base -> x:Vname -> p:Pred -> e:Expr -> ProofOf(HasBType [] e b)
--              -> (v:Int -> ProofOf(EvalsTo e (C v)) 
--                        -> ProofOf(BEvalsTo (bsubst x (Ic v) p) (Bc True)) )
--              -> ProofOf(Denotes (TRefn b x p) e)

-- TODO: Still need closing substitutions
-- TODO: Still need denotations of environments

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
    {-@ predicate2 :: w:Int -> ProofOf(EvalsTo e' (C w))
                            -> ProofOf( BEvalsTo (bsubst x (Ic w) p) (Bc True)) @-}
    predicate2 :: Int -> EvalsTo -> BEvalsTo
    predicate2 v p_e'v = predicate v (lemma_evals_trans e e' (C v) p_ee' p_e'v)
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

{-@ lemma1_bck :: e:Expr -> e':Expr -> ProofOf(EvalsTo e e') -> t:Type
                   -> ProofOf(Denotes t e') -> ProofOf(Denotes t e) @-}
lemma1_bck :: Expr -> Expr -> EvalsTo -> Type -> Denotes -> Denotes
lemma1_bck = undefined
