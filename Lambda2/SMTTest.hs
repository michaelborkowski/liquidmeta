{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SMTTest where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)

{-@ measure propOf :: a -> b @-}
{-@ type ProofOf E = { proofObj:_ | propOf proofObj = E } @-}

---------------------------------------------------------------------------
----- | TERMS of our language
---------------------------------------------------------------------------
type Vname = Int

{-@ data Expr [esize] @-}
data Expr = Bc Bool                   -- True, False
          | Ic Int                    -- 0, 1, 2, ...
          | Lambda Vname Expr         -- \x.e          abstractions
          | App Expr Expr             -- e e'          applications
  deriving (Eq, Show)

{-@ lazy esize @-}
{-@ measure esize @-}
{-@ esize :: e:Expr -> { v:Int | v >= 0 } @-}
esize :: Expr -> Int
esize (Bc _)	        = 1
esize (Ic _)		= 1
esize (Lambda x e)      = (esize e)   + 1
esize (App e e')        = (esize e)   + (esize e') + 1

{-@ type Value = { v:Expr | isValue v } @-}

{-@ reflect isValue @-} -- meaning: is a syntactic value
isValue :: Expr -> Bool
isValue (Bc _)          = True
isValue (Ic _)          = True
isValue (Lambda x e)    = True --     well-formed as expressions
isValue _               = False

type Pred = Expr -- refinements are arbitrary expresions with base type Bool

  ---   TYPES

data Basic = TBool         -- Bool
           | TInt          -- Int
  deriving (Eq, Show)

data Kind = Base         -- B, base kind
          | Star         -- *, star kind
  deriving (Eq, Show)

data FType = FTBasic Basic               -- b
  deriving (Eq, Show)

  --- BARE-TYPING ENVIRONMENTS

data FEnv = FEmpty                       -- type FEnv = [(Vname, FType) or Vname]
          | FCons  Vname FType FEnv
          | FConsT Vname Kind  FEnv
  deriving (Show) 
{-@ data FEnv where
    FEmpty :: FEnv
  | FCons  :: x:Vname -> t:FType -> g:FEnv  -> FEnv 
  | FConsT :: x:Vname -> k:Kind  -> g:FEnv  -> FEnv @-} -- @-}

--------------------------------------------------------------------------
----- | OPERATIONAL SEMANTICS (Small Step)
--------------------------------------------------------------------------

data StepP where
    Step :: Expr -> Expr -> StepP

data Step where
    EFake :: Vname -> Expr -> Expr -> Step
    EApp1 :: Expr -> Expr -> Step -> Expr -> Step
    EApp2 :: Expr -> Expr -> Step -> Expr -> Step

{-@ data Step where 
    EFake :: x:Vname -> e:Expr -> v:Value -> ProofOf( Step (App (Lambda x e) v) e)
 |  EApp1 :: e:Expr -> e':Expr -> ProofOf( Step e e' ) 
                 -> e1:Expr -> ProofOf( Step (App e e1) (App e' e1))
 |  EApp2 :: e:Expr -> e':Expr -> ProofOf( Step e e' )
                 -> v:Value -> ProofOf( Step (App v e) (App v e')) @-} -- @-}

data EvalsToP where
    EvalsTo :: Expr -> Expr -> EvalsToP

data EvalsTo where
    Refl     :: Expr -> EvalsTo
    AddStep  :: Expr -> Expr -> Step -> Expr -> EvalsTo -> EvalsTo
{-@ data EvalsTo where 
    Refl     :: e:Expr -> ProofOf ( EvalsTo e e )
 |  AddStep  :: e1:Expr -> e2:Expr -> ProofOf( Step e1 e2 ) -> e3:Expr
               -> ProofOf ( EvalsTo e2 e3 ) -> ProofOf( EvalsTo e1 e3 ) @-} -- @-} 
