{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-}  
{-@ LIQUID "--no-totality" @-}      -- TODO: assume
{-@ LIQUID "--reflection"  @-}
{- @ LIQUID "--ple-local"         @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--short-names" @-}

module PLETest2 where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)

import Basics

semantics = (Step, EvalsTo)
typing = (TInt, TBool)

-----------------------------------------------------------------------------
----- | JUDGEMENTS : the Bare-Typing Relation
-----------------------------------------------------------------------------

data HasFTypeP where
    HasFType :: FEnv -> Expr -> FType -> HasFTypeP 

data HasFType where
    FTBC   :: FEnv -> Bool -> HasFType
    FTIC   :: FEnv -> Int -> HasFType

{-@ data HasFType where
    FTBC   :: g:FEnv -> b:Bool -> ProofOf(HasFType g (Bc b) (FTBasic TBool))
 |  FTIC   :: g:FEnv -> n:Int -> ProofOf(HasFType g (Ic n) (FTBasic TInt)) @-}
 
{-@ measure ftypSize @-}
{-@ ftypSize :: HasFType -> { v:Int | v >= 0 } @-}
ftypSize :: HasFType -> Int
ftypSize (FTBC {})                           = 1
ftypSize (FTIC {})                           = 1

