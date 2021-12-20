{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LocalClosure where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics

--------------------------------------------------------------------------------
----- | JUDGMENTS : Local Closure of Locally Nameless Terms
--------------------------------------------------------------------------------

data LCExpr where
    LCBC   :: Bool  -> LCExpr
    LCIC   :: Int   -> LCExpr
    LCVar  :: Vname -> LCExpr
    LCPrm  :: Prim  -> LCExpr
    LCAbs  :: Expr  -> Names  -> (Vname -> LCExpr) -> LCExpr
    LCApp  :: Expr  -> LCExpr -> Expr -> LCExpr -> LCExpr
    LCAbsT :: Kind  -> Expr   -> Names -> (Vname -> LCExpr) -> LCExpr
    LCAppT :: Expr  -> LCExpr -> Type -> LCType -> LCExpr
    LCLet  :: Expr  -> LCExpr -> Expr -> Names -> (Vname -> LCExpr) -> LCExpr
    LCAnn  :: Expr  -> LCExpr -> Type -> LCType -> LCExpr

{-@ data LCExpr where 
        LCBC   :: b:Bool  -> ProofOf(LCExpr (Bc b))
        LCIC   :: n:Int   -> ProofOf(LCExpr (Ic n))
        LCVar  :: x:Vname -> ProofOf(LCExpr (FV x))
        LCPrm  :: c:Prim  -> ProofOf(LCExpr (Prim c))
        LCAbs  :: e:Expr  -> nms:Names 
                    -> ( { y:Vname | not (Set_mem y nms) } -> ProofOf(LCExpr (unbind y e)) )
                    -> ProofOf(LCExpr (Lambda e))
        LCApp  :: e:Expr  -> ProofOf(LCExpr e) -> e':Expr -> ProofOf(LCExpr e') 
                    -> ProofOf(LCExpr (App e e'))
        LCAbsT :: k:Kind  -> e:Expr -> nms:Names 
                    -> ( { a:Vname | not (Set_mem a nms) } -> ProofOf(LCExpr (unbind_tv a e)) )
                    -> ProofOf(LCExpr (LambdaT k e))
        LCAppT :: e:Expr  -> ProofOf(LCExpr e) -> t:UserType -> ProofOf(LCType t)
                    -> ProofOf(LCExpr (AppT e t))
        LCLet  :: e_x:Expr -> ProofOf(LCExpr e_x) -> e:Expr -> nms:Names
                    -> ( { y:Vname | not (Set_mem y nms) } -> ProofOf(LCExpr (unbind y e)) )
                    -> ProofOf(LCExpr (Let e_x e))
        LCAnn  :: e:Expr  -> ProofOf(LCExpr e) -> t:Type -> ProofOf(LCType t)
                    -> ProofOf(LCExpr (Annot e t)) @-}

data LCPreds where
    LCPEmp  :: LCPreds
    LCPCons :: Expr -> LCExpr -> Preds -> LCPreds -> LCPreds

{-@ data LCPreds where
    LCPEmp  :: ProofOf(LCPreds PEmpty)
    LCPCons :: p:Expr -> ProofOf(LCExpr p) -> ps:Preds -> ProofOf(LCPreds ps)
                 -> ProofOf(LCPreds (PCons p ps)) @-}

data LCType where 
    LCRefn :: Basic -> Preds -> Names -> (Vname -> LCPreds) -> LCType
    LCFunc :: Type  -> LCType -> Type -> Names -> (Vname -> LCType) -> LCType
    LCExis :: Type  -> LCType -> Type -> Names -> (Vname -> LCType) -> LCType
    LCPoly :: Kind  -> Type  -> Names -> (Vname -> LCType) -> LCType


