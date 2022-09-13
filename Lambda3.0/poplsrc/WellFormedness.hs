{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module WellFormedness where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import SystemFWellFormedness
import SystemFTyping

-----------------------------------------------------------------------------
----- | JUDGEMENTS : WELL-FORMEDNESS of TYPES and ENVIRONMENTS
-----------------------------------------------------------------------------

  --- Well-Formedness of Types

data WFType where 
    WFBase :: Env -> Basic -> WFType
    WFRefn :: Env -> Basic -> WFType -> Preds -> Names -> (Vname -> PHasFType) -> WFType
    WFVar1 :: Env -> Vname -> Kind -> WFType
    WFVar2 :: Env -> Vname -> Kind -> WFType -> Vname -> Type -> WFType
    WFVar3 :: Env -> Vname -> Kind -> WFType -> Vname -> Kind -> WFType
    WFFunc :: Env ->  Type -> Kind -> WFType -> Type -> Kind -> Names -> (Vname -> WFType) -> WFType
    WFExis :: Env ->  Type -> Kind -> WFType -> Type -> Kind -> Names -> (Vname -> WFType) -> WFType
    WFPoly :: Env ->  Kind -> Type -> Kind   -> Names -> (Vname -> WFType) -> WFType
    WFKind :: Env -> Type -> WFType -> WFType

{-@ data WFType where
        WFBase :: g:Env -> { b:Basic | b == TBool || b == TInt } 
                        -> ProofOf(WFType g (TRefn b PEmpty) Base)
        WFRefn :: g:Env -> b:Basic -> ProofOf(WFType g (TRefn b PEmpty) Base) 
          -> { ps:Preds | not (ps == PEmpty) } -> nms:Names
          -> ( { y:Vname | NotElem y nms }
                 -> ProofOf(PHasFType (FCons y (FTBasic b) (erase_env g)) (unbindP y ps)) )
          -> ProofOf(WFType g (TRefn b ps) Base)
        WFVar1 :: g:Env -> { a:Vname | not (in_env a g) } -> k:Kind 
          -> ProofOf(WFType (ConsT a k g) (TRefn (FTV a) PEmpty) k)
        WFVar2 :: g:Env -> { a:Vname |      in_env a g }  -> k:Kind 
          -> ProofOf(WFType g (TRefn (FTV a) PEmpty) k) 
          -> { y:Vname | y != a && not (in_env y g) } -> t:Type 
          -> ProofOf(WFType (Cons y t g)  (TRefn (FTV a) PEmpty) k)
        WFVar3 :: g:Env -> { a:Vname |      in_env a g }  -> k:Kind 
          -> ProofOf(WFType g (TRefn (FTV a) PEmpty) k) 
          -> { a':Vname | a' != a && not (in_env a' g) } -> k':Kind 
          -> ProofOf(WFType (ConsT a' k' g) (TRefn (FTV a) PEmpty) k)
        WFFunc :: g:Env -> t_x:Type -> k_x:Kind -> ProofOf(WFType g t_x k_x) -> t:Type -> k:Kind -> nms:Names 
          -> ({ y:Vname | NotElem y nms } -> ProofOf(WFType (Cons y t_x g) (unbindT y t) k) )
          -> ProofOf(WFType g (TFunc t_x t) Star)
        WFExis :: g:Env -> t_x:Type -> k_x:Kind -> ProofOf(WFType g t_x k_x) -> t:Type -> k:Kind -> nms:Names 
          -> ({ y:Vname | NotElem y nms } -> ProofOf(WFType (Cons y t_x g) (unbindT y t) k) )
          -> ProofOf(WFType g (TExists t_x t) k) 
        WFPoly :: g:Env -> k:Kind -> t:Type -> k_t:Kind -> nms:Names
          -> ({ a':Vname | NotElem a' nms } -> ProofOf(WFType (ConsT a' k g) (unbind_tvT a' t) k_t) )
          -> ProofOf(WFType g (TPoly k t) Star) 
        WFKind :: g:Env -> t:Type -> ProofOf(WFType g t Base) -> ProofOf(WFType g t Star) @-}

{-@ reflect isWFBase @-}
isWFBase :: WFType -> Bool
isWFBase (WFBase {}) = True
isWFBase _           = False

{-@ reflect isWFRefn @-}
isWFRefn :: WFType -> Bool
isWFRefn (WFRefn {}) = True
isWFRefn _           = False

{-@ reflect isWFVar @-}
isWFVar :: WFType -> Bool
isWFVar (WFVar1 {}) = True
isWFVar (WFVar2 {}) = True
isWFVar (WFVar3 {}) = True
isWFVar _           = False

{-@ reflect isWFVar1 @-}
isWFVar1 :: WFType -> Bool
isWFVar1 (WFVar1 {}) = True
isWFVar1 _           = False

{-@ reflect isWFVar2 @-}
isWFVar2 :: WFType -> Bool
isWFVar2 (WFVar2 {}) = True
isWFVar2 _           = False

{-@ reflect isWFVar3 @-}
isWFVar3 :: WFType -> Bool
isWFVar3 (WFVar3 {}) = True
isWFVar3 _           = False

{-@ reflect isWFFunc @-}
isWFFunc :: WFType -> Bool
isWFFunc (WFFunc {}) = True
isWFFunc _           = False

{-@ reflect isWFExis @-}
isWFExis :: WFType -> Bool
isWFExis (WFExis {}) = True
isWFExis _           = False

{-@ reflect isWFPoly @-}
isWFPoly :: WFType -> Bool
isWFPoly (WFPoly {}) = True
isWFPoly _           = False

{-@ reflect isWFKind @-}
isWFKind :: WFType -> Bool
isWFKind (WFKind {}) = True
isWFKind _           = False

{-@ simpleWFVar :: g:Env -> { a:Vname | in_env a g } 
        -> { k:Kind | tv_bound_in a k g } -> ProofOf(WFType g (TRefn (FTV a) PEmpty) k) @-}
simpleWFVar :: Env -> Vname -> Kind -> WFType
simpleWFVar g a k  = case g of
  (Cons y s g')    -> case ( a == y ) of   -- g = Empty is impossible
        (False)    -> WFVar2 g' a k (simpleWFVar g' a k) y s
  (ConsT a' k' g') -> case ( a == a' ) of
        (True)     -> WFVar1 g' a k      
        (False)    -> WFVar3 g' a k (simpleWFVar g' a k) a' k'

  --- Well-formedness of Environments

data WFEnv where
    WFEEmpty :: WFEnv
    WFEBind  :: Env -> WFEnv -> Vname -> Type -> Kind -> WFType -> WFEnv
    WFEBindT :: Env -> WFEnv -> Vname -> Kind -> WFEnv

{-@ data WFEnv where
        WFEEmpty :: ProofOf(WFEnv Empty)
        WFEBind  :: g:Env -> ProofOf(WFEnv g) -> { x:Vname | not (in_env x g) } -> t:Type 
                     -> k:Kind -> ProofOf(WFType g t k) -> ProofOf(WFEnv (Cons x t g)) 
        WFEBindT :: g:Env -> ProofOf(WFEnv g) -> { a:Vname | not (in_env a g) } -> k:Kind 
                                                        -> ProofOf(WFEnv (ConsT a k g)) @-}
