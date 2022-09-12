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

  --- Well-Formedness of types

data WFtype where 
    WFBase :: env -> Basic -> WFtype
    WFRefn :: env -> Basic -> WFtype -> preds -> names -> (vname -> PHasFtype) -> WFtype
    WFVar1 :: env -> vname -> kind -> WFtype
    WFVar2 :: env -> vname -> kind -> WFtype -> vname -> type -> WFtype
    WFVar3 :: env -> vname -> kind -> WFtype -> vname -> kind -> WFtype
    WFFunc :: env ->  type -> kind -> WFtype -> type -> kind -> names -> (vname -> WFtype) -> WFtype
    WFExis :: env ->  type -> kind -> WFtype -> type -> kind -> names -> (vname -> WFtype) -> WFtype
    WFPoly :: env ->  kind -> type -> kind   -> names -> (vname -> WFtype) -> WFtype
    WFKind :: env -> type -> WFtype -> WFtype

{-@ data WFtype where
        WFBase :: g:env -> { b:Basic | b == TBool || b == TInt } 
                        -> ProofOf(WFtype g (TRefn b PEmpty) Base)
        WFRefn :: g:env -> b:Basic -> ProofOf(WFtype g (TRefn b PEmpty) Base) 
          -> { ps:preds | not (ps == PEmpty) } -> nms:names
          -> ( { y:vname | NotElem y nms }
                 -> ProofOf(PHasFtype (FCons y (FTBasic b) (erase_env g)) (unbindP y ps)) )
          -> ProofOf(WFtype g (TRefn b ps) Base)
        WFVar1 :: g:env -> { a:vname | not (in_env a g) } -> k:kind 
          -> ProofOf(WFtype (ConsT a k g) (TRefn (FTV a) PEmpty) k)
        WFVar2 :: g:env -> { a:vname |      in_env a g }  -> k:kind 
          -> ProofOf(WFtype g (TRefn (FTV a) PEmpty) k) 
          -> { y:vname | y != a && not (in_env y g) } -> t:type 
          -> ProofOf(WFtype (Cons y t g)  (TRefn (FTV a) PEmpty) k)
        WFVar3 :: g:env -> { a:vname |      in_env a g }  -> k:kind 
          -> ProofOf(WFtype g (TRefn (FTV a) PEmpty) k) 
          -> { a':vname | a' != a && not (in_env a' g) } -> k':kind 
          -> ProofOf(WFtype (ConsT a' k' g) (TRefn (FTV a) PEmpty) k)
        WFFunc :: g:env -> t_x:type -> k_x:kind -> ProofOf(WFtype g t_x k_x) -> t:type -> k:kind -> nms:names 
          -> ({ y:vname | NotElem y nms } -> ProofOf(WFtype (Cons y t_x g) (unbindT y t) k) )
          -> ProofOf(WFtype g (TFunc t_x t) Star)
        WFExis :: g:env -> t_x:type -> k_x:kind -> ProofOf(WFtype g t_x k_x) -> t:type -> k:kind -> nms:names 
          -> ({ y:vname | NotElem y nms } -> ProofOf(WFtype (Cons y t_x g) (unbindT y t) k) )
          -> ProofOf(WFtype g (TExists t_x t) k) 
        WFPoly :: g:env -> k:kind -> t:type -> k_t:kind -> nms:names
          -> ({ a':vname | NotElem a' nms } -> ProofOf(WFtype (ConsT a' k g) (unbind_tvT a' t) k_t) )
          -> ProofOf(WFtype g (TPoly k t) Star) 
        WFKind :: g:env -> t:type -> ProofOf(WFtype g t Base) -> ProofOf(WFtype g t Star) @-}

{-@ reflect isWFBase @-}
isWFBase :: WFtype -> Bool
isWFBase (WFBase {}) = True
isWFBase _           = False

{-@ reflect isWFRefn @-}
isWFRefn :: WFtype -> Bool
isWFRefn (WFRefn {}) = True
isWFRefn _           = False

{-@ reflect isWFVar @-}
isWFVar :: WFtype -> Bool
isWFVar (WFVar1 {}) = True
isWFVar (WFVar2 {}) = True
isWFVar (WFVar3 {}) = True
isWFVar _           = False

{-@ reflect isWFVar1 @-}
isWFVar1 :: WFtype -> Bool
isWFVar1 (WFVar1 {}) = True
isWFVar1 _           = False

{-@ reflect isWFVar2 @-}
isWFVar2 :: WFtype -> Bool
isWFVar2 (WFVar2 {}) = True
isWFVar2 _           = False

{-@ reflect isWFVar3 @-}
isWFVar3 :: WFtype -> Bool
isWFVar3 (WFVar3 {}) = True
isWFVar3 _           = False

{-@ reflect isWFFunc @-}
isWFFunc :: WFtype -> Bool
isWFFunc (WFFunc {}) = True
isWFFunc _           = False

{-@ reflect isWFExis @-}
isWFExis :: WFtype -> Bool
isWFExis (WFExis {}) = True
isWFExis _           = False

{-@ reflect isWFPoly @-}
isWFPoly :: WFtype -> Bool
isWFPoly (WFPoly {}) = True
isWFPoly _           = False

{-@ reflect isWFKind @-}
isWFKind :: WFtype -> Bool
isWFKind (WFKind {}) = True
isWFKind _           = False

{-@ simpleWFVar :: g:env -> { a:vname | in_env a g } 
        -> { k:kind | tv_bound_in a k g } -> ProofOf(WFtype g (TRefn (FTV a) PEmpty) k) @-}
simpleWFVar :: env -> vname -> kind -> WFtype
simpleWFVar g a k  = case g of
  (Cons y s g')    -> case ( a == y ) of   -- g = Empty is impossible
        (False)    -> WFVar2 g' a k (simpleWFVar g' a k) y s
  (ConsT a' k' g') -> case ( a == a' ) of
        (True)     -> WFVar1 g' a k      
        (False)    -> WFVar3 g' a k (simpleWFVar g' a k) a' k'

  --- Well-formedness of Environments

data WFEnv where
    WFEEmpty :: WFEnv
    WFEBind  :: env -> WFEnv -> vname -> type -> kind -> WFtype -> WFEnv
    WFEBindT :: env -> WFEnv -> vname -> kind -> WFEnv

{-@ data WFEnv where
        WFEEmpty :: ProofOf(WFEnv Empty)
        WFEBind  :: g:env -> ProofOf(WFEnv g) -> { x:vname | not (in_env x g) } -> t:type 
                     -> k:kind -> ProofOf(WFtype g t k) -> ProofOf(WFEnv (Cons x t g)) 
        WFEBindT :: g:env -> ProofOf(WFEnv g) -> { a:vname | not (in_env a g) } -> k:kind 
                                                        -> ProofOf(WFEnv (ConsT a k g)) @-}
