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

{-@ reflect foo05 @-}
foo05 :: a -> Maybe a
foo05 x = Just x

-----------------------------------------------------------------------------
----- | JUDGEMENTS : WELL-FORMEDNESS of TYPES and ENVIRONMENTS
-----------------------------------------------------------------------------

  --- Well-Formedness of Types

data WFTypeP where
    WFType :: Env -> Type -> Kind -> WFTypeP

data WFType where 
    WFBase :: Env -> Basic -> Expr -> WFType
    WFRefn :: Env -> RVname -> Basic -> Expr -> WFType -> Expr -> Vname -> HasFType -> WFType
    WFVar1 :: Env -> Vname -> Expr -> Kind -> WFType
    WFVar2 :: Env -> Vname -> Expr -> Kind -> WFType -> Vname -> Type -> WFType
    WFVar3 :: Env -> Vname -> Expr -> Kind -> WFType -> Vname -> Kind -> WFType
    WFFunc :: Env -> Vname -> Type -> Kind -> WFType -> Type -> Kind -> Vname -> WFType -> WFType
    WFExis :: Env -> Vname -> Type -> Kind -> WFType -> Type -> Kind -> Vname -> WFType -> WFType
    WFPoly :: Env -> Vname -> Kind -> Type -> Kind -> Vname -> WFType -> WFType
    WFKind :: Env -> Type -> WFType -> WFType

{-@ data WFType where
        WFBase :: g:Env -> { b:Basic | b == TBool || b == TInt } -> { tt:Pred | isTrivial tt }
                        -> ProofOf(WFType g (TRefn b Z tt) Base)
        WFRefn :: g:Env -> x:RVname -> b:Basic -> { tt:Pred | isTrivial tt }
          -> ProofOf(WFType g (TRefn b Z tt) Base) -> p:Pred 
          -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (ftv p)) }
          -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y p) (FTBasic TBool)) 
          -> ProofOf(WFType g (TRefn b x p) Base)
        WFVar1 :: g:Env -> { a:Vname | not (in_env a g) } -> { tt:Pred | isTrivial tt } -> k:Kind 
          -> ProofOf(WFType (ConsT a k g) (TRefn (FTV a) Z tt) k)
        WFVar2 :: g:Env -> { a:Vname | in_env a g } -> { tt:Pred | isTrivial tt } -> k:Kind 
          -> ProofOf(WFType g (TRefn (FTV a) Z tt) k) 
          -> { y:Vname | y != a && not (in_env y g) } -> t:Type 
          -> ProofOf(WFType (Cons y t g)  (TRefn (FTV a) Z tt) k)
        WFVar3 :: g:Env -> { a:Vname | in_env a g } -> { tt:Pred | isTrivial tt } -> k:Kind 
          -> ProofOf(WFType g (TRefn (FTV a) Z tt) k) 
          -> { a':Vname | a' != a && not (in_env a' g) } -> k':Kind 
          -> ProofOf(WFType (ConsT a' k' g) (TRefn (FTV a) Z tt) k)
        WFFunc :: g:Env -> x:Vname -> t_x:Type -> k_x:Kind
          -> ProofOf(WFType g t_x k_x) -> t:Type -> k:Kind
          -> { y:Vname | not (in_env y g) && not (Set_mem y (free t)) && not (Set_mem y (freeTV t)) }
          -> ProofOf(WFType (Cons y t_x g) (unbindT x y t) k) -> ProofOf(WFType g (TFunc x t_x t) Star)
        WFExis :: g:Env -> x:Vname -> t_x:Type -> k_x:Kind
          -> ProofOf(WFType g t_x k_x) -> t:Type -> k:Kind
          -> { y:Vname | not (in_env y g) && not (Set_mem y (free t)) && not (Set_mem y (freeTV t)) }
          -> ProofOf(WFType (Cons y t_x g) (unbindT x y t) k) -> ProofOf(WFType g (TExists x t_x t) k) 
        WFPoly :: g:Env -> a:Vname -> k:Kind -> t:Type -> k_t:Kind
          -> { a':Vname | not (in_env a' g) && not (Set_mem a' (free t)) && not (Set_mem a' (freeTV t)) }
          -> ProofOf(WFType (ConsT a' k g) (unbind_tvT a a' t) k_t) -> ProofOf(WFType g (TPoly a k t) Star) 
        WFKind :: g:Env -> t:Type -> ProofOf(WFType g t Base) -> ProofOf(WFType g t Star) @-}

{-@ measure wftypSize @-}
{-@ wftypSize :: WFType -> { v:Int | v > 0 } @-}
wftypSize :: WFType -> Int
wftypSize (WFBase _ _ _)                          = 1
wftypSize (WFRefn g x b _ p_g_b p y p_yg_p_bl)    = (wftypSize p_g_b)  + 1
wftypSize (WFVar1 _ _ _ _)                        = 1
wftypSize (WFVar2 _ _ _ _ p_g_a _ _)              = (wftypSize p_g_a)  + 1
wftypSize (WFVar3 _ _ _ _ p_g_a _ _)              = (wftypSize p_g_a)  + 1
wftypSize (WFFunc g x t_x _ p_g_tx _ t y p_yg_t)  = (wftypSize p_g_tx) + (wftypSize p_yg_t) + 1
wftypSize (WFExis g x t_x _ p_g_tx _ t y p_yg_t)  = (wftypSize p_g_tx) + (wftypSize p_yg_t) + 1
wftypSize (WFPoly _ _ _ _ _ _ p_a'g_t)            = (wftypSize p_a'g_t) + 1
wftypSize (WFKind _ _ p_g_t)                      = (wftypSize p_g_t)  + 1

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

{-@ simpleWFVar :: g:Env -> { a:Vname | in_env a g } -> { tt:Pred | isTrivial tt }
        -> { k:Kind | tv_bound_in a k g } -> ProofOf(WFType g (TRefn (FTV a) Z tt) k) @-}
simpleWFVar :: Env -> Vname -> Expr -> Kind -> WFType
simpleWFVar g a tt k  = case g of
  (Cons y s g')    -> case ( a == y ) of   -- g = Empty is impossible
        (False)    -> WFVar2 g' a tt k (simpleWFVar g' a tt k) y s
  (ConsT a' k' g') -> case ( a == a' ) of
        (True)     -> WFVar1 g' a tt k      
        (False)    -> WFVar3 g' a tt k (simpleWFVar g' a tt k) a' k'

  --- Well-formedness of Environments

data WFEnvP where
    WFEnv :: Env -> WFEnvP

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

------------------------------------------------------------------------------------------
-- | AUTOMATING WELL-FORMEDNESS PROOF GENERATION for refinements that occur in practice --
------------------------------------------------------------------------------------------

{-@ reflect noDefnsInRefns @-}
noDefnsInRefns :: Env -> Type -> Bool
noDefnsInRefns g (TRefn b x p)      = noDefnsBaseAppT (unbind 0 y p)
  where
    y = fresh_var g
noDefnsInRefns g (TFunc x t_x t)    = noDefnsInRefns g t_x && noDefnsInRefns (Cons y t_x g) (unbindT x y t)
  where
    y = fresh_var g
noDefnsInRefns g (TExists x t_x t)  = noDefnsInRefns g t_x && noDefnsInRefns (Cons y t_x g) (unbindT x y t) 
  where
    y = fresh_var g
noDefnsInRefns g (TPoly   a  k  t)  = noDefnsInRefns (ConsT a' k g) (unbind_tvT a a' t)
  where
    a' = fresh_var g

{-@ reflect isWellFormed @-}
{-@ isWellFormed :: g:Env -> { t:Type | noDefnsInRefns g t } -> Kind -> Bool  / [tsize t, envsize g] @-}
isWellFormed :: Env -> Type -> Kind -> Bool
isWellFormed g (TRefn b x p) k  = case b of
    TBool    -> checkType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y p) (FTBasic TBool)
    TInt     -> checkType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y p) (FTBasic TBool)
    (BTV a)  -> False
    (FTV a) | tv_bound_in a Base g -> checkType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y p) (FTBasic TBool)
            | tv_bound_in a Star g -> k == Star && x == Z && isTrivial p
            | otherwise            -> False  
  where
    y = fresh_var g
isWellFormed g (TFunc x t_x t) k   = k == Star && isWellFormed g t_x Star 
                                               && isWellFormed (Cons y t_x g) (unbindT x y t) Star
  where
    y = fresh_var g
isWellFormed g (TExists x t_x t) k = isWellFormed g t_x Star && isWellFormed (Cons y t_x g) (unbindT x y t) k
  where
    y = fresh_var g
isWellFormed g (TPoly a  k'  t) k  = k == Star && isWellFormed (ConsT a' k' g) (unbind_tvT a a' t) Star
  where
    a' = fresh_var g


{-@ makeWFType :: g:Env 
        -> { t:Type | noDefnsInRefns g t && Set_sub (free t) (binds g) && Set_sub (freeTV t) (binds g)}
        -> { k:Kind | isWellFormed g t k } -> ProofOf(WFType g t k) / [tsize t, ksize k] @-}
makeWFType :: Env -> Type -> Kind -> WFType
makeWFType g (TRefn b x p) Base   = WFRefn g x b (Bc True) pf_g_b
                                          p y (makeHasFType (FCons y (FTBasic b) (erase_env g))
                                          (unbind 0 y p) (FTBasic TBool))
  where
    y      = fresh_var g
    pf_g_b = case b of 
      TBool   -> WFBase g TBool (Bc True)
      TInt    -> WFBase g TInt  (Bc True)
      (FTV a) | tv_bound_in a Base g            -> simpleWFVar g a (Bc True) Base
makeWFType g (TRefn b x p) Star   = case b of
  TBool                          -> WFKind g (TRefn b x p) (makeWFType g (TRefn b x p) Base)
  TInt                           -> WFKind g (TRefn b x p) (makeWFType g (TRefn b x p) Base)
  (FTV a) | tv_bound_in a Base g -> WFKind g (TRefn b x p) 
                                        (WFRefn g x b (Bc True) (simpleWFVar g a (Bc True) Base) 
                                             p y (makeHasFType (FCons y (FTBasic b) (erase_env g))
                                             (unbind 0 y p) (FTBasic TBool)))
          | tv_bound_in a Star g -> simpleWFVar g a p Star
    where
      y      = fresh_var g
makeWFType g (TFunc x t_x t) Star = WFFunc g x t_x Star (makeWFType g t_x Star) t Star y
                                      (makeWFType (Cons y t_x g) (unbindT x y t) Star)
  where
    y = fresh_var g
makeWFType g (TFunc x t_x t) _    = impossible ""
makeWFType g (TExists x t_x t) k  = WFExis g x t_x Star (makeWFType g t_x Star) t k y
                                     (makeWFType (Cons y t_x g) (unbindT x y t) k)
  where
    y = fresh_var g
makeWFType g (TPoly a k t) Star   = WFPoly g a k t Star a' (makeWFType (ConsT a' k g) (unbind_tvT a a' t) Star)
  where
    a' = fresh_var g
makeWFType g (TPoly a k t) _      = impossible ""
