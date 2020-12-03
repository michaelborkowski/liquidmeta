{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module WellFormedness where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import SystemFTyping

{-@ reflect foo06 @-}
foo06 :: a -> Maybe a
foo06 x = Just x

-----------------------------------------------------------------------------
----- | JUDGEMENTS : WELL-FORMEDNESS of TYPES and ENVIRONMENTS
-----------------------------------------------------------------------------

  --- Well-Formedness of Types

data WFTypeP where
    WFType :: Env -> Type -> WFTypeP

data WFType where 
    WFRefn :: Env -> Vname -> Basic -> Pred -> Vname -> HasFType -> WFType
    WFFunc :: Env -> Vname -> Type -> WFType -> Type -> Vname -> WFType -> WFType
    WFExis :: Env -> Vname -> Type -> WFType -> Type -> Vname -> WFType -> WFType

{-@ data WFType where
        WFRefn :: g:Env -> x:Vname -> b:Basic -> p:Pred 
          -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) }
          -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind x y p) (FTBasic TBool)) 
          -> ProofOf(WFType g (TRefn b x p))
     |  WFFunc :: g:Env -> x:Vname -> t_x:Type -> ProofOf(WFType g t_x) -> t:Type
          -> { y:Vname | not (in_env y g) && not (Set_mem y (free t)) }
          -> ProofOf(WFType (Cons y t_x g) (unbindT x y t)) -> ProofOf(WFType g (TFunc x t_x t))
     |  WFExis :: g:Env -> x:Vname -> t_x:Type -> ProofOf(WFType g t_x) -> t:Type 
          -> { y:Vname | not (in_env y g) && not (Set_mem y (free t)) }
          -> ProofOf(WFType (Cons y t_x g) (unbindT x y t)) -> ProofOf(WFType g (TExists x t_x t)) @-}

{-@ measure wftypSize @-}
{-@ wftypSize :: WFType -> { v:Int | v > 0 } @-}
wftypSize :: WFType -> Int
wftypSize (WFRefn g x b p y p_yg_p_bl)        = 1
wftypSize (WFFunc g x t_x p_g_tx t y p_yg_t)  = (wftypSize p_g_tx) + (wftypSize p_yg_t) + 1
wftypSize (WFExis g x t_x p_g_tx t y p_yg_t)  = (wftypSize p_g_tx) + (wftypSize p_yg_t) + 1

{-@ reflect isWFRefn @-}
isWFRefn :: WFType -> Bool
isWFRefn (WFRefn {}) = True
isWFRefn _           = False

{-@ reflect isWFFunc @-}
isWFFunc :: WFType -> Bool
isWFFunc (WFFunc {}) = True
isWFFunc _           = False

{-@ reflect isWFExis @-}
isWFExis :: WFType -> Bool
isWFExis (WFExis {}) = True
isWFExis _           = False

  --- Well-formedness of Environments

data WFEnvP where
    WFEnv :: Env -> WFEnvP

data WFEnv where
    WFEEmpty :: WFEnv
    WFEBind  :: Env -> WFEnv -> Vname -> Type -> WFType -> WFEnv

{-@ data WFEnv where
        WFEEmpty :: ProofOf(WFEnv Empty)
      | WFEBind  :: g:Env -> ProofOf(WFEnv g) -> { x:Vname | not (in_env x g) } -> t:Type 
                     -> ProofOf(WFType g t) -> ProofOf(WFEnv (Cons x t g))  @-}

------------------------------------------------------------------------------------------
-- | AUTOMATING WELL-FORMEDNESS PROOF GENERATION for refinements that occur in practice --
------------------------------------------------------------------------------------------

{-@ reflect noDefnsInRefns @-}
noDefnsInRefns :: Env -> Type -> Bool
noDefnsInRefns g (TRefn b x p)      = noDefnsBaseAppT (unbind x y p)
  where
    y = fresh_var g
noDefnsInRefns g (TFunc x t_x t)    = noDefnsInRefns g t_x && noDefnsInRefns (Cons y t_x g) (unbindT x y t)
  where
    y = fresh_var g
noDefnsInRefns g (TExists x t_x t)  = noDefnsInRefns g t_x && noDefnsInRefns (Cons y t_x g) (unbindT x y t) 
  where
    y = fresh_var g

{-@ reflect isWellFormed @-}
{-@ isWellFormed :: g:Env -> { t:Type | noDefnsInRefns g t } -> Bool  / [tsize t, envsize g] @-}
isWellFormed :: Env -> Type -> Bool
isWellFormed g (TRefn b x p)   
  = checkType (FCons y (FTBasic b) (erase_env g)) (unbind x y p) (FTBasic TBool)
    where
      y = fresh_var g
isWellFormed g (TFunc x t_x t)    = isWellFormed g t_x 
                                 && isWellFormed (Cons y t_x g) (unbindT x y t) 
  where
    y = fresh_var g
isWellFormed g (TExists x t_x t)  = isWellFormed g t_x  && isWellFormed (Cons y t_x g) (unbindT x y t) 
  where
    y = fresh_var g

{-@ makeWFType :: g:Env -> { t:Type | noDefnsInRefns g t && Set_sub (free t) (binds g) && isWellFormed g t }
                        -> ProofOf(WFType g t) / [tsize t] @-}
makeWFType :: Env -> Type -> WFType
makeWFType g (TRefn b x p)    = WFRefn g x b p y (makeHasFType (FCons y (FTBasic b) (erase_env g))
                                       (unbind x y p) (FTBasic TBool))
  where
    y      = fresh_var g
makeWFType g (TFunc x t_x t)     = WFFunc g x t_x (makeWFType g t_x) t y
                                      (makeWFType (Cons y t_x g) (unbindT x y t) )
  where
    y = fresh_var g
makeWFType g (TExists x t_x t)   = WFExis g x t_x (makeWFType g t_x) t y
                                     (makeWFType (Cons y t_x g) (unbindT x y t) )
  where
    y = fresh_var g
