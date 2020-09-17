{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SystemFWellFormedness where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics

{-@ reflect foo03 @-}
foo03 :: a -> Maybe a
foo03 x = Just x

--- Because the underyling System F types have type variables, we need a concept
---   of well-formedness that works for the System F types and the System F
---   binding environments consisting of 

-----------------------------------------------------------------------------
----- | JUDGEMENTS : WELL-FORMEDNESS of System F TYPES and ENVIRONMENTS
-----------------------------------------------------------------------------

  --- Well-Formedness of (System) F Types

data WFFTP where
    WFFT :: FEnv -> FType -> Kind -> WFFTP

data WFFT where 
    WFFTBasic :: FEnv -> Basic -> WFFT
    WFFTFV1   :: FEnv -> Vname -> Kind -> WFFT
    WFFTFV2   :: FEnv -> Vname -> Kind -> WFFT -> Vname -> FType -> WFFT
    WFFTFV3   :: FEnv -> Vname -> Kind -> WFFT -> Vname -> Kind  -> WFFT
    WFFTFunc  :: FEnv -> FType -> Kind -> WFFT -> FType -> Kind  -> WFFT -> WFFT
    WFFTPoly  :: FEnv -> Vname -> Kind -> FType -> Kind -> Vname -> WFFT -> WFFT
    WFFTKind  :: FEnv -> FType -> WFFT -> WFFT

-- les originales
-- |  WFFTFV2   :: g:FEnv -> a:Vname -> { k:Kind | tv_bound_inF a k g } -> ProofOf(WFFT g (FTFV a) k)
--        -> { y:Vname | y != a && not (in_envF y g) } -> t:FType 
-- |  WFFTFV3   :: g:FEnv -> a:Vname -> { k:Kind | tv_bound_inF a k g } -> ProofOf(WFFT g (FTFV a) k)
--        -> { a':Vname | a' != a && not (in_envF a' g) } -> k':Kind 
{-@ data WFFT where
    WFFTBasic :: g:FEnv -> b:Basic -> ProofOf(WFFT g (FTBasic b) Base)
 |  WFFTFV1   :: g:FEnv -> { a:Vname | not (in_envF a g) } -> k:Kind 
        -> ProofOf(WFFT (FConsT a k g) (FTFV a) k)
 |  WFFTFV2   :: g:FEnv -> a:Vname -> k:Kind -> ProofOf(WFFT g (FTFV a) k)
        -> { a':Vname | not (in_envF a' g) && a' != a } -> t:FType 
        -> ProofOf(WFFT (FCons a' t g) (FTFV a) k)
 |  WFFTFV3   :: g:FEnv -> a:Vname -> k:Kind -> ProofOf(WFFT g (FTFV a) k)
        -> { a':Vname | not (in_envF a' g) && a' != a } -> k':Kind 
        -> ProofOf(WFFT (FConsT a' k' g) (FTFV a) k)
 |  WFFTFunc  :: g:FEnv -> t1:FType -> k1:Kind -> ProofOf(WFFT g t1 k1) -> t2:FType -> k2:Kind
        -> ProofOf(WFFT g t2 k2) -> ProofOf(WFFT g (FTFunc t1 t2) Star)
 |  WFFTPoly  :: g:FEnv -> a:Vname -> k:Kind -> t:FType -> k_t:Kind
        -> { a':Vname | not (in_envF a' g) && not (Set_mem a' (ffreeTV t)) }
        -> ProofOf(WFFT (FConsT a' k g) (unbindFT a a' t) k_t) -> ProofOf(WFFT g (FTPoly a k t) Star) 
 |  WFFTKind  :: g:FEnv -> t:FType -> ProofOf(WFFT g t Base) -> ProofOf(WFFT g t Star) @-}

  -- TODO: what happened to k_t in WFPoly? why Star?

{-@ measure wfftypSize @-}
{-@ wfftypSize :: WFFT -> { v:Int | v >= 0 } @-}
wfftypSize :: WFFT -> Int
wfftypSize (WFFTBasic g b)                        = 1
wfftypSize (WFFTFV1 _ _ _)                        = 1
wfftypSize (WFFTFV2 _ _ _ p_g_a _ _)              = (wfftypSize p_g_a)  + 1
wfftypSize (WFFTFV3 _ _ _ p_g_a _ _)              = (wfftypSize p_g_a)  + 1
wfftypSize (WFFTFunc g t1 _ p_g_t1 t2 k2 p_g_t2)  = (wfftypSize p_g_t1) + (wfftypSize p_g_t2) + 1
wfftypSize (WFFTPoly _ _ _ _ _ _ p_a'g_t)         = (wfftypSize p_a'g_t) + 1
wfftypSize (WFFTKind _ _ p_g_t)                   = (wfftypSize p_g_t)  + 1

{-@ simpleWFFTFV :: g:FEnv -> { a:Vname | in_envF a g } -> { k:Kind | tv_bound_inF a k g }
                -> ProofOf(WFFT g (FTFV a) k) @-}
simpleWFFTFV :: FEnv -> Vname -> Kind -> WFFT
simpleWFFTFV g a k  = case g of
  (FCons y s g')    -> case ( a == y ) of   -- g = Empty is impossible
        (False)     -> WFFTFV2 g' a k (simpleWFFTFV g' a k) y s
  (FConsT a' k' g') -> case ( a == a' ) of
        (True)      -> WFFTFV1 g' a k      
        (False)     -> WFFTFV3 g' a k (simpleWFFTFV g' a k) a' k'

  --- Well-formedness of Environments

data WFFEP where
    WFFE :: FEnv -> WFFEP

data WFFE where
    WFFEmpty :: WFFE
    WFFBind  :: FEnv -> WFFE -> Vname -> FType -> Kind -> WFFT -> WFFE
    WFFBindT :: FEnv -> WFFE -> Vname -> Kind                  -> WFFE

{-@ data WFFE where
    WFFEmpty :: ProofOf(WFFE FEmpty)
 |  WFFBind  :: g:FEnv -> ProofOf(WFFE g) -> { x:Vname | not (in_envF x g) } -> t:FType 
                   -> k:Kind -> ProofOf(WFFT g t k) -> ProofOf(WFFE (FCons x t g)) 
 |  WFFBindT :: g:FEnv -> ProofOf(WFFE g) -> { a:Vname | not (in_envF a g) } -> k:Kind 
                                                    -> ProofOf(WFFE (FConsT a k g)) @-}

