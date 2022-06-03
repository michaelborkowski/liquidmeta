{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SystemFWellFormedness where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof,(?))
import qualified Data.Set as S

import Basics

--- Because the underyling System F types have type variables, we need a concept
---   of well-formedness that works for the System F types and the System F
---   binding environments consisting of 

-----------------------------------------------------------------------------
----- | JUDGEMENTS : WELL-FORMEDNESS of System F TYPES and ENVIRONMENTS
-----------------------------------------------------------------------------

  --- Well-Formedness of (System) F Types

data WFFT where 
    WFFTBasic :: FEnv -> Basic -> WFFT
    WFFTFV1   :: FEnv -> Vname -> Kind -> WFFT
    WFFTFV2   :: FEnv -> Vname -> Kind -> WFFT -> Vname -> FType -> WFFT
    WFFTFV3   :: FEnv -> Vname -> Kind -> WFFT -> Vname -> Kind  -> WFFT
    WFFTFunc  :: FEnv -> FType -> Kind -> WFFT -> FType -> Kind  -> WFFT -> WFFT
    WFFTPoly  :: FEnv -> Kind -> FType -> Kind -> Names -> (Vname -> WFFT) -> WFFT
    WFFTKind  :: FEnv -> FType -> WFFT -> WFFT

{-@ data WFFT where
        WFFTBasic :: g:FEnv -> { b:Basic | b == TBool || b == TInt } -> ProofOf(WFFT g (FTBasic b) Base)  
        WFFTFV1   :: g:FEnv -> { a:Vname | not (in_envF a g) } -> k:Kind 
          -> ProofOf(WFFT (FConsT a k g) (FTBasic (FTV a)) k)  
        WFFTFV2   :: g:FEnv -> a:Vname -> k:Kind -> ProofOf(WFFT g (FTBasic (FTV a)) k)
          -> { a':Vname | not (in_envF a' g) && a' != a } -> t:FType 
          -> ProofOf(WFFT (FCons a' t g) (FTBasic (FTV a)) k)  
        WFFTFV3   :: g:FEnv -> a:Vname -> k:Kind -> ProofOf(WFFT g (FTBasic (FTV a)) k)
          -> { a':Vname | not (in_envF a' g) && a' != a } -> k':Kind 
          -> ProofOf(WFFT (FConsT a' k' g) (FTBasic (FTV a)) k)  
        WFFTFunc  :: g:FEnv -> t1:FType -> k1:Kind -> ProofOf(WFFT g t1 k1) -> t2:FType -> k2:Kind
          -> ProofOf(WFFT g t2 k2) -> ProofOf(WFFT g (FTFunc t1 t2) Star)   
        WFFTPoly  :: g:FEnv -> k:Kind -> t:FType -> k_t:Kind  -> nms:Names 
          -> ( { a:Vname | NotElem a nms } -> ProofOf(WFFT (FConsT a k g) (unbindFT a t) k_t) )
          -> ProofOf(WFFT g (FTPoly k t) Star)   
        WFFTKind  :: g:FEnv -> t:FType -> ProofOf(WFFT g t Base) -> ProofOf(WFFT g t Star) @-} 

{-@ reflect isWFFTFunc @-}
isWFFTFunc :: WFFT -> Bool
isWFFTFunc (WFFTFunc {}) = True
isWFFTFunc _             = False

{-@ reflect isWFFTPoly @-}
isWFFTPoly :: WFFT -> Bool
isWFFTPoly (WFFTPoly {}) = True
isWFFTPoly _             = False

{-@ simpleWFFTFV :: g:FEnv -> { a:Vname | in_envF a g } -> { k:Kind | tv_bound_inF a k g }
                -> ProofOf(WFFT g (FTBasic (FTV a)) k) @-}
simpleWFFTFV :: FEnv -> Vname -> Kind -> WFFT
simpleWFFTFV g a k  = case g of
  (FCons y s g')    -> case ( a == y ) of   -- g = Empty is impossible
        (False)     -> WFFTFV2 g' a k (simpleWFFTFV g' a k) y s
  (FConsT a' k' g') -> case ( a == a' ) of
        (True)      -> WFFTFV1 g' a k      
        (False)     -> WFFTFV3 g' a k (simpleWFFTFV g' a k) a' k'

  --- Well-formedness of Environments

data WFFE where
    WFFEmpty :: WFFE
    WFFBind  :: FEnv -> WFFE -> Vname -> FType -> Kind -> WFFT -> WFFE
    WFFBindT :: FEnv -> WFFE -> Vname -> Kind                  -> WFFE
{-@ data WFFE where
        WFFEmpty :: ProofOf(WFFE FEmpty)  
        WFFBind  :: g:FEnv -> ProofOf(WFFE g) -> { x:Vname | not (in_envF x g) } -> t:FType 
                     -> k:Kind -> ProofOf(WFFT g t k) -> ProofOf(WFFE (FCons x t g))  
        WFFBindT :: g:FEnv -> ProofOf(WFFE g) -> { a:Vname | not (in_envF a g) } -> k:Kind 
                                                      -> ProofOf(WFFE (FConsT a k g)) @-}

----------------------------------------------------------------------------
-- | AUTOMATED INFERENCE of SYSTEM F WELL-FORMEDNESS JUDGMENTS
----------------------------------------------------------------------------

{-@ reflect shiftAtAbove @-}
{-@ shiftAtAbove :: Index -> FType -> FType @-}
shiftAtAbove :: Index -> FType -> FType
shiftAtAbove j (FTBasic b) = case b of
  (BTV i) | i >= j -> FTBasic (BTV (i+1))
  _                -> FTBasic b
shiftAtAbove j (FTFunc t_x t) = FTFunc (shiftAtAbove j t_x) (shiftAtAbove j t)
shiftAtAbove j (FTPoly k   t) = FTPoly k (shiftAtAbove (j+1) t)

data AnonEnv = AEmpty
             | ACons  Index FType AnonEnv
             | AConsT Index Kind  AnonEnv

{-@ reflect aBind @-}
aBind :: FType -> AnonEnv -> AnonEnv
aBind t AEmpty           = ACons  0     t  AEmpty
aBind t (ACons  i t' ae) = ACons  (i+1) t' (aBind t ae)
aBind t (AConsT i k  ae) = AConsT i     k  (aBind t ae)

{-@ reflect aBindT @-}
aBindT :: Kind -> AnonEnv -> AnonEnv
aBindT k AEmpty           = AConsT 0     k                   AEmpty
aBindT k (ACons  i t' ae) = ACons  i     (shiftAtAbove 0 t') (aBindT k ae)
aBindT k (AConsT i k' ae) = AConsT (i+1) k'                  (aBindT k ae)

{-@ reflect bound_inAE @-}
{-@ bound_inAE :: Index -> FType -> AnonEnv -> Bool @-}
bound_inAE :: Index -> FType -> AnonEnv -> Bool
bound_inAE i t AEmpty                         = False
bound_inAE i t (ACons  i' t' ae) | (i == i')  = (t == t')
                                 | otherwise  = bound_inAE i t ae
bound_inAE i t (AConsT j' k' ae)              = bound_inAE i t ae

{-@ reflect tv_bound_inAE @-}
{-@ tv_bound_inAE :: Index -> Kind -> AnonEnv -> Bool @-}
tv_bound_inAE :: Index -> Kind -> AnonEnv -> Bool
tv_bound_inAE j k AEmpty                         = False
tv_bound_inAE j k (ACons  i' t' ae)              = tv_bound_inAE j k ae
tv_bound_inAE j k (AConsT j' k' ae) | (j == j')  = (k == k')
                                    | otherwise  = tv_bound_inAE j k ae

{-@ reflect isWFFT @-}
{-@ isWFFT :: g:FEnv -> AnonEnv -> t:FType -> Kind -> Bool  / [ftsize t] @-}
isWFFT :: FEnv -> AnonEnv -> FType -> Kind -> Bool
isWFFT g ae (FTBasic b) k      = case b of
    TBool    -> True
    TInt     -> True
    (BTV i) | tv_bound_inAE i Base ae -> True
            | tv_bound_inAE i Star ae -> k == Star
            | otherwise               -> False
    (FTV a) | tv_bound_inF  a Base g  -> True
            | tv_bound_inF  a Star g  -> k == Star
            | otherwise               -> False
isWFFT g ae (FTFunc  t_x t) k  = k == Star && isWFFT g ae             t_x Star
                                           && isWFFT g ae             t   Star
isWFFT g ae (FTPoly   k' t) k  = k == Star && isWFFT g (aBindT k' ae) t   Star

{-@ lem_isWFFT_unbindFT :: g:FEnv -> ae:AnonEnv -> i:Index -> k':Kind -> t:FType
        -> { k:Kind | isWFFT g (AConsT i k' ae) t k }
        -> { a:Vname | not (in_envF a g) && not (Set_mem a (ffreeTV t)) }
        -> { pf:_ | isWFFT (FConsT a k' g) ae (openFT_at i a t) k } @-}
lem_isWFFT_unbindFT :: FEnv -> AnonEnv -> Index -> Kind -> FType -> Kind -> Vname -> Proof
lem_isWFFT_unbindFT g ae i k' (FTBasic b) k a  = case b of
    TBool    -> ()
    TInt     -> ()
    (BTV j)  | j == i && k' == Base -> ()
             | j == i && k' == Star -> ()
             | not (j == i) && tv_bound_inAE  j  Base ae -> ()
             | otherwise                                 -> ()
    (FTV a') | a == a'                                   -> ()
             | not (a == a') && tv_bound_inF  a' Base g  -> ()
             | otherwise                                 -> ()
lem_isWFFT_unbindFT g ae i k' (FTFunc t_x t) k a  = () ? lem_isWFFT_unbindFT g ae i k' t_x k a
                                                       ? lem_isWFFT_unbindFT g ae i k' t   k a
lem_isWFFT_unbindFT g ae i k' (FTPoly k1 t)  k a  = () ? lem_isWFFT_unbindFT g (aBindT k1 ae) (i+1) k' t k a

{-@ makeWFFT :: g:FEnv -> { t:FType | Set_sub (ffreeTV t) (bindsF g) }
                       -> { k:Kind  | isWFFT g AEmpty t k } -> ProofOf(WFFT g t k) / [ftsize t, ksize k] @-}
makeWFFT :: FEnv -> FType -> Kind -> WFFT
makeWFFT g (FTBasic b) Base    = case b of
  TBool    -> WFFTBasic g TBool
  TInt     -> WFFTBasic g TInt
  (FTV a)  -> simpleWFFTFV g a Base
makeWFFT g (FTBasic b) Star    = case b of
  TBool                           -> WFFTKind g (FTBasic b) (makeWFFT g (FTBasic b) Base)
  TInt                            -> WFFTKind g (FTBasic b) (makeWFFT g (FTBasic b) Base)
  (FTV a) | tv_bound_inF a Base g -> WFFTKind g (FTBasic b) (simpleWFFTFV g a Base)
          | tv_bound_inF a Star g -> simpleWFFTFV g a Star
makeWFFT g (FTFunc t_x t) Star = WFFTFunc g t_x Star (makeWFFT g t_x Star) t Star
                                          (makeWFFT g t Star)
makeWFFT g (FTPoly k   t) Star = WFFTPoly g k t Star nms mk_wf_t
  where
    {-@ mk_wf_t :: { a:Vname | NotElem a nms } -> ProofOf(WFFT (FConsT a k g) (unbindFT a t) Star) @-}
    mk_wf_t a = makeWFFT (FConsT a k g) (unbindFT a t)
                         (Star ? lem_isWFFT_unbindFT g AEmpty 0 k t Star a)
    nms = unionFEnv [] g
