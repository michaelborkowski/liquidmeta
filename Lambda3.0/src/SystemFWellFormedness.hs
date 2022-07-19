{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SystemFWellFormedness where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
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
    WFFTBasic :: FEnv -> Defs -> Basic -> WFFT
    WFFTFV1   :: FEnv -> Defs -> Vname -> Kind -> WFFT
    WFFTFV2   :: FEnv -> Defs -> Vname -> Kind -> WFFT -> Vname -> FType -> WFFT
    WFFTFV3   :: FEnv -> Defs -> Vname -> Kind -> WFFT -> Vname -> Kind  -> WFFT
    WFFTFunc  :: FEnv -> Defs -> FType -> Kind -> WFFT -> FType -> Kind  -> WFFT -> WFFT
    WFFTPoly  :: FEnv -> Defs -> Kind  -> FType -> Kind -> Names -> (Vname -> WFFT) -> WFFT
    WFFTData  :: FEnv -> Defs -> TCons -> FType -> Kind -> WFFT -> WFFT
    WFFTKind  :: FEnv -> Defs -> FType -> WFFT -> WFFT

{-@ data WFFT where
        WFFTBasic :: g:FEnv -> ds:Defs -> { b:Basic | b == TBool || b == TInt } 
                       -> ProofOf(WFFT g ds (FTBasic b) Base)  
        WFFTFV1   :: g:FEnv -> ds:Defs -> { a:Vname | not (in_envF a g) } -> k:Kind 
                       -> ProofOf(WFFT (FConsT a k g) ds (FTBasic (FTV a)) k)  
        WFFTFV2   :: g:FEnv -> ds:Defs -> a:Vname -> k:Kind -> ProofOf(WFFT g ds (FTBasic (FTV a)) k)
                       -> { a':Vname | not (in_envF a' g) && a' != a } -> t:FType 
                       -> ProofOf(WFFT (FCons a' t g) ds (FTBasic (FTV a)) k)  
        WFFTFV3   :: g:FEnv -> ds:Defs -> a:Vname -> k:Kind -> ProofOf(WFFT g ds (FTBasic (FTV a)) k)
                       -> { a':Vname | not (in_envF a' g) && a' != a } -> k':Kind 
                       -> ProofOf(WFFT (FConsT a' k' g) ds (FTBasic (FTV a)) k)  
        WFFTFunc  :: g:FEnv -> ds:Defs -> t1:FType -> k1:Kind -> ProofOf(WFFT g ds t1 k1) 
                       -> t2:FType -> k2:Kind -> ProofOf(WFFT g ds t2 k2) 
                       -> ProofOf(WFFT g ds (FTFunc t1 t2) Star)   
        WFFTPoly  :: g:FEnv -> ds:Defs -> k:Kind -> t:FType -> k_t:Kind  -> nms:Names 
                       -> ( { a:Vname | NotElem a nms } -> ProofOf(WFFT (FConsT a k g) ds (unbindFT a t) k_t) )
                       -> ProofOf(WFFT g ds (FTPoly k t) Star)   
        WFFTData  :: g:FEnv -> ds:Defs -> tc:TCons -> t:FType 
                       -> { k_t:Kind | tcKind tc ds == Just k_t } -> ProofOf(WFFT g ds t k_t)
                       -> ProofOf(WFFT g ds (FTData tc t) Base)
        WFFTKind  :: g:FEnv -> ds:Defs -> t:FType -> ProofOf(WFFT g ds t Base) 
                       -> ProofOf(WFFT g ds t Star) @-} 

{-@ reflect isWFFTFunc @-}
isWFFTFunc :: WFFT -> Bool
isWFFTFunc (WFFTFunc {}) = True
isWFFTFunc _             = False

{-@ reflect isWFFTPoly @-}
isWFFTPoly :: WFFT -> Bool
isWFFTPoly (WFFTPoly {}) = True
isWFFTPoly _             = False

{-@ reflect isWFFTData @-}
isWFFTData :: WFFT -> Bool
isWFFTData (WFFTData {}) = True
isWFFTData _             = False

{-@ simpleWFFTFV :: g:FEnv -> ds:Defs -> { a:Vname | in_envF a g } -> { k:Kind | tv_bound_inF a k g }
                -> ProofOf(WFFT g ds (FTBasic (FTV a)) k) @-}
simpleWFFTFV :: FEnv -> Defs -> Vname -> Kind -> WFFT
simpleWFFTFV g ds a k  = case g of
  (FCons y s g')    -> case ( a == y ) of   -- g = Empty is impossible
        (False)     -> WFFTFV2 g' ds a k (simpleWFFTFV g' ds a k) y s
  (FConsT a' k' g') -> case ( a == a' ) of
        (True)      -> WFFTFV1 g' ds a k      
        (False)     -> WFFTFV3 g' ds a k (simpleWFFTFV g' ds a k) a' k'

  --- Well-formedness of Environments

data WFFE where
    WFFEmpty :: Defs -> WFFE
    WFFBind  :: FEnv -> Defs -> WFFE -> Vname -> FType -> Kind -> WFFT -> WFFE
    WFFBindT :: FEnv -> Defs -> WFFE -> Vname -> Kind                  -> WFFE
{-@ data WFFE where
        WFFEmpty :: ds:Defs -> ProofOf(WFFE FEmpty ds)  
        WFFBind  :: g:FEnv -> ds:Defs -> ProofOf(WFFE g ds) -> { x:Vname | not (in_envF x g) } 
                     -> t:FType -> k:Kind -> ProofOf(WFFT g ds t k) -> ProofOf(WFFE (FCons x t g) ds)  
        WFFBindT :: g:FEnv -> ds:Defs -> ProofOf(WFFE g ds) -> { a:Vname | not (in_envF a g) } 
                     -> k:Kind  -> ProofOf(WFFE (FConsT a k g) ds) @-}

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
shiftAtAbove j (FTPoly k   t) = FTPoly k  (shiftAtAbove (j+1) t)
shiftAtAbove j (FTData tc  t) = FTData tc (shiftAtAbove j     t)

data AnonEnv = AnEmpty
             | AnCons  Index FType AnonEnv
             | AnConsT Index Kind  AnonEnv

{-@ reflect aBind @-}
aBind :: FType -> AnonEnv -> AnonEnv
aBind t AnEmpty           = AnCons  0     t  AnEmpty
aBind t (AnCons  i t' ae) = AnCons  (i+1) t' (aBind t ae)
aBind t (AnConsT i k  ae) = AnConsT i     k  (aBind t ae)

{-@ reflect aBindT @-}
aBindT :: Kind -> AnonEnv -> AnonEnv
aBindT k AnEmpty           = AnConsT 0     k                   AnEmpty
aBindT k (AnCons  i t' ae) = AnCons  i     (shiftAtAbove 0 t') (aBindT k ae)
aBindT k (AnConsT i k' ae) = AnConsT (i+1) k'                  (aBindT k ae)

{-@ reflect bound_inAE @-}
{-@ bound_inAE :: Index -> FType -> AnonEnv -> Bool @-}
bound_inAE :: Index -> FType -> AnonEnv -> Bool
bound_inAE i t AnEmpty                         = False
bound_inAE i t (AnCons  i' t' ae) | (i == i')  = (t == t')
                                  | otherwise  = bound_inAE i t ae
bound_inAE i t (AnConsT j' k' ae)              = bound_inAE i t ae

{-@ reflect tv_bound_inAE @-}
{-@ tv_bound_inAE :: Index -> Kind -> AnonEnv -> Bool @-}
tv_bound_inAE :: Index -> Kind -> AnonEnv -> Bool
tv_bound_inAE j k AnEmpty                         = False
tv_bound_inAE j k (AnCons  i' t' ae)              = tv_bound_inAE j k ae
tv_bound_inAE j k (AnConsT j' k' ae) | (j == j')  = (k == k')
                                     | otherwise  = tv_bound_inAE j k ae

{-@ reflect isWFFT @-}
{-@ isWFFT :: g:FEnv -> ds:Defs -> AnonEnv -> t:FType -> Kind -> Bool  / [ftsize t] @-}
isWFFT :: FEnv -> Defs -> AnonEnv -> FType -> Kind -> Bool
isWFFT g ds ae (FTBasic b) k      = case b of
    TBool    -> True
    TInt     -> True
    (BTV i) | tv_bound_inAE i Base ae -> True
            | tv_bound_inAE i Star ae -> k == Star
            | otherwise               -> False
    (FTV a) | tv_bound_inF  a Base g  -> True
            | tv_bound_inF  a Star g  -> k == Star
            | otherwise               -> False
isWFFT g ds ae (FTFunc  t_x t) k  = k == Star && isWFFT g ds ae             t_x Star
                                              && isWFFT g ds ae             t   Star
isWFFT g ds ae (FTPoly   k' t) k  = k == Star && isWFFT g ds (aBindT k' ae) t   Star
isWFFT g ds ae (FTData  tc  t) k  = case tcKind tc ds of
  Nothing    -> False
  Just k_t   -> k == Base && isWFFT g ds ae t k_t

{-@ lem_isWFFT_unbindFT :: g:FEnv -> ds:Defs -> ae:AnonEnv -> i:Index -> k':Kind -> t:FType
        -> { k:Kind | isWFFT g ds (AnConsT i k' ae) t k }
        -> { a:Vname | not (in_envF a g) && not (Set_mem a (ffreeTV t)) }
        -> { pf:_ | isWFFT (FConsT a k' g) ds ae (openFT_at i a t) k } @-}
lem_isWFFT_unbindFT :: FEnv -> Defs -> AnonEnv -> Index -> Kind -> FType -> Kind -> Vname -> Proof
lem_isWFFT_unbindFT g ds ae i k' (FTBasic b) k a  = case b of
    TBool    -> ()
    TInt     -> ()
    (BTV j)  | j == i && k' == Base -> ()
             | j == i && k' == Star -> ()
             | not (j == i) && tv_bound_inAE  j  Base ae -> ()
             | otherwise                                 -> ()
    (FTV a') | a == a'                                   -> ()
             | not (a == a') && tv_bound_inF  a' Base g  -> ()
             | otherwise                                 -> ()
lem_isWFFT_unbindFT g ds ae i k' (FTFunc t_x t) k a  
    = () ? lem_isWFFT_unbindFT g ds ae i k' t_x k a
         ? lem_isWFFT_unbindFT g ds ae i k' t   k a
lem_isWFFT_unbindFT g ds ae i k' (FTPoly k1 t)  k a  
    = () ? lem_isWFFT_unbindFT g ds (aBindT k1 ae) (i+1) k' t k a
lem_isWFFT_unbindFT g ds ae i k' (FTData tc t)  k a = case tcKind tc ds of
    Just k_t -> () ? lem_isWFFT_unbindFT g ds ae i k' t   k_t a

{-@ makeWFFT :: g:FEnv -> ds:Defs -> { t:FType | Set_sub (ffreeTV t) (bindsF g) }
                       -> { k:Kind  | isWFFT g ds AnEmpty t k } -> ProofOf(WFFT g ds t k) 
                        / [ftsize t, ksize k] @-}
makeWFFT :: FEnv -> Defs -> FType -> Kind -> WFFT
makeWFFT g ds (FTBasic b) Base    = case b of
  TBool    -> WFFTBasic g ds TBool
  TInt     -> WFFTBasic g ds TInt
  (FTV a)  -> simpleWFFTFV g ds a Base
makeWFFT g ds (FTBasic b) Star    = case b of
  TBool                           -> WFFTKind g ds (FTBasic b) (makeWFFT g ds (FTBasic b) Base)
  TInt                            -> WFFTKind g ds (FTBasic b) (makeWFFT g ds (FTBasic b) Base)
  (FTV a) | tv_bound_inF a Base g -> WFFTKind g ds (FTBasic b) (simpleWFFTFV g ds a Base)
          | tv_bound_inF a Star g -> simpleWFFTFV g ds a Star
makeWFFT g ds (FTFunc t_x t) Star = WFFTFunc g ds t_x Star (makeWFFT g ds t_x Star) t Star
                                          (makeWFFT g ds t Star)
makeWFFT g ds (FTPoly k   t) Star = WFFTPoly g ds k t Star nms mk_wf_t
  where
    {-@ mk_wf_t :: { a:Vname | NotElem a nms } -> ProofOf(WFFT (FConsT a k g) ds (unbindFT a t) Star) @-}
    mk_wf_t a = makeWFFT (FConsT a k g) ds (unbindFT a t)
                         (Star ? lem_isWFFT_unbindFT g ds AnEmpty 0 k t Star a)
    nms = unionFEnv [] g
makeWFFT g ds (FTData tc  t) Base = WFFTData g ds tc t k_t (makeWFFT g ds t k_t)
  where
    Just k_t = tcKind tc ds  
