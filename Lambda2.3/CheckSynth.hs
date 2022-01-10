{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module CheckSynth where

import Prelude hiding (length, max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import SystemFWellFormedness            --(WFFT(..),WFFE(..),isWFFT,makeWFFT,isMonoF)
import SystemFTyping
import BasicPropsEnvironments           -- new dependency order

{-@ reflect foo04b @-}
foo04b :: a -> Maybe a
foo04b x = Just x


------------------------------------------------------------
---- | Limited Bi-directional TYPE Checking and Synthesis --
------------------------------------------------------------
--
-- The only expressions fow which we are trying to automate the production of
--    are the refinements found in the types of the built in primitives, in ty(c)
--    These consist of constants, primitives, variables, function application, and
--    simplepolymorphic type application. 

--{-@ reflect len @-}
--{-@ len :: [Type] -> { n:Int | n >= 0 } @-}
--len :: [Type] -> Int 
--len []     = 0
--len (_:xs) = 1 + len xs

{-@ reflect shiftAtAbove @-}
shiftAtAbove :: Index -> FType -> FType
shiftAtAbove j (FTBasic b) = case b of
  (BTV i) | i >= j -> FTBasic (BTV (i+1))
  _                -> FTBasic b
shiftAtAbove j (FTFunc t_x t) = FTFunc (shiftAtAbove j t_x) (shiftAtAbove j t)
shiftAtAbove j (FTPoly k   t) = FTPoly k (shiftAtAbove (j+1) t)

data AnonEnv = AEmpty 
             | ACons  Index FType AnonEnv
             | AConsT Index Kind  AnonEnv

{-@ reflect bind_idx @-}
bind_idx :: AnonEnv -> Index 
bind_idx AEmpty          = 0
bind_idx (ACons  i t ae) = i + 1
bind_idx (AConsT i k ae) = bind_idx ae

{-@ reflect tv_bind_idx @-}
tv_bind_idx :: AnonEnv -> Index
tv_bind_idx AEmpty          = 0
tv_bind_idx (ACons  i t ae) = tv_bind_idx ae
tv_bind_idx (AConsT i k ae) = i + 1

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
bound_inAE :: Index -> FType -> AnonEnv -> Bool
bound_inAE i t AEmpty                         = False
bound_inAE i t (ACons  i' t' ae) | (i == i')  = (t == t')
                                 | otherwise  = bound_inAE i t ae
bound_inAE i t (AConsT j' k' ae)              = bound_inAE i t ae

{-@ reflect tv_bound_inAE @-}
tv_bound_inAE :: Index -> Kind -> AnonEnv -> Bool
tv_bound_inAE j k AEmpty                         = False
tv_bound_inAE j k (ACons  i' t' ae)              = tv_bound_inAE j k ae
tv_bound_inAE j k (AConsT j' k' ae) | (j == j')  = (k == k')
                                    | otherwise  = tv_bound_inAE j k ae

{-@ reflect lookupAE @-}
lookupAE :: Index -> AnonEnv -> Maybe FType
lookupAE i AEmpty                          = Nothing
lookupAE i (ACons  i' t' ae) | i == i'     = Just t'
                             | otherwise   = lookupAE i ae
lookupAE i (AConsT i' k' ae)               = lookupAE i ae

{-@ reflect open_tvAE_at @-}
open_tvAE_at :: Index -> Vname -> AnonEnv -> AnonEnv
open_tvAE_at j a AEmpty          = AEmpty
open_tvAE_at j a (ACons  i t ae) = ACons  i (openFT_at j a t) (open_tvAE_at j a ae)
open_tvAE_at j a (AConsT i k ae) = AConsT i k                 (open_tvAE_at j a ae)

  -- Sys F Well-Formedness Judgments

{-@ reflect isMonoF @-}
isMonoF :: FType -> Bool
isMonoF (FTBasic b)    = True
isMonoF (FTFunc t_x t) = isMonoF t_x && isMonoF t
isMonoF (FTPoly k   t) = False

{-@ reflect isWFFT @-}
{-@ isWFFT :: g:FEnv -> AnonEnv -> { t:FType | isMonoF t } -> Kind -> Bool  / [ftsize t] @-}
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
--isWFFT g ae (FTPoly   k' t) k  = k == Star && isWFFT g (aBindT k' ae) t   Star

{-@ lem_isWFFT_unbindFT :: g:FEnv -> ae:AnonEnv -> i:Index -> k':Kind -> { t:FType | isMonoF t }
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

{-@ makeWFFT :: g:FEnv -> { t:FType | isMonoF t && Set_sub (ffreeTV t) (bindsF g) }
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
--makeWFFT g (FTFunc t_x t) _    = impossible ""


{-@ reflect noDefnsBaseAppT @-}
noDefnsBaseAppT :: Expr -> Bool
noDefnsBaseAppT (Bc _)          = True
noDefnsBaseAppT (Ic _)          = True
noDefnsBaseAppT (BV _)          = True
noDefnsBaseAppT (FV _)          = True
noDefnsBaseAppT (Prim _)        = True
noDefnsBaseAppT (Lambda _)      = False
noDefnsBaseAppT (App e e')      = (noDefnsBaseAppT e) && (noDefnsBaseAppT e')
noDefnsBaseAppT (LambdaT _ _)   = False
noDefnsBaseAppT (AppT e t)      = (noDefnsBaseAppT e) && (isMonoF (erase t))
noDefnsBaseAppT (Let _ _)       = False
noDefnsBaseAppT (Annot e t)     = noDefnsBaseAppT e

{-@ reflect checkType @-} 
{-@ checkType :: FEnv ->  ae:AnonEnv 
                      -> { e:Expr | noDefnsBaseAppT e } -> t:FType -> Bool / [esize e] @-}
checkType :: FEnv -> AnonEnv -> Expr -> FType -> Bool
checkType g ae (Bc b) t         = ( t == FTBasic TBool )
checkType g ae (Ic n) t         = ( t == FTBasic TInt )
checkType g ae (Prim c) t       = ( t == erase_ty c )
checkType g ae (BV i) t         = bound_inAE i t ae
checkType g ae (FV x) t         = bound_inF x t g
checkType g ae (App e e') t     = case ( synthType g ae e' ) of
    (Just t')       -> checkType g ae e (FTFunc t' t)
    _               -> False
checkType g ae (AppT e t2) t    = case ( synthType g ae e ) of
    (Just (FTPoly Base t1))  -> ( t == ftsubBV (erase t2) t1 ) &&
                                ( isWFFT g ae (erase t2) Base ) && noExists t2 &&
                                  isLCT_at (bind_idx ae) (tv_bind_idx ae) t2 &&
                                ( S.isSubsetOf (free t2) (vbindsF g) ) &&
                                ( S.isSubsetOf (freeTV t2) (tvbindsF g) )  
    _                        -> False 
checkType g ae (Annot e liqt) t = ( checkType g ae e t ) && ( t == erase liqt ) &&
                               ( S.isSubsetOf (free liqt) (vbindsF g) ) &&
                               ( S.isSubsetOf (freeTV liqt) (tvbindsF g) ) && 
                                 isLCT_at (bind_idx ae) (tv_bind_idx ae) liqt

{-@ reflect synthType @-}
{-@ synthType :: FEnv -> AnonEnv -> { e:Expr | noDefnsBaseAppT e } 
        -> Maybe FType / [esize e] @-}
synthType :: FEnv -> AnonEnv -> Expr -> Maybe FType
synthType g ae (Bc b)          = Just ( FTBasic TBool )
synthType g ae (Ic n)          = Just ( FTBasic TInt )
synthType g ae (Prim c)        = Just ( erase_ty c )
synthType g ae (BV i)          = lookupAE i ae
synthType g ae (FV x)          = lookupF x g
synthType g ae (App e e')      = case ( synthType g ae e' ) of
    Nothing    -> Nothing
    (Just t')  -> case ( synthType g ae e ) of
        (Just (FTFunc t_x t)) -> if ( t_x == t' ) then Just t else Nothing
        _                     -> Nothing
synthType g ae (AppT e t2)     = case ( synthType g ae e ) of
    (Just (FTPoly Base t1)) -> (case ( isWFFT g ae (erase t2) Base && S.isSubsetOf (free t2) (vbindsF g) &&
                                       S.isSubsetOf (freeTV t2) (tvbindsF g) && noExists t2 &&
                                       isLCT_at (bind_idx ae) (tv_bind_idx ae) t2 ) of 
	True   -> Just (ftsubBV (erase t2) t1)
        False  -> Nothing)
    _                       -> Nothing 
synthType g ae (Annot e liqt)  = case ( checkType g ae e (erase liqt) && 
                                   S.isSubsetOf (free liqt) (vbindsF g) &&
                                   S.isSubsetOf (freeTV liqt) (tvbindsF g) && 
                                   isLCT_at (bind_idx ae) (tv_bind_idx ae) liqt ) of 
    True  -> Just (erase liqt)
    False -> Nothing

--        -> { a:Vname | not (in_envF a g) && not (Set_mem a (ffreeTV t)) } 
--                                         && not (Set_mem a (ffreeTV t)) } 
{-@ lem_checkType_unbindFT :: g:FEnv -> ae:AnonEnv -> i:Index -> k':Kind -> { e:Expr | noDefnsBaseAppT e }
        -> { t:FType| checkType g (AConsT i k' ae) e t } 
        -> { a:Vname | not (in_envF a g) && not (Set_mem a (fv e)) && not (Set_mem a (ftv e)) }
        -> { pf:_ | checkType (FConsT a k' g) ae (open_tv_at i a e) (openFT_at i a t) } / [esize e] @-}
lem_checkType_unbindFT :: FEnv -> AnonEnv -> Index -> Kind -> Expr -> FType  -> Vname -> Proof
lem_checkType_unbindFT g ae i k' (Bc _) t a         = ()
lem_checkType_unbindFT g ae i k' (Ic _) t a         = ()
lem_checkType_unbindFT g ae i k' (Prim _ ) t a      = () -- rej
lem_checkType_unbindFT g ae i k' (BV j) t a | j == i     = () -- rej, not relevant?
                                            | otherwise  = () ? toProof ( bound_inAE j t (AConsT i k' ae) === bound_inAE j t ae )
lem_checkType_unbindFT g ae i k' (FV x) t a | a == x     = () -- impossible!
                                            | otherwise  = () ? toProof ( bound_inF x t (FConsT a k' g) === bound_inF x t g)
lem_checkType_unbindFT g ae i k' (App e e') t a     = case ( synthType g (AConsT i k' ae) e' ) of
    (Just t')       -> () ? lem_checkType_unbindFT g ae i k' e (FTFunc t' t) a
                          ? lem_synthType_unbindFT g ae i k' e' t' a
--    _               -> () -- ? lem_synthType_unbindFT g ae i k' e' t' a
-- case ( synthType (FConsT a k' g) ae (open_tv_at i a e') ) of
lem_checkType_unbindFT g ae i k' (AppT e t2) t a    = case ( synthType g (AConsT i k' ae) e ) of
    (Just (FTPoly Base t1))  -> () ? lem_isWFFT_unbindFT    g ae i k' (erase t2) Base a
                                   ? lem_synthType_unbindFT g ae i k' e (FTPoly Base t1) a
--    _               -> impossible ("by lem" ? lem_synthType_unbindFT 
lem_checkType_unbindFT g ae i k' (Annot e liqt) t a = () ? lem_checkType_unbindFT g ae i k' e t {-(erase liqt)-} a
                                                         ? lem_erase_open_tvT_at i a liqt -- local cl?
--                                       && not (Set_mem a (ffreeTV t)) } 
{-@ lem_synthType_unbindFT :: g:FEnv -> ae:AnonEnv -> i:Index -> k':Kind -> { e:Expr | noDefnsBaseAppT e }
      -> { t:FType | synthType g (AConsT i k' ae) e  == Just t } 
      -> { a:Vname | not (in_envF a g) && not (Set_mem a (fv e)) && not (Set_mem a (ftv e)) }
      -> { pf:_ | synthType (FConsT a k' g) ae (open_tv_at i a e) == Just (openFT_at i a t) } / [esize e] @-}
lem_synthType_unbindFT :: FEnv -> AnonEnv -> Index -> Kind -> Expr -> FType  -> Vname -> Proof
lem_synthType_unbindFT g ae i k' (Bc _) t a         = ()
lem_synthType_unbindFT g ae i k' (Ic _) t a         = ()
lem_synthType_unbindFT g ae i k' (Prim _ ) t a      = ()
lem_synthType_unbindFT g ae i k' (BV j) t a         = () ? toProof (lookupAE j (AConsT i k' ae) === lookupAE j ae)
lem_synthType_unbindFT g ae i k' (FV x) t a         = () ? toProof (lookupF x (FConsT a k' g) === lookupF x g)
lem_synthType_unbindFT g ae i k' (App e e') t a     = case ( synthType g (AConsT i k' ae) e' ) of
    (Just t')       -> () ? lem_checkType_unbindFT g ae i k' e (FTFunc t' t) a
                          ? lem_synthType_unbindFT g ae i k' e' t' a 
lem_synthType_unbindFT g ae i k' (AppT e t2) t a    = case ( synthType g (AConsT i k' ae) e ) of
    (Just (FTPoly Base t1)) -> () ? lem_isWFFT_unbindFT    g ae i k' (erase t2) Base a
                                  ? lem_synthType_unbindFT g ae i k' e (FTPoly Base t1) a
lem_synthType_unbindFT g ae i k' (Annot e liqt) t a = () ? lem_checkType_unbindFT g ae i k' e t {-(erase liqt)-} a
                                                         ? lem_erase_open_tvT_at i a liqt
{-@ lem_check_synth :: g:FEnv -> { e:Expr | noDefnsBaseAppT e } 
        -> { t:FType | synthType g AEmpty e == Just t } -> { pf:_ | checkType g AEmpty e t } @-}
lem_check_synth :: FEnv -> Expr -> FType -> Proof
lem_check_synth g (Bc b) t         = case t of 
    (FTBasic TBool) -> ()
lem_check_synth g (Ic n) t         = case t of
    (FTBasic TInt)  -> () 
lem_check_synth g (Prim c) t       = ()
lem_check_synth g (FV x) t         = lem_lookup_boundinF x t g 
lem_check_synth g (App e e') t     = case (synthType g AEmpty e') of
    (Just t')       -> lem_check_synth g e (FTFunc t' t)   -- where  (Just t') = synthType g e' 
    Nothing         -> impossible ""
lem_check_synth g (AppT e t2) t    = case (synthType g AEmpty e) of 
    (Just (FTPoly Base t1))  -> ()
lem_check_synth g (Annot e liqt) t = ()

{-@ makeHasFType :: g:FEnv -> { e:Expr | noDefnsBaseAppT e } -> { t:FType | checkType g AEmpty e t }
        -> ProofOf(HasFType g e t) / [esize e] @-}
makeHasFType :: FEnv -> Expr -> FType -> HasFType
makeHasFType g (Bc b) t         = case t of
    (FTBasic TBool) -> FTBC g b
makeHasFType g (Ic n) t         = case t of
    (FTBasic TInt)  -> FTIC g n
makeHasFType g (Prim c) t       = FTPrm g c
makeHasFType g (FV x) t         = simpleFTVar g (x? lem_boundin_inenvF x t g ) t
makeHasFType g (App e e') t     = FTApp g e t' t pf_e_t't e' pf_e'_t'
  where
    (Just t')  = synthType g AEmpty e'
    pf_e_t't   = makeHasFType g e (FTFunc t' t)
    pf_e'_t'   = makeHasFType g e' (t' ? lem_check_synth g e' t')
makeHasFType g (AppT e rt) t    = case (synthType g AEmpty e) of 
  (Just (FTPoly Base t1)) -> FTAppT g e Base t1 pf_e_at1 rt pf_rt_wfft 
    where
      pf_e_at1        = makeHasFType g e (FTPoly Base t1 ? lem_check_synth g e (FTPoly Base t1)) 
      pf_rt_wfft      = makeWFFT g (erase rt ? lem_erase_freeTV rt
                                             ? toProof ( S.isSubsetOf (freeTV rt) (tvbindsF g) && 
                                                         S.isSubsetOf (tvbindsF g) (bindsF g) )) Base 
makeHasFType g (Annot e liqt) t = FTAnn g e t liqt pf_e_t
  where
    pf_e_t = makeHasFType g e t

{-@ reflect allNoDefnsBaseAppT @-}
allNoDefnsBaseAppT :: Preds -> Bool
allNoDefnsBaseAppT PEmpty       = True
allNoDefnsBaseAppT (PCons p ps) = noDefnsBaseAppT p && allNoDefnsBaseAppT ps

{-@ reflect checkPreds @-}
{-@ checkPreds :: FEnv -> AnonEnv -> { ps:Preds | allNoDefnsBaseAppT ps } -> Bool / [predsize ps] @-}
checkPreds :: FEnv -> AnonEnv -> Preds -> Bool
checkPreds g ae PEmpty       = True
checkPreds g ae (PCons p ps) = checkType g ae p (FTBasic TBool) && checkPreds g ae ps

{-@ makePHasFType :: g:FEnv -> { ps:Preds | allNoDefnsBaseAppT ps && checkPreds g AEmpty ps } 
       	-> ProofOf(PHasFType g ps) / [predsize ps] @-}
makePHasFType :: FEnv -> Preds -> PHasFType 
makePHasFType g PEmpty       = PFTEmp  g
makePHasFType g (PCons p ps) = PFTCons g p (makeHasFType g p (FTBasic TBool))
                                       ps (makePHasFType g ps)
