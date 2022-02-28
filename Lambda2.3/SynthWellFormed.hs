{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SynthWellFormed where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import SystemFWellFormedness
import SystemFTyping
import CheckSynth
import WellFormedness

{-@ reflect foo05b @-}
foo05b :: a -> Maybe a
foo05b x = Just x

--------------------------------------------------------------------------------------------
-- | AUTOMATING WELL-FORMEDNESS PROOF GENERATION for the types of our built-in primitives --
--------------------------------------------------------------------------------------------

{-@ reflect noDefnsInRefns @-}
{-@ noDefnsInRefns :: UserType -> Bool @-}
noDefnsInRefns :: {-Env ->-} Type -> Bool
noDefnsInRefns   (TRefn b ps)     = allNoDefnsBaseAppT ps {-(unbindP y ps)
  where
    y = fresh_var [] g-}
noDefnsInRefns   (TFunc  t_x t)   = noDefnsInRefns {-g-} t_x && noDefnsInRefns t{-(Cons y t_x g) (unbindT y t)
  where
    y = fresh_var [] g-}
--noDefnsInRefns g (TExists t_x t)  = noDefnsInRefns g t_x && noDefnsInRefns (Cons y t_x g) (unbindT y t) 
--  where
--    y = fresh_var [] g
noDefnsInRefns   (TPoly    k  t)  = noDefnsInRefns t{-(ConsT a' k g) (unbind_tvT a' t)
  where
    a' = fresh_var [] g-}

{-@ reflect isWellFormed @-} -- suffices to only build for UserTypes only
{-@ isWellFormed :: g:Env -> AnonEnv -> { t:UserType | noDefnsInRefns t } -> Kind -> Bool  
                  / [tsize t, envsize g] @-}
isWellFormed :: Env -> AnonEnv -> Type -> Kind -> Bool
isWellFormed g ae (TRefn b ps) k    = case b of
--    TBool    -> checkPreds (FCons y (FTBasic b) (erase_env g)) (unbindP y ps) -- (FTBasic TBool)
    TBool    -> checkPreds (erase_env g) (aBind (FTBasic b) ae) ps
    TInt     -> checkPreds (erase_env g) (aBind (FTBasic b) ae) ps
    (BTV i) | tv_bound_inAE i Base ae -> checkPreds (erase_env g) (aBind (FTBasic b) ae) ps
            | tv_bound_inAE i Star ae -> k == Star && ps == PEmpty
            | otherwise               -> False
    (FTV a) | tv_bound_in a Base g -> checkPreds (erase_env g) (aBind (FTBasic b) ae) ps
            | tv_bound_in a Star g -> k == Star && ps == PEmpty
            | otherwise            -> False  
--  where
--    y = fresh_var [] g
isWellFormed g ae (TFunc t_x t) k   = k == Star && isWellFormed g ae t_x Star 
                                                && isWellFormed g (aBind (erase t_x) ae) t Star
{-                                                && isWellFormed (Cons y t_x g) (unbindT y t) Star
  where
    y = fresh_var [] g-}
--isWellFormed g (TExists t_x t) k = isWellFormed g t_x Star && isWellFormed (Cons y t_x g) (unbindT y t) k
--  where
--    y = fresh_var [] g
isWellFormed g ae (TPoly  k'  t) k  = k == Star && isWellFormed g (aBindT k' ae) t Star
{-                                              && isWellFormed (ConsT a' k' g) (unbind_tvT a' t) Star
  where
    a' = fresh_var [] g-}

{-@ lem_isWF_unbind_tvT :: g:Env -> i:Index -> k':Kind -> { t:Type | noDefnsInRefns t }
          -> { k:Kind | isWellFormed g (AConsT i k' AEmpty) t k }
          -> { a:Vname | not (in_env a g) && not (Set_mem a (free t)) && not (Set_mem a (freeTV t)) }
          -> { pf:_ | isWellFormed (ConsT a k' g) AEmpty (open_tvT_at i a t) k } @-}
lem_isWF_unbind_tvT :: Env {-> AnonEnv-} -> Index -> Kind -> Type -> Kind -> Vname -> Proof
lem_isWF_unbind_tvT g i k' (TRefn   b ps) k a = ()
lem_isWF_unbind_tvT g i k' (TFunc  t_x t) k a = ()
lem_isWF_unbind_tvT g i k' (TPoly  k1  t) k a = () -- ? lem_isWF_unbind_tvT 

{-@ makeWFType :: g:Env 
        -> { t:UserType | noDefnsInRefns t && Set_sub (free t) (binds g) && 
                                              Set_sub (freeTV t) (binds g)}
        -> { k:Kind | isWellFormed g AEmpty t k } -> ProofOf(WFType g t k) / [tsize t, ksize k] @-}
makeWFType :: Env -> Type -> Kind -> WFType
makeWFType g (TRefn b ps) Base  = WFRefn g b pf_g_b ps nms mk_ps_bool
  where
    pf_g_b       = case b of 
      TBool                           -> WFBase g TBool 
      TInt                            -> WFBase g TInt  
      (FTV a) | tv_bound_in a Base g  -> simpleWFVar g a Base
    {-@ mk_ps_bool :: { y:Vname | NotElem y nms } 
          -> ProofOf(PHasFType (FCons y (FTBasic b) (erase_env g)) (unbindP y ps)) @-}
    mk_ps_bool y = makePHasFType (FCons y (FTBasic b) (erase_env g)) (unbindP y ps) 
    nms          = unionEnv [] g
makeWFType g (TRefn b ps) Star  = case b of
  TBool                          -> WFKind g (TRefn b ps) (makeWFType g (TRefn b ps) Base)
  TInt                           -> WFKind g (TRefn b ps) (makeWFType g (TRefn b ps) Base)
  (FTV a) | tv_bound_in a Base g -> WFKind g (TRefn b ps) (makeWFType g (TRefn b ps) Base)
--                                        (WFRefn g b (simpleWFVar g a Base) 
--                                             ps (makeHasFType (FCons y (FTBasic b) (erase_env g))
--                                             (unbind 0 y p) (FTBasic TBool)))
          | tv_bound_in a Star g -> simpleWFVar g a Star
--    where
--      y      = fresh_var g
makeWFType g (TFunc t_x t) Star = WFFunc g t_x Star (makeWFType g t_x Star) t Star nms mk_wf_t
  where
    {-@ mk_wf_t :: { y:Vname | NotElem y nms } -> ProofOf(WFType (Cons y t_x g) (unbindT y t) Star) @-}
    mk_wf_t y = makeWFType (Cons y t_x g) (unbindT y t) Star
    nms       = unionEnv [] g
--    y = fresh_var g
makeWFType g (TFunc t_x t) _    = impossible ""
--makeWFType g (TExists t_x t) k  = WFExis g x t_x Star (makeWFType g t_x Star) t k y
--                                     (makeWFType (Cons y t_x g) (unbindT x y t) k)
--  where
--    y = fresh_var g
makeWFType g (TPoly k t) Star   = WFPoly g k t Star nms mk_wf_t
  where
    {-@ mk_wf_t :: { a:Vname | NotElem a nms } 
            -> ProofOf(WFType (ConsT a k g) (unbind_tvT a t) Star) @-}
    mk_wf_t a = makeWFType (ConsT a k g) (unbind_tvT a t) Star
    nms       = unionEnv [] g
makeWFType g (TPoly k t) _      = impossible ""
