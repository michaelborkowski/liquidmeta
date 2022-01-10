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
import CheckSynth

{-@ reflect foo05 @-}
foo05 :: a -> Maybe a
foo05 x = Just x

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

  -- TODO: need a list of HasFType for Preds, another Proposition??

--          -> ({ y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (ftv p)) }
--          -> { y:Vname | not (in_env y g) && not (Set_mem y (free t)) && not (Set_mem y (freeTV t)) }
{-@ data WFType where
        WFBase :: g:Env -> { b:Basic | b == TBool || b == TInt } 
                        -> ProofOf(WFType g (TRefn b PEmpty) Base)
        WFRefn :: g:Env -> b:Basic -> ProofOf(WFType g (TRefn b PEmpty) Base) 
          -> ps:Preds -> nms:Names
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

{-
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
-}

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

{- -}

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
