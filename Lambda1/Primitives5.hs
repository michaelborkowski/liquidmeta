{-# LANGUAGE GADTs #-}

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Primitives5 where

--import Control.Exception (assert)
import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import BasicProps
import Typing
import Primitives
import Primitives3
import STLCLemmas
import STLCSoundness
import TechLemmas
import TechLemmas2
import DenotationalSoundness
import Substitution

-- force these into scope
semantics = (Step, EvalsTo)
typing = (HasBType, HasType, WFType, WFEnv, Subtype)
denotations = (Entails, Denotes, DenotesEnv, ValueDenoted, AugmentedCSubst)

{-@ reflect foo17 @-}
foo17 x = Just x
foo17 :: a -> Maybe a

{-
-- only true that (ty c) <: t  -- do i ned sub trans too?
{-@ assume lem_prim_tyc_sub :: g:Env -> c:Prim -> t:Type -> ProofOf(HasType g (Prim c) t)
                              -> ProofOf(Subtype g (ty c) t) @-}
lem_prim_tyc_sub :: Env -> Prim -> Type -> HasType -> Subtype
lem_prim_tyc_sub g c t (TPrm _ _)                = lem_subtype_refl g t
lem_prim_tyc_sub g c t (TSub _ _ s p_pc_s _ _ _) = () ? lem_prim_tyc_sub g c s p_pc_s
lem_prim_tyc_sub g c t _                         = impossible "no more matches"
-}



{-@ assume lem_delta_typ :: c:Prim -> v:Value -> x:Vname -> t_x:Type -> t':Type
        -> ProofOf(HasType Empty (Prim c) (TFunc x t_x t')) -> ProofOf(HasType Empty v t_x)
        -> { pf:_ | propOf pf == HasType Empty (delta c v) (tsubBV x v t') } @-} {-&&
                    not ((delta c v) == Crash) } @-} 
lem_delta_typ :: Prim -> Expr -> Vname -> Type -> Type 
                     -> HasType -> HasType -> HasType
lem_delta_typ c v x t_x t' den_tx_v = undefined

{- @ asm lem_delta_typ1 :: g:Env -> c:Prim -> v:Value -> x:Vname -> t_x:Type 
        -> { t':Type | ty(c) == TFunc x t_x t' } -> ProofOf(Denotes t_x v)
        -> { pf:_ | propOf pf == HasType g (delta c v) (tsubBV x v t') &&
                    not ((delta c v) == Crash) } @-}
--lem_delta_typ1 :: Env -> Prim -> Expr -> Vname -> Type -> Type -> Denotes -> HasType
--lem_delta_typ1 g c v x t_x t' den_tx_v = undefined

-- also Denotes t[v/x] delta(c,v)
{-
{-@ lem_delta_and_typ :: v:Value -> x:Vname -> t_x:Type -> t':Type
        -> ProofOf(HasType Empty (Prim And) (TFunc t_x t')) -> ProofOf(HasBType Empty v t_x)
        -> { pf:_ | propOf pf == HasType Empty (delta And v) t' } @-} -- &&
lem_delta_and_typ :: Expr -> Vname -> Type -> Type -> HasType -> HasType -> HasType
lem_delta_and_typ v x t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (TPrm Empty And) -> case v of
          (Bc True)  -> TAbs Empty 1 (BTBase TBool) (BV 1) (BTBase TBool)
                              1 (BTVar1 BEmpty 1 (BTBase TBool) ) -- ? toProof ( unbind 1 1 (BV 1) === FV 1 ))
          (Bc False) -> BTAbs BEmpty 1 (BTBase TBool) (Bc False) (BTBase TBool)
                              1 (BTBC (BCons 1 (BTBase TBool) BEmpty) False)
          _          -> impossible ("by lemma" ? lem_bool_values v p_v_tx)

-}
