{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-}
{- @ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Primitives3 where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import BasicProps
import Typing
import Primitives
import Primitives2a
import Primitives2b
import Primitives2c
import Primitives2d
import Primitives2e

-- force these into scope
semantics = (Step, EvalsTo)
typing = (HasBType, HasType, WFType, WFEnv, Subtype)
denotations = (Entails, Denotes, DenotesEnv, ValueDenoted)

{-@ reflect foo10 @-}
foo10 x = Just x
foo10 :: a -> Maybe a

{-@ lem_den_ty :: g:Env -> th:CSubst -> ProofOf(DenotesEnv g th)
        -> c:Prim -> ProofOf(Denotes (ctsubst th (ty c)) (Prim c)) @-}
lem_den_ty :: Env -> CSubst -> DenotesEnv -> Prim -> Denotes
lem_den_ty g th den_g_th And      = lem_den_and    ? lem_ctsubst_nofree th (ty And)
lem_den_ty g th den_g_th Or       = lem_den_or     ? lem_ctsubst_nofree th (ty Or)
lem_den_ty g th den_g_th Not      = lem_den_not    ? lem_ctsubst_nofree th (ty Not)
lem_den_ty g th den_g_th Eqv      = lem_den_eqv    ? lem_ctsubst_nofree th (ty Eqv)
lem_den_ty g th den_g_th Leq      = lem_den_leq    ? lem_ctsubst_nofree th (ty Leq)
lem_den_ty g th den_g_th (Leqn n) = lem_den_leqn n ? lem_ctsubst_nofree th (ty (Leqn n))
lem_den_ty g th den_g_th Eq       = lem_den_eq     ? lem_ctsubst_nofree th (ty Eq)
lem_den_ty g th den_g_th (Eqn n)  = lem_den_eqn  n ? lem_ctsubst_nofree th (ty (Eqn n))

