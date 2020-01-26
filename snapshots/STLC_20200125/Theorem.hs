{-# LANGUAGE GADTs #-}

-- The following module presents a mechanization of the proofs of type
-- soundness and termination for a Simply Typed Lambda Calculus
-- and is based on Lecture notes "Well-typed Programs Don't Go Wrong"
-- and "Type Soundness and Termination in One Easy Lemma" by Nadia
-- Polikarpova for CSE 130 at UC San Diego.

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--short-names" @-}

module Theorem where

import Language.Haskell.Liquid.ProofCombinators 
import Syntax
import Semantics
import Lemma

a = BStep
b = HasType
c = WBValue
d = WBEnv

{-@ thm_success :: e:Expr -> t:Type -> ProofOf(HasType CEmpty e t)
                    -> (Value, BStep)<{\v pf -> propOf pf == BStep Empty e v}> @-}
thm_success :: Expr -> Type -> HasType -> (Value, BStep)
thm_success e t p_e_t = (v, bstep_e)
  where
    (v, (bstep_e, p_v_t)) = main_lemma e t Empty CEmpty p_e_t WBEmpty
