{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-}
{- @ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesDenotations where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import BasicProps
import Typing
import Entailments
import PrimitivesSemantics
import PrimitiveDenotationsAnd
import PrimitiveDenotationsOr
import PrimitiveDenotationsEqv
import PrimitiveDenotationsLeq
import PrimitiveDenotationsEq

-- force these into scope
semantics = (Step, EvalsTo)
typing = (HasBType, HasType, WFType, WFEnv, Subtype)
denotations = (Entails, Denotes, DenotesEnv, ValueDenoted)

{-@ reflect foo10 @-}
foo10 x = Just x
foo10 :: a -> Maybe a

{-@ lem_freeBV_prim_empty :: c:Prim -> { pf:_ | Set_emp (freeBV (Prim c)) && 
                                                Set_emp (tfreeBV (ty c)) } @-}
lem_freeBV_prim_empty :: Prim -> Proof
lem_freeBV_prim_empty And      = ()
lem_freeBV_prim_empty Or       = ()
lem_freeBV_prim_empty Not      = ()
lem_freeBV_prim_empty Eqv      = ()
lem_freeBV_prim_empty Leq      = ()
lem_freeBV_prim_empty (Leqn n) = ()
lem_freeBV_prim_empty Eq       = ()
lem_freeBV_prim_empty (Eqn n)  = ()

{-@ lem_tsubFV_tybc :: x:Vname -> v_x:Value -> b:Bool
        -> { pf:_ | tsubFV x v_x (tybc b) == tybc b } @-}
lem_tsubFV_tybc :: Vname -> Expr -> Bool -> Proof
lem_tsubFV_tybc x v_x True  = ()
lem_tsubFV_tybc x v_x False = ()

{-@ lem_tsubFV_tyic :: x:Vname -> v_x:Value -> n:Int
        -> { pf:_ | tsubFV x v_x (tyic n) == tyic n } @-}
lem_tsubFV_tyic :: Vname -> Expr -> Int -> Proof
lem_tsubFV_tyic x v_x n = ()

{-@ lem_tsubFV_ty :: x:Vname -> v_x:Value -> c:Prim
        -> { pf:_ | tsubFV x v_x (ty c) == ty c } @-}
lem_tsubFV_ty :: Vname -> Expr -> Prim -> Proof
lem_tsubFV_ty x v_x And      = ()
lem_tsubFV_ty x v_x Or       = () 
lem_tsubFV_ty x v_x Not      = ()
lem_tsubFV_ty x v_x Eqv      = ()
lem_tsubFV_ty x v_x Leq      = ()
lem_tsubFV_ty x v_x (Leqn n) = ()
lem_tsubFV_ty x v_x Eq       = ()
lem_tsubFV_ty x v_x (Eqn n)  = ()

-- Lemma. Denotations of Primitive/Constant Types
{-@ lem_den_tybc :: g:Env -> th:CSubst -> ProofOf(DenotesEnv g th)
        -> b:Bool -> ProofOf(Denotes (ctsubst th (tybc b)) (Bc b)) @-}
lem_den_tybc :: Env -> CSubst -> DenotesEnv -> Bool -> Denotes
lem_den_tybc g th den_g_th b = DRefn TBool 1 (App (App (Prim Eqv) (BV 1)) (Bc b)) 
                                     (Bc b) (BTBC BEmpty b) all_steps
                                     ? lem_ctsubst_nofree th (tybc b)
                                     -- ? toProof ( blIff b b === True )
  where
    all_steps = lemma_eqv_semantics (Bc b) b (Refl (Bc b)) (Bc b) b (Refl (Bc b))
{-    step_one' = EPrim Eqv (Bc b)
    step_one  = EApp1 (App (Prim Eqv) (Bc b)) (delta Eqv (Bc b)) step_one' (Bc b)
    ev_two    = reduce_eqv b b
    all_steps = AddStep (App (App (Prim Eqv) (Bc b)) (Bc b)) (App (delta Eqv (Bc b)) (Bc b))
                        step_one (Bc True) ev_two -}

{-@ lem_den_tyic :: g:Env -> th:CSubst -> ProofOf(DenotesEnv g th)
        -> n:Int -> ProofOf(Denotes (ctsubst th (tyic n)) (Ic n)) @-}
lem_den_tyic :: Env -> CSubst -> DenotesEnv -> Int -> Denotes
lem_den_tyic g th den_g_th n = DRefn TInt 1 (App (App (Prim Eq) (BV 1)) (Ic n))
                                     (Ic n) (BTIC BEmpty n) reduce_eq ? lem_ctsubst_nofree th (tyic n)
  where
    reduce_eq = lemma_eq_semantics (Ic n) n (Refl (Ic n)) (Ic n) n (Refl (Ic n))


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

