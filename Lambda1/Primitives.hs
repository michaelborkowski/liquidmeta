{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-}
{- @ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Primitives where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import BasicProps
import Typing

-- force these into scope
semantics = (Step, EvalsTo)
typing = (HasBType, HasType, WFType, WFEnv, Subtype)
denotations = (Entails, Denotes, DenotesEnv, ValueDenoted)

{-@ reflect foo4 @-}
foo4 x = Just x
foo4 :: a -> Maybe a


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
    step_one' = EPrim Eqv (Bc b)
    step_one  = EApp1 (App (Prim Eqv) (Bc b)) (delta Eqv (Bc b)) step_one' (Bc b)
    ev_two    = reduce_eqv b b
    all_steps = AddStep (App (App (Prim Eqv) (Bc b)) (Bc b)) (App (delta Eqv (Bc b)) (Bc b))
                        step_one (Bc True) ev_two


{-@ lem_den_tyic :: g:Env -> th:CSubst -> ProofOf(DenotesEnv g th)
        -> n:Int -> ProofOf(Denotes (ctsubst th (tyic n)) (Ic n)) @-}
lem_den_tyic :: Env -> CSubst -> DenotesEnv -> Int -> Denotes
lem_den_tyic g th den_g_th n = DRefn TInt 1 (App (App (Prim Eq) (BV 1)) (Ic n))
                                     (Ic n) (BTIC BEmpty n) (reduce_eq n n)
                                     ? lem_ctsubst_nofree th (tyic n)

{-@ reduce_eq :: n:Int -> m:Int -> { pf:EvalsTo | propOf pf == 
                                        EvalsTo (App (App (Prim Eq) (Ic n)) (Ic m)) (Bc (intEq n m)) } @-}
reduce_eq :: Int -> Int -> EvalsTo
reduce_eq n m = all_steps
   where
    step_one'  = EPrim Eq (Ic n)
    step_one   = EApp1 (App (Prim Eq) (Ic n)) (delta Eq (Ic n)) step_one' (Ic m)
    step_two   = EPrim (Eqn n) (Ic m)
    all_steps  = AddStep (App (App (Prim Eq) (Ic n)) (Ic m)) (App (Prim (Eqn n)) (Ic m))
                         step_one (Bc (n == m)) 
                         (lem_step_evals (App (Prim (Eqn n)) (Ic m)) (Bc (n == m)) step_two)


{-@ reflect blAnd @-}
blAnd :: Bool -> Bool -> Bool
blAnd b b' = b && b'

{-@ reflect blOr @-}
blOr :: Bool -> Bool -> Bool
blOr b b' = b || b'

{-@ reflect blNot @-}
blNot :: Bool -> Bool
blNot b = not b

{-@ reflect blIff @-}
blIff :: Bool -> Bool -> Bool
blIff b b' = b == b'

{-@ reflect intLeq @-}
intLeq :: Int -> Int -> Bool
intLeq n m = n <= m

{-@ reflect intEq @-}
intEq :: Int -> Int -> Bool
intEq n m = n == m

{-@ lem_step_evals :: e:Expr -> e':Expr -> ProofOf(Step e e') -> ProofOf(EvalsTo e e') @-}
lem_step_evals :: Expr -> Expr -> Step -> EvalsTo
lem_step_evals e e' st_e_e' = AddStep e e' st_e_e' e' (Refl e')

{-@ lem_den_bools :: v:Value -> { t:Type | erase t == BTBase TBool } 
        -> ProofOf(Denotes t v) -> { pf:_ | v == Bc True || v == Bc False } @-}
lem_den_bools :: Expr -> Type -> Denotes -> Proof
lem_den_bools v t den_t_v = lem_bool_values v p_v_bl
  where
    p_v_bl = get_btyp_from_den t v den_t_v

{-@ lem_den_ints :: v:Value -> { t:Type | erase t == BTBase TInt } 
        -> ProofOf(Denotes t v) -> { pf:_ | isInt v } @-}
lem_den_ints :: Expr -> Type -> Denotes -> Proof
lem_den_ints v t den_t_v = lem_int_values v p_v_int
  where
    p_v_int = get_btyp_from_den t v den_t_v

{-@ reduce_eqv :: b:Bool -> b':Bool -> { pf:EvalsTo | propOf pf == EvalsTo (App (delta Eqv (Bc b)) (Bc b')) (Bc (blIff b b')) } @-}
reduce_eqv :: Bool -> Bool -> EvalsTo
reduce_eqv True b' = all_steps
  where
    step_two   = EAppAbs 1 (BV 1) (Bc b')
    all_steps  = AddStep (App (delta Eqv (Bc True)) (Bc b')) (Bc b')  
                         step_two (Bc b') (Refl (Bc b'))
reduce_eqv False b' = all_steps
  where
    step_two   = EAppAbs 1 (App (Prim Not) (BV 1)) (Bc b')
    eval_three = AddStep (App (Prim Not) (Bc b')) (Bc (not b')) (EPrim Not (Bc b')) 
                         (Bc (not b')) (Refl (Bc (not b')))
    all_steps  = AddStep (App (delta Eqv (Bc False)) (Bc b')) 
                         (App (Prim Not) (Bc b')) step_two (Bc (b' == False)) eval_three

