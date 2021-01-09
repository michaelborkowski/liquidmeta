{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesSemantics where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import PrimitivesFTyping
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasSubstitution
import Typing
import SystemFAlphaEquivalence
import BasicPropsCSubst
import BasicPropsDenotes

{-@ reflect foo30 @-}
foo30 x = Just x
foo30 :: a -> Maybe a

-----------------------------------------------------------------------
-- | BUILT-IN PRIMITIVES : Big-Step-style SEMANTICS 
-----------------------------------------------------------------------

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

{-@ lemma_reduce_to_delta :: c:Prim -> p:Pred -> { v:Value | isCompat c v } -> ProofOf(EvalsTo p v)
                          -> ProofOf(EvalsTo (App (Prim c) p) (delta c v)) @-}
lemma_reduce_to_delta :: Prim -> Expr -> Expr -> EvalsTo -> EvalsTo
lemma_reduce_to_delta c p v ev_p_v = ev_appcp
  where
    ev_appcp_1 = lemma_app_many2 (Prim c) p v ev_p_v
    st_appcp_2 = EPrim c v
    ev_appcp   = lemma_add_step_after (App (Prim c) p) (App (Prim c) v) ev_appcp_1 (delta c v) st_appcp_2
  
{-@ lemma_conj_semantics :: p:Expr -> b:Bool  -> ProofOf(EvalsTo p (Bc b))
                         -> q:Expr -> b':Bool -> ProofOf(EvalsTo q (Bc b'))
                         -> ProofOf(EvalsTo (App (App (Prim Conj) p) q) (Bc (blAnd b b'))) @-}
lemma_conj_semantics :: Expr -> Bool -> EvalsTo -> Expr -> Bool -> EvalsTo -> EvalsTo
lemma_conj_semantics p b ev_p_b q b' ev_q_b' = ev_andpq
  where
    ev_andp    = lemma_reduce_to_delta Conj p (Bc b) ev_p_b
    ev_andpq_1 = lemma_app_both_many (App (Prim Conj) p) (delta Conj (Bc b)) ev_andp q (Bc b') ev_q_b'
    {-@ st_andpq_2 :: ProofOf(Step (App (delta Conj (Bc b)) (Bc b')) (Bc (blAnd b b'))) @-}
    st_andpq_2 = if b then ( EAppAbs 1 (BV 1)     (Bc b') )
                      else ( EAppAbs 1 (Bc False) (Bc b') )
    ev_andpq   = lemma_add_step_after (App (App (Prim Conj) p) q) (App (delta Conj (Bc b)) (Bc b'))
                                      ev_andpq_1 (Bc (b && b')) st_andpq_2

{-@ lemma_and_semantics :: p:Expr -> b:Bool  -> ProofOf(EvalsTo p (Bc b))
                        -> q:Expr -> b':Bool -> ProofOf(EvalsTo q (Bc b'))
                        -> ProofOf(EvalsTo (App (App (Prim And) p) q) (Bc (blAnd b b'))) @-}
lemma_and_semantics :: Expr -> Bool -> EvalsTo -> Expr -> Bool -> EvalsTo -> EvalsTo
lemma_and_semantics p b ev_p_b q b' ev_q_b' = ev_andpq
  where
    ev_andp    = lemma_reduce_to_delta And p (Bc b) ev_p_b
    ev_andpq_1 = lemma_app_both_many (App (Prim And) p) (delta And (Bc b)) ev_andp q (Bc b') ev_q_b'
    {-@ st_andpq_2 :: ProofOf(Step (App (delta And (Bc b)) (Bc b')) (Bc (blAnd b b'))) @-}
    st_andpq_2 = if b then ( EAppAbs 1 (BV 1)     (Bc b') )
                      else ( EAppAbs 1 (Bc False) (Bc b') )
    ev_andpq   = lemma_add_step_after (App (App (Prim And) p) q) (App (delta And (Bc b)) (Bc b'))
                                      ev_andpq_1 (Bc (b && b')) st_andpq_2

{-@ lemma_or_semantics :: p:Expr -> b:Bool  -> ProofOf(EvalsTo p (Bc b))
                       -> q:Expr -> b':Bool -> ProofOf(EvalsTo q (Bc b'))
                       -> ProofOf(EvalsTo (App (App (Prim Or) p) q) (Bc (blOr b b'))) @-}
lemma_or_semantics :: Expr -> Bool -> EvalsTo -> Expr -> Bool -> EvalsTo -> EvalsTo
lemma_or_semantics p b ev_p_b q b' ev_q_b' = ev_orpq
  where
    ev_orp    = lemma_reduce_to_delta Or p (Bc b) ev_p_b
    ev_orpq_1 = lemma_app_both_many (App (Prim Or) p) (delta Or (Bc b)) ev_orp q (Bc b') ev_q_b'
    {-@ st_orpq_2 :: ProofOf(Step (App (delta Or (Bc b)) (Bc b')) (Bc (blOr b b'))) @-}
    st_orpq_2 = if b then ( EAppAbs 1 (Bc True) (Bc b') )
                     else ( EAppAbs 1 (BV 1)    (Bc b') )
    ev_orpq   = lemma_add_step_after (App (App (Prim Or) p) q) (App (delta Or (Bc b)) (Bc b'))
                                     ev_orpq_1 (Bc (b || b')) st_orpq_2

{-@ lemma_not_semantics :: p:Expr -> b:Bool  -> ProofOf(EvalsTo p (Bc b))
                        -> ProofOf(EvalsTo (App (Prim Not) p) (Bc (blNot b))) @-}
lemma_not_semantics :: Expr -> Bool -> EvalsTo -> EvalsTo
lemma_not_semantics p b ev_p_b = lemma_reduce_to_delta Not p (Bc b) ev_p_b

{-@ lemma_eqv_semantics :: p:Expr -> b:Bool  -> ProofOf(EvalsTo p (Bc b))
                        -> q:Expr -> b':Bool -> ProofOf(EvalsTo q (Bc b'))
                        -> ProofOf(EvalsTo (App (App (Prim Eqv) p) q) (Bc (blIff b b'))) @-}
lemma_eqv_semantics :: Expr -> Bool -> EvalsTo -> Expr -> Bool -> EvalsTo -> EvalsTo
lemma_eqv_semantics p b ev_p_b q b' ev_q_b' = ev_eqvpq
  where
    ev_eqvp     = lemma_reduce_to_delta Eqv p (Bc b) ev_p_b
    ev_eqvpq_1  = lemma_app_both_many (App (Prim Eqv) p) (delta Eqv (Bc b)) ev_eqvp q (Bc b') ev_q_b'
    {-@ st_eqvpq_2a :: { step:Step | ( b && propOf step == Step (App (delta Eqv (Bc b)) (Bc b')) (Bc b')) ||
                 ( not b && propOf step == Step (App (delta Eqv (Bc b)) (Bc b')) (App (Prim Not) (Bc b'))) } @-}
    st_eqvpq_2a = if b then ( EAppAbs 1 (BV 1) (Bc b') )
                       else ( EAppAbs 1 (App (Prim Not) (BV 1)) (Bc b') )
    ev_eqvpq_2b = if b then ( Refl (Bc b') )
                       else ( lemma_not_semantics (Bc b') b' (Refl (Bc b')))
    {-@ ev_eqvpq_2 :: ProofOf(EvalsTo (App (delta Eqv (Bc b)) (Bc b')) (Bc (blIff b b'))) @-}
    ev_eqvpq_2  = if b then ( AddStep (App (delta Eqv (Bc b)) (Bc b')) (Bc b') st_eqvpq_2a
                                      (Bc b') ev_eqvpq_2b )
                       else ( AddStep (App (delta Eqv (Bc b)) (Bc b')) (App (Prim Not) (Bc b'))
                                      st_eqvpq_2a (Bc (blNot b')) ev_eqvpq_2b )
    ev_eqvpq    = lemma_evals_trans (App (App (Prim Eqv) p) q) (App (delta Eqv (Bc b)) (Bc b'))
                                    (Bc (blIff b b')) ev_eqvpq_1 ev_eqvpq_2

{-@ lemma_leq_semantics :: p:Expr -> n:Int -> ProofOf(EvalsTo p (Ic n))
                        -> q:Expr -> m:Int -> ProofOf(EvalsTo q (Ic m))
                        -> ProofOf(EvalsTo (App (App (Prim Leq) p) q) (Bc (intLeq n m))) @-}
lemma_leq_semantics :: Expr -> Int -> EvalsTo -> Expr -> Int -> EvalsTo -> EvalsTo
lemma_leq_semantics p n ev_p_n q m ev_q_m = ev_leqpq
  where
    ev_leqp    = lemma_reduce_to_delta Leq p (Ic n) ev_p_n
    ev_leqpq_1 = lemma_app_both_many (App (Prim Leq) p) (delta Leq (Ic n)) ev_leqp q (Ic m) ev_q_m
    ev_leqpq_2 = lemma_leqn_semantics n (Ic m) m (Refl (Ic m))
    ev_leqpq   = lemma_evals_trans (App (App (Prim Leq) p) q) (App (Prim (Leqn n)) (Ic m)) 
                                   (Bc (n <= m)) ev_leqpq_1 ev_leqpq_2

{-@ lemma_leqn_semantics :: n:Int -> q:Expr -> m:Int -> ProofOf(EvalsTo q (Ic m))
                         -> ProofOf(EvalsTo (App (Prim (Leqn n)) q) (Bc (intLeq n m))) @-}
lemma_leqn_semantics :: Int -> Expr -> Int -> EvalsTo -> EvalsTo
lemma_leqn_semantics n q m ev_q_m = lemma_reduce_to_delta (Leqn n) q (Ic m) ev_q_m
   
{-@ lemma_eq_semantics :: p:Expr -> n:Int -> ProofOf(EvalsTo p (Ic n))
                       -> q:Expr -> m:Int -> ProofOf(EvalsTo q (Ic m))
                       -> ProofOf(EvalsTo (App (App (Prim Eq) p) q) (Bc (intEq n m))) @-}
lemma_eq_semantics :: Expr -> Int -> EvalsTo -> Expr -> Int -> EvalsTo -> EvalsTo
lemma_eq_semantics p n ev_p_n q m ev_q_m = ev_eqpq
  where
    ev_eqp    = lemma_reduce_to_delta Eq p (Ic n) ev_p_n
    ev_eqpq_1 = lemma_app_both_many (App (Prim Eq) p) (delta Eq (Ic n)) ev_eqp q (Ic m) ev_q_m
    ev_eqpq_2 = lemma_eqn_semantics n (Ic m) m (Refl (Ic m))
    ev_eqpq   = lemma_evals_trans (App (App (Prim Eq) p) q) (App (Prim (Eqn n)) (Ic m)) 
                                   (Bc (n == m)) ev_eqpq_1 ev_eqpq_2

{-@ lemma_eqn_semantics :: n:Int -> q:Expr -> m:Int -> ProofOf(EvalsTo q (Ic m))
                        -> ProofOf(EvalsTo (App (Prim (Eqn n)) q) (Bc (intEq n m))) @-}
lemma_eqn_semantics :: Int -> Expr -> Int -> EvalsTo -> EvalsTo
lemma_eqn_semantics n q m ev_q_m = lemma_reduce_to_delta (Eqn n) q (Ic m) ev_q_m
   
--replace `reduce_eqv b b'` by `lemma_eqv_semantics (Bc b) b (Refl (Bc b)) (Bc b') ....
--replace `reduce_eq  n m`  by `lemma_eq_semantics (Ic n) ....

---------------------------------------------------------------------------
-- | BUILT-IN PRIMITIVES : Big-Step-style SEMANTICS for ty(c)'s refinement 
---------------------------------------------------------------------------

{-@ lemma_semantics_refn_and :: b:Bool -> b':Bool -> b'':Bool 
                -> ProofOf(EvalsTo (App (App (Prim Eqv) (Bc b'')) (App (App (Prim And) (Bc b)) (Bc b'))) 
                                   (Bc (blIff b'' (blAnd b b'))) ) @-}
lemma_semantics_refn_and :: Bool -> Bool -> Bool -> EvalsTo
lemma_semantics_refn_and b b' b'' = reduce_eqv
  where
    reduce_and = lemma_and_semantics (Bc b) b (Refl (Bc b)) (Bc b') b' (Refl (Bc b'))
    reduce_eqv = lemma_eqv_semantics (Bc b'') b'' (Refl (Bc b'')) 
                                     (App (App (Prim And) (Bc b)) (Bc b')) (blAnd b b') reduce_and

{-@ reduce_and_tt :: b:Bool -> b':Bool -> { pf:_ | propOf pf == 
      EvalsTo (subBV 0 (Bc (blAnd b b')) (subBV 2 (Bc b') (subBV 1 (Bc b) (refn_pred And)))) (Bc True) } @-}
reduce_and_tt :: Bool -> Bool -> EvalsTo
reduce_and_tt b b' = lemma_semantics_refn_and b b' (b && b') -- (Bc b) b (Refl (Bc b)) (Bc b') b' (Refl (Bc b'))
                                             -- (Bc (blAnd b b')) (b && b') (Refl (Bc (b && b'))) 

{-@ lemma_semantics_refn_or :: b:Bool -> b':Bool -> b'':Bool 
                -> ProofOf(EvalsTo (App (App (Prim Eqv) (Bc b'')) (App (App (Prim Or) (Bc b)) (Bc b'))) 
                                   (Bc (blIff b'' (blOr b b'))) ) @-}
lemma_semantics_refn_or :: Bool -> Bool -> Bool -> EvalsTo
lemma_semantics_refn_or b b' b'' = reduce_eqv
  where
    reduce_or  = lemma_or_semantics (Bc b) b (Refl (Bc b)) (Bc b') b' (Refl (Bc b'))
    reduce_eqv = lemma_eqv_semantics (Bc b'') b'' (Refl (Bc b'')) 
                                     (App (App (Prim Or) (Bc b)) (Bc b')) (blOr b b') reduce_or

{-@ reduce_or_tt :: b:Bool -> b':Bool -> { pf:_ | propOf pf == 
      EvalsTo (subBV 0 (Bc (blOr b b')) (subBV 2 (Bc b') (subBV 1 (Bc b) (refn_pred Or)))) (Bc True) } @-}
reduce_or_tt :: Bool -> Bool -> EvalsTo
reduce_or_tt b b' = lemma_semantics_refn_or b b' (b || b')

{-@ lemma_semantics_refn_not :: b:Bool -> b':Bool
                -> ProofOf(EvalsTo (App (App (Prim Eqv) (Bc b')) (App (Prim Not) (Bc b))) 
                                   (Bc (blIff b' (blNot b)))) @-}
lemma_semantics_refn_not :: Bool -> Bool -> EvalsTo
lemma_semantics_refn_not b b' = reduce_eqv
  where
    reduce_not = lemma_not_semantics (Bc b) b (Refl (Bc b))
    reduce_eqv = lemma_eqv_semantics (Bc b') b' (Refl (Bc b')) (App (Prim Not) (Bc b)) (blNot b) reduce_not

{-@ reduce_not_tt :: b:Bool -> { pf:_ | propOf pf ==
      EvalsTo (subBV 0 (Bc (blNot b)) (subBV 2 (Bc b) (refn_pred Not))) (Bc True) } @-}
reduce_not_tt :: Bool -> EvalsTo
reduce_not_tt b = lemma_semantics_refn_not b (blNot b)

{-@ lemma_semantics_refn_eqv :: b:Bool -> b':Bool -> b'':Bool
                -> ProofOf(EvalsTo (App (App (Prim Eqv) (Bc b'')) (App (App (Prim Or) 
                                        (App (App (Prim And) (Bc b)) (Bc b')))
                                        (App (App (Prim And) (App (Prim Not) (Bc b))) (App (Prim Not) (Bc b')))))
                                   (Bc (blIff b'' (blIff b b'))) ) @-}
lemma_semantics_refn_eqv :: Bool -> Bool -> Bool -> EvalsTo
lemma_semantics_refn_eqv b b' b'' = reduce_eqv
  where
    reduce_left_and  = lemma_and_semantics (Bc b) b (Refl (Bc b)) (Bc b') b' (Refl (Bc b'))
    reduce_right_and = lemma_and_semantics (App (Prim Not) (Bc b)) (blNot b) 
                                           (lemma_not_semantics (Bc b) b (Refl (Bc b)))
                                           (App (Prim Not) (Bc b')) (blNot b')
                                           (lemma_not_semantics (Bc b') b' (Refl (Bc b')))
    reduce_or        = lemma_or_semantics (App (App (Prim And) (Bc b)) (Bc b')) (blAnd b b') reduce_left_and
                           (App (App (Prim And) (App (Prim Not) (Bc b))) (App (Prim Not) (Bc b'))) 
                           (blAnd (blNot b) (blNot b')) reduce_right_and
    reduce_eqv       = lemma_eqv_semantics (Bc b'') b'' (Refl (Bc b'')) 
                           (App (App (Prim Or) (App (App (Prim And) (Bc b)) (Bc b')))
                                 (App (App (Prim And) (App (Prim Not) (Bc b))) (App (Prim Not) (Bc b'))))
                           (blIff b b') reduce_or

{-@ reduce_eqv_tt :: b:Bool -> b':Bool -> { pf:_ | propOf pf ==
      EvalsTo (subBV 0 (Bc (blIff b b')) (subBV 2 (Bc b') (subBV 1 (Bc b) (refn_pred Eqv)))) (Bc True) } @-}
reduce_eqv_tt :: Bool -> Bool -> EvalsTo
reduce_eqv_tt b b' = lemma_semantics_refn_eqv b b' (blIff b b')

{-@ lemma_semantics_refn_leq :: n:Int -> m:Int -> b'':Bool
                -> ProofOf(EvalsTo (App (App (Prim Eqv) (Bc b'')) (App (App (Prim Leq) (Ic n)) (Ic m))) 
                                   (Bc (blIff b'' (intLeq n m)))) @-}
lemma_semantics_refn_leq :: Int -> Int -> Bool -> EvalsTo
lemma_semantics_refn_leq n m b'' = reduce_eqv
  where
    reduce_leq = lemma_leq_semantics (Ic n) n (Refl (Ic n)) (Ic m) m (Refl (Ic m))
    reduce_eqv = lemma_eqv_semantics (Bc b'') b'' (Refl (Bc b''))
                                     (App (App (Prim Leq) (Ic n)) (Ic m)) (intLeq n m) reduce_leq
  
{-@ reduce_leq_tt :: n:Int -> m:Int -> { pf:_ | propOf pf == 
      EvalsTo (subBV 0 (Bc (intLeq n m)) (subBV 2 (Ic m) (subBV 1 (Ic n) (refn_pred Leq)))) (Bc True) } @-}
reduce_leq_tt :: Int -> Int -> EvalsTo
reduce_leq_tt n m = lemma_semantics_refn_leq n m (intLeq n m)

{-@ reduce_leqn_tt :: n:Int -> m:Int -> { pf:_ | propOf pf ==
      EvalsTo (subBV 0 (Bc (intLeq n m)) (subBV 2 (Ic m) (refn_pred (Leqn n)))) (Bc True) } @-}
reduce_leqn_tt :: Int -> Int -> EvalsTo
reduce_leqn_tt n m = reduce_leq_tt n m

{-@ lemma_semantics_refn_eq :: n:Int -> m:Int -> b'':Bool
                -> ProofOf(EvalsTo (App (App (Prim Eqv) (Bc b'')) (App (App (Prim Eq) (Ic n)) (Ic m))) 
                                   (Bc (blIff b'' (intEq n m)))) @-}
lemma_semantics_refn_eq :: Int -> Int -> Bool -> EvalsTo
lemma_semantics_refn_eq n m b'' = reduce_eqv
  where
    reduce_eq  = lemma_eq_semantics (Ic n) n (Refl (Ic n)) (Ic m) m (Refl (Ic m))
    reduce_eqv = lemma_eqv_semantics (Bc b'') b'' (Refl (Bc b''))
                                     (App (App (Prim Eq) (Ic n)) (Ic m)) (intEq n m) reduce_eq
  
{-@ reduce_eq_tt :: n:Int -> m:Int -> { pf:_ | propOf pf == 
      EvalsTo (subBV 0 (Bc (intEq n m)) (subBV 2 (Ic m) (subBV 1 (Ic n) (refn_pred Eq)))) (Bc True) } @-}
reduce_eq_tt :: Int -> Int -> EvalsTo
reduce_eq_tt n m = lemma_semantics_refn_eq n m (intEq n m)

{-@ reduce_eqn_tt :: n:Int -> m:Int -> { pf:_ | propOf pf ==
      EvalsTo (subBV 0 (Bc (intEq n m)) (subBV 2 (Ic m) (refn_pred (Eqn n)))) (Bc True) } @-}
reduce_eqn_tt :: Int -> Int -> EvalsTo
reduce_eqn_tt n m = reduce_eq_tt n m

------------------------------------------------------------------------
-- | Denotations of the Basic Types
-- ---------------------------------------------------------------------


{-@ lem_den_bools :: v:Value -> { t:Type | erase t == FTBasic TBool } 
        -> ProofOf(Denotes t v) -> { pf:_ | v == Bc True || v == Bc False } @-}
lem_den_bools :: Expr -> Type -> Denotes -> Proof
lem_den_bools v t den_t_v = case ae_s_bool of 
    (AEBasic _ _ ) -> lem_bool_values v p_v_s
  where
    (AEWitness _ _ _ s ae_s_bool p_v_s) = get_aewitness_from_den t v den_t_v

{-@ lem_den_ints :: v:Value -> { t:Type | erase t == FTBasic TInt } 
        -> ProofOf(Denotes t v) -> { pf:_ | isInt v } @-}
lem_den_ints :: Expr -> Type -> Denotes -> Proof
lem_den_ints v t den_t_v = case ae_s_int of 
    (AEBasic _ _) -> lem_int_values v p_v_s
  where
    (AEWitness _ _ _ s ae_s_int p_v_s) = get_aewitness_from_den t v den_t_v
