{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-}
{- @ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Primitives2c where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import BasicProps
import Typing
import Primitives

-- force these into scope
semantics = (Step, EvalsTo)
typing = (HasBType, HasType, WFType, WFEnv, Subtype)
denotations = (Entails, Denotes, DenotesEnv, ValueDenoted)

{-@ reflect foo7 @-}
foo7 x = Just x
foo7 :: a -> Maybe a
  

{-@ reduce_eqv_tt :: b:Bool -> b':Bool -> { pf:_ | propOf pf ==
      EvalsTo (subBV 3 (Bc (blIff b b')) (subBV 2 (Bc b') (subBV 1 (Bc b) (refn_pred Eqv)))) (Bc True) } @-}
reduce_eqv_tt :: Bool -> Bool -> EvalsTo
reduce_eqv_tt b b' = final_step
  where
    rhs        = App (App (Prim Or) (App (App (Prim And) (Bc b)) (Bc b')))
                           (App (App (Prim And) (App (Prim Not) (Bc b))) (App (Prim Not) (Bc b')))
    st_eqv_3   = EPrim Eqv (Bc (blIff b b')) 
    step_one   = EApp1 (App (Prim Eqv) (Bc (blIff b b'))) (delta Eqv (Bc (blIff b b'))) st_eqv_3 rhs

    st_and_1   = EPrim And (Bc b)
    st_and_12  = EApp1 (App (Prim And) (Bc b)) (delta And (Bc b)) st_and_1 (Bc b')
    {-@ st_and_2 :: ProofOf(Step (App (delta And (Bc b)) (Bc b')) (Bc (blAnd b b')))  @-}
    st_and_2   = if b then (EAppAbs 1 (BV 1) (Bc b')) else (EAppAbs 1 (Bc False) (Bc b'))
    base_st    = Refl (Bc (b && b'))
    ev_and_12  = AddStep (App (App (Prim And) (Bc b)) (Bc b')) (App (delta And (Bc b)) (Bc b'))
                         st_and_12 (Bc (b && b')) (AddStep (App (delta And (Bc b)) (Bc b')) (Bc (b && b'))
                                                          st_and_2 (Bc (b && b')) base_st)

    step_not_1     = EPrim Not (Bc b) -- App Not b ==> delta Not b == not b 
    st_andnot1a    = EApp2 (App (Prim Not) (Bc b)) (Bc (not b)) step_not_1 (Prim And) -- And (Not b) ==> And (not b)
    st_andnot1b    = EPrim And (Bc (not b))
    st_andnotbase  = Refl (delta And (Bc (not b)))
    ev_andnot1     = AddStep (App (Prim And) (App (Prim Not) (Bc b))) (App (Prim And) (Bc (not b)))
                             st_andnot1a (delta And (Bc (not b)))
                             (AddStep (App (Prim And) (Bc (not b))) (delta And (Bc (not b)))
                                      st_andnot1b (delta And (Bc (not b))) st_andnotbase)
    step_not_2 = EPrim Not (Bc b') -- App Not b' ==> delta Not b' == not b'
    ev_not2    = AddStep (App (Prim Not) (Bc b')) (Bc (not b')) step_not_2
                         (Bc (not b')) (Refl (Bc (not b')))
    ev_andnot2a = if b then (lemma_app_both_many (App (Prim And) (App (Prim Not) (Bc b))) (delta And (Bc False))
                                     ev_andnot1 (App (Prim Not) (Bc b')) (Bc (not b')) ev_not2)
                       else (lemma_app_both_many (App (Prim And) (App (Prim Not) (Bc b))) (delta And (Bc True))
                                     ev_andnot1 (App (Prim Not) (Bc b')) (Bc (not b')) ev_not2)
                   -- we get the term evals to (App (delta And (Bc (not b))) (Bc (not b')))
    {-@ st_andnot2b :: ProofOf(Step (App (delta And (Bc (blNot b))) (Bc (blNot b'))) 
                                    (Bc (blAnd (blNot b) (blNot b')))) @-}
    st_andnot2b = if b then (EAppAbs 1 (Bc False) (Bc (not b'))) else (EAppAbs 1 (BV 1) (Bc (not b')))
    ev_andnot2b = AddStep (App (delta And (Bc (not b))) (Bc (not b'))) (Bc (blAnd (not b) (not b')))
                          st_andnot2b (Bc (blAnd (not b) (not b'))) (Refl (Bc (blAnd (not b) (not b'))))
    ev_and_n12  = lemma_evals_trans (App (App (Prim And) (App (Prim Not) (Bc b))) (App (Prim Not) (Bc b')))
                                    (App (delta And (Bc (not b))) (Bc (not b')))
                                    (Bc (blAnd (not b) (not b'))) ev_andnot2a ev_andnot2b   

    ev_or_1and1 = lemma_app_many2 (Prim Or) (App (App (Prim And) (Bc b)) (Bc b'))   
                                 (Bc (b && b')) ev_and_12
    ev_or_1and2 = AddStep (App (Prim Or) (Bc (b && b'))) (delta Or (Bc (b && b'))) 
                          (EPrim Or (Bc (b && b'))) (delta Or (Bc (b && b')))
                          (Refl (delta Or (Bc (b && b'))))
    ev_or_1and  = lemma_evals_trans (App (Prim Or) (App (App (Prim And) (Bc b)) (Bc b')))
                                    (App (Prim Or) (Bc (b && b'))) (delta Or (Bc (b && b')))
                                    ev_or_1and1 ev_or_1and2
    ev_or_2and1 = if (b && b') then (lemma_app_both_many (App (Prim Or) (App (App (Prim And) (Bc b)) (Bc b')))
                                      (delta Or (Bc True)) ev_or_1and
                                      (App (App (Prim And) (App (Prim Not) (Bc b))) (App (Prim Not) (Bc b')))
                                      (Bc ((not b) && (not b'))) ev_and_n12 )
                               else (lemma_app_both_many (App (Prim Or) (App (App (Prim And) (Bc b)) (Bc b')))
                                      (delta Or (Bc False)) ev_or_1and
                                      (App (App (Prim And) (App (Prim Not) (Bc b))) (App (Prim Not) (Bc b')))
                                      (Bc ((not b) && (not b'))) ev_and_n12 )
 
    {-@ st_or_2and2 :: ProofOf(Step (App (delta Or (Bc (blAnd b b'))) (Bc (blAnd (blNot b) (blNot b'))))
                                    (Bc (blIff b b'))) @-}
    st_or_2and2 = if (b && b') then (EAppAbs 1 (Bc True) (Bc ((not b) && (not b'))))
                               else (EAppAbs 1 (BV 1) (Bc ((not b) && (not b'))))   
    ev_or_2and2 = AddStep (App (delta Or (Bc (b && b'))) (Bc ((not b) && (not b'))))
                          (Bc (blIff b b')) st_or_2and2 (Bc (blIff b b')) (Refl (Bc (blIff b b')))
    ev_or_2and  = lemma_evals_trans rhs (App (delta Or (Bc (b && b'))) (Bc ((not b) && (not b'))))
                                    (Bc (blIff b b')) ev_or_2and1 ev_or_2and2 

    eval_two   = if (blIff b b') then (lemma_app_many2 (delta Eqv (Bc True)) rhs
                                         (Bc (blIff b b')) ev_or_2and)   
                                 else (lemma_app_many2 (delta Eqv (Bc False)) rhs
                                         (Bc (blIff b b')) ev_or_2and)  
    eval_12    = AddStep (App (App (Prim Eqv) (Bc (blIff b b'))) rhs)
                         (App (delta Eqv (Bc (blIff b b')))      rhs)
                         step_one (App (delta Eqv (Bc (blIff b b'))) (Bc (blIff b b'))) eval_two
    eval_three = reduce_eqv (blIff b b') (blIff b b')
    final_step = lemma_evals_trans (App (App (Prim Eqv) (Bc (blIff b b'))) rhs) 
                                   (App (delta Eqv (Bc (blIff b b'))) (Bc (blIff b b'))) (Bc True)
                                   eval_12 eval_three
    

{-@ lem_den_eqv :: ProofOf(Denotes (ty Eqv) (Prim Eqv)) @-}
lem_den_eqv :: Denotes
lem_den_eqv = DFunc 1 (TRefn TBool 4 (Bc True)) t'
                    (Prim Eqv) (BTPrm BEmpty Eqv) val_den_func
  where
    val_den_func :: Expr -> Denotes -> ValueDenoted
    val_den_func v_x den_tx_vx = case v_x of 
      (Bc True)  -> ValDen (App (Prim Eqv) (Bc True)) (tsubBV 1 (Bc True) t') (Lambda 1 (BV 1)) 
                      (lem_step_evals (App (Prim Eqv) (Bc True)) (Lambda 1 (BV 1)) 
                      (EPrim Eqv (Bc True))) den_t't_id
      (Bc False) -> ValDen (App (Prim Eqv) (Bc False)) (tsubBV 1 (Bc False) t') (Lambda 1 (App (Prim Not) (BV 1))) 
                      (lem_step_evals (App (Prim Eqv) (Bc False)) (Lambda 1 (App (Prim Not) (BV 1))) 
                      (EPrim Eqv (Bc False))) den_t'f_nt
      _     -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool 4 (Bc True)) den_tx_vx)
    t' = TFunc 2 (TRefn TBool 5 (Bc True)) (TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                   (App (App (Prim Or) (App (App (Prim And) (BV 1)) (BV 2)) )
                        (App (App (Prim And) (App (Prim Not) (BV 1))) (App (Prim Not) (BV 2))))))
    t't = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                   (App (App (Prim Or) (App (App (Prim And) (Bc True)) (BV 2)) )
                        (App (App (Prim And) (App (Prim Not) (Bc True))) (App (Prim Not) (BV 2)))))
    den_t't_id = DFunc 2 (TRefn TBool 5 (Bc True)) t't (Lambda 1 (BV 1)) 
                       (BTAbs BEmpty 1 (BTBase TBool) (BV 1) (BTBase TBool) 1 (BTVar1 BEmpty 1 (BTBase TBool)))
                       val_den_func2
    val_den_func2 :: Expr -> Denotes -> ValueDenoted
    val_den_func2 v_x den_tx_vx = case v_x of 
      (Bc True)  -> ValDen (App (Lambda 1 (BV 1)) (Bc True)) (tsubBV 2 (Bc True) t't) (Bc True)
                      (lem_step_evals (App (Lambda 1 (BV 1)) (Bc True)) (Bc True) 
                      (EAppAbs 1 (BV 1) (Bc True))) den_t''t_tt
      (Bc False) -> ValDen (App (Lambda 1 (BV 1)) (Bc False)) (tsubBV 2 (Bc False) t't) (Bc False)
                      (lem_step_evals (App (Lambda 1 (BV 1)) (Bc False)) (Bc False) 
                      (EAppAbs 1 (BV 1) (Bc False))) den_t''f_ff
      _          -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool 5 (Bc True)) den_tx_vx)
    t''t = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                   (App (App (Prim Or) (App (App (Prim And) (Bc True)) (Bc True)) )
                        (App (App (Prim And) (App (Prim Not) (Bc True))) (App (Prim Not) (Bc True)))))
    t''f = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                   (App (App (Prim Or) (App (App (Prim And) (Bc True)) (Bc False)) )
                        (App (App (Prim And) (App (Prim Not) (Bc True))) (App (Prim Not) (Bc False)))))
    den_t''t_tt = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                   (App (App (Prim Or) (App (App (Prim And) (Bc True)) (Bc True)) )
                        (App (App (Prim And) (App (Prim Not) (Bc True))) (App (Prim Not) (Bc True)))))
                        (Bc True) (BTBC BEmpty True) eqv_ev_prt''t_tt
    {-@ eqv_ev_prt''t_tt :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc True)) (App (App (Prim Or) (App (App (Prim And) (Bc True)) (Bc True)) ) (App (App (Prim And) (App (Prim Not) (Bc True))) (App (Prim Not) (Bc True))))) (Bc True)) @-}
    eqv_ev_prt''t_tt = reduce_eqv_tt True True
    den_t''f_ff = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                   (App (App (Prim Or) (App (App (Prim And) (Bc True)) (Bc False)) )
                        (App (App (Prim And) (App (Prim Not) (Bc True))) (App (Prim Not) (Bc False)))))
                        (Bc False) (BTBC BEmpty False) eqv_ev_prt''f_ff
    {-@ eqv_ev_prt''f_ff :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc False)) (App (App (Prim Or) (App (App (Prim And) (Bc True)) (Bc False)) ) (App (App (Prim And) (App (Prim Not) (Bc True))) (App (Prim Not) (Bc False))))) (Bc True)) @-}
    eqv_ev_prt''f_ff = reduce_eqv_tt True False

    t'f = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                   (App (App (Prim Or) (App (App (Prim And) (Bc False)) (BV 2)) )
                        (App (App (Prim And) (App (Prim Not) (Bc False))) (App (Prim Not) (BV 2)))))
    den_t'f_nt = DFunc 2 (TRefn TBool 5 (Bc True)) t'f (Lambda 1 (App (Prim Not) (BV 1)))
                       (BTAbs BEmpty 1 (BTBase TBool) (App (Prim Not) (BV 1)) (BTBase TBool) 1 
                              (BTApp (BCons 1 (BTBase TBool) BEmpty) (Prim Not) (BTBase TBool)
                                     (BTBase TBool) (BTPrm (BCons 1 (BTBase TBool) BEmpty) Not)
                                     (FV 1) (BTVar1 BEmpty 1 (BTBase TBool))))  val_den_func3
    val_den_func3 :: Expr -> Denotes -> ValueDenoted
    val_den_func3 v_x den_tx_vx = case v_x of 
      (Bc True)  -> ValDen (App (Lambda 1 (App (Prim Not) (BV 1))) (Bc True)) (tsubBV 2 (Bc True) t'f) 
                      (Bc False) (AddStep (App (Lambda 1 (App (Prim Not) (BV 1))) (Bc True)) 
                                          (App (Prim Not) (Bc True)) 
                                          (EAppAbs 1 (App (Prim Not) (BV 1)) (Bc True))
                                          (Bc False) (lem_step_evals (App (Prim Not) (Bc True))
                                                                     (Bc False) (EPrim Not (Bc True))) )
                                          den_t'''t_ff
      (Bc False) -> ValDen (App (Lambda 1 (App (Prim Not) (BV 1))) (Bc False)) (tsubBV 2 (Bc False) t'f) 
                      (Bc True) (AddStep (App (Lambda 1 (App (Prim Not) (BV 1))) (Bc False)) 
                                          (App (Prim Not) (Bc False)) 
                                          (EAppAbs 1 (App (Prim Not) (BV 1)) (Bc False))
                                          (Bc True) (lem_step_evals (App (Prim Not) (Bc False)) 
                                                                    (Bc True) (EPrim Not (Bc False))) )
                                          den_t'''f_tt
      _          -> impossible ("by lemma" ? lem_den_bools v_x (TRefn TBool 5 (Bc True)) den_tx_vx)
    t'''t = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                   (App (App (Prim Or) (App (App (Prim And) (Bc False)) (Bc True)) )
                        (App (App (Prim And) (App (Prim Not) (Bc False))) (App (Prim Not) (Bc True)))))
    t'''f = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                   (App (App (Prim Or) (App (App (Prim And) (Bc False)) (Bc False)) )
                        (App (App (Prim And) (App (Prim Not) (Bc False))) (App (Prim Not) (Bc False)))))
    den_t'''t_ff = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                   (App (App (Prim Or) (App (App (Prim And) (Bc False)) (Bc True)) )
                        (App (App (Prim And) (App (Prim Not) (Bc False))) (App (Prim Not) (Bc True)))))
                        (Bc False) (BTBC BEmpty False) eqv_ev_prt'''t_ff
    {-@ eqv_ev_prt'''t_ff :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc False)) (App (App (Prim Or) (App (App (Prim And) (Bc False)) (Bc True)) ) (App (App (Prim And) (App (Prim Not) (Bc False))) (App (Prim Not) (Bc True))))) (Bc True)) @-}
    eqv_ev_prt'''t_ff = reduce_eqv_tt False True
    den_t'''f_tt = DRefn TBool 3 (App (App (Prim Eqv) (BV 3)) 
                   (App (App (Prim Or) (App (App (Prim And) (Bc False)) (Bc False)) )
                        (App (App (Prim And) (App (Prim Not) (Bc False))) (App (Prim Not) (Bc False)))))
                        (Bc True) (BTBC BEmpty True) eqv_ev_prt'''f_tt
    {-@ eqv_ev_prt'''f_tt :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc True)) (App (App (Prim Or) (App (App (Prim And) (Bc False)) (Bc False)) ) (App (App (Prim And) (App (Prim Not) (Bc False))) (App (Prim Not) (Bc False))))) (Bc True)) @-}
    eqv_ev_prt'''f_tt = reduce_eqv_tt False False

