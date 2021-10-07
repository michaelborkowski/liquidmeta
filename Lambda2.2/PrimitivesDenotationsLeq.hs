{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--fuel=4"      @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesDenotationsLeq where

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
import BasicPropsCSubst
import BasicPropsDenotes
import Typing
import Entailments
import PrimitivesSemantics

{-@ reflect foo55 @-}
foo55 x = Just x
foo55 :: a -> Maybe a

{-@ lem_den_leq :: ProofOf(Denotes (ty Leq) (Prim Leq)) @-}
lem_den_leq :: Denotes
lem_den_leq = DFunc 1 (TRefn TInt Z (Bc True)) (ty' Leq) (Prim Leq ? val_leq) 
                    (FTPrm FEmpty Leq) val_den_func_leq
  where
    val_leq  = isValue (Prim Leq) ? isTerm (Prim Leq)

{-@ val_den_func_leq :: v_x:Value -> ProofOf(Denotes (TRefn TInt Z (Bc True)) v_x)
                                  -> ProofOf(ValueDenoted (App (Prim Leq) v_x) (tsubBV 1 v_x (ty' Leq))) @-}
val_den_func_leq :: Expr -> Denotes -> ValueDenoted
val_den_func_leq v_x den_tx_vx = case v_x of 
      (Ic n) -> ValDen (App (Prim Leq) (Ic n)) (tsubBV 1 (Ic n) (ty' Leq)) (Prim (Leqn n))
                       (lem_step_evals (App (Prim Leq) (Ic n)) (Prim (Leqn n)) 
                       (EPrim Leq (Ic n))) (den_t'leqn_leq n)
      _      -> impossible ("by lemma" ? lem_den_ints v_x (TRefn TInt Z (Bc True)) den_tx_vx)

{-@ den_t'leqn_leq ::  n:Int -> ProofOf(Denotes (tsubBV 1 (Ic n) (ty' Leq)) (Prim (Leqn n))) @-}
den_t'leqn_leq :: Int -> Denotes
den_t'leqn_leq n = DFunc 2 (TRefn TInt Z (Bc True)) t'leqn_n (Prim (Leqn n) ? val_leqn) 
                               (FTPrm FEmpty (Leqn n)) (val_den_func_leq2 n)
    ? ( tsubBV 1 (Ic n ? term_n) (ty' Leq) ? lem_tsubBV_notin 1 (Ic n ? term_n) (TRefn TInt Z (Bc True))
    === TFunc 2 (TRefn TInt Z (Bc True)) (tsubBV 1 (Ic n ? term_n) (TRefn TBool Z (refn_pred Leq))) )
  where
    t'leqn_n = tsubBV 1 (Ic n ? term_n) (TRefn TBool Z (refn_pred Leq))
    term_n   = isTerm (Ic n)
    val_leqn = isValue (Prim (Leqn n)) ? isTerm (Prim (Leqn n))

{-@ val_den_func_leq2 :: n:Int -> v_x:Value -> ProofOf(Denotes (TRefn TInt Z (Bc True)) v_x)
      -> ProofOf(ValueDenoted (App (Prim (Leqn n)) v_x) 
                              (tsubBV 2 v_x (tsubBV 1 (Ic n) (TRefn TBool Z (refn_pred Leq))))) @-}
val_den_func_leq2 :: Int -> Expr -> Denotes -> ValueDenoted
val_den_func_leq2 n v_x den_tx_vx = case v_x of 
    (Ic m) -> ValDen (App (Prim (Leqn n)) (Ic m)) (tsubBV 2 (Ic m) t'leqn_n) (Bc (n <= m) ? tm_nm)
                     (lem_step_evals (App (Prim (Leqn n)) (Ic m)) (Bc (n <= m)) 
                     (EPrim (Leqn n) (Ic m))) den_t'leqnm_lte
      where
        t'leqn_n = tsubBV 1 (Ic n ? term_n) (TRefn TBool Z (refn_pred Leq))
        den_t'leqnm_lte = DRefn TBool Z p_nm (Bc (n <= m) ? tm_nm) (FTBC FEmpty (n <= m)) ev_prt'leqnm_lte
        p_nm     = subBV 2 (Ic m) (subBV 1 (Ic n ? term_n) (refn_pred Leq))
        {-@ ev_prt'leqnm_lte :: ProofOf(EvalsTo (subBV 0 (Bc (intLeq n m)) (subBV 2 (Ic m) (subBV 1 (Ic n) (refn_pred Leq)))) (Bc True)) @-}
        --ev_prt'leqnm_lte :: EvalsTo
        ev_prt'leqnm_lte = reduce_leq_tt n m ? intLeq n m
        term_n   = isTerm (Ic n)
        tm_nm    = isTerm (Bc (n <= m))
    _      -> impossible ("by lemma" ? lem_den_ints v_x (TRefn TInt Z (Bc True)) den_tx_vx)


{-@ lem_den_leqn :: n:Int -> ProofOf(Denotes (ty (Leqn n)) (Prim (Leqn n))) @-}
lem_den_leqn :: Int -> Denotes
lem_den_leqn n = DFunc 2 (TRefn TInt Z (Bc True)) (ty' (Leqn n)) (Prim (Leqn n) ? val_leqn) 
                       (FTPrm FEmpty (Leqn n)) (val_den_func_leqn n)
  where
    val_leqn = isValue (Prim (Leqn n)) ? isTerm (Prim (Leqn n))

{-@ val_den_func_leqn :: n:Int -> v_x:Value -> ProofOf(Denotes (TRefn TInt Z (Bc True)) v_x)
                      -> ProofOf(ValueDenoted (App (Prim (Leqn n)) v_x) (tsubBV 2 v_x (ty' (Leqn n)))) @-}
val_den_func_leqn :: Int -> Expr -> Denotes -> ValueDenoted
val_den_func_leqn n v_x den_tx_vx = case v_x of 
  (Ic m) -> ValDen (App (Prim (Leqn n)) (Ic m)) (tsubBV 2 (Ic m) (ty' (Leqn n))) (Bc (n <= m) ? tm_nm)
                   (lem_step_evals (App (Prim (Leqn n)) (Ic m)) (Bc (n <= m)) (EPrim (Leqn n) (Ic m)))
                   den_t'leqnm_lte
    where
      den_t'leqnm_lte = DRefn TBool Z p_nm (Bc (n <= m) ? tm_nm) (FTBC FEmpty (n <= m)) ev_prt'leqnm_nlte
      p_nm            = subBV 2 (Ic m) (refn_pred (Leqn n))
      {- @ ev_prt'nm_nlte :: ProofOf(EvalsTo (App (App (Prim Eqv) (Bc (intLeq n m))) 
                                             (App (App (Prim Leq) (Ic n)) (Ic m))) (Bc True)) @-}
      ev_prt'leqnm_nlte = reduce_leqn_tt n m ? intLeq n m 
      tm_nm           = isTerm (Bc (n <= m))
  _      -> impossible ("by lemma" ? lem_den_ints v_x (TRefn TInt Z (Bc True)) den_tx_vx)
