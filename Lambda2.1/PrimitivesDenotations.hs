{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple-local"   @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesDenotations where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import Typing
import Entailments
import BasicPropsCSubst
import PrimitivesSemantics
{-import PrimitivesDenotationsAnd
import PrimitivesDenotationsOr
import PrimitivesDenotationsNot
import PrimitivesDenotationsEqv
import PrimitivesDenotationsLeq
import PrimitivesDenotationsEq
import PrimitivesDenotationsEql-}

{-@ reflect foo58 @-}
foo58 x = Just x
foo58 :: a -> Maybe a

{-@ ple reduce_pred_tybc @-}
{-@ reduce_pred_tybc :: b:Bool -> ProofOf(EvalsTo (subBV 0 (Bc b) (App (App (Prim Eqv) (BV 0)) (Bc b))) (Bc True)) @-}
reduce_pred_tybc :: Bool -> EvalsTo
reduce_pred_tybc b = lemma_eqv_semantics (Bc b) b (Refl (Bc b)) (Bc b) b (Refl (Bc b))

-- Lemma. Denotations of Primitive/Constant Types
{-@ lem_den_tybc :: b:Bool -> ProofOf(Denotes (tybc b) (Bc b)) @-}
lem_den_tybc ::  Bool -> Denotes
lem_den_tybc b = DRefn TBool Z (App (App (Prim Eqv) (BV 0)) (Bc b) ? pred_pf) 
                       (Bc b ? val_pf) (FTBC FEmpty b) (reduce_pred_tybc b)
                       ? toProof ( tybc b === TRefn TBool Z (App (App (Prim Eqv) (BV 0)) (Bc b)) )
  where
    val_pf    = toProof ( isValue (Bc b) === True )
    pred_pf   = toProof ( isPred (App (App (Prim Eqv) (BV 0)) (Bc b))
                    === ( isTerm (App (Prim Eqv) (BV 0)) && isTerm (Bc b) )
                    === ( isTerm (Prim Eqv) && isTerm (BV 0) && isTerm (Bc b) )
                    ===    True )
 
{-@ ple reduce_pred_tyic @-}
{-@ reduce_pred_tyic :: n:Int -> ProofOf(EvalsTo (subBV 0 (Ic n) (App (App (Prim Eq) (BV 0)) (Ic n))) (Bc True)) @-}
reduce_pred_tyic :: Int -> EvalsTo
reduce_pred_tyic n = lemma_eq_semantics (Ic n) n (Refl (Ic n)) (Ic n) n (Refl (Ic n))

{-@ lem_den_tyic :: n:Int -> ProofOf(Denotes (tyic n) (Ic n)) @-}
lem_den_tyic :: Int -> Denotes
lem_den_tyic n = DRefn TInt Z (App (App (Prim Eq) (BV 0)) (Ic n) ? pred_pf) 
                       (Ic n ? val_pf) (FTIC FEmpty n) (reduce_pred_tyic n)
                       ? toProof ( tyic n === TRefn TInt Z (App (App (Prim Eq) (BV 0)) (Ic n)) )
  where
    val_pf    = toProof ( isValue (Ic n) === True )
    pred_pf   = toProof ( isPred (App (App (Prim Eq) (BV 0)) (Ic n))
                    === ( isTerm (App (Prim Eq) (BV 0)) && isTerm (Ic n) )
                    === ( isTerm (Prim Eq) && isTerm (BV 0) && isTerm (Ic n) )
                    ===    True )

{-@ lem_den_ty :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th)
        -> c:Prim -> ProofOf(Denotes (ctsubst th (ty c)) (Prim c)) @-}
lem_den_ty :: Env -> CSub -> DenotesEnv -> Prim -> Denotes
lem_den_ty g th den_g_th c = undefined {-
lem_den_ty g th den_g_th And      = lem_den_and    ? lem_ctsubst_nofree th (ty And)
lem_den_ty g th den_g_th Or       = lem_den_or     ? lem_ctsubst_nofree th (ty Or)
lem_den_ty g th den_g_th Not      = lem_den_not () ? lem_ctsubst_nofree th (ty Not)
lem_den_ty g th den_g_th Eqv      = lem_den_eqv    ? lem_ctsubst_nofree th (ty Eqv)
lem_den_ty g th den_g_th Leq      = lem_den_leq    ? lem_ctsubst_nofree th (ty Leq)
lem_den_ty g th den_g_th (Leqn n) = lem_den_leqn n ? lem_ctsubst_nofree th (ty (Leqn n))
lem_den_ty g th den_g_th Eq       = lem_den_eq     ? lem_ctsubst_nofree th (ty Eq)
lem_den_ty g th den_g_th (Eqn n)  = lem_den_eqn  n ? lem_ctsubst_nofree th (ty (Eqn n))
lem_den_ty g th den_g_th Eql      = lem_den_eql () ? lem_ctsubst_nofree th (ty Eql)
-}
{-@ lem_denote_sound_typ_tprim :: g:Env -> c:Prim 
        ->  th:CSub  -> ProofOf(DenotesEnv g th)
        -> ProofOf(ValueDenoted (csubst th (Prim c)) (ctsubst th (ty c))) @-}
lem_denote_sound_typ_tprim :: Env -> Prim -> CSub -> DenotesEnv -> ValueDenoted
lem_denote_sound_typ_tprim g c th den_g_th 
  = ValDen (Prim c ? lem_csubst_prim th c) (ctsubst th (ty c)) (Prim c ? val_pf ? term_pf) 
           (Refl (Prim c)) den_tyc_c
      where
        den_tyc_c = lem_den_ty g th den_g_th c
        val_pf    = toProof ( isValue (Prim c) === True )
        term_pf   = toProof ( isTerm (Prim c) === True )
