{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Implications where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFTyping
import WellFormedness
import PrimitivesFTyping
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasSubstitution
import SystemFSoundness
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import PrimitivesSemantics

{-@ reflect foo31 @-}   
foo31 x = Just x 
foo31 :: a -> Maybe a 

-------------------------------------------------------------------------
------- | IMPLICATIONS
-------------------------------------------------------------------------

--        -> p:Pred -> { q:Pred | Set_emp (freeBV q) } -> ProofOf(HasFType (erase_env g) p (FTBasic TBool))
{-@ lem_implies_elimination :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th) 
        -> p:Pred ->  q:Pred  -> ProofOf(HasFType (erase_env g) p (FTBasic TBool))
                              -> ProofOf(HasFType (erase_env g) q (FTBasic TBool))
        -> ProofOf(EvalsTo (csubst th (App (App (Prim And) p) q)) (Bc True))
        -> (ProofOf(EvalsTo (csubst th p) (Bc True)), ProofOf(EvalsTo (csubst th q) (Bc True))) @-}
lem_implies_elimination :: Env -> CSub -> DenotesEnv -> Pred -> Pred -> HasFType -> HasFType
                               -> EvalsTo -> (EvalsTo, EvalsTo)
lem_implies_elimination g th den_g_th p q pf_p_bl pf_q_bl ev_thpq_tt_ 
  = let thp     = csubst th p
        thq     = csubst th q -- ? lem_csubst_freeBV th q
        pandq   = App (App (Prim And) p) q 
        ev_thpq_tt = ev_thpq_tt_ ? lem_csubst_app th (App (Prim And) p) q
                                 ? lem_csubst_app th (Prim And) p
                                 ? lem_csubst_prim th And
    in case (lemma_evals_app_value (App (Prim And) thp) thq (Bc True) ev_thpq_tt ) of
      (AppRed _ id ev_and_id _ v' ev_thq_v') -> case (lemma_evals_app_value (Prim And) thp id ev_and_id) of
        (AppRed _ _ _ _thp v ev_thp_v) -> case (v, v') of 
          (Bc True, Bc True) -> (ev_thp_v, ev_thq_v')
          (Bc b,    Bc b')   -> impossible ("by lemma" ? lem_evals_val_det (csubst th pandq)
                                                         (Bc True) ev_thpq_tt (Bc False) ev_thpq_ff)
            where
              ev_thpq_ff = lemma_and_semantics thp b ev_thp_v thq b' ev_thq_v'
          _                  -> impossible ("by lemma" ? lem_bool_values v  pf_v_bl
                                                       ? lem_bool_values v' pf_v'_bl)
            where
              pf_thp_bl  = lem_csubst_hasftype g p (TRefn TBool 1 (Bc True)) pf_p_bl th den_g_th
              pf_v_bl    = lemma_soundness thp v ev_thp_v (FTBasic TBool) pf_thp_bl
              pf_thq_bl  = lem_csubst_hasftype g q (TRefn TBool 1 (Bc True)) pf_q_bl th den_g_th
              pf_v'_bl   = lemma_soundness thq v' ev_thq_v' (FTBasic TBool) pf_thq_bl

{-@ lem_implies_conjunction :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th)
        -> p:Pred -> q:Pred
        -> ProofOf(EvalsTo (csubst th p) (Bc True))
        -> ProofOf(EvalsTo (csubst th q) (Bc True))
        -> ProofOf(EvalsTo (csubst th (App (App (Prim And) p) q)) (Bc True)) @-}
lem_implies_conjunction :: Env -> CSub -> DenotesEnv -> Pred -> Pred 
                               -> EvalsTo -> EvalsTo -> EvalsTo
lem_implies_conjunction g th den_g_th p q ev_thp_tt ev_thq_tt
  = let thp     = csubst th p
        thq     = csubst th q 
    in lemma_and_semantics thp True ev_thp_tt thq True ev_thq_tt
                           ? lem_csubst_app th (App (Prim And) p) q
                           ? lem_csubst_app th (Prim And) p
                           ? lem_csubst_prim th And
{-
{-@ lem_implies_introduction :: g:Env -> p:Pred -> q:Pred 
         -> ProofOf(HasFType (erase_env g) p (FTBasic TBool))
         -> ( th':CSub -> ProofOf(DenotesEnv g th') -> ProofOf(EvalsTo (csubst th' p) (Bc True))
                                                    -> ProofOf(EvalsTo (csubst th' q) (Bc True)) )
         -> r:Pred -> ProofOf(HasFType (erase_env g) r (FTBasic TBool))
         -> th:CSub -> ProofOf(DenotesEnv g th) 
         -> ProofOf(EvalsTo (csubst th (App (App (Prim And) p) r)) (Bc True))
         -> ProofOf(EvalsTo (csubst th (App (App (Prim And) q) r)) (Bc True)) @-}
lem_implies_introduction :: Env -> Pred -> Pred -> HasFType
                                -> ( CSub -> DenotesEnv -> EvalsTo -> EvalsTo )
                                -> Pred -> HasFType -> CSub -> DenotesEnv -> EvalsTo -> EvalsTo
lem_implies_introduction g p q pf_p_bl p_implies_q r pf_r_bl th den_g_th ev_thpandr_tt
  = let (ev_thp_tt, ev_thr_tt) = lem_implies_elimination g th den_g_th p r pf_p_bl pf_r_bl ev_thpandr_tt
        ev_thq_tt = p_implies_q th den_g_th ev_thp_tt 
    in lem_implies_conjunction g th den_g_th q r ev_thq_tt ev_thr_tt
-}
      
--        -> p:Pred -> { q:Pred | Set_emp (freeBV q) } -> ProofOf(HasFType (erase_env g) p (FTBasic TBool))
{-@ lem_implies_and_commutes :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th) 
        -> p:Pred -> q:Pred -> ProofOf(HasFType (erase_env g) p (FTBasic TBool))
                            -> ProofOf(HasFType (erase_env g) q (FTBasic TBool))
        -> ProofOf(EvalsTo (csubst th (App (App (Prim And) p) q)) (Bc True))
        -> ProofOf(EvalsTo (csubst th (App (App (Prim And) q) p)) (Bc True)) @-}
lem_implies_and_commutes :: Env -> CSub -> DenotesEnv -> Pred -> Pred 
                                -> HasFType -> HasFType -> EvalsTo -> EvalsTo
lem_implies_and_commutes g th den_g_th p q pf_p_bl pf_q_bl ev_thpq_tt 
  = let thp       = csubst th p
        thq       = csubst th q -- ? lem_csubst_freeBV th q
        (ev_thp_tt, ev_thq_tt) = lem_implies_elimination g th den_g_th p q pf_p_bl pf_q_bl 
                                    ev_thpq_tt  ? lem_csubst_app th (App (Prim And) p) q
                                                ? lem_csubst_app th (Prim And) p
                                                ? lem_csubst_prim th And
    in lemma_and_semantics thq True ev_thq_tt thp True ev_thp_tt
                                    ? lem_csubst_app th (App (Prim And) q) p
                                    ? lem_csubst_app th (Prim And) q
                                    ? lem_csubst_prim th And
