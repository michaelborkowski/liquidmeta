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
import SystemFWellFormedness
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
import BasicPropsEraseTyping
import PrimitivesSemantics
import LemmasWellFormedness

{-@ reflect foo38 @-}   
foo38 x = Just x 
foo38 :: a -> Maybe a 

-------------------------------------------------------------------------
------- | IMPLICATIONS
-------------------------------------------------------------------------

--        -> p:Pred -> { q:Pred | Set_emp (freeBV q) } -> ProofOf(HasFType (erase_env g) p (FTBasic TBool))
{-@ lem_implies_elimination :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th) -> ProofOf(WFFE (erase_env g))
        -> p:Pred -> q:Pred -> ProofOf(HasFType (erase_env g) p (FTBasic TBool))
                            -> ProofOf(HasFType (erase_env g) q (FTBasic TBool))
        -> ProofOf(EvalsTo (csubst th (Conj p q)) (Bc True))
        -> (ProofOf(EvalsTo (csubst th p) (Bc True)), ProofOf(EvalsTo (csubst th q) (Bc True))) @-}
lem_implies_elimination :: Env -> CSub -> DenotesEnv -> WFFE -> Expr -> Expr -> HasFType -> HasFType
                               -> EvalsTo -> (EvalsTo, EvalsTo)
lem_implies_elimination g th den_g_th p_g_wf p q pf_p_bl pf_q_bl ev_thpq_tt_ 
  = let thp     = csubst th p
        thq     = csubst th q -- ? lem_csubst_freeBV th q
        pandq   = Conj p q 
        ev_thpq_tt = ev_thpq_tt_ ? lem_csubst_conj th  p q
        (ConjRed _thp v ev_thp_v _ v' ev_thq_v')
                = lemma_evals_conj_value thp thq (Bc True) ev_thpq_tt
    in case (v, v') of 
          (Bc True, Bc True) -> (ev_thp_v, ev_thq_v')
          (Bc b,    Bc b')   -> impossible ("by lemma" ? lem_evals_val_det (csubst th pandq)
                                                         (Bc True) ev_thpq_tt (Bc False) ev_thpq_ff) 
            where
              ev_thpq_ff = lemma_conj_semantics thp b ev_thp_v thq b' ev_thq_v'
          _                  -> impossible ("by lemma" ? lem_bool_values v  pf_v_bl
                                                       ? lem_bool_values v' pf_v'_bl)
            where
              pf_thp_bl  = lem_csubst_hasftype_basic g p TBool pf_p_bl p_g_wf th den_g_th
              pf_v_bl    = lemma_many_preservation thp (v  ? lem_evals_pred thp v ev_thp_v)
                                           ev_thp_v (FTBasic TBool) pf_thp_bl
              pf_thq_bl  = lem_csubst_hasftype_basic g q TBool pf_q_bl p_g_wf th den_g_th
              pf_v'_bl   = lemma_many_preservation thq (v' ? lem_evals_pred thq v' ev_thq_v')
                                           ev_thq_v' (FTBasic TBool) pf_thq_bl

-- lem_strengthen_elimination :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th) -> ProofOf(WFFE (erase_env g))
{-@ lem_strengthen_elimination :: p:Pred -> q:Pred -> ProofOf(HasFType FEmpty p (FTBasic TBool))
        -> ProofOf(HasFType FEmpty q (FTBasic TBool))
        -> ProofOf(EvalsTo (strengthen p q) (Bc True))
        -> (ProofOf(EvalsTo p (Bc True)), ProofOf(EvalsTo q (Bc True))) / [esize p] @-}
lem_strengthen_elimination :: Expr -> Expr -> HasFType -> HasFType -> EvalsTo -> (EvalsTo, EvalsTo)
lem_strengthen_elimination p q pf_p_bl pf_q_bl ev_pq_tt = case p of
  (Conj p1 p2) -> (ev_p_tt, ev_q_tt) -- strengthen p q == strengthen p1 strengthen p2 q
      where
        (FTConj _ _p1 pf_p1_bl _p2 pf_p2_bl) = pf_p_bl
        pf_p2q_bl             = lem_strengthen_ftyping FEmpty p2 q pf_p2_bl pf_q_bl
        (ev_p1_tt, ev_p2q_tt) = lem_strengthen_elimination p1 (strengthen p2 q) 
                                                           pf_p1_bl pf_p2q_bl ev_pq_tt
        (ev_p2_tt, ev_q_tt)   = lem_strengthen_elimination p2 q pf_p2_bl pf_q_bl ev_p2q_tt
        ev_p_tt               = lem_implies_conjunction Empty CEmpty DEmp p1 p2 ev_p1_tt ev_p2_tt
  _            -> lem_implies_elimination Empty CEmpty DEmp WFFEmpty p q pf_p_bl pf_q_bl ev_pq_tt
--      where
  --      (FTConj _ _p pf_p_bl _q pf_q_bl) = pf_pq_bl

{-@ lem_implies_conjunction :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th)
        -> p:Pred -> q:Pred
        -> ProofOf(EvalsTo (csubst th p) (Bc True))
        -> ProofOf(EvalsTo (csubst th q) (Bc True))
        -> ProofOf(EvalsTo (csubst th (Conj p q)) (Bc True)) @-}
lem_implies_conjunction :: Env -> CSub -> DenotesEnv -> Expr -> Expr
                               -> EvalsTo -> EvalsTo -> EvalsTo
lem_implies_conjunction g th den_g_th p q ev_thp_tt ev_thq_tt
  = let thp     = csubst th p
        thq     = csubst th q 
    in lemma_conj_semantics thp True ev_thp_tt thq True ev_thq_tt
                            ? lem_csubst_conj th p q

{- `lem_implies_introduction` is in the comments of Lambda1.1/Implications.hs -}
      
--        -> p:Pred -> { q:Pred | Set_emp (freeBV q) } -> ProofOf(HasFType (erase_env g) p (FTBasic TBool))
{-@ lem_implies_conj_commutes :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th) -> ProofOf(WFFE (erase_env g))
        -> p:Pred -> q:Pred -> ProofOf(HasFType (erase_env g) p (FTBasic TBool))
                            -> ProofOf(HasFType (erase_env g) q (FTBasic TBool))
        -> ProofOf(EvalsTo (csubst th (Conj p q)) (Bc True))
        -> ProofOf(EvalsTo (csubst th (Conj q p)) (Bc True)) @-}
lem_implies_conj_commutes :: Env -> CSub -> DenotesEnv -> WFFE -> Expr -> Expr
                                 -> HasFType -> HasFType -> EvalsTo -> EvalsTo
lem_implies_conj_commutes g th den_g_th p_g_wf p q pf_p_bl pf_q_bl ev_thpq_tt 
  = let thp       = csubst th p
        thq       = csubst th q -- ? lem_csubst_freeBV th q
        (ev_thp_tt, ev_thq_tt) = lem_implies_elimination g th den_g_th p_g_wf p q pf_p_bl pf_q_bl 
                                    ev_thpq_tt  ? lem_csubst_conj th  p q
    in lemma_conj_semantics thq True ev_thq_tt thp True ev_thp_tt
                                    ? lem_csubst_conj th  q p
