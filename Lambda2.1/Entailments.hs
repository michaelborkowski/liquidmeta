{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Entailments where

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
import Implications

{-@ reflect foo32 @-}   
foo32 x = Just x 
foo32 :: a -> Maybe a 

{-@ get_evals_from_drefn :: b:Basic -> x:RVname -> p:Pred -> v:Value 
        -> ProofOf(Denotes (TRefn b x p) v) -> ProofOf(EvalsTo (subBV 0 v p) (Bc True)) @-}
get_evals_from_drefn :: Basic -> RVname -> Pred -> Expr -> Denotes -> EvalsTo
get_evals_from_drefn b x p v (DRefn _ _ _ _ _ ev_pv_tt) = ev_pv_tt

--{-@ get_evals_from_ctsubst_drefn 	@-}
--get_evals_from_ctsubst_drefn ::

{-@ lem_entails_elimination :: g:Env -> b:Basic -> x:RVname -> p:Pred
        -> { q:Pred | Set_sub (freeBV q) (Set_sng 0) }
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (fv q)) } 
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y p) (FTBasic TBool))
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y q) (FTBasic TBool))
        -> ProofOf(Entails (Cons y (TRefn b x (App (App (Prim Conj) p) q)) g) (unbind 0 y q)) @-}
lem_entails_elimination :: Env -> Basic -> RVname -> Expr -> Expr -> Vname 
                               -> HasFType -> HasFType -> Entails
lem_entails_elimination g b x p q y pf_p_bl pf_q_bl = undefined {-
 = EntPred (Cons y t1 g) (unbind 0 y q) ev_func
  where {- 1 undefined -}
    {-@ ev_func :: th:CSub -> ProofOf(DenotesEnv (Cons y t1 g) th) 
                           -> ProofOf(EvalsTo (csubst th (unbind 0 y q)) (Bc True)) @-}
    ev_func :: CSub -> DenotesEnv -> EvalsTo
    ev_func th den_g1_th = case den_g1_th of
      (DExt _g th' den_g_th' _y _t1 th'y den_th't1_th'y) ->
            snd (lem_implies_elimination (Cons y t1 g) th den_g1_th (unbind 0 y p) (unbind 0 y q) 
                     pf_p_bl pf_q_bl ( ev_thp'_tt 
               {-? toProof ( subBV x th'y (csubst th' pandq)-}
                           ? lem_csubst_subBV 0 th'y (erase (ctsubst th' t1)) {-(FTBasic b)-} 
                                              p_th'y_th't1 th' pandq
                      {- === csubst th' (subBV x th'y pandq)-}
                           ? lem_subFV_unbind 0 y th'y pandq
                      {- === csubst th' (subFV y th'y (unbind x y pandq)) 
                         === csubst th (unbind x y pandq) ) -}
            {-   ? toProof ( unbind x y pandq === subBV x (FV y) pandq
                         === App (subBV x (FV y) (App (Prim And) p)) (subBV x (FV y) q) 
                         === App (App (subBV x (FV y) (Prim And)) (subBV x (FV y) p)) (subBV x (FV y) q) 
                         === App (App (Prim And) (subBV x (FV y) p)) (subBV x (FV y) q) ) -} )
                     ? lem_binds_env_th g th' den_g_th' )
        where
          {-@ ev_thp'_tt :: ProofOf(EvalsTo (subBV 0 th'y (csubst th' (App (App (Prim Conj) p) q))) 
                                            (Bc True)) @-}
          {-@ p_th'y_th't1 :: ProofOf(HasFType FEmpty th'y (erase (ctsubst th' t1))) @-}
          ev_thp'_tt   = get_evals_from_drefn b x (csubst th' pandq) th'y (den_th't1_th'y   )
--                            ? lem_ctsubst_refn th' b x pandq) -- (unbind x y pandq) -- TODO TODO
          p_th'y_th't1 = get_ftyp_from_den (ctsubst th' t1) th'y den_th't1_th'y
--                            ? lem_erase_ctsubst th' t1
    t1    = TRefn b x (App (App (Prim Conj) p) q)
    pandq = App (App (Prim Conj) p) q {-
                     ? toProof ( fv (App (App (Prim And) p) q)
                             === S.union (fv (App (Prim And) p)) (fv q)
                             === S.union (fv p) (fv q) ) -}
                 --  ? lem_freeBV_emptyB (FCons y (FTBasic b) (erase_env g)) (unbind x y p) (FTBasic TBool) pf_p_bl
-}

{-@ lem_entails_repetition :: g:Env -> b:Basic -> x:RVname -> p:Pred
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) } 
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y p) (FTBasic TBool))
        -> ProofOf(Entails (Cons y (TRefn b x p) g) 
                           (unbind 0 y (App (App (Prim Conj) p) p)) ) @-}
lem_entails_repetition :: Env -> Basic -> RVname -> Pred -> Vname -> HasFType -> Entails
lem_entails_repetition g b x p y pf_p_bl  = undefined {- TODO
  = EntPred (Cons y (TRefn b x p) g) (unbind 0 y pandp) ev_func
      where {- 1 undefined -}
        {-@ ev_func :: th:CSub -> ProofOf(DenotesEnv (Cons y (TRefn b x p) g) th)
                               -> ProofOf(EvalsTo (csubst th (unbind 0 y pandp)) (Bc True)) @-}
        ev_func :: CSub -> DenotesEnv -> EvalsTo
        ev_func th den_yg_th = case den_yg_th of 
          (DExt _g th' den_g_th' _y _t th'y den_th't_th'y) ->
              lem_implies_conjunction (Cons y (TRefn b x p) g) th den_yg_th 
                                      (unbind 0 y p) (unbind 0 y p) 
                                      (ev_thp_tt ? lem_csubst_subBV 0 th'y (FTBasic b) p_th'y_b th' p
                                                 ? lem_subFV_unbind 0 y th'y p)
                                      ev_thp_tt  ? lem_binds_env_th g th' den_g_th'
            where
              {-@ ev_thp_tt :: ProofOf(EvalsTo (subBV 0 th'y (csubst th' p)) (Bc True)) @-}
              {-@ p_th'y_b :: ProofOf(HasFType FEmpty th'y (FTBasic b)) @-}
              ev_thp_tt     = get_evals_from_drefn b x (csubst th' p) th'y 
                               (den_th't_th'y ? lem_ctsubst_refn th' b x p) -- (unbind x y pandq) 
              p_th'y_b      = get_ftyp_from_den (ctsubst th' (TRefn b x p)) th'y den_th't_th'y
--                               ? lem_erase_ctsubst th' (TRefn b x p)
        pandp = App (App (Prim Conj) p) p
-}

{-@ lem_entails_redundancy :: g:Env -> b:Basic -> x:RVname -> p:Pred 
        -> { q:Pred | Set_sub (freeBV q) (Set_sng 0) }
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (fv q)) } 
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y p) (FTBasic TBool))
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y q) (FTBasic TBool))
        -> ProofOf(Entails (Cons y (TRefn b x (App (App (Prim Conj) p) q)) g) 
                           (unbind 0 y (App (App (Prim Conj)  (App (App (Prim Conj) p) q)) q))) @-}
lem_entails_redundancy :: Env -> Basic -> RVname -> Pred -> Pred -> Vname -> HasFType -> HasFType -> Entails
lem_entails_redundancy g b x p q y pf_p_bl pf_q_bl = undefined {-
  = EntPred (Cons y tpandq g) (unbind 0 y pandqandq) ev_func
      where
        {-@ ev_func :: th:CSub -> ProofOf(DenotesEnv (Cons y tpandq g) th)
                               -> ProofOf(EvalsTo (csubst th (unbind 0 y pandqandq)) (Bc True)) @-} 
        ev_func :: CSub -> DenotesEnv -> EvalsTo
        ev_func th den_yg_th = case den_yg_th of
          (DExt _g th' den_g_th' _y _tpq th'y den_th'tpq_th'y) ->
              lem_implies_conjunction (Cons y tpandq g) th den_yg_th
                                      (unbind 0 y pandq) (unbind 0 y q)
                                      (ev_thpq_tt ? lem_csubst_subBV 0 th'y (FTBasic b) p_th'y_b th' pandq
                                                  ? lem_subFV_unbind 0 y th'y pandq)
                                      (ev_thq_tt  ? lem_csubst_subBV 0 th'y (FTBasic b) p_th'y_b th' q
                                                  ? lem_subFV_unbind 0 y th'y q) 
                                      ? lem_binds_env_th g th' den_g_th'
            where
              {-@ ev_thpq_tt :: ProofOf(EvalsTo (subBV 0 th'y (csubst th' (App (App (Prim Conj) p) q))) 
                                                (Bc True)) @-}
              {-@ p_th'y_b :: ProofOf(HasFType FEmpty th'y (FTBasic b)) @-}
              ev_thpq_tt = get_evals_from_drefn b x (csubst th' pandq) th'y (den_th'tpq_th'y
                               ? lem_ctsubst_refn th' b x pandq) -- (unbind x y pandq)
              p_th'y_b = get_ftyp_from_den (ctsubst th' tpandq) th'y den_th'tpq_th'y
                               ? lem_erase_ctsubst th' tpandq
              (_, ev_thq_tt) = lem_implies_elimination (Cons y tpandq g) th den_yg_th
                                      (unbind 0 y p) (unbind 0 y q) pf_p_bl pf_q_bl 
                                      (ev_thpq_tt ? lem_csubst_subBV 0 th'y (FTBasic b) p_th'y_b th' pandq
                                                  ? lem_subFV_unbind 0 y th'y pandq)
                                      ? lem_binds_env_th g th' den_g_th'
        tpandq    = TRefn b x (App (App (Prim Conj) p) q) 
        pandq     =            App (App (Prim Conj) p) q
        pandqandq = App (App (Prim Conj)  (App (App (Prim Conj) p) q)) q
-}

{-@ lem_entails_trans :: g:Env -> b:Basic -> x1:RVname -> p:Pred 
        -> x2:RVname -> q:Pred -> x3:RVname -> r:Pred 
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (fv q)) 
                                                                  && not (Set_mem y (fv r)) }
        -> ProofOf(Entails (Cons y (TRefn b x1 p) g) (unbind 0 y q))
        -> ProofOf(Entails (Cons y (TRefn b x2 q) g) (unbind 0 y r))
        -> ProofOf(Entails (Cons y (TRefn b x1 p) g) (unbind 0 y r)) @-} -- these preds not already unbound
lem_entails_trans :: Env -> Basic -> RVname -> Pred -> RVname -> Pred -> RVname -> Pred 
                         -> Vname -> Entails -> Entails -> Entails
lem_entails_trans g b x1 p x2 q x3 r y (EntPred gp _unq ev_thq_func) ent_gp_r = undefined {-
 = case ent_gp_r of
  (EntPred gq _unr ev_thr_func) -> EntPred gp (unbind 0 y r) ev_thr_func'
    where
      {-@ ev_thr_func' :: th:CSub -> ProofOf(DenotesEnv (Cons y (TRefn b x1 p) g) th) 
                                    -> ProofOf(EvalsTo (csubst th (unbind 0 y r)) (Bc True)) @-}
      ev_thr_func' :: CSub -> DenotesEnv -> EvalsTo
      ev_thr_func' th den_gp_th = case den_gp_th of
        (DExt _g th' den_g_th' _y _bxp v den_thbxp_v) -> ev_thr_func th den_gq_th
          where
            p_v_b       = get_ftyp_from_den (ctsubst th' (TRefn b x1 p)) v den_thbxp_v 
                                                   ? lem_ctsubst_refn th' b x1 p 
            ev_thqv_tt  = ev_thq_func th den_gp_th ? lem_csubst_subBV 0 v (FTBasic b) p_v_b th' q
                                                   ? lem_subFV_unbind 0 y v q
            den_thbxq_v = DRefn b x2 (csubst th' q) v p_v_b ev_thqv_tt ? lem_ctsubst_refn th' b x2 q
            den_gq_th   = DExt g th' den_g_th' y (TRefn b x2 q) v den_thbxq_v
-} 


{-  NOT NEEDED: This is no longer needed, nothing is logically dependent on this anymore
{-@ lem_entails_conj_commutes :: g:Env -> { b:Basic | b == TBool || b == TInt } -> x:RVname -> p:Pred 
        -> { q:Pred | Set_sub (freeBV q) (Set_sng 0) }
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (fv q)) } 
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y p) (FTBasic TBool))
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y q) (FTBasic TBool))
        -> ProofOf(Entails (Cons y (TRefn b x (App (App (Prim Conj) p) q)) g) 
                                              (unbind 0 y (App (App (Prim Conj) q) p))) @-}
lem_entails_conj_commutes :: Env -> Basic -> RVname -> Pred -> Pred -> Vname 
                                 -> HasFType -> HasFType -> Entails
lem_entails_conj_commutes g b x p q y pf_p_bl pf_q_bl 
 = EntPred (Cons y t1 g) (unbind 0 y qandp) ev_func
  where
    {-@ ev_func :: th:CSub -> ProofOf(DenotesEnv (Cons y t1 g) th) 
                       -> ProofOf(EvalsTo (csubst th (unbind 0 y qandp)) (Bc True)) @-}
    ev_func :: CSub -> DenotesEnv -> EvalsTo
    ev_func th den_g1_th = case den_g1_th of
      (DExt _g th' den_g_th' _y _t1 th'y den_th't1_th'y) ->
            lem_implies_conj_commutes (Cons y t1 g) th den_g1_th (unbind 0 y p) (unbind 0 y q) pf_p_bl
                          pf_q_bl ( ev_thp'_tt {-? toProof ( subBV x th'y (csubst th' pandq) -}
                                                 ? lem_csubst_subBV 0 th'y (FTBasic b) p_th'y_b th' pandq
                                                    {- === csubst th' (subBV x th'y pandq) -}
                                                         ? lem_subFV_unbind 0 y th'y pandq
                                                    {- === csubst th' (subFV y th'y (unbind x y pandq)) 
                                                       === csubst th (unbind x y pandq) -} ) 
                       {-? toProof ( unbind x y pandq === subBV x (FV y) pandq
                               === App (subBV x (FV y) (App (Prim And) p)) (subBV x (FV y) q) 
                               === App (App (subBV x (FV y) (Prim And)) (subBV x (FV y) p)) (subBV x (FV y) q) 
                               === App (App (Prim And) (subBV x (FV y) p)) (subBV x (FV y) q) ) ) 
                       ? toProof ( unbind x y qandp === subBV x (FV y) qandp
                               === App (subBV x (FV y) (App (Prim And) q)) (subBV x (FV y) p) 
                               === App (App (subBV x (FV y) (Prim And)) (subBV x (FV y) q)) (subBV x (FV y) p) 
                               === App (App (Prim And) (subBV x (FV y) q)) (subBV x (FV y) p) )  -}
                       ? lem_binds_env_th g th' den_g_th'
        where
          {-@ ev_thp'_tt :: ProofOf(EvalsTo (subBV 0 th'y (csubst th' (App (App (Prim Conj) p) q))) 
                                            (Bc True)) @-}
          {-@ p_th'y_b :: ProofOf(HasFType FEmpty th'y (erase t1)) @-}
          ev_thp'_tt = get_evals_from_drefn b x (csubst th' pandq) th'y (den_th't1_th'y
                         ? lem_ctsubst_refn th' b x pandq) -- (unbind x y pandq)
          p_th'y_b = get_ftyp_from_den (ctsubst th' t1) th'y den_th't1_th'y
                         ? lem_erase_ctsubst th' t1 
    t1    = TRefn b x (App (App (Prim Conj) p) q)
    pandq = App (App (Prim Conj) p) q
                       {-? toProof ( fv (App (App (Prim And) p) q)
                               === S.union (fv (App (Prim And) p)) (fv q)
                               === S.union (fv p) (fv q) ) -}
                       {-? lem_freeBV_emptyB (FCons y (FTBasic b) (erase_env g)) 
                                           (unbind x y p) (FTBasic TBool) pf_p_bl -}
    g1       = (FCons y (FTBasic b) (erase_env g))
    qandp = App (App (Prim Conj) q) p
                       {-? toProof ( fv (App (App (Prim And) q) p)
                               === S.union (fv (App (Prim And) q)) (fv p)
                               === S.union (fv q) (fv p) ) -}
-}

{- NOT NEEDED: we effectively assume all RVname binders are the same
{-@ lem_entails_change_bv :: g:Env -> b:Basic -> x:RVname -> p:Pred -> x':RVname -> p':Pred
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (fv p')) &&
                       unbind x y p == unbind x' y p' }
        -> ProofOf(Entails (Cons y (TRefn b x p) g) (unbind x' y p')) @-}
lem_entails_change_bv :: Env -> Basic -> Vname -> Pred -> Vname -> Pred -> Vname -> Entails
lem_entails_change_bv g b x p x' p' y  
 = EntPred (Cons y (TRefn b x p) g) (unbind x' y p') ev_func
  where
    {-@ ev_func :: th:CSub -> ProofOf(DenotesEnv (Cons y (TRefn b x p) g) th)
                             -> ProofOf(EvalsTo (csubst th (unbind x' y p')) (Bc True)) @-}
    ev_func :: CSub -> DenotesEnv -> EvalsTo
    ev_func th den_gp_th = case den_gp_th of   
      (DExt _g th' den_g_th' _y _bxp v den_th'bxp_v) -> ev_th'p'v_tt
        where
          p_v_b        = get_ftyp_from_den (ctsubst th' (TRefn b x p)) v 
                                           (den_th'bxp_v ? lem_ctsubst_refn th' b x p)
          ev_th'pv_tt  = get_evals_from_drefn b x (csubst th' p) v 
                                           (den_th'bxp_v ? lem_ctsubst_refn th' b x p)
          ev_th'p'v_tt = ev_th'pv_tt ? lem_csubst_subBV x v (FTBasic b) p_v_b th' p
                                     ? lem_subFV_unbind x y v p
-}
