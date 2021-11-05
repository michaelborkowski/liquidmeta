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
import Implications

{-@ reflect foo32 @-}   
foo32 x = Just x 
foo32 :: a -> Maybe a 

{-@ get_evals_from_drefn :: b:Basic -> x:Vname -> p:Pred -> v:Value 
        -> ProofOf(Denotes (TRefn b x p) v) -> ProofOf(EvalsTo (subBV x v p) (Bc True)) @-}
get_evals_from_drefn :: Basic -> Vname -> Pred -> Expr -> Denotes -> EvalsTo
get_evals_from_drefn b x p v (DRefn _ _ _ _ _ ev_pv_tt) = ev_pv_tt

{-@ lem_entails_elimination :: g:Env -> b:Basic -> x:Vname -> p:Pred 
        -> { q:Pred | Set_sub (freeBV q) (Set_sng x) }
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (fv q)) } 
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind x y p) (FTBasic TBool))
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind x y q) (FTBasic TBool))
        -> ProofOf(Entails (Cons y (TRefn b x (App (App (Prim And) p) q)) g) (unbind x y p)) @-}
lem_entails_elimination :: Env -> Basic -> Vname -> Pred -> Pred -> Vname -> HasFType -> HasFType -> Entails
lem_entails_elimination g b x p q y pf_p_bl pf_q_bl  
 = EntPred (Cons y t1 g) (unbind x y p) ev_func
  where
    {-@ ev_func :: th:CSub -> ProofOf(DenotesEnv (Cons y t1 g) th) 
                       -> ProofOf(EvalsTo (csubst th (unbind x y p)) (Bc True)) @-}
    ev_func :: CSub -> DenotesEnv -> EvalsTo
    ev_func th den_g1_th = case den_g1_th of
      (DExt _g th' den_g_th' _y _t1 th'y den_th't1_th'y) ->
            fst (lem_implies_elimination (Cons y t1 g) th den_g1_th (unbind x y p) (unbind x y q) 
                          pf_p_bl pf_q_bl ( ev_thp'_tt {-? toProof ( subBV x th'y (csubst th' pandq)-}
                                                         ? lem_csubst_subBV x th'y (FTBasic b) p_th'y_b th' pandq
                                                     {- === csubst th' (subBV x th'y pandq)-}
                                                         ? lem_subFV_unbind x y th'y pandq
                                                     {- === csubst th' (subFV y th'y (unbind x y pandq)) 
                                                       === csubst th (unbind x y pandq) ) -}
                    {-   ? toProof ( unbind x y pandq === subBV x (FV y) pandq
                               === App (subBV x (FV y) (App (Prim And) p)) (subBV x (FV y) q) 
                               === App (App (subBV x (FV y) (Prim And)) (subBV x (FV y) p)) (subBV x (FV y) q) 
                               === App (App (Prim And) (subBV x (FV y) p)) (subBV x (FV y) q) ) -} )
                       ? lem_binds_env_th g th' den_g_th' )
        where
          {-@ ev_thp'_tt :: ProofOf(EvalsTo (subBV x th'y (csubst th' (App (App (Prim And) p) q))) (Bc True)) @-}
          {-@ p_th'y_b :: ProofOf(HasFType FEmpty th'y (erase t1)) @-}
          ev_thp'_tt = get_evals_from_drefn b x (csubst th' pandq) th'y (den_th't1_th'y
                         ? lem_ctsubst_refn th' b x pandq) -- (unbind x y pandq)
          p_th'y_b = get_ftyp_from_den (ctsubst th' t1) th'y den_th't1_th'y
                         ? lem_erase_ctsubst th' t1
    t1    = TRefn b x (App (App (Prim And) p) q)
    pandq = App (App (Prim And) p) q {-
                     ? toProof ( fv (App (App (Prim And) p) q)
                             === S.union (fv (App (Prim And) p)) (fv q)
                             === S.union (fv p) (fv q) ) -}
                 --  ? lem_freeBV_emptyB (FCons y (FTBasic b) (erase_env g)) (unbind x y p) (FTBasic TBool) pf_p_bl

{-@ lem_entails_repetition :: g:Env -> b:Basic -> x:Vname -> p:Pred
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) } 
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind x y p) (FTBasic TBool))
        -> ProofOf(Entails (Cons y (TRefn b x p) g) 
                           (unbind x y (App (App (Prim And) p) p)) ) @-}
lem_entails_repetition :: Env -> Basic -> Vname -> Pred -> Vname -> HasFType -> Entails
lem_entails_repetition g b x p y pf_p_bl 
  = EntPred (Cons y (TRefn b x p) g) (unbind x y pandp) ev_func
      where
        {-@ ev_func :: th:CSub -> ProofOf(DenotesEnv (Cons y (TRefn b x p) g) th)
                               -> ProofOf(EvalsTo (csubst th (unbind x y pandp)) (Bc True)) @-}
        ev_func :: CSub -> DenotesEnv -> EvalsTo
        ev_func th den_yg_th = case den_yg_th of 
          (DExt _g th' den_g_th' _y _t th'y den_th't_th'y) ->
              lem_implies_conjunction (Cons y (TRefn b x p) g) th den_yg_th 
                                      (unbind x y p) (unbind x y p) 
                                      (ev_thp_tt ? lem_csubst_subBV x th'y (FTBasic b) p_th'y_b th' p
                                                 ? lem_subFV_unbind x y th'y p)
                                      ev_thp_tt  ? lem_binds_env_th g th' den_g_th'
            where
              {-@ ev_thp_tt :: ProofOf(EvalsTo (subBV x th'y (csubst th' p)) (Bc True)) @-}
              {-@ p_th'y_b :: ProofOf(HasFType FEmpty th'y (FTBasic b)) @-}
              ev_thp_tt = get_evals_from_drefn b x (csubst th' p) th'y 
                               (den_th't_th'y ? lem_ctsubst_refn th' b x p) -- (unbind x y pandq)
              p_th'y_b = get_ftyp_from_den (ctsubst th' (TRefn b x p)) th'y den_th't_th'y
                               ? lem_erase_ctsubst th' (TRefn b x p)
        pandp = App (App (Prim And) p) p

{-@ lem_subtype_repetition :: g:Env -> b:Basic -> x:Vname ->  p:Pred 
        -> ProofOf(WFType g (TRefn b x p))
        -> ProofOf(Subtype g (TRefn b x p) (TRefn b x (App (App (Prim And) p) p))) @-}
lem_subtype_repetition :: Env -> Basic -> Vname -> Pred -> WFType -> Subtype
lem_subtype_repetition g b x p (WFRefn _ _ _ _ y pf_p_bl) 
  = SBase g x b p x pandp y ent_pandp
      where
        pandp     = App (App (Prim And) p) p
        ent_pandp = lem_entails_repetition g b x p y pf_p_bl

{-@ lem_entails_redundancy :: g:Env -> b:Basic -> x:Vname -> p:Pred 
        -> { q:Pred | Set_sub (freeBV q) (Set_sng x) }
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (fv q)) } 
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind x y p) (FTBasic TBool))
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind x y q) (FTBasic TBool))
        -> ProofOf(Entails (Cons y (TRefn b x (App (App (Prim And) p) q)) g) 
                           (unbind x y (App (App (Prim And)  (App (App (Prim And) p) q)) q))) @-}
lem_entails_redundancy :: Env -> Basic -> Vname -> Pred -> Pred -> Vname -> HasFType -> HasFType -> Entails
lem_entails_redundancy g b x p q y pf_p_bl pf_q_bl 
  = EntPred (Cons y tpandq g) (unbind x y pandqandq) ev_func
      where
        {-@ ev_func :: th:CSub -> ProofOf(DenotesEnv (Cons y tpandq g) th)
                               -> ProofOf(EvalsTo (csubst th (unbind x y pandqandq)) (Bc True)) @-} 
        ev_func :: CSub -> DenotesEnv -> EvalsTo
        ev_func th den_yg_th = case den_yg_th of
          (DExt _g th' den_g_th' _y _tpq th'y den_th'tpq_th'y) ->
              lem_implies_conjunction (Cons y tpandq g) th den_yg_th
                                      (unbind x y pandq) (unbind x y q)
                                      (ev_thpq_tt ? lem_csubst_subBV x th'y (FTBasic b) p_th'y_b th' pandq
                                                  ? lem_subFV_unbind x y th'y pandq)
                                      (ev_thq_tt  ? lem_csubst_subBV x th'y (FTBasic b) p_th'y_b th' q
                                                  ? lem_subFV_unbind x y th'y q) 
                                      ? lem_binds_env_th g th' den_g_th'
            where
              {-@ ev_thpq_tt :: ProofOf(EvalsTo (subBV x th'y (csubst th' (App (App (Prim And) p) q))) 
                                                (Bc True)) @-}
              {-@ p_th'y_b :: ProofOf(HasFType FEmpty th'y (FTBasic b)) @-}
              ev_thpq_tt = get_evals_from_drefn b x (csubst th' pandq) th'y (den_th'tpq_th'y
                               ? lem_ctsubst_refn th' b x pandq) -- (unbind x y pandq)
              p_th'y_b = get_ftyp_from_den (ctsubst th' tpandq) th'y den_th'tpq_th'y
                               ? lem_erase_ctsubst th' tpandq
              (_, ev_thq_tt) = lem_implies_elimination (Cons y tpandq g) th den_yg_th
                                      (unbind x y p) (unbind x y q) pf_p_bl pf_q_bl 
                                      (ev_thpq_tt ? lem_csubst_subBV x th'y (FTBasic b) p_th'y_b th' pandq
                                                  ? lem_subFV_unbind x y th'y pandq)
                                      ? lem_binds_env_th g th' den_g_th'
        tpandq    = TRefn b x (App (App (Prim And) p) q) 
        pandq     =            App (App (Prim And) p) q
        pandqandq = App (App (Prim And)  (App (App (Prim And) p) q)) q

{-@ lem_self_refn_sub :: g:Env -> b:Basic -> z:Vname -> p:Pred -> ProofOf(WFEnv g)
        -> ProofOf(WFType g (TRefn b z p)) ->  e:Expr 
        -> ProofOf(HasFType (erase_env g) e (FTBasic b))
        -> ProofOf(Subtype g (self (TRefn b z p) e) (TRefn b z p)) @-}          
lem_self_refn_sub :: Env -> Basic -> Vname -> Pred -> WFEnv -> WFType -> Expr 
                         -> HasFType -> Subtype
lem_self_refn_sub g b z p p_g_wf p_g_t@(WFRefn _ _ _ _ w pf_p_bl) e_ p_e_t 
  = SBase g z b selfp z p w ent_selfp_p
      where
        e           = e_ ? lem_freeBV_emptyB (erase_env g) e_ (FTBasic b) p_e_t
                         ? lem_fv_subset_bindsF (erase_env g) e_ (FTBasic b) p_e_t
                         ? lem_subBV_notin z (FV w) e_
        (Prim c)    = equals b
        er_wg       = FCons w (FTBasic b) (erase_env g)
        {-@ q :: { q:Expr | freeBV q == Set_sng z && not (Set_mem w (fv q)) &&
                            unbind z w q == App (App (equals b) (FV w)) e } @-}
        q           = App (App (equals b) (BV z)) e 
        p_wg_e_t    = lem_weaken_ftyp (erase_env g) FEmpty e (FTBasic b) p_e_t w (FTBasic b)
        pf_eqb_bl   = FTApp er_wg (equals b) (FTBasic b) (FTFunc (FTBasic b) (FTBasic TBool))
                            (FTPrm er_wg c) (FV w) (FTVar1 (erase_env g) w (FTBasic b))
        {-@ pf_q_bl :: ProofOf(HasFType er_wg (unbind z w q) (FTBasic TBool)) @-} -- equals b is Eqv/Eq
        pf_q_bl     = FTApp er_wg (App (equals b) (FV w)) (FTBasic b) (FTBasic TBool)
                            pf_eqb_bl e p_wg_e_t 
        selfp       = selfify p b z e
        ent_selfp_p = lem_entails_elimination g b z p q w pf_p_bl pf_q_bl 

                                 -- is this needed? can i change it back to b incl. FTV?
{-@ lem_entails_and_commutes :: g:Env -> { b:Basic | b == TBool || b == TInt } -> x:Vname -> p:Pred 
        -> { q:Pred | Set_sub (freeBV q) (Set_sng x) }
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (fv q)) } 
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind x y p) (FTBasic TBool))
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind x y q) (FTBasic TBool))
        -> ProofOf(Entails (Cons y (TRefn b x (App (App (Prim And) p) q)) g) 
                                              (unbind x y (App (App (Prim And) q) p))) @-}
lem_entails_and_commutes :: Env -> Basic -> Vname -> Pred -> Pred -> Vname -> HasFType -> HasFType -> Entails
lem_entails_and_commutes g b x p q y pf_p_bl pf_q_bl 
 = EntPred (Cons y t1 g) (unbind x y qandp) ev_func
  where
    {-@ ev_func :: th:CSub -> ProofOf(DenotesEnv (Cons y t1 g) th) 
                       -> ProofOf(EvalsTo (csubst th (unbind x y qandp)) (Bc True)) @-}
    ev_func :: CSub -> DenotesEnv -> EvalsTo
    ev_func th den_g1_th = case den_g1_th of
      (DExt _g th' den_g_th' _y _t1 th'y den_th't1_th'y) ->
            lem_implies_and_commutes (Cons y t1 g) th den_g1_th (unbind x y p) (unbind x y q) pf_p_bl
                          pf_q_bl ( ev_thp'_tt {-? toProof ( subBV x th'y (csubst th' pandq) -}
                                                         ? lem_csubst_subBV x th'y (FTBasic b) p_th'y_b th' pandq
                                                    {- === csubst th' (subBV x th'y pandq) -}
                                                         ? lem_subFV_unbind x y th'y pandq
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
          {-@ ev_thp'_tt :: ProofOf(EvalsTo (subBV x th'y (csubst th' (App (App (Prim And) p) q))) (Bc True)) @-}
          {-@ p_th'y_b :: ProofOf(HasFType FEmpty th'y (erase t1)) @-}
          ev_thp'_tt = get_evals_from_drefn b x (csubst th' pandq) th'y (den_th't1_th'y
                         ? lem_ctsubst_refn th' b x pandq) -- (unbind x y pandq)
          p_th'y_b = get_ftyp_from_den (ctsubst th' t1) th'y den_th't1_th'y
                         ? lem_erase_ctsubst th' t1 
    t1    = TRefn b x (App (App (Prim And) p) q)
    pandq = App (App (Prim And) p) q
                       {-? toProof ( fv (App (App (Prim And) p) q)
                               === S.union (fv (App (Prim And) p)) (fv q)
                               === S.union (fv p) (fv q) ) -}
                       {-? lem_freeBV_emptyB (FCons y (FTBasic b) (erase_env g)) 
                                           (unbind x y p) (FTBasic TBool) pf_p_bl -}
    g1       = (FCons y (FTBasic b) (erase_env g))
    qandp = App (App (Prim And) q) p
                       {-? toProof ( fv (App (App (Prim And) q) p)
                               === S.union (fv (App (Prim And) q)) (fv p)
                               === S.union (fv q) (fv p) ) -}

{-@ lem_entails_trans :: g:Env -> b:Basic -> x1:Vname -> p:Pred -> x2:Vname -> q:Pred -> x3:Vname -> r:Pred 
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (fv q)) 
                                                                  && not (Set_mem y (fv r)) }
        -> ProofOf(Entails (Cons y (TRefn b x1 p) g) (unbind x2 y q))
        -> ProofOf(Entails (Cons y (TRefn b x2 q) g) (unbind x3 y r))
        -> ProofOf(Entails (Cons y (TRefn b x1 p) g) (unbind x3 y r)) @-} -- these preds are not already unbound
lem_entails_trans :: Env -> Basic -> Vname -> Pred -> Vname -> Pred -> Vname -> Pred 
                         -> Vname -> Entails -> Entails -> Entails
lem_entails_trans g b x1 p x2 q x3 r y (EntPred gp _unq ev_thq_func) ent_gp_r 
 = case ent_gp_r of
  (EntPred gq _unr ev_thr_func) -> EntPred gp (unbind x3 y r) ev_thr_func'
    where
      {-@ ev_thr_func' :: th:CSub -> ProofOf(DenotesEnv (Cons y (TRefn b x1 p) g) th) 
                                    -> ProofOf(EvalsTo (csubst th (unbind x3 y r)) (Bc True)) @-}
      ev_thr_func' :: CSub -> DenotesEnv -> EvalsTo
      ev_thr_func' th den_gp_th = case den_gp_th of
        (DExt _g th' den_g_th' _y _bxp v den_thbxp_v) -> ev_thr_func th den_gq_th
          where
            p_v_b       = get_ftyp_from_den (ctsubst th' (TRefn b x1 p)) v den_thbxp_v 
                                                   ? lem_ctsubst_refn th' b x1 p 
            ev_thqv_tt  = ev_thq_func th den_gp_th ? lem_csubst_subBV x2 v (FTBasic b) p_v_b th' q
                                                   ? lem_subFV_unbind x2 y v q
            den_thbxq_v = DRefn b x2 (csubst th' q) v p_v_b ev_thqv_tt ? lem_ctsubst_refn th' b x2 q
            den_gq_th   = DExt g th' den_g_th' y (TRefn b x2 q) v den_thbxq_v

{-@ lem_entails_change_bv :: g:Env -> b:Basic -> x:Vname -> p:Pred -> x':Vname -> p':Pred
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

{-@ lem_self_tt_sub_eql :: g:Env -> b:Basic -> z:Vname -> z':Vname -> { x:Vname | not (in_env x g) } 
        -> ProofOf(Subtype (Cons x (TRefn b z (Bc True)) g) 
             (self (TRefn b z (Bc True)) (FV x)) (TRefn b z' (App (App (equals b) (BV z')) (FV x)))) @-} 
lem_self_tt_sub_eql :: Env -> Basic -> Vname -> Vname -> Vname -> Subtype
lem_self_tt_sub_eql g b z z' x 
    = SBase (Cons x t g) z b ttq z' eqx' w ent_ttq_eqx'
      where
        ent_ttq_qtt  = lem_entails_and_commutes (Cons x t g) b z (Bc True) eqx w pf_tt_bl pf_eqx_bl
        ent_qtt_eqx  = lem_entails_elimination (Cons x t g) b z eqx (Bc True) w pf_eqx_bl pf_tt_bl
        ent_ttq_eqx  = lem_entails_trans (Cons x t g) b z (App (App (Prim And) (Bc True)) eqx) 
                                         z (App (App (Prim And) eqx) (Bc True)) z eqx 
                                         w ent_ttq_qtt ent_qtt_eqx
        {-@ ent_eqx_eqx' :: { ent:Entails | propOf ent == Entails (Cons w (TRefn b z eqx) (Cons x t g)) 
                                                                  (unbind z' w eqx') } @-}
        ent_eqx_eqx' = lem_entails_change_bv (Cons x t g) b z eqx z' eqx' w
        ent_ttq_eqx' = lem_entails_trans (Cons x t g) b z (App (App (Prim And) (Bc True)) eqx)
                                         z eqx z' eqx' w ent_ttq_eqx ent_eqx_eqx'
        ttq          = App (App (Prim And) (Bc True)) eqx 
                         ? toProof ( selfify (Bc True) b z (FV x)
                                 === App (App (Prim And) (Bc True)) (App (App (equals b) (BV z)) (FV x)) 
                                 === App (App (Prim And) (Bc True)) eqx)
        qtt          = App (App (Prim And) eqx) (Bc True) 
        {-@ eqx' :: { q:Expr | freeBV q == Set_sng z' && not (Set_mem w (fv q)) && fv q == Set_sng x &&
                            subBV z' (FV w) q == App (App (equals b) (FV w)) (FV x) &&
                            unbind z' w q == unbind z w eqx &&
                            selfify (Bc True) b z' (FV x) == App (App (Prim And) (Bc True)) q} @-}
        eqx'         = (App (App (equals b) (BV z')) (FV x))
        {-@ eqx :: { q:Expr | freeBV q == Set_sng z && not (Set_mem w (fv q)) && fv q == Set_sng x &&
                            subBV z (FV w) q == App (App (equals b) (FV w)) (FV x) &&
                            selfify (Bc True) b z (FV x) == App (App (Prim And) (Bc True)) q} @-}
        eqx          = (App (App (equals b) (BV z)) (FV x))

        w            = fresh_var_excluding g x
        g2           = (FCons w (FTBasic b) (erase_env (Cons x t g)))
        t            = TRefn b z (Bc True)
        pf_tt_bl     = FTBC g2 True
        (Prim c)     = equals b
        pf_eqx_bl    = FTApp g2 (App (equals b) (FV w)) (FTBasic b) (FTBasic TBool)
                         (FTApp g2 (equals b) (FTBasic b) (FTFunc (FTBasic b) (FTBasic TBool))
                                (FTPrm g2 c) (FV w) (FTVar1 (erase_env (Cons x t g)) w (FTBasic b)))
                         (FV x) (FTVar2 (erase_env (Cons x t g)) x (FTBasic b)
                                        (FTVar1 (erase_env g) x (FTBasic b)) w (FTBasic b)) 

