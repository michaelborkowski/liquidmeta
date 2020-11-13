{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Entailments where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import SameBinders
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
import SystemFSoundness
import Typing
import SystemFAlphaEquivalence
import BasicPropsCSubst
import BasicPropsDenotes

{-@ reflect foo31 @-}   
foo31 x = Just x 
foo31 :: a -> Maybe a 

-------------------------------------------------------------
-- | Lemma. Selfified Types are subtypes of the Original Type
-- -----------------------------------------------------------

--        -> p:Pred -> { q:Pred | Set_emp (freeBV q) } -> ProofOf(HasFType (erase_env g) p (FTBasic TBool))
{-@ lem_implies_elimination :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th) 
        -> p:Pred ->  q:Pred  -> ProofOf(HasFType (erase_env g) p (FTBasic TBool))
        -> ProofOf(EvalsTo (csubst th (App (App (Prim And) p) q)) (Bc True))
        -> ProofOf(EvalsTo (csubst th p) (Bc True)) @-}
lem_implies_elimination :: Env -> CSub -> DenotesEnv -> Pred -> Pred -> HasFType -> EvalsTo -> EvalsTo
lem_implies_elimination g th den_g_th p q pf_p_bl ev_thpq_tt 
  = let thp     = csubst th p
        thq     = csubst th q -- ? lem_csubst_freeBV th q
        pandq   = App (App (Prim And) p) q 
        thpandq = csubst th pandq ? lem_csubst_app th (App (Prim And) p) q
                                  ? lem_csubst_app th (Prim And) p
                                  ? lem_csubst_prim th And
    in case (lemma_evals_app_value (App (Prim And) thp) thq (Bc True) ev_thpq_tt ) of
      (AppRed _ id ev_and_id _ v'_ ev_q_v') -> case (lemma_evals_app_value (Prim And) thp id ev_and_id) of
        (AppRed _ _ _ _thp v ev_thp_v) -> case v of 
          (Bc True)     -> ev_thp_v
          (Bc False)    -> impossible ("by lemma" ? lem_evals_val_det (csubst th pandq)
                                                    (Bc True) ev_thpq_tt (Bc False) ev_thpq_ff)
            where
              v'         = v'_ -- ? lemma_evals_freeBV thq v'_ ev_q_v' 
              ev_and1    = lemma_app_many2 (Prim And) thp (Bc False) ev_thp_v 
              st_and2    = EPrim And (Bc False) 
              ev_and     = lemma_evals_trans (App (Prim And) thp) (App (Prim And) (Bc False)) 
                                   (Lambda 1 (Bc False)) ev_and1
                                   (AddStep (App (Prim And) (Bc False)) (Lambda 1 (Bc False))
                                            st_and2 (Lambda 1 (Bc False)) (Refl (Lambda 1 (Bc False)))) 
              ev_thp'1   = lemma_app_both_many (App (Prim And) thp) (Lambda 1 (Bc False)) ev_and
                                               thq v' ev_q_v'
              ev_thpq_ff = lemma_evals_trans thpandq (App (Lambda 1 (Bc False)) v') (Bc False)
                                   ev_thp'1 (AddStep (App (Lambda 1 (Bc False)) v') (Bc False)
                                                     (EAppAbs 1 (Bc False) v') (Bc False) (Refl (Bc False)))
          _             -> impossible ("by lemma" ? lem_bool_values v pf_v_bl)
            where
              pf_thp_bl  = lem_csubst_hasbtype' g p (TRefn TBool 1 (Bc True)) pf_p_bl th den_g_th
              pf_v_bl    = lemma_soundness thp v ev_thp_v (FTBasic TBool) pf_thp_bl

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
 = undefined {- 1 - }  
 = EntPred (Cons y t1 g) (unbind x y p) ev_func
  where
    {-@ ev_func :: th:CSub -> ProofOf(DenotesEnv (Cons y t1 g) th) 
                       -> ProofOf(EvalsTo (csubst th (unbind x y p)) (Bc True)) @-}
    ev_func :: CSub -> DenotesEnv -> EvalsTo
    ev_func th den_g1_th = case den_g1_th of
      (DExt _g th' den_g_th' _y _t1 th'y den_th't1_th'y) ->
            lem_implies_elimination (Cons y t1 g) th den_g1_th (unbind x y p) (unbind x y q) 
                          pf_p_bl ( ev_thp'_tt {-? toProof ( subBV x th'y (csubst th' pandq)-}
                                                         ? lem_csubst_subBV x th'y (FTBasic b) p_th'y_b th' pandq
                                                     {- === csubst th' (subBV x th'y pandq)-}
                                                         ? lem_subFV_unbind x y th'y pandq
                                                     {- === csubst th' (subFV y th'y (unbind x y pandq)) 
                                                       === csubst th (unbind x y pandq) ) -}
                    {-   ? toProof ( unbind x y pandq === subBV x (FV y) pandq
                               === App (subBV x (FV y) (App (Prim And) p)) (subBV x (FV y) q) 
                               === App (App (subBV x (FV y) (Prim And)) (subBV x (FV y) p)) (subBV x (FV y) q) 
                               === App (App (Prim And) (subBV x (FV y) p)) (subBV x (FV y) q) ) -} )
                       ? lem_binds_env_th g th' den_g_th'
        where
          {-@ ev_thp'_tt :: ProofOf(EvalsTo (subBV x th'y (csubst th' (App (App (Prim And) p) q))) (Bc True)) @-}
          {-@ p_th'y_b :: ProofOf(HasFType FEmpty th'y (erase t1)) @-}
          ev_thp'_tt = get_evals_from_drefn b x (csubst th' pandq) th'y (den_th't1_th'y
                         ? lem_ctsubst_refn th' b x pandq) -- (unbind x y pandq)
          p_th'y_b = get_ftyp_from_den (ctsubst th' t1) th'y den_th't1_th'y
                         ? lem_erase_ctsubst th' t1
      (DExtT {}) -> undefined
    t1    = TRefn b x (App (App (Prim And) p) q)
    pandq = App (App (Prim And) p) q {-
                     ? toProof ( fv (App (App (Prim And) p) q)
                             === S.union (fv (App (Prim And) p)) (fv q)
                             === S.union (fv p) (fv q) ) -}
                 --  ? lem_freeBV_emptyB (FCons y (FTBasic b) (erase_env g)) (unbind x y p) (FTBasic TBool) pf_p_bl
-}

{-@ lem_self_refn_sub :: g:Env -> b:Basic -> z:Vname -> p:Pred -> ProofOf(WFEnv g)
        -> ProofOf(WFType g (TRefn b z p) Base) -> { x:Vname | not (in_env x g) } -> k:Kind
        -> ProofOf(Subtype (Cons x (TRefn b z p) g) (self (TRefn b z p) (FV x) k) (TRefn b z p)) @-}          
lem_self_refn_sub :: Env -> Basic -> Vname -> Pred -> WFEnv -> WFType -> Vname -> Kind -> Subtype
lem_self_refn_sub = undefined {- TODO: need to account for new definition of equals and self
lem_self_refn_sub g b z p p_g_wf p_g_t x 
  = SBase (Cons x t g) z b p' z p w ent_p'_p
      where
        ent_p'_p = lem_entails_elimination (Cons x t g) b z p q w pf_p_bl' pf_q_bl'
        {-@ pf_q_bl' :: ProofOf(HasFType g2 (unbind z w q) (FTBasic TBool)) @-} -- equals b is Eqv/Eq
        pf_q_bl' = FTApp g2 (App (Prim (equals b)) (FV w)) (FTBasic b) (FTBasic TBool)
                         (FTApp g2 (Prim (equals b)) (FTBasic b) (FTFunc (FTBasic b) (FTBasic TBool))
                                (FTPrm g2 (equals b)) (FV w) (FTVar1 (erase_env (Cons x t g)) w (FTBasic b)))
                         (FV x) (FTVar2 (erase_env (Cons x t g)) x (FTBasic b)
                                        (FTVar1 (erase_env g) x (FTBasic b)) w (FTBasic b)) 
        {-@ q :: { q:Expr | freeBV q == Set_sng z && not (Set_mem w (fv q)) &&
                            subBV z (FV w) q == App (App (Prim (equals b)) (FV w)) (FV x) &&
                            selfify p b z x == App (App (Prim And) p) q} @-}
        q        = (App (App (Prim (equals b)) (BV z)) (FV x))
        {-@ p' :: { p':Expr | p' == selfify p b z x } @-}
        p'       = App (App (Prim And) p) q 
                     ? toProof ( selfify p b z x
                             === App (App (Prim And) p) (App (App (Prim (equals b)) (BV z)) (FV x)) 
                             === App (App (Prim And) p) q)
        w_       = fresh_var_excluding g x
        w        = w_ ? lem_free_bound_in_env g t Base p_g_t w_
        t        = TRefn b z p
        pf_g_wf  = lem_erase_env_wfenv g p_g_wf
        pf_wg_wf = WFFBind (erase_env g) pf_g_wf w (FTBasic b) Base (lem_erase_wftype g t Base p_g_t)
        pf_p_bl' = lem_weaken_ftyp (erase_env g) (FCons w (FTBasic b) FEmpty) pf_wg_wf
                                   (unbind z w p) (FTBasic TBool) pf_p_bl x (erase t)
        {-@ z1 :: { z1:Vname | not (in_env z1 g) } @-}
        (WFRefn _g _z _b _pgb _p z1 pf_p1_bl) = p_g_t 
        p_z1g_wf = WFFBind (erase_env g) pf_g_wf z1 (FTBasic b) Base (lem_erase_wftype g t Base p_g_t)
        pf_p_bl  = lem_change_var_ftyp (erase_env g) z1 (FTBasic b) FEmpty p_z1g_wf (unbind z z1 p) 
                           (FTBasic TBool) pf_p1_bl w ? lem_subFV_unbind z z1 (FV w) p
        g2       = (FCons w (FTBasic b) (erase_env (Cons x t g))) 
{ - -}

--        -> p:Pred -> { q:Pred | Set_emp (freeBV q) } -> ProofOf(HasFType (erase_env g) p (FTBasic TBool))
{-@ lem_implies_and_commutes :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th) 
        -> p:Pred -> q:Pred -> ProofOf(HasFType (erase_env g) p (FTBasic TBool))
        -> ProofOf(HasFType (erase_env g) q (FTBasic TBool))
        -> ProofOf(EvalsTo (csubst th (App (App (Prim And) p) q)) (Bc True))
        -> ProofOf(EvalsTo (csubst th (App (App (Prim And) q) p)) (Bc True)) @-}
lem_implies_and_commutes :: Env -> CSub -> DenotesEnv -> Pred -> Pred 
                                -> HasFType -> HasFType -> EvalsTo -> EvalsTo
{-lem_implies_and_commutes = undefined {- CHECKED -}-}
lem_implies_and_commutes g th den_g_th p q pf_p_bl pf_q_bl ev_thpq_tt 
  = let thp       = csubst th p
        thq       = csubst th q -- ? lem_csubst_freeBV th q
        pandq     = App (App (Prim And) p) q 
        thpandq   = csubst th pandq ? lem_csubst_app th (App (Prim And) p) q
                                    ? lem_csubst_app th (Prim And) p
                                    ? lem_csubst_prim th And
        qandp     = App (App (Prim And) q) p
        thqandp   = csubst th qandp ? lem_csubst_app th (App (Prim And) q) p
                                    ? lem_csubst_app th (Prim And) q
                                    ? lem_csubst_prim th And
        ev_thp_tt = lem_implies_elimination g th den_g_th p q pf_p_bl ev_thpq_tt
                                    ? lem_csubst_app th (App (Prim And) p) q
                                    ? lem_csubst_app th (Prim And) p
                                    ? lem_csubst_prim th And
    in case (lemma_evals_app_value (App (Prim And) thp) thq (Bc True) ev_thpq_tt ) of
      (AppRed _ id ev_and_id _ v'_ ev_thq_v') -> case v'_ of
          (Bc True)     -> ev_thqp_tt
            where
              v'         = v'_ -- ? lemma_evals_freeBV thq v'_ ev_thq_v' 
              ev_and1    = lemma_app_many2 (Prim And) thq (Bc True) ev_thq_v'
              ev_and_id  = lemma_add_step_after (App (Prim And) thq) (App (Prim And) (Bc True))
                                                ev_and1 (Lambda 1 (BV 1)) (EPrim And (Bc True))
              ev_thqp_1  = lemma_app_both_many (App (Prim And) thq) (Lambda 1 (BV 1)) ev_and_id
                                               thp (Bc True) ev_thp_tt
              ev_thqp_tt = lemma_add_step_after thqandp (App (Lambda 1 (BV 1)) (Bc True)) ev_thqp_1
                                                (Bc True) (EAppAbs 1 (BV 1) (Bc True))
          (Bc False)    -> impossible ("by lemma" ? lem_evals_val_det (csubst th pandq)
                                                    (Bc True) ev_thpq_tt (Bc False) ev_thpq_ff)
            where
              ev_and1    = lemma_app_many2 (Prim And) thp (Bc True) ev_thp_tt
              ev_and     = lemma_add_step_after (App (Prim And) thp) (App (Prim And) (Bc True))
                                                ev_and1 (Lambda 1 (BV 1)) (EPrim And (Bc True))
              ev_thpq_1  = lemma_app_both_many (App (Prim And) thp) (Lambda 1 (BV 1)) ev_and
                                               thq (Bc False) ev_thq_v'
              ev_thpq_ff = lemma_add_step_after thpandq (App (Lambda 1 (BV 1)) (Bc False)) ev_thpq_1  
                                                (Bc False) (EAppAbs 1 (BV 1) (Bc False)) 
          _             -> impossible ("by lemma" ? lem_bool_values v' pf_v'_bl)
            where
              v'         = v'_ -- ? lemma_evals_freeBV thq v'_ ev_thq_v' 
              pf_thq_bl  = lem_csubst_hasbtype' g q (TRefn TBool 1 (Bc True)) pf_q_bl th den_g_th
              pf_v'_bl   = lemma_soundness thq v' ev_thq_v' (FTBasic TBool) pf_thq_bl
{- -}

{-@ lem_entails_and_commutes :: g:Env -> b:Basic -> x:Vname -> p:Pred 
        -> { q:Pred | Set_sub (freeBV q) (Set_sng x) }
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (fv q)) } 
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind x y p) (FTBasic TBool))
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind x y q) (FTBasic TBool))
        -> ProofOf(Entails (Cons y (TRefn b x (App (App (Prim And) p) q)) g) 
                                              (unbind x y (App (App (Prim And) q) p))) @-}
lem_entails_and_commutes :: Env -> Basic -> Vname -> Pred -> Pred -> Vname -> HasFType -> HasFType -> Entails
{-lem_entails_and_commutes = undefined {- CHECKED -}-}
lem_entails_and_commutes g b x p q y pf_p_bl pf_q_bl = EntPred (Cons y t1 g) (unbind x y qandp) ev_func
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
          p_th'y_b = undefined {-get_ftyp_from_den (ctsubst th' t1) th'y den_th't1_th'y
                         ? lem_erase_ctsubst th' t1 -}
      (DExtT {}) -> undefined
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
{- -}

{-@ lem_entails_trans :: g:Env -> b:Basic -> x1:Vname -> p:Pred -> x2:Vname -> q:Pred -> x3:Vname -> r:Pred 
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (fv q)) 
                                                                  && not (Set_mem y (fv r)) }
        -> ProofOf(Entails (Cons y (TRefn b x1 p) g) (unbind x2 y q))
        -> ProofOf(Entails (Cons y (TRefn b x2 q) g) (unbind x3 y r))
        -> ProofOf(Entails (Cons y (TRefn b x1 p) g) (unbind x3 y r)) @-} -- these preds are not already unbound
lem_entails_trans :: Env -> Basic -> Vname -> Pred -> Vname -> Pred -> Vname -> Pred 
                         -> Vname -> Entails -> Entails -> Entails
{- lem_entails_trans = undefined { - -}
lem_entails_trans g b x1 p x2 q x3 r y (EntPred gp _unq ev_thq_func) ent_gp_r = case ent_gp_r of
  (EntPred gq _unr ev_thr_func) -> EntPred gp (unbind x3 y r) ev_thr_func'
    where
      {-@ ev_thr_func' :: th:CSub -> ProofOf(DenotesEnv (Cons y (TRefn b x1 p) g) th) 
                                    -> ProofOf(EvalsTo (csubst th (unbind x3 y r)) (Bc True)) @-}
      ev_thr_func' :: CSub -> DenotesEnv -> EvalsTo
      ev_thr_func' th den_gp_th = case den_gp_th of
        (DExt _g th' den_g_th' _y _bxp v den_thbxp_v) -> ev_thr_func th den_gq_th
          where
            p_v_b       = undefined {- get_ftyp_from_den (ctsubst th' (TRefn b x1 p)) v den_thbxp_v 
                                                   ? lem_ctsubst_refn th' b x1 p -}
            ev_thqv_tt  = ev_thq_func th den_gp_th ? lem_csubst_subBV x2 v (FTBasic b) p_v_b th' q
                                                   ? lem_subFV_unbind x2 y v q
            den_thbxq_v = DRefn b x2 (csubst th' q) v p_v_b ev_thqv_tt ? lem_ctsubst_refn th' b x2 q
            den_gq_th   = DExt g th' den_g_th' y (TRefn b x2 q) v den_thbxq_v
        (DExtT {}) -> undefined
{- -}

{-@ lem_entails_change_bv :: g:Env -> b:Basic -> x:Vname -> p:Pred -> x':Vname -> p':Pred
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (fv p')) &&
                       unbind x y p == unbind x' y p' }
        -> ProofOf(Entails (Cons y (TRefn b x p) g) (unbind x' y p')) @-}
lem_entails_change_bv :: Env -> Basic -> Vname -> Pred -> Vname -> Pred -> Vname -> Entails
lem_entails_change_bv = undefined {- - }
lem_entails_change_bv g b x p x' p' y = EntPred (Cons y (TRefn b x p) g) 
                                             (unbind x' y p') ev_func
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
      (DExtT {}) -> undefined
{ - -}

{-@ lem_self_tt_sub_eql :: g:Env -> b:Basic -> z:Vname -> z':Vname -> { x:Vname | not (in_env x g) } 
        -> ProofOf(Subtype (Cons x (TRefn b z (Bc True)) g) 
             (self (TRefn b z (Bc True)) (FV x) Base) (TRefn b z' (App (App (equals b) (BV z')) (FV x)))) @-} 
lem_self_tt_sub_eql :: Env -> Basic -> Vname -> Vname -> Vname -> Subtype
lem_self_tt_sub_eql = undefined {- TODO: update for new def'n of equals
lem_self_tt_sub_eql g b z z' x = SBase (Cons x t g) z b ttq z' eqx' w ent_ttq_eqx'
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
                         ? toProof ( selfify (Bc True) b z x
                                 === App (App (Prim And) (Bc True)) (App (App (Prim (equals b)) (BV z)) (FV x)) 
                                 === App (App (Prim And) (Bc True)) eqx)
        qtt          = App (App (Prim And) eqx) (Bc True) 
        {-@ eqx' :: { q:Expr | freeBV q == Set_sng z' && not (Set_mem w (fv q)) && fv q == Set_sng x &&
                            subBV z' (FV w) q == App (App (Prim (equals b)) (FV w)) (FV x) &&
                            unbind z' w q == unbind z w eqx &&
                            selfify (Bc True) b z' x == App (App (Prim And) (Bc True)) q} @-}
        eqx'         = (App (App (Prim (equals b)) (BV z')) (FV x))
        {-@ eqx :: { q:Expr | freeBV q == Set_sng z && not (Set_mem w (fv q)) && fv q == Set_sng x &&
                            subBV z (FV w) q == App (App (Prim (equals b)) (FV w)) (FV x) &&
                            selfify (Bc True) b z x == App (App (Prim And) (Bc True)) q} @-}
        eqx          = (App (App (Prim (equals b)) (BV z)) (FV x))

        w            = fresh_var_excluding g x
        g2           = (FCons w (FTBasic b) (erase_env (Cons x t g)))
        t            = TRefn b z (Bc True)
        pf_tt_bl     = FTBC g2 True
        pf_eqx_bl    = FTApp g2 (App (Prim (equals b)) (FV w)) (FTBasic b) (FTBasic TBool)
                         (FTApp g2 (Prim (equals b)) (FTBasic b) (FTFunc (FTBasic b) (FTBasic TBool))
                                (FTPrm g2 (equals b)) (FV w) (FTVar1 (erase_env (Cons x t g)) w (FTBasic b)))
                         (FV x) (FTVar2 (erase_env (Cons x t g)) x (FTBasic b)
                                        (FTVar1 (erase_env g) x (FTBasic b)) w (FTBasic b)) 
{ - -}
