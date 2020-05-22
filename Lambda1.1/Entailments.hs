{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-} 
{- @ LIQUID "--no-totality" @-} 
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Entailments where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import BasicProps
import STLCLemmas
import STLCSoundness
import Typing

-- we must force these into scope for LH
semantics = (Step, EvalsTo)
typing = (HasBType, HasType, WFType, WFEnv, Subtype)
denotations = (Entails, Denotes, DenotesEnv, ValueDenoted)

{-@ reflect foo3a @-}   
foo3a x = Just x 
foo3a :: a -> Maybe a 

-------------------------------------------------------------
-- | Lemma. Selfified Types are subtypes of the Original Type
-- -----------------------------------------------------------

{-@ reflect equals @-}
{-@ equals :: b:Base -> { c:Prim | Set_emp (fv (Prim c)) && Set_emp (freeBV (Prim c)) } @-}
equals :: Base -> Prim
equals TBool = Eqv
equals TInt  = Eq

{-@ lem_implies_elimination :: g:Env -> th:CSubst -> ProofOf(DenotesEnv g th) 
        -> p:Pred -> { q:Pred | Set_emp (freeBV q) } -> ProofOf(HasBType (erase_env g) p (BTBase TBool))
        -> ProofOf(EvalsTo (csubst th (App (App (Prim And) p) q)) (Bc True))
        -> ProofOf(EvalsTo (csubst th p) (Bc True)) @-}
lem_implies_elimination :: Env -> CSubst -> DenotesEnv -> Pred -> Pred -> HasBType -> EvalsTo -> EvalsTo
lem_implies_elimination g th den_g_th p q pf_p_bl ev_thpq_tt 
  = let thp     = csubst th p
        thq     = csubst th q ? lem_csubst_freeBV th q
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
              v'         = v'_ ? lemma_evals_freeBV thq v'_ ev_q_v' 
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
              pf_v_bl    = lemma_soundness thp v ev_thp_v (BTBase TBool) pf_thp_bl

{-@ get_evals_from_drefn :: b:Base -> x:Vname -> p:Pred -> v:Value 
        -> ProofOf(Denotes (TRefn b x p) v) -> ProofOf(EvalsTo (subBV x v p) (Bc True)) @-}
get_evals_from_drefn :: Base -> Vname -> Pred -> Expr -> Denotes -> EvalsTo
get_evals_from_drefn b x p v (DRefn _ _ _ _ _ ev_pv_tt) = ev_pv_tt

{-@ lem_entails_elimination :: g:Env -> b:Base -> x:Vname -> p:Pred 
        -> { q:Pred | Set_sub (freeBV q) (Set_sng x) }
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (fv q)) } 
        -> ProofOf(HasBType (BCons y (BTBase b) (erase_env g)) (unbind x y p) (BTBase TBool))
        -> ProofOf(HasBType (BCons y (BTBase b) (erase_env g)) (unbind x y q) (BTBase TBool))
        -> ProofOf(Entails (Cons y (TRefn b x (App (App (Prim And) p) q)) g) (unbind x y p)) @-}
lem_entails_elimination :: Env -> Base -> Vname -> Pred -> Pred -> Vname -> HasBType -> HasBType -> Entails
lem_entails_elimination g b x p q y pf_p_bl pf_q_bl = EntPred (Cons y t1 g) (unbind x y p) ev_func
  where
    {-@ ev_func :: th:CSubst -> ProofOf(DenotesEnv (Cons y t1 g) th) 
                       -> ProofOf(EvalsTo (csubst th (unbind x y p)) (Bc True)) @-}
    ev_func :: CSubst -> DenotesEnv -> EvalsTo
    ev_func th den_g1_th = case den_g1_th of
      (DExt _g th' den_g_th' _y _t1 th'y den_th't1_th'y) ->
            lem_implies_elimination (Cons y t1 g) th den_g1_th (unbind x y p) (unbind x y q) 
                          pf_p_bl ( ev_thp'_tt ? toProof ( subBV x th'y (csubst th' pandq)
                                                         ? lem_csubst_subBV x th'y (BTBase b) p_th'y_b th' pandq
                                                       === csubst th' (subBV x th'y pandq)
                                                         ? lem_subFV_unbind x y th'y pandq
                                                       === csubst th' (subFV y th'y (unbind x y pandq)) 
                                                       === csubst th (unbind x y pandq) ) 
                       ? toProof ( unbind x y pandq === subBV x (FV y) pandq
                               === App (subBV x (FV y) (App (Prim And) p)) (subBV x (FV y) q) 
                               === App (App (subBV x (FV y) (Prim And)) (subBV x (FV y) p)) (subBV x (FV y) q) 
                               === App (App (Prim And) (subBV x (FV y) p)) (subBV x (FV y) q) )  
                       ? lem_binds_env_th g th' den_g_th'
        where
          {-@ ev_thp'_tt :: ProofOf(EvalsTo (subBV x th'y (csubst th' (App (App (Prim And) p) q))) (Bc True)) @-}
          {-@ p_th'y_b :: ProofOf(HasBType BEmpty th'y (erase t1)) @-}
          ev_thp'_tt = get_evals_from_drefn b x (csubst th' pandq) th'y (den_th't1_th'y
                         ? lem_ctsubst_refn th' b x pandq) -- (unbind x y pandq)
          p_th'y_b = get_btyp_from_den (ctsubst th' t1) th'y den_th't1_th'y
                         ? lem_erase_ctsubst th' t1
    t1    = TRefn b x (App (App (Prim And) p) q)
    pandq = App (App (Prim And) p) q
                       ? toProof ( fv (App (App (Prim And) p) q)
                               === S.union (fv (App (Prim And) p)) (fv q)
                               === S.union (fv p) (fv q) )
                       ? lem_freeBV_emptyB (BCons y (BTBase b) (erase_env g)) (unbind x y p) (BTBase TBool) pf_p_bl 


{-@ lem_self_refn_sub :: g:Env -> b:Base -> z:Vname -> p:Pred -> ProofOf(WFType g (TRefn b z p)) 
        -> { x:Vname | not (in_env x g) } 
        -> ProofOf(Subtype (Cons x (TRefn b z p) g) (self (TRefn b z p) x) (TRefn b z p)) @-}          
lem_self_refn_sub :: Env -> Base -> Vname -> Pred -> WFType -> Vname -> Subtype
lem_self_refn_sub g b z p p_g_t x = SBase (Cons x t g) z b p' z p w ent_p'_p
      where
        ent_p'_p = lem_entails_elimination (Cons x t g) b z p q w pf_p_bl' pf_q_bl'
        {-@ pf_q_bl' :: ProofOf(HasBType g2 (unbind z w q) (BTBase TBool)) @-} -- equals b is Eqv/Eq
        pf_q_bl' = BTApp g2 (App (Prim (equals b)) (FV w)) (BTBase b) (BTBase TBool)
                         (BTApp g2 (Prim (equals b)) (BTBase b) (BTFunc (BTBase b) (BTBase TBool))
                                (BTPrm g2 (equals b)) (FV w) (BTVar1 (erase_env (Cons x t g)) w (BTBase b)))
                         (FV x) (BTVar2 (erase_env (Cons x t g)) x (BTBase b)
                                        (BTVar1 (erase_env g) x (BTBase b)) w (BTBase b)) 
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
        w        = w_ ? lem_free_bound_in_env g t p_g_t w_
        t        = TRefn b z p
        pf_p_bl' = lem_weaken_btyp (erase_env g) (BCons w (BTBase b) BEmpty) (unbind z w p) (BTBase TBool) 
                                   pf_p_bl x (erase t)
        {-@ z1 :: { z1:Vname | not (in_env z1 g) } @-}
        (WFRefn _g _z _b _p z1 pf_p1_bl) = p_g_t 
        pf_p_bl  = lem_change_var_btyp (erase_env g) z1 (BTBase b) BEmpty (unbind z z1 p) (BTBase TBool) pf_p1_bl w
                           ? lem_subFV_unbind z z1 (FV w) p
        g2       = (BCons w (BTBase b) (erase_env (Cons x t g)))
    
