{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-i @ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasExactness where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Strengthenings
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import PrimitivesWFType
import SystemFLemmasFTyping
import SystemFLemmasFTyping2
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import BasicPropsEraseTyping
import Implications
import Entailments
import SubtypingFromEntailments
import LemmasChangeVarWF
import LemmasWeakenWF
import LemmasWellFormedness
import LemmasTyping
import LemmasSubtyping
import LemmasWeakenTyp
import DenotationsSelfify
import DenotationsSoundness
import PrimitivesSemantics

{-@ reflect foo62 @-}
foo62 x = Just x           
foo62 :: a -> Maybe a    

{-@ lem_csubst_eqlPred_ftyp :: g:Env -> ProofOf(WFEnv g) -> b:Basic -> x:RVname -> p:Pred
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (ftv p)) }
        -> ProofOf(WFType g (TRefn b x p) Base) -> e:Term -> ProofOf(HasFType (erase_env g) e (FTBasic b))
        -> { th:CSub | not (Set_mem y (bindsC th)) } -> ProofOf(DenotesEnv g th)  
        -> { v:Value | Set_emp (fv v) && Set_emp (ftv v) && Set_emp (freeBV v) && Set_emp (freeBTV v) } 
        -> ProofOf(HasFType FEmpty v (erase (ctsubst th (TRefn b x p ))))
        -> ProofOf(Denotes  (ctsubst th (TRefn b x (selfify p b x e))) v)
        -> ProofOf(HasFType FEmpty (subBV 0 v (csubst th (eqlPred (TRefn b x p) e))) (FTBasic TBool)) @-}
lem_csubst_eqlPred_ftyp :: Env -> WFEnv -> Basic -> RVname -> Expr -> Vname -> WFType -> Expr
                               -> HasFType -> CSub -> DenotesEnv -> Expr -> HasFType -> Denotes -> HasFType
lem_csubst_eqlPred_ftyp g p_g_wf b x1 p1 y p_g_s e p_e_s th den_g_th v p_v_thb den_thselfs_v = pf_eqlthe_bl
  where
    yg            = Cons y (TRefn b x1 (selfify p1 b x1 e)) g
    self_s        =         TRefn b x1 (selfify p1 b x1 e)
    p_er_g_wf     = lem_erase_env_wfenv g p_g_wf
    p_yg_wf       = WFFBind (erase_env g) p_er_g_wf y  (FTBasic b) Base 
                            (lem_erase_wftype g (TRefn b x1 p1) Base p_g_s)
    yth           = CCons y v th
    den_yg_yth    = DExt g th den_g_th y self_s v den_thselfs_v
    {-@ unb_eqlpred :: { ee:Expr | ee == App (App (AppT (Prim Eql) (TRefn b x1 p1)) (FV y)) e } @-}
    unb_eqlpred    = unbind 0 y (eqlPred (TRefn b x1 p1) e) -- (App (App (AppT (Prim Eql) (TRefn b x1 p1)) (BV 0)) e)
                       ? lem_subBV_notin  0 (FV y ? toProof (isTerm (FV y) === True)) 
                             (e ? lem_freeBV_emptyB (erase_env g) e (FTBasic b) p_e_s)
                       ? lem_tsubBV_notin 0 (FV y) (TRefn b x1 p1)

    {-@ pf_y_eqle_bl :: ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) unb_eqlpred (FTBasic TBool)) @-}
    pf_y_eqle_bl  = lem_eqlPred_ftyping    g b x1 p1      p_g_s p_er_g_wf y e p_e_s
--App (App (AppT (Prim Eql) (ctsubst th s)) v) 
--                                    (csubst th e) 
    pf_eqlthe_bl   = lem_csubst_hasftype' yg  unb_eqlpred  (TRefn TBool Z (Bc True))
                                          pf_y_eqle_bl p_yg_wf  yth  den_yg_yth   
 --                                                     ? lem_subFV_notin  y v e
  --                                                   ? lem_tsubFV_notin y v (TRefn b x1 p1)
      --                                               ? lem_csubst_nofv  th v
                                    ? lem_ctsubst_nofree yth (TRefn TBool Z (Bc True) ? free_pf)
                                    ? lem_csubst_and_unbind 0 y v (erase (ctsubst th (TRefn b x1 p1))) p_v_thb th 
                                          (eqlPred (TRefn b x1 p1) e {-)
                                        (App (App (AppT (Prim Eql) (TRefn b x1 p1)) (BV 0)) e ) -}
                                          ? lem_free_bound_in_env g (TRefn b x1 p1) Base p_g_s y
                                          ? lem_fv_bound_in_fenv (erase_env g) e (FTBasic b) p_e_s y)
    free_pf       = toProof ( freeTV (TRefn TBool Z (Bc True)) === ftv (Bc True) === S.empty )

