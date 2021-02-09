{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple-local"   @-}
{- @ LIQUID "--fuel=1"      @-}
{-@ LIQUID "--short-names" @-}

module EntailmentsExtra where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Strengthenings
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
import LemmasWeakenWFTV
import PrimitivesSemantics
import LemmasWellFormedness
import SubstitutionWFAgain
import Implications
import Entailments
import DenotationsSoundness
import SubstitutionLemmaEntTV
import SubstitutionLemmaWFEnv

{-@ reflect foo66 @-}   
foo66 x = Just x 
foo66 :: a -> Maybe a 

--        -> x3:RVname -> r:Pred -> k3:Kind -> ProofOf(WFType g (TRefn b x3 r) k3)
{-@ ple lem_entails_trans @-}
{-@ lem_entails_trans :: g:Env -> ProofOf(WFEnv g) -> b:Basic 
        -> x1:RVname -> p:Pred -> k1:Kind -> ProofOf(WFType g (TRefn b x1 p) k1)
        -> x2:RVname -> q:Pred -> k2:Kind -> ProofOf(WFType g (TRefn b x2 q) k2)
        -> x3:RVname -> r:Pred 
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (fv q)) 
                                                                  && not (Set_mem y (fv r)) }
        -> ProofOf(Entails (Cons y (TRefn b x1 p) g) (unbind 0 y q))
        -> ProofOf(Entails (Cons y (TRefn b x2 q) g) (unbind 0 y r))
        -> ProofOf(Entails (Cons y (TRefn b x1 p) g) (unbind 0 y r)) @-} -- these preds not already unbound
lem_entails_trans :: Env -> WFEnv -> Basic -> RVname -> Expr -> Kind -> WFType
                  -> RVname -> Expr -> Kind -> WFType -> RVname -> Expr {-> Kind -> WFType -}
                  -> Vname -> Entails -> Entails -> Entails
lem_entails_trans g p_g_wf b x1 p k1 p_g_t1 x2 q k2 p_g_t2 x3 r {-k3 p_g_t3-} y 
                  ent_gp_q@(EntPred gp _unq ev_thq_func) ent_gp_r 
 = undefined {- CHECKED
  = case ent_gp_r of 
      (EntPred gq _unr ev_thr_func) -> EntPred gp (unbind 0 y r) ev_thr_func'
        where
          sub_t1_t2 = SBase g x1 b p x2 q y ent_gp_q
          {-@ ev_thr_func' :: th':CSub -> ProofOf(DenotesEnv (Cons y (TRefn b x1 p) g) th') 
                                       -> ProofOf(EvalsTo (csubst th' (unbind 0 y r)) (Bc True)) @-}
          ev_thr_func' :: CSub -> DenotesEnv -> EvalsTo
          ev_thr_func' th' den_gp_th' = case den_gp_th' of
            (DExt _g th den_g_th _y _bxp v den_thbxp_v) -> ev_thr_func th' den_gq_th'
              where
                den_thbxq_v = lem_denote_sound_sub g (TRefn b x1 p) k1 (TRefn b x2 q) k2
                                                   sub_t1_t2 p_g_wf p_g_t1 p_g_t2
                                                   th den_g_th v den_thbxp_v
                den_gq_th'  = DExt g th den_g_th y (TRefn b x2 q) v den_thbxq_v
-}

{-@ lem_entails_elimination' :: g:Env -> ProofOf(WFEnv g) 
        -> b:Basic -> x:RVname -> { p:Pred | Set_sub (freeBV p) (Set_sng 0) }
        -> { q:Pred | Set_sub (freeBV q) (Set_sng 0) }
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (fv q)) } 
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y p) (FTBasic TBool))
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y q) (FTBasic TBool))
        -> ProofOf(WFType g (TRefn b x (strengthen p q)) Base)
        -> ProofOf(Entails (Cons y (TRefn b x (strengthen p q)) g) (unbind 0 y q)) / [esize p] @-}
lem_entails_elimination' :: Env -> WFEnv -> Basic -> RVname -> Expr -> Expr -> Vname 
                               -> HasFType -> HasFType -> WFType -> Entails
lem_entails_elimination' g p_g_wf b x p@(Conj p1 p2) q y pf_p_bl pf_q_bl p_g_t1 
 = undefined {- CHECKED
  = lem_entails_trans g p_g_wf b x (strengthen p1 (strengthen p2 q)) Base p_g_t1 
                      x (strengthen p2 q) Base p_g_t2 x q {-Base p_g_t3-}
                      y ent_pq_p2q ent_p2q_q
      where
        (FTConj _ _p1 pf_p1_bl _p2 pf_p2_bl) = pf_p_bl ? unb_pf
        pf_p2q_bl  = lem_strengthen_ftyping (FCons y (FTBasic b) (erase_env g ? binds_pf)) 
                                            (unbind 0 y p2 ? pred) (unbind 0 y q) pf_p2_bl pf_q_bl
                   ? ( unbind 0 y (strengthen p2 q)
                   === subBV 0 (FV y ? val_pf) (strengthen p2 q)
                     ? lem_subBV_strengthen 0 (FV y ? val_pf) (p2 ? pred) q
                   === strengthen (subBV 0 (FV y ? val_pf) p2) (subBV 0 (FV y ? val_pf) q)
                   === strengthen (unbind 0 y p2) (unbind 0 y q) )
        (tt, p_g_tt) = lem_ftyp_trivial_for_wf_trefn g b x (strengthen (Conj p1 p2 ? pred) q) Base p_g_t1
        p_g_t2     = WFRefn g x b tt p_g_tt (strengthen (p2 ? pred) q) 
                            (y ? lem_free_bound_in_env g (TRefn b x (strengthen p q)) Base p_g_t1 y
                               ? free (TRefn b x (strengthen p q)) ? freeTV (TRefn b x (strengthen p q))
                               ? ( fv (strengthen (Conj p1 p2) q )
                               === fv (strengthen (p1 ? pred) (strengthen (p2 ? pred) q)) 
                               === S.union (fv p1) (fv (strengthen (p2 ? pred) q)) )
                               ? ( ftv (strengthen (Conj p1 p2) q )
                               === ftv (strengthen (p1 ? pred) (strengthen (p2 ? pred) q)) 
                               === S.union (ftv p1) (ftv (strengthen (p2 ? pred) q)) ) )
                            pf_p2q_bl
        ent_pq_p2q = lem_entails_elimination' g p_g_wf b x p1 (strengthen (p2 ? pred) q) (y ? fv_pf)
                                              pf_p1_bl pf_p2q_bl p_g_t1 
        ent_p2q_q  = lem_entails_elimination' g p_g_wf b x p2 q (y ? fv_pf) pf_p2_bl pf_q_bl p_g_t2

        binds_pf   = ( in_envF y (erase_env g) === in_env y g )
                   ? ( bindsF (erase_env g) === binds g )
        fv_pf      = fv (Conj p1 p2)  ? fv (strengthen p2 q)
        pred       = isPred (Conj p1 p2)
        str_pf     = strengthen (Conj p1 p2) q === strengthen (p1 ? pred) (strengthen (p2 ? pred) q)
        unb_pf     = (unbind 0 y (Conj p1 p2) === subBV 0 (FV y ? val_pf) (Conj p1 p2) 
                 === Conj (subBV 0 (FV y ? val_pf) p1) (subBV 0 (FV y ? val_pf) p2) 
                 === Conj (unbind 0 y p1) (unbind 0 y p2) )
        val_pf     = isValue (FV y) ? isTerm (FV y)
-}
lem_entails_elimination' g p_g_wf b x p q y pf_p_bl pf_q_bl p_g_t1 
 = undefined {- CHECKED
  = lem_entails_elimination g p_er_g_wf b x p q y pf_p_bl pf_q_bl (p_g_t1
                            ? ( strengthen p q === Conj p q ))
      where
        p_er_g_wf = lem_erase_env_wfenv g p_g_wf
-}

{-@ ple lem_entails_conjunction @-}
{-@ lem_entails_conjunction :: g:Env -> ProofOf(WFFE (erase_env g)) -> b:Basic -> x:RVname -> r:Pred
        -> { p:Pred | Set_sub (freeBV p) (Set_sng 0) } -> { q:Pred | Set_sub (freeBV q) (Set_sng 0) }
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (fv q)) } 
        -> ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y p)) 
        -> ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y q)) 
        -> ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y (Conj p q))) @-}
lem_entails_conjunction :: Env -> WFFE -> Basic -> RVname -> Expr -> Expr -> Expr -> Vname 
                               -> Entails -> Entails -> Entails
lem_entails_conjunction g p_g_wf b x r p q y ent_yenv_p ent_yenv_q 
 = undefined {- CHECKED
  = EntPred (Cons y (TRefn b x r) g) (unbind 0 y (Conj p q)) ev_func
      where
        {-@ ev_func :: th':CSub -> ProofOf(DenotesEnv (Cons y (TRefn b x r) g) th')
                                -> ProofOf(EvalsTo (csubst th' (unbind 0 y (Conj p q))) (Bc True)) @-}
        ev_func :: CSub -> DenotesEnv -> EvalsTo
        ev_func th' den_yg_th' = case den_yg_th' of
          (DExt _g th den_g_th _y _t1 v den_tht1_v)
            -> lem_implies_conjunction (Cons y (TRefn b x r) g) th' den_yg_th'
                                       (unbind 0 y p) (unbind 0 y q) ev_th'p_tt ev_th'q_tt
                 where
                   (EntPred _yg  _unr ev_th'p_func) = ent_yenv_p
                   (EntPred _    _    ev_th'q_func) = ent_yenv_q
                   ev_th'p_tt  = ev_th'p_func th' den_yg_th'
                   ev_th'q_tt  = ev_th'q_func th' den_yg_th'
-}

{-@ ple lem_entails_disjunction @-}
{-@ lem_entails_disjunction :: g:Env -> ProofOf(WFFE (erase_env g)) -> b:Basic -> x:RVname -> r:Pred
        -> k:Kind -> ProofOf(WFType g (TRefn b x r) k)
        -> { p:Pred | Set_sub (freeBV p) (Set_sng 0) } -> { q:Pred | Set_sub (freeBV q) (Set_sng 0) }
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (fv q)) } 
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y p) (FTBasic TBool))
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y q) (FTBasic TBool))
        -> ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y (Conj p q))) 
        -> (ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y p)), 
            ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y q)) ) @-}
lem_entails_disjunction :: Env -> WFFE -> Basic -> RVname -> Expr -> Kind -> WFType -> Expr -> Expr 
                        -> Vname -> HasFType -> HasFType -> Entails -> (Entails, Entails)
lem_entails_disjunction g p_g_wf b x r k p_g_t1 p q y pf_p_bl pf_q_bl ent_yenv_pq 
 = undefined {- CHECKED
  = (EntPred (Cons y (TRefn b x r) g) (unbind 0 y p) evp_func,
     EntPred (Cons y (TRefn b x r) g) (unbind 0 y q) evq_func)
      where
        (EntPred _yg  _unpq ev_th'pq_func) = ent_yenv_pq
        p_g_b   = lem_erase_wftype g (TRefn b x r) k p_g_t1
        p_yg_wf = WFFBind (erase_env g) p_g_wf y (FTBasic b) k p_g_b
        {-@ evp_func :: th':CSub -> ProofOf(DenotesEnv (Cons y (TRefn b x r) g) th')
                                 -> ProofOf(EvalsTo (csubst th' (unbind 0 y p)) (Bc True)) @-}
        evp_func :: CSub -> DenotesEnv -> EvalsTo
        evp_func th' den_yg_th' = case den_yg_th' of
          (DExt _g th den_g_th _y _t1 v den_tht1_v)
            -> fst (lem_implies_elimination (Cons y (TRefn b x r) g) th' den_yg_th' p_yg_wf
                                  (unbind 0 y p) (unbind 0 y q) pf_p_bl pf_q_bl ev_th'pq_tt)
                 where
                   (EntPred _    _    ev_th'pq_func) = ent_yenv_pq
                   ev_th'pq_tt  = ev_th'pq_func th' den_yg_th'
        {-@ evq_func :: th':CSub -> ProofOf(DenotesEnv (Cons y (TRefn b x r) g) th')
                                 -> ProofOf(EvalsTo (csubst th' (unbind 0 y q)) (Bc True)) @-}
        evq_func :: CSub -> DenotesEnv -> EvalsTo
        evq_func th' den_yg_th' = case den_yg_th' of
          (DExt _g th den_g_th _y _t1 v den_tht1_v)
            -> snd (lem_implies_elimination (Cons y (TRefn b x r) g) th' den_yg_th' p_yg_wf
                                  (unbind 0 y p) (unbind 0 y q) pf_p_bl pf_q_bl ev_th'pq_tt)
                 where
                   (EntPred _    _    ev_th'pq_func) = ent_yenv_pq
                   ev_th'pq_tt  = ev_th'pq_func th' den_yg_th'
-}

{-@ lem_entails_conjunction' :: g:Env -> ProofOf(WFFE (erase_env g)) -> b:Basic -> x:RVname -> r:Pred
        -> k:Kind -> ProofOf(WFType g (TRefn b x r) k)
        -> { p:Pred | Set_sub (freeBV p) (Set_sng 0) } -> { q:Pred | Set_sub (freeBV q) (Set_sng 0) }
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (fv q)) } 
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y p) (FTBasic TBool))
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y q) (FTBasic TBool))
        -> ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y p)) 
        -> ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y q)) 
        -> ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y (strengthen p q))) / [esize p] @-}
lem_entails_conjunction' :: Env -> WFFE -> Basic -> RVname -> Expr -> Kind -> WFType -> Expr 
                       -> Expr -> Vname -> HasFType -> HasFType -> Entails -> Entails -> Entails
lem_entails_conjunction' g p_g_wf b x r k p_g_t1 p@(Conj p1 p2) q y pf_p_bl pf_q_bl 
                         ent_yenv_p ent_yenv_q 
 = undefined {- CHECKED
  = lem_entails_conjunction' g p_g_wf b x r k p_g_t1 p1 (strengthen p2 q) (y ? fv_pf) pf_p1_bl 
                             pf_p2q_bl ent_yenv_p1 ent_yenv_p2q ? str_pf
      where
        (FTConj _ _p1 pf_p1_bl _p2 pf_p2_bl) = pf_p_bl ? unb_pf
        pf_p2q_bl  = lem_strengthen_ftyping (FCons y (FTBasic b) (erase_env g ? binds_pf)) 
                                            (unbind 0 y p2) (unbind 0 y q) pf_p2_bl pf_q_bl
                   ? ( unbind 0 y (strengthen p2 q)
                   === subBV 0 (FV y ? val_pf) (strengthen p2 q)
                     ? lem_subBV_strengthen 0 (FV y ? val_pf) (p2 ? pred) q
                   === strengthen (subBV 0 (FV y ? val_pf) p2) (subBV 0 (FV y ? val_pf) q)
                   === strengthen (unbind 0 y p2) (unbind 0 y q) )
        {-@ ent_yenv_p1  :: ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y p1)) @-}
        {-@ ent_yenv_p2  :: ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y p2)) @-}
        (ent_yenv_p1, ent_yenv_p2) 
                     = lem_entails_disjunction  g p_g_wf b x r k p_g_t1 p1 p2 (y ? fv_pf) pf_p1_bl pf_p2_bl 
                                                ent_yenv_p
        {-@ ent_yenv_p2q :: ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y (strengthen p2 q))) @-}
        ent_yenv_p2q = lem_entails_conjunction' g p_g_wf b x r k p_g_t1 p2 q  (y ? fv_pf) pf_p2_bl pf_q_bl 
                                                ent_yenv_p2 ent_yenv_q
        binds_pf   = ( in_envF y (erase_env g) === in_env y g )
                   ? ( bindsF (erase_env g) === binds g )
        fv_pf      = fv (Conj p1 p2) ? fv (strengthen p2 q) 
        pred       = isPred (Conj p1 p2)
        str_pf     = strengthen (Conj p1 p2) q === strengthen (p1 ? pred) (strengthen (p2 ? pred) q)
        unb_pf     = (unbind 0 y (Conj p1 p2) === subBV 0 (FV y ? val_pf) (Conj p1 p2) 
                 === Conj (subBV 0 (FV y ? val_pf) p1) (subBV 0 (FV y ? val_pf) p2) 
                 === Conj (unbind 0 y p1) (unbind 0 y p2) )
        val_pf     = isValue (FV y) ? isTerm (FV y)
-}
lem_entails_conjunction' g p_g_wf b x r k p_g_t1 p q y pf_p_bl pf_q_bl ent_yenv_p ent_yenv_q 
 = undefined {- CHECKED
  = lem_entails_conjunction g p_g_wf b x r p q y ent_yenv_p ent_yenv_q
                            ? ( strengthen p q === Conj p q )
-}

{-@ lem_entails_disjunction' :: g:Env -> ProofOf(WFFE (erase_env g)) -> b:Basic -> x:RVname -> r:Pred
        -> k:Kind -> ProofOf(WFType g (TRefn b x r) k)
        -> { p:Pred | Set_sub (freeBV p) (Set_sng 0) } -> { q:Pred | Set_sub (freeBV q) (Set_sng 0) }
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (fv q)) } 
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y p) (FTBasic TBool))
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y q) (FTBasic TBool))
        -> ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y (strengthen p q))) 
        -> (ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y p)), 
            ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y q)) ) / [esize p] @-}
lem_entails_disjunction' :: Env -> WFFE -> Basic -> RVname -> Expr -> Kind -> WFType -> Expr 
                     -> Expr -> Vname -> HasFType -> HasFType -> Entails -> (Entails, Entails)
lem_entails_disjunction' g p_g_wf b x r k p_g_t1 p@(Conj p1 p2) q y pf_p_bl pf_q_bl ent_yenv_pq 
 = undefined {- CHECKED
  = (ent_yenv_p, ent_yenv_q)
      where
        (FTConj _ _p1 pf_p1_bl _p2 pf_p2_bl) = pf_p_bl ? unb_pf
        pf_p2q_bl  = lem_strengthen_ftyping (FCons y (FTBasic b) (erase_env g ? binds_pf)) 
                                            (unbind 0 y p2 ? pred) (unbind 0 y q) pf_p2_bl pf_q_bl
                   ? ( unbind 0 y (strengthen p2 q)
                   === subBV 0 (FV y ? val_pf) (strengthen p2 q)
                     ? lem_subBV_strengthen 0 (FV y ? val_pf) (p2 ? pred) q
                   === strengthen (subBV 0 (FV y ? val_pf) p2) (subBV 0 (FV y ? val_pf) q)
                   === strengthen (unbind 0 y p2) (unbind 0 y q) )
        {-@ ent_yenv_p1  :: ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y p1)) @-}
        {-@ ent_yenv_p2q :: ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y (strengthen p2 q))) @-}
        (ent_yenv_p1, ent_yenv_p2q) 
                   = lem_entails_disjunction' g p_g_wf b x r k p_g_t1 p1 (strengthen (p2 ? pred) q) 
                                              (y ? fv_pf) pf_p1_bl pf_p2q_bl 
                                              (ent_yenv_pq ? str_pf)
        {-@ ent_yenv_p2  :: ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y p2)) @-}
        {-@ ent_yenv_q   :: ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y q)) @-}
        (ent_yenv_p2, ent_yenv_q)
                   = lem_entails_disjunction' g p_g_wf b x r k p_g_t1 p2 q y
                                              pf_p2_bl pf_q_bl ent_yenv_p2q
        {-@ ent_yenv_p   :: ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y (Conj p1 p2))) @-}
        ent_yenv_p = lem_entails_conjunction  g p_g_wf b x r p1 p2 (y ? fv_pf) ent_yenv_p1 ent_yenv_p2

        binds_pf   = ( in_envF y (erase_env g) === in_env y g )
                   ? ( bindsF (erase_env g) === binds g )
        fv_pf      = fv (Conj p1 p2)  ? fv (strengthen p2 q)
        pred       = isPred (Conj p1 p2)
        str_pf     = strengthen (Conj p1 p2) q === strengthen (p1 ? pred) (strengthen (p2 ? pred) q)
        unb_pf     = (unbind 0 y (Conj p1 p2) === subBV 0 (FV y ? val_pf) (Conj p1 p2) 
                 === Conj (subBV 0 (FV y ? val_pf) p1) (subBV 0 (FV y ? val_pf) p2) 
                 === Conj (unbind 0 y p1) (unbind 0 y p2) )
        val_pf     = isValue (FV y) ? isTerm (FV y)
-}
lem_entails_disjunction' g p_g_wf b x r k p_g_t1 p q y pf_p_bl pf_q_bl ent_yenv_pq 
 = undefined {- CHECKED
  = lem_entails_disjunction g p_g_wf b x r k p_g_t1 p q y pf_p_bl pf_q_bl 
                            (ent_yenv_pq ? ( strengthen p q === Conj p q ))
-}

{-@ ple lem_subst_tv_sub_sbase_ftv @-}
{-@ lem_subst_tv_sub_sbase_ftv :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
      -> { a:Vname | (not (in_env a g)) && not (in_env a g') } 
      -> b':Basic -> z:RVname -> q:Pred -> k_a:Kind -> ProofOf(WFType g (TRefn b' z q) k_a) 
      -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) 
      -> z1:RVname -> p1:Pred -> k_s:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') (TRefn (FTV a) z1 p1) k_s)
      -> z2:RVname -> p2:Pred -> k_t:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') (TRefn (FTV a) z2 p2) k_t)
      -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (ConsT a k_a g) g') 
                                             (TRefn (FTV a) z1 p1) (TRefn (FTV a) z2 p2)  && isSBase p_s_t }
      -> ProofOf(Subtype (concatE g (esubFTV a (TRefn b' z q) g')) (tsubFTV a (TRefn b' z q) (TRefn (FTV a) z1 p1)) 
                                                              (tsubFTV a (TRefn b' z q) (TRefn (FTV a) z2 p2))) @-}
lem_subst_tv_sub_sbase_ftv :: Env -> Env -> Vname -> Basic -> RVname -> Expr -> Kind -> WFType -> WFEnv
      -> RVname -> Expr -> Kind -> WFType -> RVname -> Expr -> Kind -> WFType -> Subtype -> Subtype
lem_subst_tv_sub_sbase_ftv g g' a b' z q k_a p_g_ta p_env_wf z1 p1 k_s p_env_s z2 p2 k_t p_env_t 
                       (SBase env _z1 b _p1 _z2 _p2 y_ ent_yenv_p2) 
  = SBase (concatE g (esubFTV a t_a g')) z b' (strengthen (subFTV a t_a p1) q)
          z (strengthen (subFTV a (t_a ? noex) p2) q) y ent_yenv'_p2taq ? t1pf ? t2pf
      where 
        t_a              = TRefn b' z q
        s                = TRefn (FTV a) z1 p1 
        y                = y_  ? lem_in_env_esubFTV g' a (t_a ? noex) y_ 
                               ? lem_in_env_concat g  g' y_ 
                               ? lem_in_env_concat (ConsT a k_a g) g' y_
                               ? lem_free_bound_in_env g t_a k_a p_g_ta (y_ ? lem_in_env_concat (ConsT a k_a g) g' y_)
  --      p_ag_wf          = lem_truncate_wfenv (ConsT a k_a g) g' p_env_wf
--        (WFEBindT _ pg_wf _ _) = p_ag_wf
        p_er_g_ta        = lem_erase_wftype g t_a k_a p_g_ta
        p_yenv_wf        = WFEBind (concatE (ConsT a k_a g) g') p_env_wf y s k_s p_env_s
        p_er_env_wf      = lem_erase_env_wfenv env p_env_wf
        p_er_wenv_wf     = WFFBind (erase_env env) p_er_env_wf (fresh_var env) (FTBasic b) 
                                   k_s (lem_erase_wftype env s k_s p_env_s ? er_s)
        p_er_yenv_wf     = WFFBind (erase_env env) p_er_env_wf (y ? binds_pf) (FTBasic b) 
                                   k_s (lem_erase_wftype env s k_s p_env_s ? er_s)
        env'             = concatE g (esubFTV a t_a g')
        p_env'_wf        = lem_subst_tv_wfenv g g' a t_a k_a p_g_ta p_env_wf
        p_er_env'_wf     = lem_erase_env_wfenv env' p_env'_wf
        {-@ t1 :: { t1_:Type | t1_ == tsubFTV a t_a s } @-}
        t1               = TRefn b' z (strengthen (subFTV a (t_a ? noex) p1) q) ? t1pf
        p_env'_t1        = lem_subst_tv_wf'   g g' a t_a k_a p_g_ta p_env_wf s k_s p_env_s
        p_er_wenv'_wf    = WFFBind (erase_env env') p_er_env'_wf (fresh_var env' ? binds_fr) (FTBasic b') 
                                   k_s (lem_erase_wftype env' t1 k_s p_env'_t1) ? concF_wenv'
        pf'_p1taq_bl     = lem_ftyp_for_wf_trefn' env' b' z (strengthen (subFTV a (t_a ? noex) p1) q)
                                                  k_s p_env'_t1 p_er_env'_wf
        pf_p1taq_bl      = lem_change_var_ftyp (erase_env env') (fresh_var env') (FTBasic b') FEmpty
                                   p_er_wenv'_wf (strengthen (subFTV a t_a p1) q)
                                   (FTBasic TBool) pf'_p1taq_bl (y ? yemp)
                                   ? concF_yenv' ? lem_subFV_unbind 0 (fresh_var env') (FV y ? val) 
                                                      (strengthen (subFTV a (t_a ? noex) p1) q ? fvp1q)
        pf'_p1_bl        = lem_ftyp_for_wf_trefn' env b z1 p1 k_s p_env_s p_er_env_wf
        pf'_p2_bl        = lem_ftyp_for_wf_trefn' env b z2 p2 k_t p_env_t p_er_env_wf
        pf_p1_bl         = lem_change_var_ftyp (erase_env env) (fresh_var env) (FTBasic b) FEmpty        
                                   p_er_wenv_wf (unbind 0 (fresh_var env) p1) (FTBasic TBool) pf'_p1_bl y
                                   ? concF_yenv ? lem_erase_concat (ConsT a k_a g) (Cons y s g' ? er_yg')
                                   ? lem_subFV_unbind 0 (fresh_var env) (FV y ? val) p1
        {-@ pf_p2_bl :: ProofOf(HasFType (FCons y (FTBasic b) (erase_env env)) (unbind 0 y p2) (FTBasic TBool)) @-}
        pf_p2_bl         = lem_change_var_ftyp (erase_env env) (fresh_var env) (FTBasic b) FEmpty        
                                   p_er_wenv_wf (unbind 0 (fresh_var env) p2) (FTBasic TBool) pf'_p2_bl (y ? yemp)
                                   ? concF_yenv ? lem_erase_concat (ConsT a k_a g) (Cons y s g' ? er_yg')
                                   ? lem_subFV_unbind 0 (fresh_var env) (FV y ? val) p2
        pf_p1ta_bl       = lem_subst_tv_ftyp (erase_env g) (FCons y (FTBasic b) (erase_env g'))
                                   a (t_a ? fvta) k_a p_er_g_ta p_er_yenv_wf (unbind 0 y p1)
                                   (FTBasic TBool) pf_p1_bl
                                   ? lem_erase_esubFTV a (t_a ? noex) (Cons y s g' ? er_yg') -- ? er_env'
                                   ? lem_erase_concat g (esubFTV a (t_a ? noex) g')
                                   ? lem_commute_subFTV_unbind a (t_a ? noex)
                                       (0 ? lem_tfreeBV_empty g t_a k_a p_g_ta) y p1
        {-@ pf_p2ta_bl :: ProofOf(HasFType (FCons y (FTBasic b) (erase_env env')) (unbind 0 y (subFTV a t_a p2)) (FTBasic TBool)) @-}
        pf_p2ta_bl       = lem_subst_tv_ftyp (erase_env g) (FCons y (FTBasic b) (erase_env g')) 
                                   (a ? binds_a) (t_a ? fvta) k_a p_er_g_ta p_er_yenv_wf (unbind 0 y p2)
                                   (FTBasic TBool) pf_p2_bl
                                   ? lem_erase_esubFTV a (t_a ? noex) (Cons y s g' ? er_yg') -- ? er_env'
                                   ? lem_erase_concat g (esubFTV a (t_a ? noex) g')
                                   ? lem_commute_subFTV_unbind a (t_a ? noex)
                                       (0 ? lem_tfreeBV_empty g t_a k_a p_g_ta) y p2
        p_env'_ta        = lem_weaken_many_wf' g (esubFTV a t_a g') p_env'_wf t_a k_a p_g_ta
        pf'_q_bl         = lem_ftyp_for_wf_trefn' env' b' z q k_a p_env'_ta p_er_env'_wf
        pf_q_bl          = lem_change_var_ftyp (erase_env env') (fresh_var env' ? binds_fr) (FTBasic b') (FEmpty ? femp)
                                   p_er_wenv'_wf (unbind 0 (fresh_var env') q) (FTBasic TBool) pf'_q_bl (y ? yemp)
                                   ? concF_yenv' ? lem_subFV_unbind 0 (fresh_var env') (FV y) q

        {- @ ent_yenv_p2     :: Entails (Cons y  s env)  (unbind 0 y p2) @-}
        {- @ ent_yenv'_p2ta  :: Entails (Cons y t1 env') (unbind 0 y (subFTV a t_a p2)) @-}
        ent_yenv'_p2ta   = lem_subst_tv_ent g (Cons y s g') a t_a k_a p_g_ta p_yenv_wf
                                            p2 ent_yenv_p2
        {- @ ent_yenv'_p1taq :: Entails (Cons y t1 env') (unbind 0 y (strengthen (subFTV a t_a p1) q)) @-}
        ent_yenv'_p1taq  = lem_entails_itself' env' p_er_env'_wf b' z (strengthen (subFTV a t_a p1) q)
                                               y pf_p1taq_bl k_s p_env'_t1
        {- @ ent_yenv'_q     ::  Entails (Cons y t1 env') (unbind 0 y q) @-}
        ent_yenv'_q      = snd ( lem_entails_disjunction' env' p_er_env'_wf  b' z
                                         (strengthen (subFTV a t_a p1) q) k_s p_env'_t1
                                         (subFTV a t_a p1) q y pf_p1ta_bl pf_q_bl ent_yenv'_p1taq )
        {- @ ent_yenv'_p2taq :: Entails (Cons y t1 env') (unbind 0 y (strengthen (subFTV a t_a p2) q)) @-}
        ent_yenv'_p2taq  = lem_entails_conjunction' env' p_er_env'_wf  b' z
                                         (strengthen (subFTV a t_a p1) q) k_s p_env'_t1
                                         (subFTV a t_a p2) q (y ? fvq) pf_p2ta_bl pf_q_bl 
                                         ent_yenv'_p2ta ent_yenv'_q
        -- evidence needed without PLE
        binds_a          = ( in_envF a (erase_env g) === in_env a g )
        binds_fr         = not (in_envF (fresh_var env') (erase_env env')) === not (in_env (fresh_var env) env)
        binds_pf         = ( in_envF y (erase_env g) === in_env y g )
                         ? ( bindsF (erase_env g) === binds g )
        concF_wenv'      = concatF (FCons (fresh_var env') (FTBasic b') (erase_env env')) FEmpty
        concF_yenv'      = concatF (FCons y (FTBasic b') (erase_env env')) FEmpty
        concF_yenv       = concatF (FCons y (FTBasic b) (erase_env env)) FEmpty
--        er_env'          = erase_env (concatE g (esubFTV a (t_a ? noex) g'))
        er_yg'           = erase_env (Cons y s g') ? er_s === FCons y (FTBasic b) (erase_env g')
        er_s             = erase (TRefn (FTV a) z1 p1)
        femp             = bindsF FEmpty
        fvp1q            = free t1  ? freeTV t1
        fvq              = free t_a ? freeTV t_a
        fvta             = lem_free_subset_binds g t_a k_a p_g_ta 
                         ? lem_tfreeBV_empty     g t_a k_a p_g_ta  
        noex             = noExists (TRefn b' z q)
        t1pf             =   tsubFTV a (t_a ? noex) (TRefn (FTV a) z1 p1) 
                         === push (subFTV a (t_a ? noex) p1) (TRefn b' z q)
                         === TRefn b' z (strengthen (subFTV a (t_a ? noex) p1) q)
        t2pf             =   tsubFTV a (t_a ? noex) (TRefn (FTV a) z1 p2) 
                         === push (subFTV a (t_a ? noex) p2) (TRefn b' z q)
                         === TRefn b' z (strengthen (subFTV a (t_a ? noex) p2) q)
        val              = isValue (FV y) ? isTerm (FV y)
        yemp             = not (in_envF y FEmpty) === not (S.member y (bindsF FEmpty))
