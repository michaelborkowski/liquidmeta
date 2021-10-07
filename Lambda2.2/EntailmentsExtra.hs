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

{-@ ple lem_entails_itself' @-}
{-@ lem_entails_itself' :: g:Env -> ProofOf(WFFE (erase_env g)) -> b:Basic -> x:RVname -> p:Pred
        -> k:Kind -> ProofOf(WFType g (TRefn b x p) k) -> { y:Vname | not (in_env y g) } 
        -> ProofOf(Entails (Cons y (TRefn b x p) g) (unbind 0 y p ) ) @-}
lem_entails_itself' :: Env -> WFFE -> Basic -> RVname -> Expr -> Kind -> WFType -> Vname -> Entails
lem_entails_itself' g p_g_wf b x p k p_g_t y
  = EntPred (Cons y (TRefn b x p) g) (unbind 0 y p) ev_func
      where 
        {-@ ev_func :: th:CSub -> ProofOf(DenotesEnv (Cons y (TRefn b x p) g) th)
                               -> ProofOf(EvalsTo (csubst th (unbind 0 y p)) (Bc True)) @-}
        ev_func :: CSub -> DenotesEnv -> EvalsTo
        ev_func th den_yg_th = case den_yg_th of 
          (DExt _g th' den_g_th' _y _t th'y den_th't_th'y) 
            -> ev_thp_tt ? lem_csubst_subBV 0 th'y (erase (ctsubst th' (TRefn b x p)))             
                                             p_th'y_b th' p
                         ? lem_subFV_unbind 0 y th'y (p ? notin_pf)
            where
              {-@ ev_thp_tt :: ProofOf(EvalsTo (subBV 0 th'y (csubst th' p)) (Bc True)) @-}
              {-@ p_th'y_b :: ProofOf(HasFType FEmpty th'y (erase (ctsubst th' (TRefn b x p)))) @-}
              ev_thp_tt     = get_evals_from_ctsubst_drefn' g th' den_g_th' p_g_wf b x 
                                                            p k p_g_t th'y den_th't_th'y
              p_th'y_b      = get_ftyp_from_den (ctsubst th' (TRefn b x p)) th'y den_th't_th'y
              notin_pf      = lem_free_bound_in_env g (TRefn b x p) k p_g_t y

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
lem_entails_elimination' g p_g_wf b x p q y pf_p_bl pf_q_bl p_g_t1 
  = lem_entails_elimination g p_er_g_wf b x p q y pf_p_bl pf_q_bl (p_g_t1
                            ? ( strengthen p q === Conj p q ))
      where
        p_er_g_wf = lem_erase_env_wfenv g p_g_wf

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
lem_entails_conjunction' g p_g_wf b x r k p_g_t1 p q y pf_p_bl pf_q_bl ent_yenv_p ent_yenv_q 
  = lem_entails_conjunction g p_g_wf b x r p q y ent_yenv_p ent_yenv_q
                            ? ( strengthen p q === Conj p q )

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
lem_entails_disjunction' g p_g_wf b x r k p_g_t1 p q y pf_p_bl pf_q_bl ent_yenv_pq 
  = lem_entails_disjunction g p_g_wf b x r k p_g_t1 p q y pf_p_bl pf_q_bl 
                            (ent_yenv_pq ? ( strengthen p q === Conj p q ))
