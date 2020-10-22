{-# LANGUAGE GADTs #-}

{-@ LIQUID "--no-termination" @-} -- TODO assume
{-@ LIQUID "--no-totality" @-} -- TODO assume
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module DenotationsSoundnessSub where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import Entailments
import LemmasChangeVarWF
import LemmasWeakenWF
import LemmasWellFormedness
import LemmasTyping
import LemmasSubtyping
import LemmasChangeVarTyp
import LemmasWeakenTyp
--import SubstitutionLemmaWF
import DenotationsSelfify

{-@ reflect foo41 @-}
foo41 x = Just x
foo41 :: a -> Maybe a

{-@ lem_denote_sound_sub :: g:Env -> t1:Type -> k1:Kind -> t2:Type -> k2:Kind 
                -> { p_t1_t2:_ | propOf p_t1_t2 == Subtype g t1 t2 }
                -> ProofOf(WFEnv g) -> ProofOf(WFType g t1 k1) -> ProofOf(WFType g t2 k2) 
                -> th:CSub -> ProofOf(DenotesEnv g th) -> v:Value 
                -> ProofOf(Denotes (ctsubst th t1) v) 
                -> ProofOf(Denotes (ctsubst th t2) v) / [subtypSize p_t1_t2] @-}
lem_denote_sound_sub :: Env -> Type -> Kind -> Type -> Kind -> Subtype -> WFEnv -> WFType -> WFType
                            -> CSub -> DenotesEnv -> Expr -> Denotes -> Denotes 
lem_denote_sound_sub g t1 k1 t2 k2 (SBase _g x1 b p1 x2 p2 y pf_ent_p2) p_g_wf p_g_t1 p_g_t2
                    -- t1 = b{x1:p1}, t2 = b{x2:p2}  -- Pf(Entails g' p2[y/x2])
                       th den_g_th val den_t1_v
  = undefined {-}
  = case den_t1_v of
      (DRefn _b _ _ also_val pf_v_b pf_th_p1v_tt) -> case (pf_ent_p2) of   -- EvalsTo th(p1[v/x1]) tt
        (EntPred y_g _p2 ev_thp2_tt)     -- forall th' in [[x1,g]]. EvalsTo th'(p2[x1/x2]) tt 
            -> DRefn b x2 (csubst th p2) also_val pf_v_b' pf_th'_p2v_tt
                     `withProof` lem_ctsubst_refn th b x2 p2
                where
                  pf_v_b'       = pf_v_b `withProof`  lem_ctsubst_refn th b x1 p1 
                  den_g'_th'    = DExt g th den_g_th y t1 val den_t1_v
                  th'           = CCons y (val ? lem_den_nofv val (ctsubst th t1) den_t1_v)
                                        (th ? lem_binds_env_th g th den_g_th) -- y is fresh repl. x1
                                        -- th' = (y |-> v, th) \in [[ Cons y t1 g ]]
                  pf_th'_p2v_tt = ev_thp2_tt th' den_g'_th' 
                                    `withProof` lem_csubst_and_unbind x2 y val (FTBasic b) pf_v_b' th p2
      (_) -> impossible ("by lemma" ? lem_ctsubst_refn th b x1 p1) -}
lem_denote_sound_sub g t1 k1 t2 k2 -----------------------------------
             p_t1_t2@(SFunc _g x1 s1 x2 s2 p_g_s2_s1 t1' t2' y p_g'_t1_t2) p_g_wf p_g_t1 p_g_t2
                                                -- Subtype (Cons y s2 g) t1'[y/x1] t2'[y/x2]
             th den_g_th _v den_tht1_v 
  = undefined {-
  = case den_tht1_v of 
      (DFunc _x1 ths1 tht1' val pf_v_er_t1 _pf_den_tht1'_vv')
        -> DFunc x2 (ctsubst th s2) (ctsubst th t2') val pf_v_er_t2 (pf_den_tht2'_vv')
                 `withProof` lem_ctsubst_func th x1 s1 t1'
                 `withProof` lem_ctsubst_func th x2 s2 t2'
          where
            (WFFunc _ _ _s1 p_g_s1 _t1' z p_zg_t1') = p_g_t1
            (WFFunc _ _ _s2 p_g_s2 _t2' w p_wg_t2') = p_g_t2 
            _p_yg_t1'    = lem_change_var_wf g z s1 Empty (unbindT x1 z t1') p_zg_t1' y
                                      `withProof` lem_tsubFV_unbindT x1 z (FV y) t1'
            {-@ p_yg_t1' :: ProofOf(WFType (Cons y s2 g) (unbindT x1 y t1')) @-}
            p_yg_t1'     = lem_subtype_in_env_wf g Empty y s2 s1 p_g_s2_s1 (unbindT x1 y t1') _p_yg_t1'
            {-@ p_yg_t2' :: ProofOf(WFType (Cons y s2 g) (unbindT x2 y t2')) @-}
            p_yg_t2'     = lem_change_var_wf g w s2 Empty (unbindT x2 w t2') p_wg_t2' y
                                      `withProof` lem_tsubFV_unbindT x2 w (FV y) t2'
            pf_v_er_t2   = pf_v_er_t1 `withProof` lem_erase_th_sub g t1 t2 p_t1_t2 th
                                      `withProof` lem_ctsubst_func th x1 s1 t1'
                                      `withProof` lem_ctsubst_func th x2 s2 t2'
            g'           = Cons y s2 (g ? lem_binds_env_th g th den_g_th)
            ths2_ths1    = lem_denote_sound_sub g s2 s1 p_g_s2_s1 p_g_wf p_g_s2 p_g_s1 th den_g_th 
            tht1'_tht2'  = lem_denote_sound_sub g' (unbindT x1 y t1') (unbindT x2 y t2')
                                                p_g'_t1_t2 (WFEBind g p_g_wf y s2 p_g_s2)
                                                p_yg_t1' p_yg_t2'
            {-@ pf_den_tht2'_vv' :: v':Value -> ProofOf(Denotes (ctsubst th s2) v') 
                   -> ProofOf(ValueDenoted (App val v') (tsubBV x2 v' (ctsubst th t2'))) @-}
            pf_den_tht2'_vv' v' den_ths2_v' = ValDen (App val v') (tsubBV x2 v' (ctsubst th t2'))
                                                    v''  evalpf   den_t2'v'_v'' 
              where
                pf_v'_er_s2    = get_btyp_from_den (ctsubst th s2)  v' den_ths2_v' 
                                         `withProof` lem_erase_th_sub g s2 s1 p_g_s2_s1 th 
                th'            = CCons y v' th -- (y |-> v', th) in [[y:s2,g]]
                den_g'_th'     = DExt g th den_g_th y s2 (v' ? lem_den_nofv v' (ctsubst th s2) den_ths2_v') 
                                      den_ths2_v' 
                (ValDen _ _ v'' evalpf denpf) = get_obj_from_dfunc x1 (ctsubst th s1) (ctsubst th t1') 
                         val den_tht1_v v' 
                         (ths2_ths1 v' (den_ths2_v' `withProof` lem_ctsubst_func th x2 s2 t2')
                                                    `withProof` lem_ctsubst_func th x1 s1 t1')
                pf_vv'_er_t1'  = BTApp BEmpty val (erase (ctsubst th s1)) 
                                       (erase (ctsubst th t1')) pf_v_er_t1
                                       v' (get_btyp_from_den (ctsubst th s2) v' den_ths2_v')
                pf_v''_er_t1'  = lemma_soundness (App val v') v'' evalpf
                                                 (erase t1') pf_vv'_er_t1'
                {-@ den_t2'v'_v'' :: ProofOf(Denotes (tsubBV x2 v' (ctsubst th t2')) v'') @-}
                den_t2'v'_v''  = tht1'_tht2' th' den_g'_th' v'' 
                                      (denpf `withProof` lem_ctsubst_and_unbindT 
                                                            x1 y v' (erase (ctsubst th s1)) 
                                                            pf_v'_er_s2 th t1')
                                      `withProof` lem_ctsubst_func th x2 s2 t2'
                                      `withProof` lem_ctsubst_func th x1 s1 t1'
                                      `withProof` lem_ctsubst_and_unbindT x2 y v' 
                                          (erase (ctsubst th s2)) 
                                          (get_btyp_from_den (ctsubst th s2) v' den_ths2_v') 
                                          th t2'
      (_) -> impossible ("by lemma" ? lem_ctsubst_func th x1 s1 t1')-}
lem_denote_sound_sub g t1 k1 t2 k2 -- @(TExists x t_x t')  -----------------------------------
             p_t1_t2@(SWitn _g v_x t_x p_vx_tx _t1 x t2' p_t1_t2'vx) 
             p_g_wf p_g_t1 p_g_t2 th den_g_th v den_tht1_v
    = undefined {-
    = DExis x (ctsubst th t_x) (ctsubst th t2') v p_v_er_t2' thvx -- v'  
            den_thtx_thvx (den_tht2'vx_v `withProof` lem_value_refl also_thvx thvx pf1)
        where -- By the inductive hypothesis and mutual induction:
          (WFExis _ _ _tx p_g_tx _ y _p_yg_t2') = p_g_t2 ? toProof ( t2 === TExists x t_x t2' )
          {-@ p_yg_t2' :: ProofOf(WFType (concatE (Cons y t_x g) Empty) (unbindT x y t2')) @-}
          p_yg_t2' = _p_yg_t2' --`withProof` lem_tsubFV_unbindT x w (FV y) t2'
          p_yg_wf  = WFEBind g p_g_wf y t_x p_g_tx
          {-@ p_g_t2'vx :: ProofOf(WFType g (tsubBV x v_x t2')) @-}
          p_g_t2'vx = lem_subst_wf g Empty y v_x t_x p_vx_tx p_yg_wf (unbindT x y t2') p_yg_t2'
                              `withProof` lem_tsubFV_unbindT x y v_x t2' 
          den_tht2'vx_v = lem_denote_sound_sub g t1 (tsubBV x v_x t2') p_t1_t2'vx p_g_wf 
                              p_g_t1 p_g_t2'vx th den_g_th v den_tht1_v -- v \in [[ t2'[v_x/x] ]]
                              `withProof` lem_ctsubst_exis th x t_x t2'    
                              `withProof` lem_commute_ctsubst_tsubBV th x v_x t2'
          also_thvx     = csubst th v_x `withProof` lem_csubst_value th v_x  -- new
          {-@ thvx :: { v:Expr | isValue v && Set_emp (freeBV v) } @-} 
          (ValDen _ _ thvx pf1 pf2)      = lem_denote_sound_typ g v_x t_x p_vx_tx p_g_wf th den_g_th
          {-@ den_thtx_thvx :: ProofOf(Denotes (ctsubst th t_x) thvx) @-}
          den_thtx_thvx = pf2  -- th(v_x) in [[th(t_x)]]. Let v' = th(v_x)...
                          `withProof` lem_commute_ctsubst_tsubBV th x v_x t2'
          -- these are ingredients to show that v \in [[th(TExists x t_x t2')]]
          p_v_er_t2'    = get_btyp_from_den (ctsubst th (tsubBV x v_x t2')) v den_tht2'vx_v
                              `withProof` lem_erase_ctsubst th t2'
                              `withProof` lem_erase_tsubBV x v_x t2'
                              `withProof` lem_erase_ctsubst th (tsubBV x v_x t2')-}
lem_denote_sound_sub g t1 k1 t2 k2 -- @(TExists x t_x t') t2 --------------------------------------
             p_t1_t2@(SBind _g x t_x t' _t2 y p_t'yx_t2) p_g_wf p_g_t1 p_g_t2 th den_g_th v 
             den_tht1_v -- @(DExis _ thtx tht' _v pf_v_er_t' v_x den_thtx_vx den_tht'vx_v)
    = undefined {-
    = case (t1, den_tht1_v) of 
        (TExists _ _ _, DExis _ thtx tht' _v pf_v_er_t' v_x den_thtx_vx den_tht'vx_v) 
          -> den_tht2_v
            where -- by the inductive hypothesis we have
              (WFExis _ _ _tx p_g_tx _ w p_wg_t') = p_g_t1
              g'         = Cons y t_x g
              p_g'_wf    = WFEBind g p_g_wf y t_x p_g_tx
              p_g'_t'    = lem_change_var_wf g w t_x Empty (unbindT x w t') p_wg_t' y
                              `withProof` lem_tsubFV_unbindT x w (FV y) t' 
              p_g'_t2    = lem_weaken_wf g Empty t2 p_g_t2 y t_x -- p_g_tx
              den_g'_th' = DExt g th den_g_th y t_x v_x den_thtx_vx
              pf_vx_ertx = get_btyp_from_den thtx v_x den_thtx_vx
              den_tht'_v = den_tht'vx_v `withProof` lem_ctsubst_exis th x t_x t'
                               `withProof` lem_ctsubst_and_unbindT x y v_x (erase thtx) 
                                                                   pf_vx_ertx th t'
              den_tht2_v = lem_denote_sound_sub g' (unbindT x y t') t2 p_t'yx_t2 
                               p_g'_wf p_g'_t' p_g'_t2 th' den_g'_th' v den_tht'_v
                               `withProof` lem_ctsubst_head_not_free y v_x th t2
              th'        = CCons y (v_x ? lem_den_nofv v_x thtx den_thtx_vx)
                                   (th  ? lem_binds_env_th g th den_g_th)
        (_, _) -> impossible ("by lemma" ? lem_ctsubst_exis th x t_x t')-}
lem_denote_sound_sub g t1 k1 t2 k2
             p_t1_t2@(SPoly {}) p_g_wf p_g_t1 p_g_t2 th den_g_th v den_tht1_v
    = undefined
