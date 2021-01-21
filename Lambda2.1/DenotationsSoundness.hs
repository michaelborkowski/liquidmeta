{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module DenotationsSoundness where

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
import SystemFSoundness
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import BasicPropsEraseTyping
import Entailments
import PrimitivesSemantics
import LemmasChangeVarWF
import LemmasWeakenWF
import LemmasWellFormedness
import LemmasTyping
import LemmasSubtyping
import LemmasChangeVarTyp
import LemmasWeakenTyp
import SubstitutionLemmaWF
import DenotationsSelfify
import PrimitivesDenotations

{-@ reflect foo59 @-}
foo59 x = Just x
foo59 :: a -> Maybe a

{-@ lem_denote_sound_sub_sbase :: g:Env -> t1:Type -> k1:Kind -> t2:Type -> k2:Kind 
                -> { p_t1_t2:_ | propOf p_t1_t2 == Subtype g t1 t2 && isSBase p_t1_t2}
                -> ProofOf(WFEnv g) -> ProofOf(WFType g t1 k1) -> ProofOf(WFType g t2 k2) 
                ->  th:CSub 
                -> ProofOf(DenotesEnv g th) -> v:Value -> ProofOf(Denotes (ctsubst th t1) v) 
                -> ProofOf(Denotes (ctsubst th t2) v) / [subtypSize p_t1_t2,0] @-}
lem_denote_sound_sub_sbase :: Env -> Type -> Kind -> Type -> Kind -> Subtype -> WFEnv -> WFType -> WFType
                            -> CSub -> DenotesEnv -> Expr -> Denotes -> Denotes 
lem_denote_sound_sub_sbase g t1 k1 t2 k2 (SBase _g x1 b p1 x2 p2 y pf_ent_p2) p_g_wf p_g_t1 p_g_t2
                    -- t1 = b{x1:p1}, t2 = b{x2:p2}  -- Pf(Entails g' p2[y/x2])
                       th den_g_th val_ den_t1_v  = undefined {- recheck
  = case b of 
      (FTV a) -> lem_denote_ctsubst_refn_var' g a x2 p2 th den_g_th val den_tha_v ev_thp2v_tt
        where
          val                       = val_ ? lem_den_nofv val_ (ctsubst th t1) den_t1_v
                                           ? lem_den_nobv val_ (ctsubst th t1) den_t1_v
          (s, p_val_s)              = get_ftyp_from_den (ctsubst th t1) val den_t1_v
          (den_tha_v, ev_thp1v_tt)  = lem_denote_ctsubst_refn_var g a x1 p1 th den_g_th val den_t1_v
          th'                       = CCons y val (th ? lem_binds_env_th g th den_g_th)
          den_g'_th'                = DExt g th den_g_th y t1 val den_t1_v
          (EntPred _ _ rd_th'p2_tt) = pf_ent_p2
          ev_thp2v_tt               = rd_th'p2_tt th' den_g'_th' 
                                           ? lem_csubst_and_unbind x2 y val s p_val_s th p2
       {-case (kind_for_tv a (g ? lem_wf_refn_tv_in_env g a x1 p1 k1 p_g_t1)) of
        Star  -> den_t1_v ? lem_wf_refn_tv_star g a x1 p1 k1 p_g_t1
                          ? lem_wf_refn_tv_star g a x2 p2 k2 p_g_t2
        Base  -> lem_denote_push_ent_pred g a x1 p1 x2 p2 y pf_ent_p2 th (csubst_tv th a) 
                                          den_g_th val_ (den_t1_v
                                          ? lem_ctsubst_refn_tv g th den_g_th a x1 p1)-}
      (BTV a) -> impossible ("by lemma" ? lem_btv_not_wf g a x1 p1 k1 p_g_t1)
      _       -> case den_t1_v of
        (DRefn b_ _ _ also_val pf_v_b pf_th_p1v_tt) -> case (pf_ent_p2) of   -- EvalsTo th(p1[v/x1]) tt
          (EntPred y_g _p2 ev_thp2_tt)     -- forall th' in [[x1,g]]. EvalsTo th'(p2[x1/x2]) tt 
            -> DRefn b x2 (csubst th p2) also_val pf_v_b' pf_th'_p2v_tt
                     `withProof` lem_ctsubst_refn th b x2 p2
                 where
                   val           = val_ ? lem_den_nofv val_ (ctsubst th t1) den_t1_v
                                        ? lem_den_nobv val_ (ctsubst th t1) den_t1_v
                   pf_v_b'       = pf_v_b `withProof`  lem_ctsubst_refn th b x1 p1 
                   den_g'_th'    = DExt g th den_g_th y t1 val den_t1_v
                   th'           = CCons y val (th ? lem_binds_env_th g th den_g_th) -- y is fresh repl. x1
                                         -- th' = (y |-> v, th) \in [[ Cons y t1 g ]]
                   pf_th'_p2v_tt = ev_thp2_tt th' den_g'_th' 
                                     `withProof` lem_csubst_and_unbind x2 y val (FTBasic b) pf_v_b' th p2
        (_) -> impossible ("by lemma" ? lem_ctsubst_refn th b x1 p1) 
-}

{-@ lem_denote_sound_sub_sfunc :: g:Env -> t1:Type -> k1:Kind -> t2:Type -> k2:Kind 
                -> { p_t1_t2:_ | propOf p_t1_t2 == Subtype g t1 t2 && isSFunc p_t1_t2}
                -> ProofOf(WFEnv g) -> ProofOf(WFType g t1 k1) -> ProofOf(WFType g t2 k2) 
                ->  th:CSub 
                -> ProofOf(DenotesEnv g th) -> v:Value -> ProofOf(Denotes (ctsubst th t1) v) 
                -> ProofOf(Denotes (ctsubst th t2) v) / [subtypSize p_t1_t2,0] @-}
lem_denote_sound_sub_sfunc :: Env -> Type -> Kind -> Type -> Kind -> Subtype -> WFEnv -> WFType -> WFType
                            -> CSub -> DenotesEnv -> Expr -> Denotes -> Denotes 
lem_denote_sound_sub_sfunc g t1 k1 t2 k2 p_t1_t2@(SFunc _g x1 s1 x2 s2 p_g_s2_s1 t1' t2' y p_g'_t1_t2) 
                           p_g_wf p_g_t1 p_g_t2 th den_g_th _v den_tht1_v  = undefined {- recheck
  = case den_tht1_v of       -- p_t1_t2 :: Subtype (Cons y s2 g) t1'[y/x1] t2'[y/x2]
      (DFunc _x1 ths1 tht1' val s_x s eqv_sxs_ertht1 pf_v_sxs _pf_den_tht1'_vv')
        -> DFunc x2 (ctsubst th s2) (ctsubst th t2') val s_x s eqv_sxs_tht2 pf_v_sxs
		 --  (pf_v_er_tht2 ? lem_ctsubst_func th x2 s2 t2')
                  (pf_den_tht2'_vv') `withProof` lem_ctsubst_func th x1 s1 t1'
                                     `withProof` lem_ctsubst_func th x2 s2 t2'
          where
            (WFFunc _ _ _s1 k_s1 p_g_s1 _t1' k1' z p_zg_t1') = lem_wffunc_for_wf_tfunc g x1 s1 t1' k1 p_g_t1
            (WFFunc _ _ _s2 k_s2 p_g_s2 _t2' k2' w p_wg_t2') = lem_wffunc_for_wf_tfunc g x2 s2 t2' k2 p_g_t2
            p_zg_wf      = WFEBind g p_g_wf z s1 k_s1 p_g_s1
            p_wg_wf      = WFEBind g p_g_wf w s2 k_s2 p_g_s2
            _p_yg_t1'    = lem_change_var_wf' g z s1 Empty p_zg_wf (unbindT x1 z t1') k1' p_zg_t1' y
                                      `withProof` lem_tsubFV_unbindT x1 z (FV y) t1'
            {-@ p_yg_t1' :: ProofOf(WFType (Cons y s2 g) (unbindT x1 y t1') k1') @-}
            p_yg_t1'     = lem_subtype_in_env_wf g Empty y s2 s1 p_g_s2_s1 (unbindT x1 y t1') k1' _p_yg_t1'
            {-@ p_yg_t2' :: ProofOf(WFType (Cons y s2 g) (unbindT x2 y t2') k2') @-}
            p_yg_t2'     = lem_change_var_wf' g w s2 Empty p_wg_wf (unbindT x2 w t2') k2' p_wg_t2' y
                                      `withProof` lem_tsubFV_unbindT x2 w (FV y) t2'
            eqv_tht1tht2 = lem_erase_th_sub g t1 t2 p_t1_t2 th
            eqv_sxs_tht2 = lem_alpha_trans FEmpty (FTFunc s_x s) (erase (ctsubst th t1))
                                           (erase (ctsubst th t2)) eqv_sxs_ertht1 eqv_tht1tht2
                                           `withProof` lem_ctsubst_func th x2 s2 t2'
            g'           = Cons y s2 (g ? lem_binds_env_th g th den_g_th)
            ths2_ths1    = lem_denote_sound_sub g s2 k_s2 s1 k_s1 p_g_s2_s1 p_g_wf p_g_s2 p_g_s1 th den_g_th 
            tht1'_tht2'  = lem_denote_sound_sub g' (unbindT x1 y t1') k1' (unbindT x2 y t2') k2'
                                                p_g'_t1_t2 (WFEBind g p_g_wf y s2 k_s2 p_g_s2)
                                                p_yg_t1' p_yg_t2'

            {-@ pf_den_tht2'_vv' :: v':Value -> ProofOf(Denotes (ctsubst th s2) v') 
                   -> ProofOf(ValueDenoted (App val v') (tsubBV x2 v' (ctsubst th t2'))) @-}
            pf_den_tht2'_vv' v'_ den_ths2_v' = ValDen (App val v') (tsubBV x2 v' (ctsubst th t2'))
                                                    v''  evalpf   den_t2'v'_v'' 
              where
                v'             = v'_ ? lem_den_nofv v'_ (ctsubst th s2) den_ths2_v'
                                     ? lem_den_nobv v'_ (ctsubst th s2) den_ths2_v'
                (s0, pf_v'_s0) = get_ftyp_from_den (ctsubst th s2)  v' den_ths2_v' 
                th'            = CCons y v' th -- (y |-> v', th) in [[y:s2,g]]
                den_g'_th'     = DExt g th den_g_th y s2 (v' {-? lem_den_nofv v' (ctsubst th s2) den_ths2_v'-}) 
                                      den_ths2_v' 
                (ValDen _ _ v'' evalpf denpf) = get_obj_from_dfunc x1 (ctsubst th s1) (ctsubst th t1') 
                         val den_tht1_v v' 
                         (ths2_ths1 v' (den_ths2_v' `withProof` lem_ctsubst_func th x2 s2 t2')
                                                    `withProof` lem_ctsubst_func th x1 s1 t1')
                {-@ den_t2'v'_v'' :: ProofOf(Denotes (tsubBV x2 v' (ctsubst th t2')) v'') @-}
                den_t2'v'_v''  = tht1'_tht2' th' den_g'_th' v'' 
                                      (denpf `withProof` lem_ctsubst_and_unbindT 
                                                            x1 y v' s0 pf_v'_s0 th t1')
                                      `withProof` lem_ctsubst_func th x2 s2 t2'
                                      `withProof` lem_ctsubst_func th x1 s1 t1'
                                      `withProof` lem_ctsubst_and_unbindT x2 y v' s0 pf_v'_s0 th t2'
      (_) -> impossible ("by lemma" ? lem_ctsubst_func th x1 s1 t1')
-}

{-@ lem_denote_sound_sub_switn :: g:Env -> t1:Type -> k1:Kind -> t2:Type -> k2:Kind 
                -> { p_t1_t2:_ | propOf p_t1_t2 == Subtype g t1 t2 && isSWitn p_t1_t2}
                -> ProofOf(WFEnv g) -> ProofOf(WFType g t1 k1) -> ProofOf(WFType g t2 k2) 
                ->  th:CSub 
                -> ProofOf(DenotesEnv g th) -> v:Value -> ProofOf(Denotes (ctsubst th t1) v) 
                -> ProofOf(Denotes (ctsubst th t2) v) / [subtypSize p_t1_t2, 0] @-}
lem_denote_sound_sub_switn :: Env -> Type -> Kind -> Type -> Kind -> Subtype -> WFEnv -> WFType -> WFType
                            -> CSub -> DenotesEnv -> Expr -> Denotes -> Denotes 
lem_denote_sound_sub_switn g t1 k1 t2 k2 -- @(TExists x t_x t')  -----------------------------------
             p_t1_t2@(SWitn _g v_x t_x p_vx_tx _t1 x t2' p_t1_t2'vx) 
             p_g_wf p_g_t1 p_g_t2 th den_g_th v den_tht1_v   = undefined {- recheck
    = DExis x (ctsubst th t_x) (ctsubst th t2') v s eqv_s_ert2' p_v_s thvx -- v'  
            den_thtx_thvx (den_tht2'vx_v `withProof` lem_value_refl also_thvx thvx pf1)
        where -- By the inductive hypothesis and mutual induction:
          (WFExis _ _ _tx k_x p_g_tx _ _ y _p_yg_t2') = lem_wfexis_for_wf_texists g x t_x t2' k2 p_g_t2 
                                                            ? toProof ( t2 === TExists x t_x t2' )
          {-@ p_yg_t2' :: ProofOf(WFType (concatE (Cons y t_x g) Empty) (unbindT x y t2') k2) @-}
          p_yg_t2' = _p_yg_t2' --`withProof` lem_tsubFV_unbindT x w (FV y) t2'
          p_yg_wf  = WFEBind g p_g_wf y t_x k_x p_g_tx
          {-@ p_g_t2'vx :: ProofOf(WFType g (tsubBV x v_x t2') k2) @-}
          p_g_t2'vx = lem_subst_wf' g Empty y v_x t_x p_vx_tx p_yg_wf (unbindT x y t2') k2 p_yg_t2'
                              `withProof` lem_tsubFV_unbindT x y v_x t2' 
          den_tht2'vx_v = lem_denote_sound_sub g t1 k1 (tsubBV x v_x t2') k2 p_t1_t2'vx p_g_wf 
                              p_g_t1 p_g_t2'vx th den_g_th v den_tht1_v -- v \in [[ t2'[v_x/x] ]]
                              `withProof` lem_ctsubst_exis th x t_x t2'    
                              `withProof` lem_commute_ctsubst_tsubBV th x v_x t2'
          also_thvx     = csubst th v_x `withProof` lem_csubst_value th v_x  -- new
          {-@ thvx :: { v:Expr | isValue v } @-} -- Set_emp freeBV v
          (ValDen _ _ thvx pf1 pf2)      = lem_denote_sound_typ g v_x t_x p_vx_tx p_g_wf th den_g_th
          {-@ den_thtx_thvx :: ProofOf(Denotes (ctsubst th t_x) thvx) @-}
          den_thtx_thvx = pf2  -- th(v_x) in [[th(t_x)]]. Let v' = th(v_x)...
                          `withProof` lem_commute_ctsubst_tsubBV th x v_x t2'
          -- these are ingredients to show that v \in [[th(TExists x t_x t2')]]
          (AEWitness _ _ _ s eqv_s_ert2' p_v_s) = get_aewitness_from_den 
                              (ctsubst th (tsubBV x v_x t2')) v den_tht2'vx_v
                              `withProof` lem_erase_ctsubst th t2'
                              `withProof` lem_erase_tsubBV x v_x t2'
                              `withProof` lem_erase_ctsubst th (tsubBV x v_x t2')
-}

{-@ lem_denote_sound_sub_sbind :: g:Env -> t1:Type -> k1:Kind -> t2:Type -> k2:Kind 
                -> { p_t1_t2:_ | propOf p_t1_t2 == Subtype g t1 t2 && isSBind p_t1_t2}
                -> ProofOf(WFEnv g) -> ProofOf(WFType g t1 k1) -> ProofOf(WFType g t2 k2) 
                ->  th:CSub 
                -> ProofOf(DenotesEnv g th) -> v:Value -> ProofOf(Denotes (ctsubst th t1) v) 
                -> ProofOf(Denotes (ctsubst th t2) v) / [subtypSize p_t1_t2,0] @-}
lem_denote_sound_sub_sbind :: Env -> Type -> Kind -> Type -> Kind -> Subtype -> WFEnv -> WFType -> WFType
                            -> CSub -> DenotesEnv -> Expr -> Denotes -> Denotes 
lem_denote_sound_sub_sbind g t1 k1 t2 k2 -- t1 == (TExists x t_x t') 
             p_t1_t2@(SBind _g x t_x t' _t2 y p_t'yx_t2) p_g_wf p_g_t1 p_g_t2 th den_g_th v den_tht1_v = undefined {- recheck
    = case (t1, den_tht1_v) of 
        (TExists _ _ _, DExis _ thtx tht' _v s eqv_s_ertht' pf_v_s v_x den_thtx_vx den_tht'vx_v) 
          -> den_tht2_v
            where -- by the inductive hypothesis we have
              (WFExis _ _ _tx k_x p_g_tx _ _ w p_wg_t') =lem_wfexis_for_wf_texists g x t_x t' k1 p_g_t1
              g'         = Cons y t_x g
              p_wg_wf    = WFEBind g p_g_wf w t_x k_x p_g_tx
              p_g'_wf    = WFEBind g p_g_wf y t_x k_x p_g_tx 
              p_g'_t'    = lem_change_var_wf' g w t_x Empty p_wg_wf (unbindT x w t') k1 p_wg_t' y
                              `withProof` lem_tsubFV_unbindT x w (FV y) t' 
              p_g'_t2    = lem_weaken_wf' g Empty p_g_wf t2 k2 p_g_t2 y t_x -- p_g_tx
              den_g'_th' = DExt g th den_g_th y t_x v_x den_thtx_vx
              (sx, pf_vx_sx) = get_ftyp_from_den thtx v_x den_thtx_vx
              den_tht'_v = den_tht'vx_v `withProof` lem_ctsubst_exis th x t_x t'
                               `withProof` lem_ctsubst_and_unbindT x y v_x sx pf_vx_sx th t'
              den_tht2_v = lem_denote_sound_sub g' (unbindT x y t') k1 t2 k2 p_t'yx_t2 
                               p_g'_wf p_g'_t' p_g'_t2 th' den_g'_th' v den_tht'_v
                               `withProof` lem_ctsubst_head_not_free y v_x th t2
              th'        = CCons y (v_x ? lem_den_nofv v_x thtx den_thtx_vx
                                        ? lem_den_nobv v_x thtx den_thtx_vx)
                                   (th  ? lem_binds_env_th g th den_g_th)
        (_, _) -> impossible ("by lemma" ? lem_ctsubst_exis th x t_x t')
-}

{-@ lem_denote_sound_sub_spoly :: g:Env -> t1:Type -> k1:Kind -> t2:Type -> k2:Kind 
                -> { p_t1_t2:_ | propOf p_t1_t2 == Subtype g t1 t2 && isSPoly p_t1_t2}
                -> ProofOf(WFEnv g) -> ProofOf(WFType g t1 k1) -> ProofOf(WFType g t2 k2) 
                ->  th:CSub 
                -> ProofOf(DenotesEnv g th) -> v:Value -> ProofOf(Denotes (ctsubst th t1) v) 
                -> ProofOf(Denotes (ctsubst th t2) v) / [subtypSize p_t1_t2,0] @-}
lem_denote_sound_sub_spoly :: Env -> Type -> Kind -> Type -> Kind -> Subtype -> WFEnv -> WFType -> WFType
                            -> CSub -> DenotesEnv -> Expr -> Denotes -> Denotes 
lem_denote_sound_sub_spoly g t1 Star t2 Star p_t1_t2@(SPoly _g a1 k t1' a2 t2' a p_ag_t1'_t2')
                           p_g_wf p_g_t1 p_g_t2 th den_g_th _v den_tht1_v  = undefined {- recheck
  = case den_tht1_v of   
      (DPoly _a1 _k tht1' val a0 s eqv_a0s_ertht1 pf_v_a0s _pf_den_tht1'_vta)
        -> DPoly a2 k (ctsubst th t2') val a0 s eqv_a0s_ertht2 pf_v_a0s pf_den_tht2'_vta
                 ? lem_ctsubst_poly th a1 k t1'
          where                                                                   -- lem_ctsubst_poly
            (WFPoly _ _ _ _t1' k1' a1' p_a1'g_t1') = lem_wfpoly_for_wf_tpoly g a1 k t1' p_g_t1
            (WFPoly _ _ _ _t2' k2' a2' p_a2'g_t2') = lem_wfpoly_for_wf_tpoly g a2 k t2' p_g_t2
            p_a1'g_wf    = WFEBindT g p_g_wf a1' k
            p_a2'g_wf    = WFEBindT g p_g_wf a2' k
            {-@ p_ag_t1' :: ProofOf(WFType (ConsT a k g) (unbind_tvT a1 a t1') k1') @-}
            p_ag_t1'     = lem_change_tvar_wf g a1' k Empty p_a1'g_wf (unbind_tvT a1 a1' t1') k1' 
                                   p_a1'g_t1' a ? lem_tchgFTV_unbind_tvT a1 a1' a t1'
            {-@ p_ag_t2' :: ProofOf(WFType (ConsT a k g) (unbind_tvT a2 a t2') k2') @-}
            p_ag_t2'     = lem_change_tvar_wf g a2' k Empty p_a2'g_wf (unbind_tvT a2 a2' t2') k2' 
                                   p_a2'g_t2' a ? lem_tchgFTV_unbind_tvT a2 a2' a t2'
            g'           = ConsT a k (g ? lem_binds_env_th g th den_g_th)
            tht1'_tht2'  = lem_denote_sound_sub g' (unbind_tvT a1 a t1') k1' (unbind_tvT a2 a t2') k2'
                                   p_ag_t1'_t2' (WFEBindT g p_g_wf a k) p_ag_t1' p_ag_t2'
            eqv_tht1tht2 = lem_erase_th_sub g t1 t2 p_t1_t2 th
            eqv_a0s_ertht2 = lem_alpha_trans FEmpty (FTPoly a0 k s) (erase (ctsubst th t1))
                                   (erase (ctsubst th t2)) (eqv_a0s_ertht1 ? lem_ctsubst_poly th a1 k t1')
                                   eqv_tht1tht2 `withProof` lem_ctsubst_poly th a2 k t2'
            {- @ pf_den_tht2'_vta :: { t_a:Type | same_binders t_a (ctsubst th t2') } -}
            {-@ pf_den_tht2'_vta :: t_a:Type -> ProofOf(WFType Empty t_a k)
                   -> ProofOf(ValueDenoted (AppT val t_a) (tsubBTV a2 t_a (ctsubst th t2'))) @-}
            pf_den_tht2'_vta t_a_ p_emp_ta = ValDen (AppT val t_a) (tsubBTV a2 t_a (ctsubst th t2'))
                                                    v''  evalpf   den_tht2'vta_v'' 
              where
                t_a              = t_a_ ? lem_free_subset_binds Empty t_a_ k p_emp_ta
                                        ? lem_tfreeBV_empty     Empty t_a_ k p_emp_ta 
                th'              = CConsT a t_a th -- (a |-> t_a, th) in [[a:k,g]]
                den_g'_th'       = DExtT g th den_g_th a k t_a p_emp_ta  
                (ValDen _ _ v'' evalpf denpf) = get_obj_from_dpoly a1 k (ctsubst th t1') val
                         (den_tht1_v ? lem_ctsubst_poly th a1 k t1') t_a p_emp_ta
                {-@ den_tht2'vta_v'' :: ProofOf(Denotes (tsubBTV a2 t_a (ctsubst th t2')) v'') @-}
                den_tht2'vta_v'' = tht1'_tht2' th' den_g'_th' v'' -- rest is v'' \in [[th(t1')]] :
                                      (denpf ? lem_ctsubst_and_unbind_tvT a1 a t_a k p_emp_ta th t1')
                                      `withProof` lem_ctsubst_poly th a2 k t2'
                                      `withProof` lem_ctsubst_poly th a1 k t1'
                                             ? lem_ctsubst_and_unbind_tvT a2 a t_a k p_emp_ta th t2'
      (_) -> impossible ("by lemma" ? lem_ctsubst_poly th a1 k t1')
-}
lem_denote_sound_sub_spoly g t1 Base t2 k2   p_t1_t2@(SPoly _g a1 k t1' a2 t2' a p_ag_t1'_t2')
                           p_g_wf p_g_t1 p_g_t2 th den_g_th _v den_tht1_v
  = impossible ("by lemma" ? lem_wf_tpoly_star g a1 k t1' p_g_t1)
lem_denote_sound_sub_spoly g t1 k1   t2 Base p_t1_t2@(SPoly _g a1 k t1' a2 t2' a p_ag_t1'_t2')
                           p_g_wf p_g_t1 p_g_t2 th den_g_th _v den_tht1_v
  = impossible ("by lemma" ? lem_wf_tpoly_star g a2 k t2' p_g_t2)

{-@ lem_denote_sound_sub :: g:Env -> t1:Type -> k1:Kind -> t2:Type -> k2:Kind 
                -> { p_t1_t2:_ | propOf p_t1_t2 == Subtype g t1 t2 }
                -> ProofOf(WFEnv g) -> ProofOf(WFType g t1 k1) -> ProofOf(WFType g t2 k2) 
                -> th:CSub 
                -> ProofOf(DenotesEnv g th) -> v:Value -> ProofOf(Denotes (ctsubst th t1) v) 
                -> ProofOf(Denotes (ctsubst th t2) v) / [subtypSize p_t1_t2,1] @-}
lem_denote_sound_sub :: Env -> Type -> Kind -> Type -> Kind -> Subtype -> WFEnv -> WFType -> WFType
                            -> CSub -> DenotesEnv -> Expr -> Denotes -> Denotes 
lem_denote_sound_sub g t1 k1 t2 k2 p_t1_t2@(SBase _g x1 b p1 x2 p2 y pf_ent_p2) p_g_wf 
                     p_g_t1 p_g_t2 th den_g_th val den_t1_v
  = lem_denote_sound_sub_sbase g t1 k1 t2 k2 p_t1_t2 p_g_wf p_g_t1 p_g_t2 th den_g_th val den_t1_v
lem_denote_sound_sub g t1 k1 t2 k2 
             p_t1_t2@(SFunc _g x1 s1 x2 s2 p_g_s2_s1 t1' t2' y p_g'_t1_t2) p_g_wf p_g_t1 p_g_t2
             th den_g_th v den_tht1_v 
  = lem_denote_sound_sub_sfunc g t1 k1 t2 k2 p_t1_t2 p_g_wf p_g_t1 p_g_t2 th den_g_th v den_tht1_v
lem_denote_sound_sub g t1 k1 t2 k2 -- @(TExists x t_x t')  --------
             p_t1_t2@(SWitn _g v_x t_x p_vx_tx _t1 x t2' p_t1_t2'vx) 
             p_g_wf p_g_t1 p_g_t2 th den_g_th v den_tht1_v
  = lem_denote_sound_sub_switn g t1 k1 t2 k2 p_t1_t2 p_g_wf p_g_t1 p_g_t2 th den_g_th v den_tht1_v
lem_denote_sound_sub g t1 k1 t2 k2 -- @(TExists x t_x t') t2 ------
             p_t1_t2@(SBind _g x t_x t' _t2 y p_t'yx_t2) p_g_wf p_g_t1 p_g_t2 th den_g_th v 
             den_tht1_v 
  = lem_denote_sound_sub_sbind g t1 k1 t2 k2 p_t1_t2 p_g_wf p_g_t1 p_g_t2 th den_g_th v den_tht1_v
lem_denote_sound_sub g t1 k1 t2 k2
             p_t1_t2@(SPoly {}) p_g_wf p_g_t1 p_g_t2 th den_g_th v den_tht1_v
  = lem_denote_sound_sub_spoly g t1 k1 t2 k2 p_t1_t2 p_g_wf p_g_t1 p_g_t2 th den_g_th v den_tht1_v


{-@ lem_denote_sound_typ_tvar1 :: g:Env -> e:Term -> t:Type 
                -> { p_e_t:HasType | propOf p_e_t == HasType g e t && isTVar1 p_e_t } -> ProofOf(WFEnv g) 
                ->  th:CSub  -> ProofOf(DenotesEnv g th)  
                -> ProofOf(ValueDenoted (csubst th e) (ctsubst th t)) / [typSize p_e_t, 0] @-}
lem_denote_sound_typ_tvar1 :: Env -> Expr -> Type -> HasType -> WFEnv -> CSub 
                            -> DenotesEnv -> ValueDenoted
lem_denote_sound_typ_tvar1 g e t (TVar1 g' x t' k' p_g'_t') (WFEBind _ wf_g' _ _ _ _p_g'_t') th den_g_th 
  = case den_g_th of              -- e == FV x, t == self t x 
      (DExt _g' th' den_g'_th' _x _t' w den_th't'_w)  -- w = th(x)
        -> ValDen (csubst th e) (ctsubst th t) w ev_the_v' den_tht_thx
             where
               ev_the_v' = Refl w `withProof` lem_den_nofv w (ctsubst th' t') den_th't'_w
                                  `withProof` lem_den_nobv w (ctsubst th' t') den_th't'_w
                                  `withProof` lem_csubst_nofv th' w
               den_tht_thx = lem_denotations_selfify (ctsubst th' t') k' w w (Refl w) den_th't'_w               
                                        ? lem_free_bound_in_env g' t' k' p_g'_t' x
                                        ? lem_binds_env_th g' th' den_g'_th'
                                        ? toProof ( ctsubst (CCons x w th') t'
                                                === ctsubst th' (tsubFV x w t') 
                                                === ctsubst th' t' )
                                        ? lem_ctsubst_self th t' (FV x) k'

{-@ lem_denote_sound_typ_tvar2 :: g:Env -> e:Term -> t:Type 
                -> { p_e_t:HasType | propOf p_e_t == HasType g e t && isTVar2 p_e_t } -> ProofOf(WFEnv g) 
                ->  th:CSub  -> ProofOf(DenotesEnv g th)  
                -> ProofOf(ValueDenoted (csubst th e) (ctsubst th t)) / [typSize p_e_t, 0] @-}
lem_denote_sound_typ_tvar2 :: Env -> Expr -> Type -> HasType -> WFEnv -> CSub 
                            -> DenotesEnv -> ValueDenoted
lem_denote_sound_typ_tvar2 g e t (TVar2 g' x _t p_x_t y t_y) pf_g_wf th den_g_th
  = case den_g_th of 
      (DExt _g' th' den_g'_th' _y _ v_y den_tht_thy) 
        -> ValDen (csubst th e) (ctsubst th t) thx ev_the_v' den_tht_thx
            where
              (WFEBind _ pf_g'_wf _ _ _ p_g'_ty) = pf_g_wf
              {-@  thx :: Value @-} 
              (ValDen _ _ thx pf1 pf2) = lem_denote_sound_typ g' e t p_x_t pf_g'_wf th' den_g'_th' 
              p_g'_t      = lem_typing_wf g' (FV x) t p_x_t pf_g'_wf 
              ev_the_v'   = pf1 `withProof` lem_den_nofv thx (ctsubst th' t) pf2
                                `withProof` lem_csubst_nofv th' thx
              den_tht_thx = pf2 ? lem_free_bound_in_env g' t Star p_g'_t y
                                ? lem_binds_env_th g' th' den_g'_th' 
                                ? lem_tsubFV_notin y v_y t

{-@ lem_denote_sound_typ_tvar3 :: g:Env -> e:Term -> t:Type 
                -> { p_e_t:HasType | propOf p_e_t == HasType g e t && isTVar3 p_e_t } -> ProofOf(WFEnv g) 
                ->  th:CSub  -> ProofOf(DenotesEnv g th)  
                -> ProofOf(ValueDenoted (csubst th e) (ctsubst th t)) / [typSize p_e_t, 0] @-}
lem_denote_sound_typ_tvar3 :: Env -> Expr -> Type -> HasType -> WFEnv -> CSub 
                            -> DenotesEnv -> ValueDenoted
lem_denote_sound_typ_tvar3 g e t (TVar3 g' x _t p_x_t a k_a) pf_g_wf th den_g_th
  = case den_g_th of 
      (DExtT _g' th' den_g'_th' _a _ka t_a p_emp_ta) 
        -> ValDen (csubst th e) (ctsubst th t) thx ev_the_v' den_tht_thx
             where
               (WFEBindT _ pf_g'_wf _ _) = pf_g_wf
               {-@ thx :: Value @-}
               (ValDen _ _ thx pf1 pf2) = lem_denote_sound_typ g' e t p_x_t pf_g'_wf th' den_g'_th'
               p_g'_t      = lem_typing_wf g' (FV x) t p_x_t pf_g'_wf 
               ev_the_v'   = pf1 `withProof` lem_den_nofv thx (ctsubst th' t) pf2
                                 `withProof` lem_csubst_nofv th' thx
               den_tht_thx = pf2 ? lem_free_bound_in_env g' t Star p_g'_t a
                                 ? lem_binds_env_th g' th' den_g'_th'
                                 ? lem_tsubFTV_notin a t_a t

{-@ lem_denote_sound_typ_tabs :: g:Env -> e:Term -> t:Type 
                -> { p_e_t:HasType | propOf p_e_t == HasType g e t && isTAbs p_e_t } -> ProofOf(WFEnv g) 
                ->  th:CSub  -> ProofOf(DenotesEnv g th)  
                -> ProofOf(ValueDenoted (csubst th e) (ctsubst th t)) / [typSize p_e_t, 0] @-}
lem_denote_sound_typ_tabs :: Env -> Expr -> Type -> HasType -> WFEnv -> CSub 
                            -> DenotesEnv -> ValueDenoted
lem_denote_sound_typ_tabs g e t p_e_t@(TAbs _g x t_x k_x p_g_tx e' t' y p_yg_e'_t') p_g_wf th den_g_th = undefined {- recheck
  = ValDen (csubst th e) (ctsubst th t) v ev_the_v den_tht_v
      where 
        {-@ v :: { z:Value | z == csubst th e && e == Lambda x e'} @-}  -- need to show (Lambda x e') is a value 
        v = Lambda x (csubst th e') ? lem_csubst_lambda th x e' 
        ev_the_v  = Refl (csubst th e) ? lem_csubst_lambda th x e'
        (AEWitness _ _ _ s eqv_s_er_tht p_e_s) = lem_csubst_hasftype g e t p_e_t p_g_wf
                          th den_g_th ? lem_erase_ctsubst th t_x ? lem_erase_ctsubst th t'
                                      ? lem_ctsubst_func th x t_x t'
        (AEFunc _ s_x _ _ s' _ _) = eqv_s_er_tht -- s = s_x -> s' =a= erase th(x:t_x -> t')
        den_tht_v = DFunc x (ctsubst th t_x) (ctsubst th t') v s_x s' eqv_s_er_tht p_e_s
                          pf_den_tht'vx_vvx -- ? lem_ctsubst_func th x t_x t'
        {-@ pf_den_tht'vx_vvx :: v_x:Value -> ProofOf(Denotes (ctsubst th t_x) v_x)
                     -> ProofOf(ValueDenoted (App v v_x) (tsubBV x v_x (ctsubst th t'))) @-}
        pf_den_tht'vx_vvx :: Expr -> Denotes -> ValueDenoted
        pf_den_tht'vx_vvx v_x den_thtx_vx = ValDen (App v v_x) (tsubBV x v_x (ctsubst th t'))
                                 v' ev_vvx_v' (den_tht'vx_v' ? lem_ctsubst_and_unbindT x y 
                                                                   v_x s_x' pf_vx_sx' th t')
          where
            th'            = CCons y v_x (th ? lem_binds_env_th g th den_g_th)
            den_g'_th'     = DExt g th den_g_th y t_x (v_x ? lem_den_nofv v_x (ctsubst th t_x) den_thtx_vx
                                                           ? lem_den_nobv v_x (ctsubst th t_x) den_thtx_vx)
                                  den_thtx_vx
            (s_x', pf_vx_sx') = get_ftyp_from_den (ctsubst th t_x) v_x den_thtx_vx ? lem_erase_ctsubst th t_x
            (ValDen _ _ v' ev_th'e'_v' den_tht'vx_v') = lem_denote_sound_typ (Cons y t_x g) (unbind x y e') 
                                            (unbindT x y t') p_yg_e'_t' 
                                            (WFEBind g p_g_wf y t_x k_x p_g_tx) th' den_g'_th'
            step_vvx_th'e' = EAppAbs x (csubst th e') v_x  
            ev_vvx_v'      = AddStep (App v v_x) (subBV x v_x (csubst th e')) step_vvx_th'e'
                                     v' (ev_th'e'_v' ? lem_csubst_and_unbind x y v_x s_x' pf_vx_sx' th e') 
-}

{-@ lem_denote_sound_typ_tapp :: g:Env -> e:Term -> t:Type 
                -> { p_e_t:HasType | propOf p_e_t == HasType g e t && isTApp p_e_t } -> ProofOf(WFEnv g) 
                ->  th:CSub  -> ProofOf(DenotesEnv g th)  
                -> ProofOf(ValueDenoted (csubst th e) (ctsubst th t)) / [typSize p_e_t, 0] @-}
lem_denote_sound_typ_tapp :: Env -> Expr -> Type -> HasType -> WFEnv -> CSub 
                            -> DenotesEnv -> ValueDenoted
lem_denote_sound_typ_tapp g e t p_e_t@(TApp _g e' x t_x t' p_e_txt' e_x p_ex_tx) p_g_wf th den_g_th = undefined {- recheck
  = ValDen (csubst th e) (ctsubst th t)  v''  ev_the_v''  den_tht_v'' 
     where
      (ValDen _ _ v'  ev_the'_v' den_thtxt'_v'_) = lem_denote_sound_typ g e' (TFunc x t_x t') 
                                                       p_e_txt' p_g_wf th den_g_th
      (ValDen _ _ v_x ev_thex_vx den_thtx_vx)    = lem_denote_sound_typ g e_x t_x p_ex_tx 
                                                       p_g_wf th den_g_th
      {-@ den_thtxt'_v' :: { pf:Denotes | propOf pf == Denotes (ctsubst th (TFunc x t_x t')) v' } @-}
      den_thtxt'_v'  = den_thtxt'_v'_ ? lem_ctsubst_func th x t_x t'

      (DFunc _ _ _ _v' s_x s eqv_sxs_ert p_v'_sxs reducer) = den_thtxt'_v' 
      (ValDen _ _ v'' ev_v'vx_v'' den_tht'vx_v'') = reducer v_x den_thtx_vx
      ev_the_v'vx    = lemma_app_both_many (csubst th e')  v'  ev_the'_v'
                                           (csubst th e_x) v_x ev_thex_vx
                           `withProof` lem_csubst_app th e' e_x
      {-@ ev_the_v'' :: ProofOf(EvalsTo (csubst th e) v'') @-}
      ev_the_v''     = lemma_evals_trans (csubst th (App e' e_x)) (App v' v_x) v''
                                      ev_the_v'vx ev_v'vx_v''
                           `withProof` lem_csubst_app th e' e_x
      eqvft_v'_ert   = AEWitness FEmpty v' (erase (ctsubst th (TFunc x t_x t'))) (FTFunc s_x s)
                           eqv_sxs_ert p_v'_sxs ? lem_ctsubst_func th x t_x t'
      eqvft_vx_thtx  = get_aewitness_from_den (ctsubst th t_x) v_x den_thtx_vx
                                              ? lem_erase_ctsubst th t_x
      (AEWitness _ _ _ s' eqv_s'_t' p_v'vx_s') = lem_alpha_ftapp FEmpty v' v_x
                           (erase (ctsubst th t_x)) (erase (ctsubst th t')) 
                           eqvft_v'_ert eqvft_vx_thtx
      p_v''_s'       = lemma_soundness (App v' v_x) v'' ev_v'vx_v'' s' p_v'vx_s'   
      {-@ den_tht_v'' :: ProofOf(Denotes (ctsubst th t) v'') @-}
      den_tht_v''    = DExis x (ctsubst th t_x) (ctsubst th t') v'' s' eqv_s'_t' p_v''_s' v_x 
                           den_thtx_vx den_tht'vx_v'' ? lem_ctsubst_exis th x t_x t' 
-}

{-@ lem_denote_sound_typ_tabst :: g:Env -> e:Term -> t:Type 
                -> { p_e_t:HasType | propOf p_e_t == HasType g e t && isTAbsT p_e_t } -> ProofOf(WFEnv g) 
                ->  th:CSub -> ProofOf(DenotesEnv g th)  
                -> ProofOf(ValueDenoted (csubst th e) (ctsubst th t)) / [typSize p_e_t, 0] @-}
lem_denote_sound_typ_tabst :: Env -> Expr -> Type -> HasType -> WFEnv -> CSub 
                            -> DenotesEnv -> ValueDenoted
lem_denote_sound_typ_tabst g e t p_e_t@(TAbsT _g a k e' t' k' a' p_e'_t' p_a'g_t') p_g_wf th den_g_th = undefined {- recheck 
  = ValDen (csubst th e) (ctsubst th t) v ev_the_v den_tht_v
      where 
        {-@ v :: { z:Value | z == csubst th e && e == LambdaT a k e'} @-}  -- need to show (Lambda x e') is a value 
        v = LambdaT a k (csubst th e') ? lem_csubst_lambdaT th a k e' 
        ev_the_v  = Refl (csubst th e) ? lem_csubst_lambdaT th a k e'
        (AEWitness _ _ _ s eqv_s_er_tht p_e_s) = lem_csubst_hasftype g e t p_e_t p_g_wf
                          th den_g_th ? lem_erase_ctsubst th t'
                                      ? lem_ctsubst_poly th a k t'
        (AEPoly _ a0 _ s' _ _ _ _) = eqv_s_er_tht -- s = \all a0:k. s' =a= erase th(\all a:k. t')        
        den_tht_v = DPoly a k (ctsubst th t') v a0 s' eqv_s_er_tht p_e_s
                          pf_den_tht'ta_vta
        {-@ pf_den_tht'ta_vta :: t_a:Type -> ProofOf(WFType Empty t_a k)
                     -> ProofOf(ValueDenoted (AppT v t_a) (tsubBTV a t_a (ctsubst th t'))) @-}
        pf_den_tht'ta_vta :: Type -> WFType -> ValueDenoted
        pf_den_tht'ta_vta t_a p_emp_ta = ValDen (AppT v t_a) (tsubBTV a t_a (ctsubst th t'))
                                 v' ev_vta_v' (den_tht'ta_v' 
                                     ? lem_ctsubst_and_unbind_tvT a a' t_a k p_emp_ta th t')
          where
            th'            = CConsT a' t_a (th ? lem_binds_env_th g th den_g_th)
            den_g'_th'     = DExtT g th den_g_th a' k (t_a ? lem_free_subset_binds Empty t_a k p_emp_ta
                                                           ? lem_tfreeBV_empty Empty t_a k p_emp_ta)
                                   p_emp_ta

            (ValDen _ _ v' ev_th'e'_v' den_tht'ta_v') = lem_denote_sound_typ (ConsT a' k g) 
                                   (unbind_tv a a' e') (unbind_tvT a a' t') p_e'_t' 
                                   (WFEBindT g p_g_wf a' k) th' den_g'_th'
            step_vta_th'e' = EAppTAbs a k (csubst th e') t_a
            ev_vta_v'      = AddStep (AppT v t_a) (subBTV a t_a (csubst th e')) step_vta_th'e'
                                     v' (ev_th'e'_v' ? lem_csubst_and_unbind_tv a a' t_a k p_emp_ta th e')
-}

{-@ lem_denote_sound_typ_tappt :: g:Env -> e:Term -> t:Type 
                -> { p_e_t:HasType | propOf p_e_t == HasType g e t && isTAppT p_e_t } -> ProofOf(WFEnv g) 
                ->  th:CSub  -> ProofOf(DenotesEnv g th)  
                -> ProofOf(ValueDenoted (csubst th e) (ctsubst th t)) / [typSize p_e_t, 0] @-}
lem_denote_sound_typ_tappt :: Env -> Expr -> Type -> HasType -> WFEnv -> CSub 
                            -> DenotesEnv -> ValueDenoted
lem_denote_sound_typ_tappt g e t (TAppT _ e' a k s p_e_as t' p_g_t') p_g_wf th den_g_th  = undefined {- recheck
  = ValDen (csubst th e) (ctsubst th t) v'' ev_the_v'' (den_tht_v''
                        ? lem_ctsubst_tsubBTV g a t' k p_g_t' th den_g_th s
                        ? toProof ( t === tsubBTV a t' s ))
      where
        {-@ den_thas_v' :: { pf:Denotes | propOf pf == Denotes (TPoly a k (ctsubst th s)) v' } @-} 
        (ValDen _ _ v' ev_the'_v' den_thas_v') = lem_denote_sound_typ g e' (TPoly a k s)
                                                     p_e_as p_g_wf th den_g_th
                                                     ? lem_ctsubst_poly th a k s   
        ev_the_v'tht' = lemma_appT_many (csubst th e') v' (ctsubst th t') ev_the'_v'
                                        ? lem_csubst_appT th e' t'
        p_emp_tht'    = lem_ctsubst_wf g t' k p_g_t' p_g_wf th den_g_th
        (DPoly _ _ _ _ _ _ _ _ prover) = den_thas_v'
        {-@ den_tht_v'' :: {pf:Denotes | propOf pf == Denotes (tsubBTV a (ctsubst th t') (ctsubst th s)) v''} @-}
        (ValDen _ _ v'' ev_v'tht'_v'' den_tht_v'') = prover (ctsubst th t') p_emp_tht'
        ev_the_v''    = lemma_evals_trans (csubst th e) (AppT v' (ctsubst th t')) v''
                                          ev_the_v'tht' ev_v'tht'_v''
-}

{-@ lem_denote_sound_typ_tlet :: g:Env -> e:Term -> t:Type 
                -> { p_e_t:HasType | propOf p_e_t == HasType g e t && isTLet p_e_t } -> ProofOf(WFEnv g) 
                ->  th:CSub  -> ProofOf(DenotesEnv g th)  
                -> ProofOf(ValueDenoted (csubst th e) (ctsubst th t)) / [typSize p_e_t, 0] @-}
lem_denote_sound_typ_tlet :: Env -> Expr -> Type -> HasType -> WFEnv -> CSub 
                            -> DenotesEnv -> ValueDenoted
lem_denote_sound_typ_tlet g e t (TLet _g e_x t_x p_ex_tx x e' _t k p_g_t y p_yg_e'_t) p_g_wf th den_g_th = undefined {- recheck
  = case (lem_denote_sound_typ g e_x t_x p_ex_tx p_g_wf th den_g_th) of 
      (ValDen _ _ v_x_ ev_thex_vx den_thtx_vx) 
        -> ValDen (csubst th e) (ctsubst th t) v ev_the_v den_tht_v 
          where
            {-@ v_x :: { v_x:Value | Set_emp (fv v_x) && v_x == v_x_ } @-}
            v_x                = v_x_ ? lem_den_nofv v_x_ (ctsubst th t_x) den_thtx_vx
                                      ? lem_den_nobv v_x_ (ctsubst th t_x) den_thtx_vx
            (s_x, p_vx_sx)     = get_ftyp_from_den (ctsubst th t_x) v_x den_thtx_vx
                                      ? lem_erase_ctsubst th t_x
            th'                = CCons y v_x (th ? lem_binds_env_th g th den_g_th)
            den_g'_th'         = DExt g th den_g_th y t_x v_x den_thtx_vx 
            p_g_tx             = lem_typing_wf g e_x t_x p_ex_tx p_g_wf 
            {-@ v :: Value @-}
            (ValDen _ _ v ev_th'e'_v den_th't_v) = lem_denote_sound_typ (Cons y t_x g) (unbind x y e')
                                      (unbindT x y t) p_yg_e'_t
                                      (WFEBind g p_g_wf y t_x Star p_g_tx) th' den_g'_th'  
                                      ? lem_ctsubst_and_unbindT x y v_x s_x p_vx_sx th t
            ev_the_vxthe'      = lemma_let_many x (csubst th e_x) v_x (csubst th e') ev_thex_vx
            step_vxthe'_th'e'  = ELetV x v_x (csubst th e')
            ev_vxthe'_v        = AddStep (Let x v_x (csubst th e')) (subBV x v_x (csubst th e'))
                                   step_vxthe'_th'e' v 
                                   (ev_th'e'_v ? lem_csubst_and_unbind x y v_x s_x p_vx_sx th e')
            ev_the_v           = lemma_evals_trans (csubst th e) (Let x v_x (csubst th e')) v
                                      (ev_the_vxthe' ? lem_csubst_let th x e_x e') ev_vxthe'_v
            {-@ den_tht_v :: ProofOf(Denotes (ctsubst th t) v) @-}
            den_tht_v          = den_th't_v ? lem_ctsubst_and_unbindT x y v_x s_x p_vx_sx th t
                                      ? lem_tfreeBV_empty g t k p_g_t
                                      ? lem_ctsubst_nofreeBV th t
                                      ? lem_tsubBV_notin x v_x (ctsubst th t) 
-}

{-@ lem_denote_sound_typ_tann :: g:Env -> e:Term -> t:Type 
                -> { p_e_t:HasType | propOf p_e_t == HasType g e t && isTAnn p_e_t } -> ProofOf(WFEnv g) 
                ->  th:CSub  -> ProofOf(DenotesEnv g th)  
                -> ProofOf(ValueDenoted (csubst th e) (ctsubst th t)) / [typSize p_e_t, 0] @-}
lem_denote_sound_typ_tann :: Env -> Expr -> Type -> HasType -> WFEnv -> CSub 
                            -> DenotesEnv -> ValueDenoted
lem_denote_sound_typ_tann g e t (TAnn _g e' _t p_e'_t) p_g_wf th den_g_th  
  = ValDen (csubst th e) (ctsubst th t) v (ev_the_v ? toProof ( e === Annot e' t) ? lem_csubst_annot th e' t)
           den_tht_v
    where
      (ValDen _ _ v ev_the'_v den_tht_v) = lem_denote_sound_typ g e' t p_e'_t p_g_wf th den_g_th
      ev_the't_vt = lemma_annot_many (csubst th e') v (ctsubst th t) ev_the'_v 
      step_vt_v   = EAnnV v (ctsubst th t)
      ev_vt_v     = AddStep (Annot v (ctsubst th t)) v step_vt_v v (Refl v)
      {-@ ev_the_v :: { pf:EvalsTo | propOf pf == EvalsTo (Annot (csubst th e') (ctsubst th t)) v && 
                                             e == Annot e' t } @-}
      ev_the_v    = lemma_evals_trans (Annot (csubst th e') (ctsubst th t)) 
                                      (Annot v (ctsubst th t)) v ev_the't_vt ev_vt_v 

{-@ lem_denote_sound_typ :: g:Env -> e:Term -> t:Type 
                -> { p_e_t:HasType | propOf p_e_t == HasType g e t } -> ProofOf(WFEnv g)
                ->  th:CSub  -> ProofOf(DenotesEnv g th)  
                -> ProofOf(ValueDenoted (csubst th e) (ctsubst th t)) / [typSize p_e_t, 1] @-}
lem_denote_sound_typ :: Env -> Expr -> Type -> HasType -> WFEnv -> CSub 
                            -> DenotesEnv -> ValueDenoted
lem_denote_sound_typ g e t p_e_t@(TBC _g b) p_g_wf th den_g_th  
  = ValDen (csubst th e) (ctsubst th t) value ev_the_v' den_bl_b 
        where
          {-@ value :: { z:Value | Set_emp (freeBV z) && z == Bc b } @-}
          value     = e
          ev_the_v' = Refl e `withProof` lem_csubst_bc th b
          den_bl_b  = lem_den_tybc g th den_g_th b
lem_denote_sound_typ g e t p_e_t@(TIC _g n) p_g_wf th den_g_th  
  = ValDen (csubst th e) (ctsubst th t) value ev_the_v' den_int_n
      where
        {-@ value :: { z:Value | Set_emp (freeBV z) && z = Ic n } @-}
        value     = e
        ev_the_v' = Refl e `withProof` lem_csubst_ic th n
        den_int_n = lem_den_tyic g th den_g_th n 
lem_denote_sound_typ g e t p_e_t@(TVar1 g' x t' _ _) p_g_wf@(WFEBind _ wf_g' _ _ _ p_g'_t') th den_g_th 
  = lem_denote_sound_typ_tvar1 g e t p_e_t p_g_wf th den_g_th
lem_denote_sound_typ g e t p_e_t@(TVar2 g' x _t p_x_t y t_y) 
                     p_g_wf@(WFEBind _ wf_g' _ _ _ p_g'_ty) th den_g_th  
  = lem_denote_sound_typ_tvar2 g e t p_e_t p_g_wf th den_g_th
lem_denote_sound_typ g e t p_e_t@(TVar3 g' x _t p_x_t a k_a) 
                     p_g_wf@(WFEBindT _ wf_g' _ _) th den_g_th
  = lem_denote_sound_typ_tvar3 g e t p_e_t p_g_wf th den_g_th
lem_denote_sound_typ g e t p_e_t@(TPrm _g c) p_g_wf th den_g_th 
  = ValDen (csubst th e) (ctsubst th t) value ev_the_v' den_tyc_c
      where
        {-@ value :: { z:Value | Set_emp (fv z) && z == Prim c} @-}
        value     = e 
        ev_the_v' = Refl e `withProof` lem_csubst_prim th c
        den_tyc_c = lem_den_ty g th den_g_th c
lem_denote_sound_typ g e t p_e_t@(TAbs _g x t_x k_x p_g_tx e' t' y p_yg_e'_t') p_g_wf th den_g_th
  = lem_denote_sound_typ_tabs g e t p_e_t p_g_wf th den_g_th
lem_denote_sound_typ g e t p_e_t@(TApp _g e' x t_x t' p_e_txt' e_x p_ex_tx) p_g_wf th den_g_th
  = lem_denote_sound_typ_tapp g e t p_e_t p_g_wf th den_g_th
lem_denote_sound_typ g e t p_e_t@(TAbsT {}) p_g_wf th den_g_th
  = lem_denote_sound_typ_tabst g e t p_e_t p_g_wf th den_g_th
lem_denote_sound_typ g e t p_e_t@(TAppT {}) p_g_wf th den_g_th 
  = lem_denote_sound_typ_tappt g e t p_e_t p_g_wf th den_g_th
lem_denote_sound_typ g e t p_e_t@(TLet _g e_x t_x p_ex_tx x e' _t k p_g_t y p_yg_e'_t) p_g_wf th den_g_th
  = lem_denote_sound_typ_tlet g e t p_e_t p_g_wf th den_g_th
lem_denote_sound_typ g e t p_e_t@(TAnn _g e' _t p_e'_t) p_g_wf th den_g_th
  = lem_denote_sound_typ_tann g e t p_e_t p_g_wf th den_g_th
lem_denote_sound_typ g e t (TSub _g _e s p_e_s _t k p_g_t p_s_t) p_g_wf th den_g_th 
  = ValDen (csubst th e) (ctsubst th t) v ev_the_v den_tht_v
    where
      p_g_s     = lem_typing_wf g e s p_e_s p_g_wf
      (ValDen _ _ v ev_the_v den_ths_v) = lem_denote_sound_typ g e s p_e_s p_g_wf th den_g_th
      den_tht_v = lem_denote_sound_sub g s Star t k p_s_t p_g_wf p_g_s p_g_t th den_g_th v den_ths_v 
