{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-} 
{- @ LIQUID "--no-totality" @-} 
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module DenotationalSoundness where

--import Control.Exception (assert)
import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import BasicProps
import Typing
import Primitives
import Primitives3
import STLCLemmas
import STLCSoundness
import TechLemmas
import TechLemmas2

-- force these into scope
semantics = (Step, EvalsTo)
typing = (HasBType, HasType, WFType, WFEnv, Subtype)
denotations = (Entails, ValueDenoted, Denotes, DenotesEnv)

{-@ reflect foo15 @-}
foo15 x = Just x
foo15 :: a -> Maybe a

{-@ lem_denote_sound_sub :: g:Env -> t1:Type -> t2:Type -> { p_t1_t2:_ | propOf p_t1_t2 == Subtype g t1 t2 }
                -> ProofOf(WFEnv g) -> ProofOf(WFType g t1) -> ProofOf(WFType g t2) 
                -> th:CSubst -> ProofOf(DenotesEnv g th) -> v:Value 
                -> ProofOf(Denotes (ctsubst th t1) v) 
                -> ProofOf(Denotes (ctsubst th t2) v) / [subtypSize p_t1_t2] @-}
lem_denote_sound_sub :: Env -> Type -> Type -> Subtype -> WFEnv -> WFType -> WFType
                            -> CSubst -> DenotesEnv -> Expr -> Denotes -> Denotes 
lem_denote_sound_sub g t1 t2 (SBase _g x1 b p1 x2 p2 y pf_ent_p2) p_g_wf p_g_t1 p_g_t2
                    -- t1 = b{x1:p1}, t2 = b{x2:p2}  -- Pf(Entails g' p2[y/x2])
                       th den_g_th val den_t1_v
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
                                    `withProof` lem_csubst_and_unbind x2 y val (BTBase b) pf_v_b' th p2
      (_) -> impossible ("by lemma" ? lem_ctsubst_refn th b x1 p1)
lem_denote_sound_sub g t1 t2  -----------------------------------
--lem_denote_sound_sub g t1@(TFunc _ _ _) t2@(TFunc _ _ _)  -----------------------------------
             p_t1_t2@(SFunc _g x1 s1 x2 s2 p_g_s2_s1 t1' t2' y p_g'_t1_t2) p_g_wf p_g_t1 p_g_t2
                                                -- Subtype (Cons y s2 g) t1'[y/x1] t2'[y/x2]
             th den_g_th _v den_tht1_v 
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
      (_) -> impossible ("by lemma" ? lem_ctsubst_func th x1 s1 t1')
lem_denote_sound_sub g t1 t2 -- @(TExists x t_x t')  -----------------------------------
             p_t1_t2@(SWitn _g v_x t_x p_vx_tx _t1 x t2' p_t1_t2'vx) 
             p_g_wf p_g_t1 p_g_t2 th den_g_th v den_tht1_v
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
                              `withProof` lem_erase_ctsubst th (tsubBV x v_x t2')
lem_denote_sound_sub g t1 t2 -- @(TExists x t_x t') t2 --------------------------------------
             p_t1_t2@(SBind _g x t_x t' _t2 y p_t'yx_t2) p_g_wf p_g_t1 p_g_t2 th den_g_th v 
             den_tht1_v -- @(DExis _ thtx tht' _v pf_v_er_t' v_x den_thtx_vx den_tht'vx_v)
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
        (_, _) -> impossible ("by lemma" ? lem_ctsubst_exis th x t_x t')

{-@ lem_denote_sound_typ :: g:Env -> e:Expr -> t:Type 
                -> { p_e_t:HasType | propOf p_e_t == HasType g e t } -> ProofOf(WFEnv g)
                -> th:CSubst -> ProofOf(DenotesEnv g th)  
                -> ProofOf(ValueDenoted (csubst th e) (ctsubst th t)) / [typSize p_e_t] @-}
lem_denote_sound_typ :: Env -> Expr -> Type -> HasType -> WFEnv -> CSubst 
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
lem_denote_sound_typ g e t (TVar1 g' x _t) (WFEBind _ wf_g' _ _ p_g'_t) th den_g_th 
  = case den_g_th of 
      (DExt _g' th' den_g'_th' _x _ w den_th't_th'x) 
        -> ValDen (csubst th e) (ctsubst th t) w ev_the_v' den_tht_thx
             where
               ev_the_v' = Refl w `withProof` lem_den_nofv w (ctsubst th' t) den_tht_thx
                                  `withProof` lem_csubst_nofv th' w
               den_tht_thx = den_th't_th'x ? lem_free_bound_in_env g' t p_g'_t x
                                           ? lem_binds_env_th g' th' den_g'_th'
                                           ? toProof ( ctsubst (CCons x w th') t
                                                             === ctsubst th' (tsubFV x w t) 
                                                             === ctsubst th' t )
lem_denote_sound_typ g e t (TVar2 g' x _t p_x_t y t_y) 
                     wf_g@(WFEBind _ wf_g' _ _ p_g'_ty) th den_g_th  
  = case den_g_th of 
      (DExt _g' th' den_g'_th' _y _ v_y den_tht_thy) 
        -> ValDen (csubst th e) (ctsubst th t) thx ev_the_v' den_tht_thx
            where
              {-@  thx :: { z:Value | Set_emp (freeBV z) } @-}
              (ValDen _ _ thx pf1 pf2) = lem_denote_sound_typ g' e t p_x_t wf_g' th' den_g'_th' 
              p_g'_t      = lem_typing_wf g' (FV x) t p_x_t wf_g' 
              ev_the_v'   = pf1 `withProof` lem_den_nofv thx (ctsubst th' t) pf2
                                `withProof` lem_csubst_nofv th' thx
              den_tht_thx = pf2 ? lem_free_bound_in_env g' t p_g'_t y
                                ? lem_binds_env_th g' th' den_g'_th'
                                ? toProof ( ctsubst (CCons y v_y th') t
                                        === ctsubst th' (tsubFV y v_y t) 
                                        === ctsubst th' t ) 
lem_denote_sound_typ g e t p_e_t@(TPrm _g c) p_g_wf th den_g_th 
  = ValDen (csubst th e) (ctsubst th t) value ev_the_v' den_tyc_c
      where
        {-@ value :: { z:Value | Set_emp (fv z) && z == Prim c} @-}
        value     = e 
        ev_the_v' = Refl e `withProof` lem_csubst_prim th c
        den_tyc_c = lem_den_ty g th den_g_th c
lem_denote_sound_typ g e t p_e_t@(TAbs _g x t_x p_g_tx e' t' y p_yg_e'_t') p_g_wf th den_g_th
  = ValDen (csubst th e) (ctsubst th t) v ev_the_v den_tht_v
    where 
      {-@ v :: { z:Value | z == csubst th e && e == Lambda x e'} @-}  -- need to show (Lambda x e') is a value first 
      v = Lambda x (csubst th e') ? lem_csubst_lambda th x e' 
                                  ? lem_freeBV_empty g (Lambda x e') t p_e_t p_g_wf
                                  ? lem_csubst_freeBV th (Lambda x e')
      ev_the_v = Refl (csubst th e) ? lem_csubst_lambda th x e'
      p_v_er_txt' = lem_csubst_hasbtype g e t p_e_t p_g_wf th den_g_th
                      `withProof` lem_erase_ctsubst th t_x
                      `withProof` lem_erase_ctsubst th t'
      den_tht_v = DFunc x (ctsubst th t_x) (ctsubst th t') v p_v_er_txt' pf_den_tht'vx_vvx
                      `withProof` lem_ctsubst_func th x t_x t'
      {-@ pf_den_tht'vx_vvx :: v_x:Value -> ProofOf(Denotes (ctsubst th t_x) v_x)
                   -> ProofOf(ValueDenoted (App v v_x) (tsubBV x v_x (ctsubst th t'))) @-}
      pf_den_tht'vx_vvx :: Expr -> Denotes -> ValueDenoted
      pf_den_tht'vx_vvx v_x den_thtx_vx = ValDen (App v v_x) (tsubBV x v_x (ctsubst th t'))
                                            v' ev_vvx_v' 
                                            (den_tht'vx_v' ? lem_ctsubst_and_unbindT x y v_x (erase t_x)
                                                                                     pf_vx_er_tx th t')
        where
          th'            = CCons y v_x (th ? lem_binds_env_th g th den_g_th)
          den_g'_th'     = DExt g th den_g_th y t_x (v_x ? lem_den_nofv v_x (ctsubst th t_x) den_thtx_vx)
                                den_thtx_vx
          pf_vx_er_tx    = get_btyp_from_den (ctsubst th t_x) v_x den_thtx_vx 
                              `withProof` lem_erase_ctsubst th t_x
          pf_v'_er_t'    = BTApp (erase_env g) v (erase t_x) (erase t') p_v_er_txt'
                                              v_x pf_vx_er_tx
          (ValDen _ _ v' ev_th'e'_v' den_tht'vx_v') = lem_denote_sound_typ (Cons y t_x g) (unbind x y e') 
                                          (unbindT x y t') p_yg_e'_t' 
                                          (WFEBind g p_g_wf y t_x p_g_tx) th' den_g'_th'
          step_vvx_th'e' = EAppAbs x (csubst th e') v_x  
          ev_vvx_v'      = AddStep (App v v_x) (subBV x v_x (csubst th e')) step_vvx_th'e'
                                   v' (ev_th'e'_v' ? lem_csubst_and_unbind x y v_x (erase t_x) 
                                                                           pf_vx_er_tx th e')
lem_denote_sound_typ g e t p_e_t@(TApp _g e' x t_x t' p_e_txt' e_x p_ex_tx) p_g_wf th den_g_th
  = ValDen (csubst th e) (ctsubst th t)  v''  ev_the_v''  den_tht_v'' 
    where
      (ValDen _ _ v' ev_the'_v' den_thtxt'_v') = lem_denote_sound_typ g e' (TFunc x t_x t') 
                                                        p_e_txt' p_g_wf th den_g_th
      (ValDen _ _ v_x ev_thex_vx den_thtx_vx)  = lem_denote_sound_typ g e_x t_x p_ex_tx 
                                                        p_g_wf th den_g_th
      {-@ my_den_thtxt'_v' :: { pf:Denotes | propOf pf == Denotes (ctsubst th (TFunc x t_x t')) v' } @-}
      my_den_thtxt'_v' = den_thtxt'_v' `withProof` lem_ctsubst_func th x t_x t'
      (DFunc _ _ _ _v' p_v'_ertxt reducer) = my_den_thtxt'_v' --`withProof` lem_ctsubst_func th x t_x t'
      (ValDen _ _ v'' ev_v'vx_v'' den_tht'vx_v'') = reducer v_x den_thtx_vx
      ev_the_v'vx    = lemma_app_both_many (csubst th e')  v'  ev_the'_v'
                                           (csubst th e_x) v_x ev_thex_vx
                           `withProof` lem_csubst_app th e' e_x
      {-@ ev_the_v'' :: ProofOf(EvalsTo (csubst th e) v'') @-}
      ev_the_v''     = lemma_evals_trans (csubst th (App e' e_x)) (App v' v_x) v''
                                      ev_the_v'vx ev_v'vx_v''
                           `withProof` lem_csubst_app th e' e_x
      p_v'vx_ert     = BTApp BEmpty v' (erase t_x) (erase t') 
                           (p_v'_ertxt `withProof` lem_ctsubst_func th x t_x t'
                                       `withProof` lem_erase_ctsubst th t_x
                                       `withProof` lem_erase_ctsubst th t') v_x    
                           (get_btyp_from_den (ctsubst th t_x) v_x den_thtx_vx
                           `withProof` lem_erase_ctsubst th t_x)
                           `withProof` lem_erase_ctsubst th t'
      p_v''_ert      = lemma_soundness (App v' v_x) v'' ev_v'vx_v'' (erase t') p_v'vx_ert
      {-@ den_tht_v'' :: ProofOf(Denotes (ctsubst th t) v'') @-}
      den_tht_v''    = DExis x (ctsubst th t_x) (ctsubst th t') v'' p_v''_ert v_x 
                           den_thtx_vx den_tht'vx_v''
                           `withProof` lem_ctsubst_exis th x t_x t'
lem_denote_sound_typ g e t (TLet _g e_x t_x p_ex_tx x e' _t p_g_t y p_yg_e'_t) p_g_wf th den_g_th
  = case (lem_denote_sound_typ g e_x t_x p_ex_tx p_g_wf th den_g_th) of 
      (ValDen _ _ v_x_ ev_thex_vx den_thtx_vx) 
        -> ValDen (csubst th e) (ctsubst th t) v ev_the_v den_tht_v 
          where
            {-@ v_x :: { v_x:Value | Set_emp (fv v_x) && v_x == v_x_ } @-}
            v_x                = v_x_ ? lem_den_nofv v_x_ (ctsubst th t_x) den_thtx_vx
            p_vx_er_tx         = get_btyp_from_den (ctsubst th t_x) v_x den_thtx_vx
                                      ? lem_erase_ctsubst th t_x
            th'                = CCons y v_x (th ? lem_binds_env_th g th den_g_th)
            den_g'_th'         = DExt g th den_g_th y t_x v_x den_thtx_vx 
            p_g_tx             = lem_typing_wf g e_x t_x p_ex_tx p_g_wf 
            {-@ v :: Value @-}
            (ValDen _ _ v ev_th'e'_v den_th't_v) = lem_denote_sound_typ (Cons y t_x g) (unbind x y e')
                                      (unbindT x y t) p_yg_e'_t
                                      (WFEBind g p_g_wf y t_x p_g_tx) th' den_g'_th'  
                                      ? lem_ctsubst_and_unbindT x y v_x (erase t_x)
                                            p_vx_er_tx th t
            ev_the_vxthe'      = lemma_let_many x (csubst th e_x) v_x (csubst th e') ev_thex_vx
            step_vxthe'_th'e'  = ELetV x v_x (csubst th e')
            ev_vxthe'_v        = AddStep (Let x v_x (csubst th e')) (subBV x v_x (csubst th e'))
                                   step_vxthe'_th'e' v 
                                   (ev_th'e'_v ? lem_csubst_and_unbind x y v_x (erase t_x) 
                                                     p_vx_er_tx th e')
            ev_the_v           = lemma_evals_trans (csubst th e) (Let x v_x (csubst th e')) v
                                      (ev_the_vxthe' ? lem_csubst_let th x e_x e') ev_vxthe'_v
            {-@ den_tht_v :: ProofOf(Denotes (ctsubst th t) v) @-}
            den_tht_v          = den_th't_v ? lem_ctsubst_and_unbindT x y v_x (erase t_x) p_vx_er_tx th t
                                      ? lem_ctsubst_tfreeBV th t
                                      ? lem_tfreeBV_empty g t p_g_t p_g_wf
                                      ? lem_tsubBV_inval x v_x (ctsubst th t)
lem_denote_sound_typ g e t (TAnn _g e' _t p_e'_t) p_g_wf th den_g_th
  = ValDen (csubst th e) (ctsubst th t) v (ev_the_v ? toProof ( e === Annot e' t) ? lem_csubst_annot th e' t)
           den_tht_v
    where
      (ValDen _ _ v ev_the'_v den_tht_v) = lem_denote_sound_typ g e' t p_e'_t p_g_wf th den_g_th
      ev_the't_vt = lemma_annot_many (csubst th e') v (ctsubst th t) ev_the'_v 
      step_vt_v   = EAnnV v (ctsubst th t)
      ev_vt_v     = AddStep (Annot v (ctsubst th t)) v step_vt_v v (Refl v)
      {-@ ev_the_v :: { pf:EvalsTo | propOf pf == EvalsTo (Annot (csubst th e') (ctsubst th t)) v && e == Annot e' t } @-}
      ev_the_v    = lemma_evals_trans (Annot (csubst th e') (ctsubst th t)) 
                                      (Annot v (ctsubst th t)) v ev_the't_vt ev_vt_v 
lem_denote_sound_typ g e t (TSub _g _e s p_e_s _t p_g_t p_s_t) p_g_wf th den_g_th
  = ValDen (csubst th e) (ctsubst th t) v ev_the_v den_tht_v
    where
      p_g_s     = lem_typing_wf g e s p_e_s p_g_wf
      (ValDen _ _ v ev_the_v den_ths_v) = lem_denote_sound_typ g e s p_e_s p_g_wf th den_g_th
      den_tht_v = lem_denote_sound_sub g s t p_s_t p_g_wf p_g_s p_g_t th den_g_th v den_ths_v      

