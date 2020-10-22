{-# LANGUAGE GADTs #-}

{-@ LIQUID "--no-termination" @-} -- TODO assume
{-@ LIQUID "--no-totality" @-} -- TODO assume
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module DenotationsSoundnessTyp where

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
import DenotationsSoundnessSub
import PrimitivesSemantics
import PrimitivesDenotations

{-@ reflect foo51 @-}
foo51 x = Just x
foo51 :: a -> Maybe a

{-@ lem_denote_exact_type :: th:CSub -> { x:Vname | not (in_csubst x th) }
        -> { t:Type | Set_sub (free t) (bindsC th) } -> { w:Value | Set_emp (fv w) }
        -> ProofOf(Denotes (ctubst th t) w)
        -> ProofOf(Denotes (ctsubst (CCons x w th) (self t (FV x))) w) @-}
lem_denote_exact_type :: CSub -> Vname -> Type -> Expr -> Denotes -> Denotes
lem_denote_exact_type th x (TRefn b z p) w den_tht_w = case den_tht_w of
  (DRefn _ _ _ _ pf_w_b ev_thpw_tt_) -> DRefn b z p w pf_w_b ev_thpexw_tt
    where
      thp_exact    = App (App (Prim And) (csubst th p)) (App (App (Prim (equals b)) (BV z)) w)
              ? () {- toProof ( ctsubst (CCons x w th) (self (TRefn b z p) x) -}
                        ? lem_unroll_ctsubst_left th x w (self (TRefn b z p) (FV x))
                   {- === tsubFV x w (ctsubst th (self (TRefn b z p) x)) -}
                        ? lem_ctsubst_self_notin th (TRefn b z p) x
                   {- === tsubFV x w (self (ctsubst th (TRefn b z p)) x)
                      === tsubFV x w (self (TRefn b z (csubst th p)) x) -}
                        ? lem_tsubFV_value_self b z (csubst th p) x w     
                   {- === TRefn b z (App (App (Prim And) (csubst th p))
                                         (App (App (Prim (equals b)) (BV z)) w)) ) -}
      {-@ thp_exact_w :: { p':Pred | p' == subBV z w thp_exact } @-}
      thp_exact_w  = App (App (Prim And) (subBV z w (csubst th p))) (App (App (Prim (equals b)) w) w)
                         ? toProof ( subBV z w w === w )  --------------------------------
      {-@ ev_thpw_tt :: ProofOf(EvalsTo (subBV z w (csubst th p)) (Bc True)) @-}
      ev_thpw_tt   = ev_thpw_tt_                   
      ev_andthpw1  = EApp2 (subBV z w (csubst th p)) (Bc True) ev_thpw_tt (Prim And)
      ev_andthpw_t = lemma_add_step_after (App (Prim And) (subBV z w (csubst th p)))
                                          (App (Prim And) (Bc True)) ev_andthpw1
                                          (Lambda 1 (BV 1)) (EPrim And (Bc True))

      eql_w        = App (App (Prim (equals b)) w) w
      {-@ ev_eqw_tt :: ProofOf(EvalsTo (App (App (Prim (equals b)) w) w) (Bc True)) @-}
      ev_eqw_tt    = case b of
        TBool -> case w of
          (Bc True)  -> lemma_eqv_semantics (Bc True)  True  (Refl (Bc True))  (Bc True)  True  (Refl (Bc True))
          (Bc False) -> lemma_eqv_semantics (Bc False) False (Refl (Bc False)) (Bc False) False (Refl (Bc False))
          _          -> impossible ("by lemma" ? lem_bool_values w pf_w_b)
        TInt  -> case w of
          (Ic n)     -> lemma_eq_semantics (Ic n) n (Refl (Ic n)) (Ic n) n (Refl (Ic n))
          _          -> impossible ("by lemma" ? lem_int_values w pf_w_b)

      ev_thpexw_1  = lemma_app_both_many (App (Prim And) (subBV z w (csubst th p)))
                                         (Lambda 1 (BV 1)) ev_andthpw_t 
                                         (App (App (Prim (equals b)) w) w) (Bc True) ev_eqw_tt
      ev_thpexw_tt = lemma_add_step_after thp_exact_w (App (Lambda 1 (BV 1)) (Bc True))
                                          ev_thpexw_1 (Bc True) (EAppAbs 1 (BV 1) (Bc True))
lem_denote_exact_type th x (TFunc z t_z t') w den_tht_w 
    = den_tht_w ? toProof ( ctsubst (CCons x w th) (self t (FV x))           
                        === ctsubst (CCons x w th) t
                        === ctsubst th (subFV x w t) 
                        === ctsubst th t )
lem_denote_exact_type th x (TExists z t_z t') w den_tht_w = undefined
lem_denote_exact_type th x (TPoly a k_a t') w den_tht_w 
    = den_tht_w ? toProof ( ctsubst (CCons x w th) (self t (FV x))           
                        === ctsubst (CCons x w th) t
                        === ctsubst th (subFV x w t) 
                        === ctsubst th t )

{-@ lem_denote_sound_typ :: g:Env -> e:Expr -> t:Type 
                -> { p_e_t:HasType | propOf p_e_t == HasType g e t } -> ProofOf(WFEnv g)
                -> th:CSub -> ProofOf(DenotesEnv g th)  
                -> ProofOf(ValueDenoted (csubst th e) (ctsubst th t)) / [typSize p_e_t] @-}
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
lem_denote_sound_typ g e t (TVar1 g' x t') (WFEBind _ wf_g' _ _ _ p_g'_t') th den_g_th 
  = undefined {-case den_g_th of              -- t == self t x 
      (DExt _g' th' den_g'_th' _x _t' w den_th't'_w) 
        -> ValDen (csubst th e) (ctsubst th t) w ev_the_v' den_tht_thx
             where
               ev_the_v' = Refl w `withProof` lem_den_nofv w (ctsubst th' t) den_tht_thx
                                  `withProof` lem_csubst_nofv th' w
               den_tht_thx = den_th't'_w ? lem_free_bound_in_env g' t' p_g'_t' x
                                         ? lem_binds_env_th g' th' den_g'_th'
--                                         ? toProof ( ctsubst (CCons x w th') (self t x)
--
                                         ? toProof ( ctsubst (CCons x w th') t'
                                                === ctsubst th' (tsubFV x w t') 
                                                === ctsubst th' t' )-}
lem_denote_sound_typ g e t (TVar2 g' x _t p_x_t y t_y) 
                     wf_g@(WFEBind _ wf_g' _ _ _ p_g'_ty) th den_g_th  
  = undefined {- case den_g_th of 
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
                                        === ctsubst th' t ) -}
lem_denote_sound_typ g e t (TVar3 g' x _t p_x_t a k_a) 
                     wf_g@(WFEBindT _ wf_g' _ _) th den_g_th  = undefined
lem_denote_sound_typ g e t p_e_t@(TPrm _g c) p_g_wf th den_g_th 
  = ValDen (csubst th e) (ctsubst th t) value ev_the_v' den_tyc_c
      where
        {-@ value :: { z:Value | Set_emp (fv z) && z == Prim c} @-}
        value     = e 
        ev_the_v' = Refl e `withProof` lem_csubst_prim th c
        den_tyc_c = lem_den_ty g th den_g_th c
lem_denote_sound_typ g e t p_e_t@(TAbs _g x t_x k_x p_g_tx e' t' y p_yg_e'_t') p_g_wf th den_g_th
  = undefined {- ValDen (csubst th e) (ctsubst th t) v ev_the_v den_tht_v
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
                                                                           pf_vx_er_tx th e') -}
lem_denote_sound_typ g e t p_e_t@(TApp _g e' x t_x t' p_e_txt' e_x p_ex_tx) p_g_wf th den_g_th
  = undefined {- ValDen (csubst th e) (ctsubst th t)  v''  ev_the_v''  den_tht_v'' 
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
                           `withProof` lem_ctsubst_exis th x t_x t' -}
lem_denote_sound_typ g e t (TAbsT {}) p_g_wf th den_g_th = undefined
lem_denote_sound_typ g e t (TAppT {}) p_g_wf th den_g_th = undefined
lem_denote_sound_typ g e t (TLet _g e_x t_x p_ex_tx x e' _t k p_g_t y p_yg_e'_t) p_g_wf th den_g_th
  = undefined {- case (lem_denote_sound_typ g e_x t_x p_ex_tx p_g_wf th den_g_th) of 
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
                                      ? lem_tsubBV_inval x v_x (ctsubst th t) -}
lem_denote_sound_typ g e t (TAnn _g e' _t p_e'_t) p_g_wf th den_g_th
  = undefined {-0 ValDen (csubst th e) (ctsubst th t) v (ev_the_v ? toProof ( e === Annot e' t) ? lem_csubst_annot th e' t)
           den_tht_v
    where
      (ValDen _ _ v ev_the'_v den_tht_v) = lem_denote_sound_typ g e' t p_e'_t p_g_wf th den_g_th
      ev_the't_vt = lemma_annot_many (csubst th e') v (ctsubst th t) ev_the'_v 
      step_vt_v   = EAnnV v (ctsubst th t)
      ev_vt_v     = AddStep (Annot v (ctsubst th t)) v step_vt_v v (Refl v)
      {-@ ev_the_v :: { pf:EvalsTo | propOf pf == EvalsTo (Annot (csubst th e') (ctsubst th t)) v && e == Annot e' t } @-}
      ev_the_v    = lemma_evals_trans (Annot (csubst th e') (ctsubst th t)) 
                                      (Annot v (ctsubst th t)) v ev_the't_vt ev_vt_v -}
lem_denote_sound_typ g e t (TSub _g _e s p_e_s _t k p_g_t p_s_t) p_g_wf th den_g_th
  = ValDen (csubst th e) (ctsubst th t) v ev_the_v den_tht_v
    where
      p_g_s     = lem_typing_wf g e s p_e_s p_g_wf
      (ValDen _ _ v ev_the_v den_ths_v) = lem_denote_sound_typ g e s p_e_s p_g_wf th den_g_th
      den_tht_v = lem_denote_sound_sub g s Star t k p_s_t p_g_wf p_g_s p_g_t th den_g_th v den_ths_v 
