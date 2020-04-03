{-# LANGUAGE GADTs #-}

--{-@ LIQUID "--higherorder" @-}
{- @ LIQUID "--diff"        @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module DenotationalSoundness where

--import Control.Exception (assert)
import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Syntax
import Semantics
import Typing
import Primitives
import BasicLemmas

-- force these into scope
semantics = (Step, EvalsTo)
typing = (HasBType, HasType, WFType, WFEnv, Subtype)
denotations = (Entails, ValueDenoted, Denotes, DenotesEnv)


{-@ lem_denote_sound_sub :: g:Env -> t1:Type -> t2:Type -> ProofOf(Subtype g t1 t2)
                -> th:CSubst -> ProofOf(DenotesEnv g th) -> v:Value 
                -> ProofOf(Denotes (ctsubst th t1) v) 
                -> ProofOf(Denotes (ctsubst th t2) v) @-}
lem_denote_sound_sub :: Env -> Type -> Type -> Subtype -> CSubst -> DenotesEnv
                            -> Expr -> Denotes -> Denotes 
lem_denote_sound_sub g t1 t2 (SBase _g x1 b p1 x2 p2 y pf_ent_p2)
--lem_denote_sound_sub g t1@(TRefn _ _ _) t2@(TRefn _ _ _) (SBase _g x1 b p1 x2 p2 y pf_ent_p2)
                    -- t1 = b{x1:p1}, t2 = b{x2:p2}  -- Pf(Entails g' p2[y/x2])
                       th den_g_th val den_t1_v@(DRefn _b _ _ _val pf_v_b pf_th_p1v_tt)
    = case (pf_ent_p2) of                                        -- EvalsTo th(p1[v/x1]) tt
        (EntPred y_g _p2 ev_thp2_tt) 
                       -- forall th' in [[x1,g]]. EvalsTo th'(p2[x1/x2]) tt 
            -> DRefn b x2 (csubst th p2) _val pf_v_b' pf_th'_p2v_tt
                     `withProof` lem_ctsubst_refn th b x2 p2
                where
                  pf_v_b'       = pf_v_b `withProof`  lem_ctsubst_refn th b x1 p1 
                  th'           = CCons y val th -- y is fresh repl. x1
                                 -- th' = (y |-> v, th) \in [[ Cons y t1 g ]]
                  den_g'_th'    = DExt g th den_g_th y t1 val den_t1_v
                  pf_th'_p2v_tt = ev_thp2_tt th' den_g'_th' 
                                    `withProof` lem_csubst_and_unbind x2 y val b pf_v_b' th p2
{-lem_denote_sound_sub g t1 t2  -----------------------------------
--lem_denote_sound_sub g t1@(TFunc _ _ _) t2@(TFunc _ _ _)  -----------------------------------
             p_t1_t2@(SFunc _g x1 s1 x2 s2 p_g_s2_s1 t1' t2' y p_g'_t1_t2)
                                                -- Subtype (Cons y s2 g) t1'[y/x1] t2'[y/x2]
             th den_g_th _v den_tht1_v@(DFunc _x1 ths1 tht1' val pf_v_er_t1 _pf_den_tht1'_vv')
   =   DFunc x2 (ctsubst th s2) (ctsubst th t2') val pf_v_er_t2 (pf_den_tht2'_vv')
            `withProof` lem_ctsubst_func th x1 s1 t1'
            `withProof` lem_ctsubst_func th x2 s2 t2'
        where
          pf_v_er_t2   = pf_v_er_t1 `withProof` lem_erase_th_sub g t1 t2 p_t1_t2 th
                                    `withProof` lem_ctsubst_func th x1 s1 t1'
                                    `withProof` lem_ctsubst_func th x2 s2 t2'
          g'           = Cons y s2 g
          ths2_ths1    = lem_denote_sound_sub g s2 s1 p_g_s2_s1 th den_g_th 
          tht1'_tht2'  = lem_denote_sound_sub g' (unbindT x1 y t1') (unbindT x2 y t2')
                                              p_g'_t1_t2 
          {-@ pf_den_tht2'_vv' :: ( v':Value 
               -> ProofOf(Denotes (ctsubst th s2) v') -> (Value, (EvalsTo, Denotes))
                 <{\v'' pfs -> (propOf (fst pfs) == EvalsTo (App val v') v'')
                    && (propOf (snd pfs) == Denotes (tsubBV x2 v' (ctsubst th t2')) v'')}>) @-}
          pf_den_tht2'_vv' v' den_ths2_v' = (v'', (fst pfs, den_t2'v'_v'')) 
              where
                pf_v'_er_s2    = get_btyp_from_den (ctsubst th s2)  v' den_ths2_v' 
                                         `withProof` lem_erase_th_sub g s2 s1 p_g_s2_s1 th 
                th'            = CCons y v' th -- (y |-> v', th) in [[y:s2,g]]
                den_g'_th'     = DExt g th den_g_th y s2 v' den_ths2_v' 
                (v'', pfs)     = get_obj_from_dfunc x1 (ctsubst th s1) (ctsubst th t1') 
                         val den_tht1_v v' 
                         (ths2_ths1 v' (den_ths2_v' `withProof` lem_ctsubst_func th x2 s2 t2')
                         `withProof` lem_ctsubst_func th x1 s1 t1')
                pf_vv'_er_t1'  = BTApp BEmpty val (erase (ctsubst th s1)) 
                                       (erase (ctsubst th t1')) pf_v_er_t1
                                       v' (get_btyp_from_den (ctsubst th s2) v' den_ths2_v')
                pf_v''_er_t1'  = lemma_soundness (App val v') v'' (fst pfs)
                                                 (erase t1') pf_vv'_er_t1'
                {-@ den_t2'v'_v'' :: ProofOf(Denotes (tsubBV x2 v' (ctsubst th t2')) v'') @-}
                den_t2'v'_v''  = tht1'_tht2' th' den_g'_th' v'' 
                                      (snd pfs `withProof` lem_ctsubst_and_unbindT 
                                                            x1 y v' (erase (ctsubst th s1)) 
                                                            pf_v'_er_s2 th t1')
                                      `withProof` lem_ctsubst_func th x2 s2 t2'
                                      `withProof` lem_ctsubst_func th x1 s1 t1'
                                      `withProof` lem_ctsubst_and_unbindT x2 y v' 
                                          (erase (ctsubst th s2)) 
                                          (get_btyp_from_den (ctsubst th s2) v' den_ths2_v') 
                                          th t2'
-}{-
lem_denote_sound_sub g t1 t2 -- @(TExists x t_x t')  -----------------------------------
             p_t1_t2@(SWitn _g v_x t_x p_vx_tx _t1 x t2' p_t1_t2'vx) 
             th den_g_th v den_tht1_v
    = DExis x (ctsubst th t_x) (ctsubst th t2') v p_v_er_t2' thvx -- v'  
            den_thtx_thvx den_tht2'vx_v --`withProof` lem_value_refl v' thvx (fst pfs)
        where -- By the inductive hypothesis and mutual induction:
          den_tht2'vx_v = lem_denote_sound_sub g t1 (tsubBV x v_x t2') p_t1_t2'vx 
                              th den_g_th v den_tht1_v -- v \in [[ t2'[v_x/x] ]]
                              `withProof` lem_ctsubst_exis th x t_x t2'    
                              `withProof` lem_commute_ctsubst_tsubBV th x v_x t2'
          _thvx            = csubst th v_x `withProof` lem_csubst_value th v_x  -- new
          {- @ (thvx, pfs)_ :: (v'::{ v:Expr | isValue v && Set_emp (freeBV v) }, 
                     ({ pf1:EvalsTo | propOf pf1 == EvalsTo (csubst th v_x) v'}, 
                      { pf2:Denotes | propOf pf2 == Denotes (ctsubst th t_x) v'})) @-}
          {-@ thvx :: { v:Expr | isValue v && Set_emp (freeBV v) } @-} 
          {- @ pfs :: ({ pf1:EvalsTo | propOf pf1 == EvalsTo (csubst th v_x) thvx}, 
                      { pf2:Denotes | propOf pf2 == Denotes (ctsubst th t_x) thvx}) @-}
          (Quint _ _ thvx pf1 pf2)      = lem_denote_sound_typ g v_x t_x p_vx_tx th den_g_th
          {-@ den_thtx_thvx :: ProofOf(Denotes (ctsubst th t_x) thvx) @-}
          den_thtx_thvx = pf2 --snd pfs  -- th(v_x) in [[th(t_x)]]. Let v' = th(v_x)...
          -- these are ingredients to show that v \in [[th(TExists x t_x t2')]]
          p_v_er_t2'    = get_btyp_from_den (ctsubst th (tsubBV x v_x t2')) v den_tht2'vx_v
                              `withProof` lem_erase_ctsubst th t2'
                              `withProof` lem_erase_tsubBV x v_x t2'
                              `withProof` lem_erase_ctsubst th (tsubBV x v_x t2')
--          v'            = csubst th v_x `withProof` lem_csubst_value th v_x
--                              `withProof` lem_value_refl (csubst th v_x) thvx (fst pfs)
-}
lem_denote_sound_sub g t1 t2 -- @(TExists x t_x t') t2 --------------------------------------
             p_t1_t2@(SBind _g x t_x t' _t2 y p_t'yx_t2) th den_g_th v 
             den_tht1_v -- @(DExis _ thtx tht' _v pf_v_er_t' v_x den_thtx_vx den_tht'vx_v)
    = case (t1, den_tht1_v) of 
        (TExists _ _ _, DExis _ thtx tht' _v pf_v_er_t' v_x den_thtx_vx den_tht'vx_v) 
          -> den_tht2_v
            where -- by the inductive hypothesis we have
              g'         = Cons y t_x g
              th'        = CCons y v_x th
              den_g'_th' = DExt g th den_g_th y t_x v_x den_thtx_vx
              pf_vx_ertx = get_btyp_from_den thtx v_x den_thtx_vx
              den_tht'_v = den_tht'vx_v `withProof` lem_ctsubst_exis th x t_x t'
                               `withProof` lem_ctsubst_and_unbindT x y v_x (erase thtx) 
                                                                   pf_vx_ertx th t'
              den_tht2_v = lem_denote_sound_sub g' (unbindT x y t') t2 p_t'yx_t2 
                               th' den_g'_th' v den_tht'_v
                               `withProof` lem_ctsubst_head_not_free y v_x th t2
        --(TExists _ _ _, _) -> impossible "certainly"
        (_, _) -> impossible ("clearly" ? lem_ctsubst_exis th x t_x t')


-- this is the old type I am replacing
{- @ lem_denote_sound_typ :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
                -> th:CSubst -> ProofOf(DenotesEnv g th)  
                -> (Value, (EvalsTo, Denotes))<{\v' pfs -> 
                     (propOf (fst pfs) == EvalsTo (csubst th e) v') &&
                     (propOf (snd pfs) == Denotes (ctsubst th t) v')}> @-}
{- @ lem_denote_sound_typ :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t) -> ProofOf(WFEnv g)
                -> th:CSubst -> ProofOf(DenotesEnv g th)  
                -> { pfs:ValueDenoted | in_cs pfs == th && in_exp pfs == e && in_typ pfs == t } @-}



{-@ data Hex2 a b c d e f <p :: a -> b -> c -> d -> e -> f -> Bool>
       = Hex2 { in_cs2 :: a, in_exp2 :: b, in_typ2 :: c, 
                 val2 :: d, evals2 :: e, den2 :: f<p in_cs2 in_exp2 in_typ2 val2 evals2> } @-}
data Hex2 a b c d e f = Hex2 { in_cs2 :: a,  in_exp2 :: b, in_typ2 :: c, 
                               val2 :: d, evals2 :: e, den2 :: f }

{-@ type ValueDenoted2 = Hex2 <{\th e t v pf_evl pf_den -> isValue v && Set_emp (freeBV v) 
                                     && (propOf pf_evl == EvalsTo (csubst th e) v)
                                     && (propOf pf_den == Denotes (ctsubst th t) v) }> 
                            CSubst Expr Type Expr EvalsTo Denotes @-}
type ValueDenoted2     = Hex2 CSubst Expr Type Expr EvalsTo Denotes

{-@ lem_denote_sound_typ :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t) -> ProofOf(WFEnv g)
                -> th:CSubst -> ProofOf(DenotesEnv g th)  
                -> ProofOf(ValueDenoted (csubst th e) (ctsubst th t)) @-}
lem_denote_sound_typ :: Env -> Expr -> Type -> HasType -> WFEnv -> CSubst 
                            -> DenotesEnv -> ValueDenoted
lem_denote_sound_typ g e t p_e_t@(TBC _g b) p_g_wf th den_g_th  
  = ValDen (csubst th e) (ctsubst th t) value ev_the_v' den_bl_b 
        where
          {-@ value :: { z:Value | Set_emp (freeBV z) && z == Bc b } @-}
          value     = e
          {- @ ev_the_v' :: ProofOf(EvalsTo (csubst th e) e) @-}
          ev_the_v' = Refl e `withProof` lem_csubst_bc th b
          {- @ den_bl_b :: { pf:Denotes | propOf pf == Denotes (ctsubst th t) (Bc b) } @-}
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
      (DEmp)                                       -> impossible ""
      (DExt _g' th' den_g'_th' _x _ w den_th't_th'x) 
        -> ValDen (csubst th e) (ctsubst th t) w ev_the_v' den_tht_thx
        {-> Hex { in_cs = th, in_exp = e, in_typ = t,
                 val = w, evals = ev_the_v', den = den_tht_thx }-}
             where
               ev_the_v' = Refl w `withProof` lem_den_nofv w (ctsubst th' t) den_tht_thx
                                  `withProof` lem_csubst_nofv th' w
                                  `withProof` toProof ( csubst (CCons x w th') (FV x)
                                                    === csubst th' (subFV x w (FV x))
                                                    === csubst th' w === w)
               den_tht_thx = den_th't_th'x `withProof` lem_free_bound_in_env g' t p_g'_t x
                                           `withProof` toProof ( ctsubst (CCons x w th') t
                                                             === ctsubst th' (tsubFV x w t) 
                                                             === ctsubst th' t )
lem_denote_sound_typ g e t (TVar2 g' x _t p_x_t y t_y) 
                     wf_g@(WFEBind _ wf_g' _ _ p_g'_ty) th den_g_th  
  = case den_g_th of
      (DEmp)           -> impossible ""
      (DExt _g' th' den_g'_th' _y _ v_y den_tht_thy) 
        -> ValDen (csubst th e) (ctsubst th t) thx ev_the_v' den_tht_thx
        {-> Hex { in_cs = th, in_exp = e, in_typ = t,
                 val = thx, evals = ev_the_v', den = den_tht_thx }-}
            where
              {-@  thx :: { z:Value | Set_emp (freeBV z) } @-}
              (ValDen _ _ thx pf1 pf2) = lem_denote_sound_typ g' e t p_x_t wf_g' th' den_g'_th' 
              p_g'_t      = lem_typing_wf g' (FV x) t p_x_t wf_g' 
              {- @ ev_the_v' :: ProofOf(EvalsTo (csubst th' e) thx) @-}
              ev_the_v'   = pf1 `withProof` lem_den_nofv thx (ctsubst th' t) pf2
                                `withProof` lem_csubst_nofv th' thx
                                `withProof` toProof ( csubst (CCons y v_y th') (FV x)
                                                  === csubst th' (subFV y v_y (FV x))
                                                  === csubst th' (FV x) ) -- === thx
              {- @ den_tht_thx :: ProofOf(Denotes (ctsubst th' t) thx) @-}
              den_tht_thx = pf2 `withProof` lem_free_bound_in_env g' t p_g'_t y
                                `withProof` toProof ( ctsubst (CCons y v_y th') t
                                                  === ctsubst th' (tsubFV y v_y t) 
                                                  === ctsubst th' t )
lem_denote_sound_typ g e t p_e_t@(TPrm _g c) p_g_wf th den_g_th 
  = ValDen (csubst th e) (ctsubst th t) value ev_the_v' den_tyc_c
      where
        {-@ value :: { z:Value | Set_emp (fv z) && z == Prim c} @-}
        value     = e 
        ev_the_v' = Refl e `withProof` lem_csubst_prim th c
        den_tyc_c = lem_den_ty g th den_g_th c
lem_denote_sound_typ g e t (TAbs _g x t_x p_g_tx e' t' y p_yg_e'_t') p_g_wf th den_g_th
  = ValDen (csubst th e) (ctsubst th t) ??? ev_????? den_?????
    where
      v = Lambda x (csubst th e') -- proof = th(e) -- proof freeBV this = emp 
      
      ???? = lem_denote_sound_typ (Cons y t_x g) (unbind x y e') (unbindT x y t') p_yg_e'_t'
                                  (???) ??? ???
{-lem_denote_sound_typ g e t p_e_t@(TApp _g e' x t_x t' p_e_txt' e_x p_ex_tx) p_g_wf th den_g_th
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
-}
--lem_denote_sound_typ g e t 

{-  
 |  TAbs  :: g:Env -> x:Vname -> t_x:Type -> ProofOf(WFType g t_x) 
                -> e:Expr -> t:Type 
                -> { y:Vname | not (in_env y g) && not (Set_mem y (fv e)) &&
                                                   not (Set_mem y (free t)) } 
                -> ProofOf(HasType (Cons y t_x g) (unbind x y e) (unbindT x y t))
                -> ProofOf(HasType g (Lambda x e) (TFunc x t_x t))
 |  TLet  :: g:Env -> e_x:Expr -> t_x:Type -> ProofOf(HasType g e_x t_x)
                -> x:Vname -> e:Expr -> t:Type -> ProofOf(WFType g t)
                -> { y:Vname | not (in_env y g) && not (Set_mem y (fv e)) &&
                                                   not (Set_mem y (free t)) }
                -> ProofOf(HasType (Cons y t_x g) (unbind x y e) (unbindT x y t))
                -> ProofOf(HasType g (Let x e_x e) t)
 |  TAnn  :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
                -> ProofOf(HasType g (Annot e t) t)
 |  TSub  :: g:Env -> e:Expr -> s:Type -> ProofOf(HasType g e s) -> t:Type 
                -> ProofOf(WFType g t) -> ProofOf(Subtype g s t) 
                -> ProofOf(HasType g e t) -} 

{- @ lem_substitution_sub :: @-}

