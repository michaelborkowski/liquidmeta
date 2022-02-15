{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasTransitive where

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
import SystemFLemmasSubstitution
import Typing
import LemmasWeakenWF
import LemmasWellFormedness
import LemmasTyping
import LemmasSubtyping
--import LemmasWeakenTyp
--import SubstitutionLemmaWF
import LemmasExactness
--import SubstitutionLemmaTyp
import LemmasNarrowingTyp

{-@ lem_sub_trans_sbase :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> k':Kind -> ProofOf(WFType g t' k') 
            -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t'  && isSBase p_t_t' }
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' && isSBase p_t'_t'' }
            -> ProofOf(Subtype g t t'') @-} -- / [subtypSize' p_t_t' + subtypSize' p_t'_t'', 0] @- }
lem_sub_trans_sbase :: Env -> WFEnv -> Type -> Kind -> WFType -> Type -> Kind -> WFType
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_sbase g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t''
              (SBase _  b  p1 p2 nms mk_imp_p1_p2) (SBase _ _b _p2 p3 nms' mk_imp_p2_p3)
  = SBase g b p1 p3 nms'' mk_imp_p1_p3
      where
        {-@ mk_imp_p1_p3 :: { y:Vname | NotElem y nms'' }
              -> ProofOf(Implies (Cons y (TRefn b PEmpty) g) (unbindP y p1) (unbindP y p3)) @-}
        mk_imp_p1_p3 y = ITrans (Cons y (TRefn b PEmpty) g) (unbindP y p1) (unbindP y p2)
                                (unbindP y p3) (mk_imp_p1_p2 y) (mk_imp_p2_p3 y)

{-@ lem_sub_trans_sfunc :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> k':Kind -> ProofOf(WFType g t' k') 
            -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t'  && isSFunc p_t_t' }
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' && isSFunc p_t'_t'' }
            -> ProofOf(Subtype g t t'') @-} -- / [subtypSize' p_t_t' + subtypSize' p_t'_t'', 0] @-}
lem_sub_trans_sfunc :: Env -> WFEnv -> Type -> Kind -> WFType -> Type -> Kind -> WFType
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_sfunc g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t''
              (SFunc n  _  s1 s2 p_s2_s1  t1 t2 nms  mk_p_y2g_t1_t2)
              (SFunc n' _ _s2 s3 p_s3_s2 _t2 t3 nms' mk_p_z3g_t2_t3)
  = SFunc n'' g s1 s3 p_s3_s1 t1 t3 nms'' mk_p_z3g_t1_t3
      where
        {-@ mk_p_z3g_t1_t3 :: { z:Vname | NotElem z nms'' }
              -> { pf:Subtype | propOf pf == Subtype (Cons z s3 g)
                                                     (unbindT z t1) (unbindT z t3) } @-} -- &&
 --                             sizeOf pf <= n + subtypSize p_sx_tx + tdepth s_x + 2 } @-} 
        mk_p_z3g_t1_t3 z = lem_sub_trans (Cons z s3 g) p_z3g_wf  (unbindT z t1) k_t1 p_w3g_t1 
                               (unbindT z t2) k_t2 p_w3g_t2 (unbindT z t3) k_t3 (mk_p_w3g_t3 z)
                               p_y3g_t1_t2 {-(mk_p_z3g_t1_t2 z)-} (mk_p_z3g_t2_t3 z)
          where
            p_z3g_wf     = WFEBind g p_g_wf z s3 k_s3 p_g_s3
            p_w3g_t1     = lem_narrow_wf g Empty z s3 s1 p_s3_s1 (unbindT z t1) k_t1 (mk_p_w1g_t1 z)
            p_w3g_t2     = lem_narrow_wf g Empty z s3 s2 p_s3_s2 (unbindT z t2) k_t2 (mk_p_w2g_t2 z)
            p_y3g_t1_t2  = lem_narrow_sub g Empty z s3 k_s3 p_g_s3 s2 p_s3_s2 p_g_wf
                                     (unbindT z t1) {-k_t1 p_y2g_t1 -}
                                     (unbindT z t2) {-k_t2 p_y2g_t2 -} (mk_p_y2g_t1_t2 z)
        (WFFunc _ _ k_s1 p_g_s1 _ k_t1 nms1 mk_p_w1g_t1) 
            = lem_wffunc_for_wf_tfunc g s1 t1 k   p_g_t
        (WFFunc _ _ k_s2 p_g_s2 _ k_t2 nms2 mk_p_w2g_t2) 
            = lem_wffunc_for_wf_tfunc g s2 t2 k'  p_g_t' 
        (WFFunc _ _ k_s3 p_g_s3 _ k_t3 nms3 mk_p_w3g_t3) 
            = lem_wffunc_for_wf_tfunc g s3 t3 k'' p_g_t'' 
        p_s3_s1     = lem_sub_trans g p_g_wf s3 k_s3 p_g_s3 s2 k_s2 p_g_s2 
                                             s1 k_s1 p_g_s1 p_s3_s2 p_s2_s1
        nms''            = unionEnv (union (union nms nms') (union nms1 (union nms2 nms3))) g
        n''              = undefined
  
{-@ lem_sub_trans_spoly :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> k':Kind -> ProofOf(WFType g t' k') 
            -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t'  && isSPoly p_t_t' }
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' && isSPoly p_t'_t'' }
            -> ProofOf(Subtype g t t'') @-} -- / [subtypSize' p_t_t' + subtypSize' p_t'_t'', 0] @-}
lem_sub_trans_spoly :: Env -> WFEnv -> Type -> Kind -> WFType -> Type -> Kind -> WFType
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_spoly g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t''
              (SPoly n _ k1 t1 t2 nms mk_p_ag_t1_t2) (SPoly n' _ _ _ t3 nms' mk_p_ag_t2_t3)
  = SPoly n'' g k1 t1 t3 nms'' mk_p_ag_t1_t3
      where
        {-@ mk_p_ag_t1_t3 :: { a:Vname | NotElem a nms'' }
              -> { pf:Subtype | propOf pf == Subtype (ConsT a k1 g)
                                                     (unbind_tvT a t1) (unbind_tvT a t3) } @-} -- &&
        mk_p_ag_t1_t3 a = lem_sub_trans (ConsT a k1 g) p_ag_wf 
                                    (unbind_tvT a t1) k_t1 (mk_p_ag_t1 a)
                                    (unbind_tvT a t2) k_t2 (mk_p_ag_t2 a)
                                    (unbind_tvT a t3) k_t3 (mk_p_ag_t3 a) 
                                    (mk_p_ag_t1_t2 a) (mk_p_ag_t2_t3 a)
          where
            p_a'g_wf    = WFEBindT g p_g_wf a  k1        
        p_g_t_st    = if k   == Star then p_g_t   else WFKind g t   p_g_t
        p_g_t'_st   = if k'  == Star then p_g_t'  else WFKind g t'  p_g_t'
        p_g_t''_st  = if k'' == Star then p_g_t'' else WFKind g t'' p_g_t''
        (WFPoly _ _ _ k_t1 nms1 mk_p_ag_t1) = lem_wfpoly_for_wf_tpoly g k1 t1 p_g_t_st
        (WFPoly _ _ _ k_t2 nms2 mk_p_ag_t2) = lem_wfpoly_for_wf_tpoly g k1 t2 p_g_t'_st
        (WFPoly _ _ _ k_t3 nms3 mk_p_ag_t3) = lem_wfpoly_for_wf_tpoly g k1 t3 p_g_t''_st
        n''         = undefined

{-@ lem_sub_trans_switnR :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> k':Kind -> ProofOf(WFType g t' k') 
            -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t' }
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' && isSWitn p_t'_t'' }
            -> ProofOf(Subtype g t t'') @-} -- / [subtypSize' p_t_t' + subtypSize' p_t'_t'', 0] @-}
lem_sub_trans_switnR :: Env -> WFEnv -> Type -> Kind -> WFType -> Type -> Kind -> WFType
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_switnR g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t'' p_g_t_t'
                     (SWitn n _ v_y s_y p_vy_sy _t' s'' p_g_t'_s''vy)  -- t'' == \ex s_y. s''
  = SWitn n' g v_y s_y p_vy_sy t s'' p_g_t_s''vy
      where
        (WFExis _ _ k_sy p_g_sy _ _ nms mk_p_wg_s'') 
                    = lem_wfexis_for_wf_texists g y s_y s'' k'' p_g_t''
--        p_wg_wf     = WFEBind g p_g_wf w s_y k_sy p_g_sy
        w           = fresh_var nms g
        p_vy_er_sy  = lem_typing_hasftype g v_y s_y p_vy_sy p_g_wf 
        p_g_s''vy   = lem_subst_wf g Empty w v_y s_y p_vy_er_sy (unbindT w s'') k'' (mk_p_wg_s'' w)
                                   ? lem_tsubFV_unbindT w v_y s''
        p_g_t_s''vy = lem_sub_trans g p_g_wf t k p_g_t t' k' p_g_t' (tsubBV v_y s'') k'' 
                                    p_g_s''vy p_g_t_t' p_g_t'_s''vy
        n'          = undefined

{-
{-@ lem_sub_trans_switnbind :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> k':Kind -> ProofOf(WFType g t' k') 
            -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t'  && isSWitn p_t_t' }
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' && isSBind p_t'_t'' }
            -> ProofOf(Subtype g t t'') / [subtypSize' p_t_t' + subtypSize' p_t'_t'', 0] @-}
lem_sub_trans_switnbind :: Env -> WFEnv -> Type -> Kind -> WFType -> Type -> Kind -> WFType
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_switnbind g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t''
        (SWitn _ v_x s_x p_vx_sx _t x s' p_g_t_s'vx) (SBind _ _x _sx _s' _t'' y p_yg_s'_t'')
  = lem_sub_trans g p_g_wf t k p_g_t (tsubBV x v_x s') k' p_g_s'vx 
                  t'' k'' p_g_t'' p_g_t_s'vx p_g_s'vx_t''
      where
        (WFExis _ _ _ k_sx p_g_sx _ k_s' w p_wg_s') 
                     = lem_wfexis_for_wf_texists g x s_x s' k' p_g_t'
        p_wg_wf      = WFEBind g p_g_wf w s_x k_sx p_g_sx
        p_yg_wf      = WFEBind g p_g_wf y s_x k_sx p_g_sx
        p_yg_s'      = lem_change_var_wf' g w s_x Empty p_wg_wf (unbindT x w s') k' p_wg_s' y
                           ? lem_tsubFV_unbindT x w (FV y) s'
        p_yg_t''     = lem_weaken_wf' g Empty p_g_wf t'' k'' p_g_t'' y s_x
        p_g_s'vx     = lem_subst_wf'  g Empty w v_x s_x p_vx_sx p_wg_wf (unbindT x w s') k' p_wg_s'
                                      ? lem_tsubFV_unbindT x w v_x s'
        p_g_s'vx_t'' = lem_subst_sub g Empty y v_x s_x p_vx_sx p_yg_wf (unbindT x y s') k' p_yg_s'
                                     t'' k'' p_yg_t'' p_yg_s'_t''
                                     ? lem_tsubFV_unbindT x y v_x s'
                                     ? lem_tsubFV_notin y v_x t''

{-@ lem_sub_trans_sbindL :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> k':Kind -> ProofOf(WFType g t' k') 
            -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t' && isSBind p_t_t'}
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' }
            -> ProofOf(Subtype g t t'') / [subtypSize' p_t_t' + subtypSize' p_t'_t'', 0] @-}
lem_sub_trans_sbindL :: Env -> WFEnv -> Type -> Kind -> WFType -> Type -> Kind -> WFType
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_sbindL g p_g_wf t k p_g_t t' k' p_g_t' t''_ k'' p_g_t''
              (SBind _ x s_x s _t' y_ p_yg_s_t') p_g_t'_t'' = case (isTExists t) of
  True  -> SBind g x s_x s t'' y p_yg_s_t''
      where
        t''         = t''_ ? lem_tfreeBV_empty g t''_ k'' p_g_t'' 
        y           = y_ ? lem_free_bound_in_env g t'' k'' p_g_t'' y_ 
        (WFExis _ _ _ k_sx p_g_sx _ k_s w p_wg_s) = lem_wfexis_for_wf_texists g x s_x s k p_g_t
        p_wg_wf     = WFEBind g p_g_wf w s_x k_sx p_g_sx
        p_yg_wf     = WFEBind g p_g_wf y s_x k_sx p_g_sx
        p_yg_s      = lem_change_var_wf' g w s_x Empty p_wg_wf (unbindT x w s) k_s p_wg_s y
                          ? lem_tsubFV_unbindT x w (FV y) s
        p_yg_t'     = lem_weaken_wf' g Empty p_g_wf t'  k'  p_g_t'  y s_x
        p_yg_t''    = lem_weaken_wf' g Empty p_g_wf t'' k'' p_g_t'' y s_x
        p_yg_t'_t'' = lem_weaken_subtype g Empty p_g_wf t' k' p_g_t' t'' k'' p_g_t''
                                         p_g_t'_t'' y s_x
        p_yg_s_t''  = lem_sub_trans (Cons y s_x g) p_yg_wf (unbindT x y s) k_s p_yg_s t' k' p_yg_t'
                                    t'' k'' p_yg_t'' p_yg_s_t' p_yg_t'_t''
  False -> impossible ""


{-@ lem_sub_trans_go_sbase :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> k':Kind -> ProofOf(WFType g t' k') 
            -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t' && isSBase p_t_t'}
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' }
            -> ProofOf(Subtype g t t'') / [subtypSize' p_t_t' + subtypSize' p_t'_t'', 1] @-}
lem_sub_trans_go_sbase :: Env -> WFEnv -> Type -> Kind -> WFType -> Type -> Kind -> WFType
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_go_sbase g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t''
              p_t_t' p_t'_t''@(SBase _ _x2 _b _p2 x3 p3 z p_zp2_p3)
  = lem_sub_trans_sbase g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t'' p_t_t' p_t'_t''
lem_sub_trans_go_sbase g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t'' p_g_t_t'
              p_g_t'_t''@(SWitn _ v_y s_y p_vy_sy _t' y s'' p_g_t'_s''vy)
  = lem_sub_trans_switnR g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t'' p_g_t_t' p_g_t'_t''
lem_sub_trans_go_sbase g _ t _ _ t' _ _ t'' _ _ (SBase {}) (SFunc {}) = impossible ""
lem_sub_trans_go_sbase g _ t _ _ t' _ _ t'' _ _ (SBase {}) (SBind {}) = impossible ""
lem_sub_trans_go_sbase g _ t _ _ t' _ _ t'' _ _ (SBase {}) (SPoly {}) = impossible ""

{-@ lem_sub_trans_go_sfunc :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> k':Kind -> ProofOf(WFType g t' k') 
            -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t' && isSFunc p_t_t'}
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' }
            -> ProofOf(Subtype g t t'') / [subtypSize' p_t_t' + subtypSize' p_t'_t'', 1] @-}
lem_sub_trans_go_sfunc :: Env -> WFEnv -> Type -> Kind -> WFType -> Type -> Kind -> WFType
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_go_sfunc g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t''
              p_t_t'{- @(SFunc   _  x1  s1 x2 s2 p_s2_s1  t1 t2 y  p_y2g_t1_t2)-}
              p_t'_t''@(SFunc _ _x2 _s2 x3 s3 p_s3_s2 _t2 t3 z_ p_z3g_t2_t3)
  = lem_sub_trans_sfunc g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t'' p_t_t' p_t'_t''
lem_sub_trans_go_sfunc g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t'' p_g_t_t'
              p_g_t'_t''@(SWitn _ v_y s_y p_vy_sy _t' y s'' p_g_t'_s''vy)
  = lem_sub_trans_switnR g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t'' p_g_t_t' p_g_t'_t''
lem_sub_trans_go_sfunc g _ t _ _ t' _ _ t'' _ _ (SFunc {}) (SBase {}) = impossible ""
lem_sub_trans_go_sfunc g _ t _ _ t' _ _ t'' _ _ (SFunc {}) (SBind {}) = impossible ""
lem_sub_trans_go_sfunc g _ t _ _ t' _ _ t'' _ _ (SFunc {}) (SPoly {}) = impossible ""

{-@ lem_sub_trans_go_spoly :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> k':Kind -> ProofOf(WFType g t' k') 
            -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t' && isSPoly p_t_t'}
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' }
            -> ProofOf(Subtype g t t'') / [subtypSize' p_t_t' + subtypSize' p_t'_t'', 1] @-}
lem_sub_trans_go_spoly :: Env -> WFEnv -> Type -> Kind -> WFType -> Type -> Kind -> WFType
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_go_spoly g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t''
              p_t_t'{- @(SPoly _ a1 k1 t1 a2 t2 a'_ p_a'g_t1_t2)-} p_t'_t''@(SPoly _ _ _ _ a3 t3 a'' p_a''g_t2_t3)
  = lem_sub_trans_spoly g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t'' p_t_t' p_t'_t''
lem_sub_trans_go_spoly g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t'' p_g_t_t'
              p_g_t'_t''@(SWitn _ v_y s_y p_vy_sy _t' y s'' p_g_t'_s''vy)
  = lem_sub_trans_switnR g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t'' p_g_t_t' p_g_t'_t''
lem_sub_trans_go_spoly g _ t _ _ t' _ _ t'' _ _ (SPoly {}) (SBase {}) = impossible ""
lem_sub_trans_go_spoly g _ t _ _ t' _ _ t'' _ _ (SPoly {}) (SFunc {}) = impossible ""
lem_sub_trans_go_spoly g _ t _ _ t' _ _ t'' _ _ (SPoly {}) (SBind {}) = impossible ""

{-@ lem_sub_trans_go_switn :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> k':Kind -> ProofOf(WFType g t' k') 
            -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t' && isSWitn p_t_t'}
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' }
            -> ProofOf(Subtype g t t'') / [subtypSize' p_t_t' + subtypSize' p_t'_t'', 1] @-}
lem_sub_trans_go_switn :: Env -> WFEnv -> Type -> Kind -> WFType -> Type -> Kind -> WFType
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_go_switn g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t'' p_g_t_t'
              p_g_t'_t''@(SWitn _ v_y s_y p_vy_sy _t' y s'' p_g_t'_s''vy)
  = lem_sub_trans_switnR g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t'' p_g_t_t' p_g_t'_t''
lem_sub_trans_go_switn g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t''
        p_t_t'{- @(SWitn _ v_x s_x p_vx_sx _t x s' p_g_t_s'vx)-} p_t'_t''@(SBind _ _x _sx _s' _t'' y p_yg_s'_t'')
  = lem_sub_trans_switnbind g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t'' p_t_t' p_t'_t''
lem_sub_trans_go_switn g _ t _ _ t' _ _ t'' _ _ (SWitn {}) (SBase {}) = impossible ""
lem_sub_trans_go_switn g _ t _ _ t' _ _ t'' _ _ (SWitn {}) (SFunc {}) = impossible ""
lem_sub_trans_go_switn g _ t _ _ t' _ _ t'' _ _ (SWitn {}) (SPoly {}) = impossible ""
-}

{-@ lem_sub_trans :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> k':Kind -> ProofOf(WFType g t' k') 
            -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t' }
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' }
            -> ProofOf(Subtype g t t'') @-} -- / [subtypSize' p_t_t' + subtypSize' p_t'_t'', 2] @-}
lem_sub_trans :: Env -> WFEnv -> Type -> Kind -> WFType -> Type -> Kind -> WFType
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t'' p_t_t' p_t'_t'' = undefined {-
lem_sub_trans g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t''
              p_t_t'@(SBase _  x1  b  p1 x2 p2 y_ p_yp1_p2) p_t'_t'' -- @(SBase _ _x2 _b _p2 x3 p3 z p_zp2_p3)
  = lem_sub_trans_go_sbase g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t'' p_t_t' p_t'_t''
lem_sub_trans g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t''
              p_t_t'@(SFunc   _  x1  s1 x2 s2 p_s2_s1  t1 t2 y  p_y2g_t1_t2) p_t'_t''
              --p_t'_t''@(SFunc _ _x2 _s2 x3 s3 p_s3_s2 _t2 t3 z_ p_z3g_t2_t3)
  = lem_sub_trans_go_sfunc g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t'' p_t_t' p_t'_t''
lem_sub_trans g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t''
              p_t_t'@(SPoly _ a1 k1 t1 a2 t2 a'_ p_a'g_t1_t2) p_t'_t'' -- @(SPoly _ _ _ _ a3 t3 a'' p_a''g_t2_t3)
  = lem_sub_trans_go_spoly g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t'' p_t_t' p_t'_t''
lem_sub_trans g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t''
        p_t_t'@(SWitn _ v_x s_x p_vx_sx _t x s' p_g_t_s'vx) p_t'_t'' -- @(SBind _ _x _sx _s' _t'' y p_yg_s'_t'')
  = lem_sub_trans_go_switn g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t'' p_t_t' p_t'_t''
lem_sub_trans g p_g_wf t k p_g_t t' k' p_g_t' t''_ k'' p_g_t''
              p_g_t_t'@(SBind _ x s_x s _t' y_ p_yg_s_t') p_g_t'_t'' 
  = lem_sub_trans_sbindL g p_g_wf t k p_g_t t' k' p_g_t' t''_ k'' p_g_t'' p_g_t_t' p_g_t'_t''
-}
