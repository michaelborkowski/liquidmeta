{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasTransitive where

import Prelude hiding (max,min)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof,(?))
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import BasicPropsSubstitution
import BasicPropsEnvironments
import WellFormedness
import BasicPropsWellFormedness
import SystemFLemmasSubstitution
import Typing
import LemmasWeakenWF
import LemmasWellFormedness
import SubstitutionLemmaWF
import LemmasTyping
import LemmasSubtyping
import LemmasWeakenTyp
import LemmasExactness
import SubstitutionLemmaTyp
import LemmasNarrowingTyp

{-@ lem_sub_trans_sbase :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t'  && isSBase p_t_t' }
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' && isSBase p_t'_t'' }
            -> { p_t_t'':Subtype  | propOf p_t_t''  == Subtype g t  t'' }
             / [tdepth t + tdepth t' + tdepth t'', 0] @-}
lem_sub_trans_sbase :: Env -> WFEnv -> Type -> Kind -> WFType -> Type {-> Kind -> WFType-}
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_sbase g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t''
              (SBase _  b  p1 p2 nms mk_imp_p1_p2) (SBase _ _b _p2 p3 nms' mk_imp_p2_p3)
  = SBase g b p1 p3 nms'' mk_imp_p1_p3
      where
        {-@ mk_imp_p1_p3 :: { y:Vname | NotElem y nms'' }
              -> ProofOf(Implies (Cons y (TRefn b PEmpty) g) (unbindP y p1) (unbindP y p3)) @-}
        mk_imp_p1_p3 y = ITrans (Cons y (TRefn b PEmpty) g) (unbindP y p1) (unbindP y p2)
                                (unbindP y p3) (mk_imp_p1_p2 y) (mk_imp_p2_p3 y)
        nms''          = unionEnv (union nms nms') g

{-@ lem_sub_trans_sfunc :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t'  && isSFunc p_t_t' }
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' && isSFunc p_t'_t'' }
            -> { p_t_t'':Subtype  | propOf p_t_t''  == Subtype g t  t'' } 
             / [tdepth t + tdepth t' + tdepth t'', 0] @-}
lem_sub_trans_sfunc :: Env -> WFEnv -> Type -> Kind -> WFType -> Type {-> Kind -> WFType-}
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_sfunc g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t''
              (SFunc _  s1 s2 p_s2_s1  t1 t2 nms  mk_p_y2g_t1_t2)
              (SFunc _ _s2 s3 p_s3_s2 _t2 t3 nms' mk_p_z3g_t2_t3)
  = SFunc g s1 s3 p_s3_s1 t1 t3 nms'' mk_p_z3g_t1_t3
      where
        {-@ mk_p_z3g_t1_t3 :: { z:Vname | NotElem z nms'' }
              -> { pf:Subtype | propOf pf == Subtype (Cons z s3 g) (unbindT z t1) (unbindT z t3) } @-}
        mk_p_z3g_t1_t3 z = lem_sub_trans (Cons z s3 g) p_z3g_wf  (unbindT z t1) k_t1 p_w3g_t1 
                               (unbindT z t2) {-k_t2 p_w3g_t2-} (unbindT z t3) k_t3 (mk_p_w3g_t3 z)
                               p_y3g_t1_t2 {-(mk_p_z3g_t1_t2 z)-} (mk_p_z3g_t2_t3 z)
          where
            p_z3g_wf     = WFEBind g p_g_wf z s3 k_s3 p_g_s3
            p_w3g_t1     = lem_narrow_wf g Empty z s3 s1 p_s3_s1 (unbindT z t1) k_t1 (mk_p_w1g_t1 z)
            p_y3g_t1_t2  = lem_narrow_sub g Empty z s3 k_s3 p_g_s3 s2 p_s3_s2 p_g_wf
                                     (unbindT z t1) (unbindT z t2) (mk_p_y2g_t1_t2 z)
        (WFFunc _ _ k_s1 p_g_s1 _ k_t1 nms1 mk_p_w1g_t1) 
            = lem_wffunc_for_wf_tfunc g s1 t1 k   p_g_t
        (WFFunc _ _ k_s3 p_g_s3 _ k_t3 nms3 mk_p_w3g_t3) 
            = lem_wffunc_for_wf_tfunc g s3 t3 k'' p_g_t'' 
        p_s3_s1     = lem_sub_trans g p_g_wf s3 k_s3 p_g_s3 s2 s1 k_s1 p_g_s1 p_s3_s2 p_s2_s1
        nms''            = unionEnv (union (union nms nms') (union nms1 {-(union nms2-} nms3{-)-})) g

{-@ lem_sub_trans_spoly :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t'  && isSPoly p_t_t' }
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' && isSPoly p_t'_t'' }
            -> { p_t_t'':Subtype  | propOf p_t_t''  == Subtype g t  t'' }
             / [tdepth t + tdepth t' + tdepth t'', 0] @-}
lem_sub_trans_spoly :: Env -> WFEnv -> Type -> Kind -> WFType -> Type {-> Kind -> WFType-}
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_spoly g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t''
              (SPoly _ k1 t1 t2 nms mk_p_ag_t1_t2) (SPoly _ _ _ t3 nms' mk_p_ag_t2_t3)
  = SPoly g k1 t1 t3 nms'' mk_p_ag_t1_t3
      where
        {-@ mk_p_ag_t1_t3 :: { a:Vname | NotElem a nms'' }
              -> { pf:Subtype | propOf pf == Subtype (ConsT a k1 g)
                                                     (unbind_tvT a t1) (unbind_tvT a t3) } @-}
        mk_p_ag_t1_t3 a = lem_sub_trans (ConsT a k1 g) p_ag_wf 
                                    (unbind_tvT a t1) k_t1 (mk_p_ag_t1 a)
                                    (unbind_tvT a t2) 
                                    (unbind_tvT a t3) k_t3 (mk_p_ag_t3 a) 
                                    (mk_p_ag_t1_t2 a) (mk_p_ag_t2_t3 a)
          where
            p_ag_wf    = WFEBindT g p_g_wf a  k1        
        p_g_t_st    = if k   == Star then p_g_t   else WFKind g t   p_g_t
        p_g_t''_st  = if k'' == Star then p_g_t'' else WFKind g t'' p_g_t''
        (WFPoly _ _ _ k_t1 nms1 mk_p_ag_t1) = lem_wfpoly_for_wf_tpoly g k1 t1 p_g_t_st
        (WFPoly _ _ _ k_t3 nms3 mk_p_ag_t3) = lem_wfpoly_for_wf_tpoly g k1 t3 p_g_t''_st
        nms''       = unionEnv (union (union nms nms') (union {-(union-} nms1 {-nms2)-} nms3)) g

{-@ lem_sub_trans_switnR :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t' }
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' && isSWitn p_t'_t'' }
            -> { p_t_t'':Subtype  | propOf p_t_t''  == Subtype g t  t'' }
             / [tdepth t + tdepth t' + tdepth t'', 0] @-}
lem_sub_trans_switnR :: Env -> WFEnv -> Type -> Kind -> WFType -> Type {-> Kind -> WFType-}
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_switnR g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_g_t_t'
                     (SWitn _ v_y s_y p_vy_sy _t' s'' p_g_t'_s''vy)  -- t'' == \ex s_y. s''
  = SWitn g v_y s_y p_vy_sy t s'' p_g_t_s''vy
      where
        (WFExis _ _ k_sy p_g_sy _ _ nms mk_p_wg_s'') 
                    = lem_wfexis_for_wf_texists g s_y s'' k'' p_g_t''
        w           = fresh_var nms g
        p_vy_er_sy  = lem_typing_hasftype g v_y s_y p_vy_sy p_g_wf 
        p_g_s''vy   = lem_subst_wf g Empty w v_y s_y p_vy_er_sy (unbindT w s'') k'' (mk_p_wg_s'' w)
                                   ? lem_tsubFV_unbindT w v_y 
                                       (s'' ? lem_free_subset_binds g t'' k'' p_g_t'')
        p_g_t_s''vy = lem_sub_trans g p_g_wf t k p_g_t t' {-k' p_g_t'-} (tsubBV v_y s'') k'' 
                                    p_g_s''vy p_g_t_t' p_g_t'_s''vy

{-@ lem_sub_trans_switnbind :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t'  && isSWitn p_t_t' }
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' && isSBind p_t'_t'' }
            -> { p_t_t'':Subtype  | propOf p_t_t''  == Subtype g t  t'' }
             / [tdepth t + tdepth t' + tdepth t'', 0] @-}
lem_sub_trans_switnbind :: Env -> WFEnv -> Type -> Kind -> WFType -> Type {-> Kind -> WFType-}
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_switnbind g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t''
        (SWitn _ v_x s_x p_vx_sx _t s' p_g_t_s'vx) (SBind _ _sx _s' _t'' nms mk_p_yg_s'_t'')
  = lem_sub_trans g p_g_wf t k p_g_t (tsubBV v_x s')  t'' k'' p_g_t'' p_g_t_s'vx p_g_s'vx_t''
      where
        w            = fresh_varT {-(union-} nms {-nms')-} g s'
        p_vx_er_sx   = lem_typing_hasftype g v_x s_x p_vx_sx p_g_wf
        p_g_s'vx_t'' = lem_subst_sub g Empty w v_x s_x p_vx_sx p_g_wf (unbindT w s') 
                                     t''  (mk_p_yg_s'_t'' w)
                                     ? lem_tsubFV_unbindT w v_x   s'
                                     ? lem_tsubFV_notin w  v_x
                                         (t'' ? lem_free_subset_binds g t'' k'' p_g_t'')

{-@ lem_sub_trans_sbindL :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t' && isSBind p_t_t'}
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' }
            -> { p_t_t'':Subtype  | propOf p_t_t''  == Subtype g t  t'' }
             / [tdepth t + tdepth t' + tdepth t'', 0] @-}
lem_sub_trans_sbindL :: Env -> WFEnv -> Type -> Kind -> WFType -> Type {-> Kind -> WFType-}
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_sbindL g p_g_wf t k p_g_t t' {-k' p_g_t'-} t''_ k'' p_g_t''
              (SBind _ s_x s _t' nms mk_p_yg_s_t') p_g_t'_t'' = case (isTExists t) of
  True  -> SBind g s_x s t'' nms'' mk_p_yg_s_t''
      where
        {-@ mk_p_yg_s_t'' :: { y:Vname | NotElem y nms'' }
              -> { pf:Subtype | propOf pf == Subtype (Cons y s_x g) (unbindT y s) t'' } @-}
        mk_p_yg_s_t'' y = lem_sub_trans (Cons y s_x g) p_yg_wf (unbindT y s) k_s (mk_p_yg_s y)
                                        t' t'' k'' p_yg_t'' (mk_p_yg_s_t' y) p_yg_t'_t''
          where
            p_yg_wf     = WFEBind g p_g_wf y s_x k_sx p_g_sx
            p_yg_t''    = lem_weaken_wf g Empty t'' k'' p_g_t'' y s_x
            p_yg_t'_t'' = lem_weaken_subtype g Empty t'  t''  p_g_t'_t'' y s_x
        t''         = t''_ ? lem_wftype_islct g t''_ k'' p_g_t'' 
        (WFExis _ _ k_sx p_g_sx _ k_s nms' mk_p_yg_s) = lem_wfexis_for_wf_texists g s_x s k p_g_t
        nms''           = unionEnv (union nms nms') g
  False -> impossible ""

{-@ lem_sub_trans_go_sbase :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t' && isSBase p_t_t'}
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' }
            -> { p_t_t'':Subtype  | propOf p_t_t''  == Subtype g t  t'' }
             / [tdepth t + tdepth t' + tdepth t'', 1] @-}
lem_sub_trans_go_sbase :: Env -> WFEnv -> Type -> Kind -> WFType -> Type {-> Kind -> WFType-}
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_go_sbase  g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_t_t' p_t'_t''@(SBase {})
  = lem_sub_trans_sbase g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_t_t' p_t'_t''
lem_sub_trans_go_sbase   g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_g_t_t' p_g_t'_t''@(SWitn {})
  = lem_sub_trans_switnR g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_g_t_t' p_g_t'_t''
lem_sub_trans_go_sbase g _ t _ _ t' {-_ _-} t'' _ _ (SBase {}) (SFunc {}) = impossible ""
lem_sub_trans_go_sbase g _ t _ _ t' {-_ _-} t'' _ _ (SBase {}) (SBind {}) = impossible ""
lem_sub_trans_go_sbase g _ t _ _ t' {-_ _-} t'' _ _ (SBase {}) (SPoly {}) = impossible ""

{-@ lem_sub_trans_go_sfunc :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t' && isSFunc p_t_t'}
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' }
            -> { p_t_t'':Subtype  | propOf p_t_t''  == Subtype g t  t'' }
             / [tdepth t + tdepth t' + tdepth t'', 1] @-}
lem_sub_trans_go_sfunc :: Env -> WFEnv -> Type -> Kind -> WFType -> Type {-> Kind -> WFType-}
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_go_sfunc  g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_t_t' p_t'_t''@(SFunc {})
  = lem_sub_trans_sfunc g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_t_t' p_t'_t''
lem_sub_trans_go_sfunc   g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_g_t_t' p_g_t'_t''@(SWitn {})
  = lem_sub_trans_switnR g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_g_t_t' p_g_t'_t''
lem_sub_trans_go_sfunc g _ t _ _ t' {-_ _-} t'' _ _ (SFunc {}) (SBase {}) = impossible ""
lem_sub_trans_go_sfunc g _ t _ _ t' {-_ _-} t'' _ _ (SFunc {}) (SBind {}) = impossible ""
lem_sub_trans_go_sfunc g _ t _ _ t' {-_ _-} t'' _ _ (SFunc {}) (SPoly {}) = impossible ""

{-@ lem_sub_trans_go_spoly :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t' && isSPoly p_t_t'}
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' }
            -> { p_t_t'':Subtype  | propOf p_t_t''  == Subtype g t  t'' }
             / [tdepth t + tdepth t' + tdepth t'', 1] @-}
lem_sub_trans_go_spoly :: Env -> WFEnv -> Type -> Kind -> WFType -> Type {-> Kind -> WFType-}
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_go_spoly  g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_t_t' p_t'_t''@(SPoly {})
  = lem_sub_trans_spoly g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_t_t' p_t'_t''
lem_sub_trans_go_spoly   g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_g_t_t' p_g_t'_t''@(SWitn {})
  = lem_sub_trans_switnR g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_g_t_t' p_g_t'_t''
lem_sub_trans_go_spoly g _ t _ _ t' {-_ _-} t'' _ _ (SPoly {}) (SBase {}) = impossible ""
lem_sub_trans_go_spoly g _ t _ _ t' {-_ _-} t'' _ _ (SPoly {}) (SFunc {}) = impossible ""
lem_sub_trans_go_spoly g _ t _ _ t' {-_ _-} t'' _ _ (SPoly {}) (SBind {}) = impossible ""

{-@ lem_sub_trans_go_switn :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t' && isSWitn p_t_t'}
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' }
            -> { p_t_t'':Subtype  | propOf p_t_t''  == Subtype g t  t'' }
             / [tdepth t + tdepth t' + tdepth t'', 1] @-}
lem_sub_trans_go_switn :: Env -> WFEnv -> Type -> Kind -> WFType -> Type {-> Kind -> WFType-}
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_go_switn   g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_g_t_t' p_g_t'_t''@(SWitn {})
  = lem_sub_trans_switnR g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_g_t_t' p_g_t'_t''
lem_sub_trans_go_switn      g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_t_t' p_t'_t''@(SBind {})
  = lem_sub_trans_switnbind g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_t_t' p_t'_t''
lem_sub_trans_go_switn g _ t _ _ t' {-_ _-} t'' _ _ (SWitn {}) (SBase {}) = impossible ""
lem_sub_trans_go_switn g _ t _ _ t' {-_ _-} t'' _ _ (SWitn {}) (SFunc {}) = impossible ""
lem_sub_trans_go_switn g _ t _ _ t' {-_ _-} t'' _ _ (SWitn {}) (SPoly {}) = impossible ""

{-@ lem_sub_trans :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t' }
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' }
            -> { p_t_t'':Subtype  | propOf p_t_t''  == Subtype g t  t'' }
             / [tdepth t + tdepth t' + tdepth t'', 2] @-}
lem_sub_trans :: Env -> WFEnv -> Type -> Kind -> WFType -> Type {-> Kind -> WFType-}
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_t_t'@(SBase {}) p_t'_t'' 
  = lem_sub_trans_go_sbase g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_t_t' p_t'_t''
lem_sub_trans g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_t_t'@(SFunc {}) p_t'_t''
  = lem_sub_trans_go_sfunc g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_t_t' p_t'_t''
lem_sub_trans g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_t_t'@(SPoly {}) p_t'_t'' 
  = lem_sub_trans_go_spoly g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_t_t' p_t'_t''
lem_sub_trans g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_t_t'@(SWitn {}) p_t'_t'' 
  = lem_sub_trans_go_switn g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_t_t' p_t'_t''
lem_sub_trans g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_g_t_t'@(SBind {}) p_g_t'_t'' 
  = lem_sub_trans_sbindL g p_g_wf t k p_g_t t' {-k' p_g_t'-} t'' k'' p_g_t'' p_g_t_t' p_g_t'_t''
