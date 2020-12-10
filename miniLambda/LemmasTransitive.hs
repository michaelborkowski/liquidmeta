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
import LemmasChangeVarEnt
import LemmasChangeVarTyp
import LemmasWeakenTyp
import SubstitutionLemmaWF
import DenotationsSelfify
import DenotationsSoundness
import PrimitivesSemantics
import PrimitivesDenotations
import LemmasExactness
import SubstitutionLemmaEnt
import SubstitutionLemmaTyp
import LemmasNarrowingEnt
import LemmasNarrowingTyp

{-@ reflect foo57 @-}
foo57 x = Just x
foo57 :: a -> Maybe a


--            -> ProofOf(Subtype g t t'') / [typSize t, typSize t', typSize t''] @-}
{-@ lem_sub_trans :: g:Env -> ProofOf(WFEnv g) -> t:Type -> ProofOf(WFType g t)
            -> t':Type  -> ProofOf(WFType g t' ) 
            -> t'':Type -> ProofOf(WFType g t'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t' }
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' }
            -> ProofOf(Subtype g t t'') / [subtypSize' p_t_t' + subtypSize' p_t'_t''] @-}
lem_sub_trans :: Env -> WFEnv -> Type -> WFType -> Type ->  WFType
                     -> Type -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans g p_g_wf t p_g_t t' p_g_t' t'' p_g_t''
              (SBase _  x1  b  p1 x2 p2 y_ p_yp1_p2) (SBase _ _x2 _b _p2 x3 p3 z p_zp2_p3)
  = SBase g x1 b p1 x3 p3 y p_yp1_p3
      where
        y        = y_ ? lem_free_bound_in_env g t   p_g_t   y_
                      ? lem_free_bound_in_env g t'' p_g_t'' y_
        p_zg_wf  = WFEBind g p_g_wf z (TRefn b x2 p2) p_g_t' 
        p_yp2_p3 = lem_change_var_ent g z (TRefn b x2 p2) Empty p_zg_wf 
                      (unbind x3 z p3 ? lem_free_subset_binds g t''  p_g_t'') p_zp2_p3 y
                      ? lem_subFV_unbind x3 z (FV y) p3
        p_yp1_p3 = lem_entails_trans g b x1 p1 x2 p2 x3 p3 y p_yp1_p2 p_yp2_p3 
lem_sub_trans g p_g_wf t p_g_t t' p_g_t' t''  p_g_t''
              (SFunc _  x1  s1 x2 s2 p_s2_s1  t1 t2 y  p_y2g_t1_t2)
              (SFunc _ _x2 _s2 x3 s3 p_s3_s2 _t2 t3 z_ p_z3g_t2_t3)
  = SFunc g x1 s1 x3 s3 p_s3_s1 t1 t3 z p_z3g_t1_t3
      where
        z           = z_ ? lem_free_bound_in_env g t    p_g_t   z_
                         ? lem_free_bound_in_env g t''  p_g_t'' z_
        (WFFunc _ _ _  p_g_s1 _ w1 p_w1g_t1) = p_g_t
        (WFFunc _ _ _  p_g_s2 _ w2 p_w2g_t2) = p_g_t' 
        (WFFunc _ _ _  p_g_s3 _ w3 p_w3g_t3) = p_g_t'' 
        p_s3_s1     = lem_sub_trans g p_g_wf s3 p_g_s3 s2 p_g_s2 
                                             s1 p_g_s1 p_s3_s2 p_s2_s1
        p_y3g_wf    = WFEBind g p_g_wf y s3 p_g_s3
        p_z3g_wf    = WFEBind g p_g_wf z s3 p_g_s3
        p_w3g_t1    = lem_subtype_in_env_wf g Empty w1 s3 s1 p_s3_s1 (unbindT x1 w1 t1) p_w1g_t1
        p_w3g_t2    = lem_subtype_in_env_wf g Empty w2 s3 s2 p_s3_s2 (unbindT x2 w2 t2) p_w2g_t2
        p_y3g_t1    = lem_change_var_wf g w1 s3 Empty (unbindT x1 w1 t1) p_w3g_t1 y
                                             ? lem_tsubFV_unbindT x1 w1 (FV y) t1
        p_y3g_t2    = lem_change_var_wf g w2 s3 Empty (unbindT x2 w2 t2) p_w3g_t2 y
                                             ? lem_tsubFV_unbindT x2 w2 (FV y) t2
        p_z3g_t1    = lem_change_var_wf g w1 s3 Empty (unbindT x1 w1 t1) p_w3g_t1 z
                                             ? lem_tsubFV_unbindT x1 w1 (FV z) t1
        p_z3g_t2    = lem_change_var_wf g w2 s3 Empty (unbindT x2 w2 t2) p_w3g_t2 z
                                             ? lem_tsubFV_unbindT x2 w2 (FV z) t2
        p_z3g_t3    = lem_change_var_wf g w3 s3 Empty (unbindT x3 w3 t3) p_w3g_t3 z
                                             ? lem_tsubFV_unbindT x3 w3 (FV z) t3

        p_y2g_wf    = WFEBind g p_g_wf y s2 p_g_s2
        p_w2g_t1    = lem_subtype_in_env_wf g Empty w1 s2 s1 p_s2_s1 (unbindT x1 w1 t1) p_w1g_t1
        p_y2g_t1    = lem_change_var_wf g w1 s2 Empty (unbindT x1 w1 t1) p_w2g_t1 y
                                             ? lem_tsubFV_unbindT x1 w1 (FV y) t1
        p_y2g_t2    = lem_change_var_wf g w2 s2 Empty (unbindT x2 w2 t2) p_w2g_t2 y
                                             ? lem_tsubFV_unbindT x2 w2 (FV y) t2
        p_y3g_t1_t2 = lem_narrow_sub g Empty y s3 p_g_s3 s2 p_s3_s2 p_y2g_wf
                                             (unbindT x1 y t1) p_y2g_t1 (unbindT x2 y t2) p_y2g_t2 
                                             p_y2g_t1_t2
        p_z3g_t1_t2 = lem_change_var_subtype g y s3 Empty p_y3g_wf (unbindT x1 y t1) p_y3g_t1
                                             (unbindT x2 y t2) p_y3g_t2 p_y3g_t1_t2 z
                                             ? lem_tsubFV_unbindT x1 y (FV z) t1
                                             ? lem_tsubFV_unbindT x2 y (FV z) t2
        p_z3g_t1_t3 = lem_sub_trans (Cons z s3 g) p_z3g_wf (unbindT x1 z t1) p_z3g_t1
                           (unbindT x2 z t2) p_z3g_t2 (unbindT x3 z t3) p_z3g_t3    
                           p_z3g_t1_t2 p_z3g_t2_t3 
                    
lem_sub_trans g p_g_wf t p_g_t t' p_g_t' t'' p_g_t'' p_g_t_t'
              (SWitn _ v_y s_y p_vy_sy _t' y s'' p_g_t'_s''vy)
  = SWitn g v_y s_y p_vy_sy t y s'' p_g_t_s''vy
      where
--        y           = y_  ? lem_free_bound_in_env g t'' k'' p_g_t'' y_
        (WFExis _ _ _ p_g_sy _ w p_wg_s'') = p_g_t''
        p_wg_wf     = WFEBind g p_g_wf w s_y p_g_sy
        p_g_s''vy   = lem_subst_wf' g Empty w v_y s_y p_vy_sy p_wg_wf (unbindT y w s'') p_wg_s''
                                    ? lem_tsubFV_unbindT y w v_y s''
        p_g_t_s''vy = lem_sub_trans g p_g_wf t p_g_t t' p_g_t' (tsubBV y v_y s'')  
                                    p_g_s''vy p_g_t_t' p_g_t'_s''vy 
lem_sub_trans g p_g_wf t p_g_t t' p_g_t' t'' p_g_t''
        (SWitn _ v_x s_x p_vx_sx _t x s' p_g_t_s'vx) (SBind _ _x _sx _s' _t'' y p_yg_s'_t'')
  = lem_sub_trans g p_g_wf t p_g_t (tsubBV x v_x s') p_g_s'vx 
                  t'' p_g_t'' p_g_t_s'vx p_g_s'vx_t'' 
      where
        (WFExis _ _ _ p_g_sx _ w p_wg_s') = p_g_t' -- ? toProof ( t' === TExists x s_x s')
        p_wg_wf      = WFEBind g p_g_wf w s_x p_g_sx
        p_yg_wf      = WFEBind g p_g_wf y s_x p_g_sx
        p_yg_s'      = lem_change_var_wf g w s_x Empty (unbindT x w s') p_wg_s' y
                           ? lem_tsubFV_unbindT x w (FV y) s'
        p_yg_t''     = lem_weaken_wf g Empty t'' p_g_t'' y s_x
        p_g_s'vx     = lem_subst_wf' g Empty w v_x s_x p_vx_sx p_wg_wf (unbindT x w s') p_wg_s'
                                     ? lem_tsubFV_unbindT x w v_x s'
        p_g_s'vx_t'' = lem_subst_sub g Empty y v_x s_x p_vx_sx p_yg_wf (unbindT x y s') p_yg_s'
                                     t'' p_yg_t'' p_yg_s'_t''
                                     ? lem_tsubFV_unbindT x y v_x s'
                                     ? lem_tsubFV_notin y v_x t''
lem_sub_trans g p_g_wf t p_g_t t' p_g_t' t''_ p_g_t''
              (SBind _ x s_x s _t' y_ p_yg_s_t') p_g_t'_t''  = case (isTExists t) of 
  True  -> SBind g x s_x s t'' y p_yg_s_t''
      where
        t''         = t''_ ? lem_tfreeBV_empty g t''_ p_g_t'' 
        y           = y_ ? lem_free_bound_in_env g t'' p_g_t'' y_ 
        (WFExis _ _ _ p_g_sx _ w p_wg_s) = p_g_t
        p_yg_wf     = WFEBind g p_g_wf y s_x p_g_sx
        p_yg_s      = lem_change_var_wf g w s_x Empty (unbindT x w s) p_wg_s y
                          ? lem_tsubFV_unbindT x w (FV y) s
        p_yg_t'     = lem_weaken_wf g Empty t'  p_g_t'  y s_x
        p_yg_t''    = lem_weaken_wf g Empty t'' p_g_t'' y s_x
        p_yg_t'_t'' = lem_weaken_subtype g Empty p_g_wf t' p_g_t' t'' p_g_t'' p_g_t'_t'' y s_x
        p_yg_s_t''  = lem_sub_trans (Cons y s_x g) p_yg_wf (unbindT x y s) p_yg_s t'  p_yg_t'
                                    t'' p_yg_t'' p_yg_s_t' p_yg_t'_t'' 
  False -> impossible ""
lem_sub_trans g _ t _ t' _ t'' _ (SBase {}) (SFunc {}) = impossible ""
lem_sub_trans g _ t _ t' _ t'' _ (SBase {}) (SBind {}) = impossible ""
lem_sub_trans g _ t _ t' _ t'' _ (SFunc {}) (SBase {}) = impossible ""
lem_sub_trans g _ t _ t' _ t'' _ (SFunc {}) (SBind {}) = impossible ""
lem_sub_trans g _ t _ t' _ t'' _ (SWitn {}) (SBase {}) = impossible ""
lem_sub_trans g _ t _ t' _ t'' _ (SWitn {}) (SFunc {}) = impossible ""
