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
import SubstitutionWFAgain
import DenotationsSelfify
import PrimitivesSemantics
import PrimitivesDenotations
import DenotationsSoundness
import LemmasExactness
import SubstitutionLemmaEnt
import SubstitutionLemmaTyp
import EntailmentsExtra
import LemmasNarrowingEnt
import LemmasNarrowingTyp

{-@ reflect foo71 @-}
foo71 x = Just x
foo71 :: a -> Maybe a

{-@ lem_sub_trans_sbase :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> k':Kind -> ProofOf(WFType g t' k') 
            -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t'  && isSBase p_t_t' }
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' && isSBase p_t'_t'' }
            -> ProofOf(Subtype g t t'') / [subtypSize' p_t_t' + subtypSize' p_t'_t'', 0] @-}
lem_sub_trans_sbase :: Env -> WFEnv -> Type -> Kind -> WFType -> Type -> Kind -> WFType
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_sbase g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t''
              (SBase _  x1  b  p1 x2 p2 y_ p_yp1_p2) (SBase _ _x2 _b _p2 x3 p3 z p_zp2_p3)
  = SBase g x1 b p1 x3 p3 y p_yp1_p3
      where
        y        = y_ ? lem_free_bound_in_env g t   k   p_g_t   y_
                      ? lem_free_bound_in_env g t'' k'' p_g_t'' y_
        p_zg_wf  = WFEBind g p_g_wf z (TRefn b x2 p2) k' p_g_t' 
        p_yp2_p3 = lem_change_var_ent g z (TRefn b x2 p2) Empty p_zg_wf 
                      (unbind 0 z p3 ? lem_free_subset_binds g t'' k'' p_g_t'') p_zp2_p3 y
                      ? lem_subFV_unbind 0 z (FV y) p3
        p_yp1_p3 = lem_entails_trans g p_g_wf b x1 p1 k p_g_t x2 p2 k' p_g_t' x3 p3 y 
                                     p_yp1_p2 p_yp2_p3 

{-@ lem_sub_trans_sfunc :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> k':Kind -> ProofOf(WFType g t' k') 
            -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t'  && isSFunc p_t_t' }
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' && isSFunc p_t'_t'' }
            -> ProofOf(Subtype g t t'') / [subtypSize' p_t_t' + subtypSize' p_t'_t'', 0] @-}
lem_sub_trans_sfunc :: Env -> WFEnv -> Type -> Kind -> WFType -> Type -> Kind -> WFType
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_sfunc g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t''
              (SFunc _  x1  s1 x2 s2 p_s2_s1  t1 t2 y  p_y2g_t1_t2)
              (SFunc _ _x2 _s2 x3 s3 p_s3_s2 _t2 t3 z_ p_z3g_t2_t3)
  = SFunc g x1 s1 x3 s3 p_s3_s1 t1 t3 z p_z3g_t1_t3
      where
        z           = z_ ? lem_free_bound_in_env g t   k   p_g_t   z_
                         ? lem_free_bound_in_env g t'' k'' p_g_t'' z_
        (WFFunc _ _ _ k_s1 p_g_s1 _ k_t1 w1 p_w1g_t1) = lem_wffunc_for_wf_tfunc g x1 s1 t1 k   p_g_t
        (WFFunc _ _ _ k_s2 p_g_s2 _ k_t2 w2 p_w2g_t2) = lem_wffunc_for_wf_tfunc g x2 s2 t2 k'  p_g_t' 
        (WFFunc _ _ _ k_s3 p_g_s3 _ k_t3 w3 p_w3g_t3) = lem_wffunc_for_wf_tfunc g x3 s3 t3 k'' p_g_t'' 
        p_s3_s1     = lem_sub_trans g p_g_wf s3 k_s3 p_g_s3 s2 k_s2 p_g_s2 
                                             s1 k_s1 p_g_s1 p_s3_s2 p_s2_s1
        p_w1g_wf    = WFEBind g p_g_wf w1 s3 k_s3 p_g_s3
        p_w2g_wf    = WFEBind g p_g_wf w2 s3 k_s3 p_g_s3
        p_w3g_wf    = WFEBind g p_g_wf w3 s3 k_s3 p_g_s3
        p_y3g_wf    = WFEBind g p_g_wf y s3 k_s3 p_g_s3
        p_z3g_wf    = WFEBind g p_g_wf z s3 k_s3 p_g_s3
        p_w3g_t1    = lem_subtype_in_env_wf g Empty w1 s3 s1 p_s3_s1 (unbindT x1 w1 t1) k_t1 p_w1g_t1
        p_w3g_t2    = lem_subtype_in_env_wf g Empty w2 s3 s2 p_s3_s2 (unbindT x2 w2 t2) k_t2 p_w2g_t2
        p_y3g_t1    = lem_change_var_wf' g w1 s3 Empty p_w1g_wf (unbindT x1 w1 t1) k_t1 p_w3g_t1 y
                                         ? lem_tsubFV_unbindT x1 w1 (FV y) t1
        p_y3g_t2    = lem_change_var_wf' g w2 s3 Empty p_w2g_wf (unbindT x2 w2 t2) k_t2 p_w3g_t2 y
                                         ? lem_tsubFV_unbindT x2 w2 (FV y) t2
        p_z3g_t1    = lem_change_var_wf' g w1 s3 Empty p_w1g_wf (unbindT x1 w1 t1) k_t1 p_w3g_t1 z
                                         ? lem_tsubFV_unbindT x1 w1 (FV z) t1
        p_z3g_t2    = lem_change_var_wf' g w2 s3 Empty p_w2g_wf (unbindT x2 w2 t2) k_t2 p_w3g_t2 z
                                         ? lem_tsubFV_unbindT x2 w2 (FV z) t2
        p_z3g_t3    = lem_change_var_wf' g w3 s3 Empty p_w3g_wf (unbindT x3 w3 t3) k_t3 p_w3g_t3 z
                                         ? lem_tsubFV_unbindT x3 w3 (FV z) t3
        p_y2g_wf    = WFEBind g p_g_wf y  s2 k_s2 p_g_s2
        p_w12g_wf   = WFEBind g p_g_wf w1 s2 k_s2 p_g_s2
        p_w22g_wf   = WFEBind g p_g_wf w2 s2 k_s2 p_g_s2
        p_w2g_t1    = lem_subtype_in_env_wf g Empty w1 s2 s1 p_s2_s1 (unbindT x1 w1 t1) k_t1 p_w1g_t1
        p_y2g_t1    = lem_change_var_wf' g w1 s2 Empty p_w12g_wf (unbindT x1 w1 t1) k_t1 p_w2g_t1 y
                                             ? lem_tsubFV_unbindT x1 w1 (FV y) t1
        p_y2g_t2    = lem_change_var_wf' g w2 s2 Empty p_w22g_wf (unbindT x2 w2 t2) k_t2 p_w2g_t2 y
                                             ? lem_tsubFV_unbindT x2 w2 (FV y) t2
        p_y3g_t1_t2 = lem_narrow_sub g Empty y s3 k_s3 p_g_s3 s2 p_s3_s2 p_y2g_wf
                                     (unbindT x1 y t1) k_t1 p_y2g_t1 
                                     (unbindT x2 y t2) k_t2 p_y2g_t2 p_y2g_t1_t2
        p_z3g_t1_t2 = lem_change_var_subtype g y s3 Empty p_y3g_wf (unbindT x1 y t1) k_t1 p_y3g_t1
                                             (unbindT x2 y t2) k_t2 p_y3g_t2 p_y3g_t1_t2 z
                                             ? lem_tsubFV_unbindT x1 y (FV z) t1
                                             ? lem_tsubFV_unbindT x2 y (FV z) t2
        p_z3g_t1_t3 = lem_sub_trans (Cons z s3 g) p_z3g_wf (unbindT x1 z t1) k_t1 p_z3g_t1
                           (unbindT x2 z t2) k_t2 p_z3g_t2 (unbindT x3 z t3) k_t3 p_z3g_t3    
                           p_z3g_t1_t2 p_z3g_t2_t3

{-@ lem_sub_trans_spoly :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> k':Kind -> ProofOf(WFType g t' k') 
            -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t'  && isSPoly p_t_t' }
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' && isSPoly p_t'_t'' }
            -> ProofOf(Subtype g t t'') / [subtypSize' p_t_t' + subtypSize' p_t'_t'', 0] @-}
lem_sub_trans_spoly :: Env -> WFEnv -> Type -> Kind -> WFType -> Type -> Kind -> WFType
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_spoly g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t''
              (SPoly _ a1 k1 t1 a2 t2 a'_ p_a'g_t1_t2) (SPoly _ _ _ _ a3 t3 a'' p_a''g_t2_t3)
  = SPoly g a1 k1 t1 a3 t3 a' p_a'g_t1_t3
      where
        a'          = a'_ ? lem_free_bound_in_env g t   k   p_g_t   a'_
                          ? lem_free_bound_in_env g t'' k'' p_g_t'' a'_
        p_g_t_st    = if k   == Star then p_g_t   else WFKind g t   p_g_t
        p_g_t'_st   = if k'  == Star then p_g_t'  else WFKind g t'  p_g_t'
        p_g_t''_st  = if k'' == Star then p_g_t'' else WFKind g t'' p_g_t''
        (WFPoly _ _ _ _ k_t1 a'1 p_a'1g_t1) = lem_wfpoly_for_wf_tpoly g a1 k1 t1 p_g_t_st
        (WFPoly _ _ _ _ k_t2 a'2 p_a'2g_t2) = lem_wfpoly_for_wf_tpoly g a2 k1 t2 p_g_t'_st
        (WFPoly _ _ _ _ k_t3 a'3 p_a'3g_t3) = lem_wfpoly_for_wf_tpoly g a3 k1 t3 p_g_t''_st
        p_a'1g_wf   = WFEBindT g p_g_wf a'1 k1        
        p_a'2g_wf   = WFEBindT g p_g_wf a'2 k1        
        p_a'3g_wf   = WFEBindT g p_g_wf a'3 k1
        p_a'g_wf    = WFEBindT g p_g_wf a'  k1        
        p_a''g_wf   = WFEBindT g p_g_wf a'' k1
        p_a'g_t1    = lem_change_tvar_wf' g a'1 k1 Empty p_a'1g_wf (unbind_tvT a1 a'1 t1) k_t1
                                          p_a'1g_t1 a'  ? lem_tchgFTV_unbind_tvT a1 a'1 a'  t1
        p_a'g_t2    = lem_change_tvar_wf' g a'2 k1 Empty p_a'2g_wf (unbind_tvT a2 a'2 t2) k_t2
                                          p_a'2g_t2 a'  ? lem_tchgFTV_unbind_tvT a2 a'2 a'  t2
        p_a''g_t2   = lem_change_tvar_wf' g a'2 k1 Empty p_a'2g_wf (unbind_tvT a2 a'2 t2) k_t2
                                          p_a'2g_t2 a'' ? lem_tchgFTV_unbind_tvT a2 a'2 a'' t2
        p_a'g_t3    = lem_change_tvar_wf' g a'3 k1 Empty p_a'3g_wf (unbind_tvT a3 a'3 t3) k_t3
                                          p_a'3g_t3 a'  ? lem_tchgFTV_unbind_tvT a3 a'3 a'  t3
        p_a''g_t3   = lem_change_tvar_wf' g a'3 k1 Empty p_a'3g_wf (unbind_tvT a3 a'3 t3) k_t3
                                          p_a'3g_t3 a'' ? lem_tchgFTV_unbind_tvT a3 a'3 a'' t3
        p_a'g_t2_t3 = lem_change_tvar_subtype g a'' k1 Empty p_a''g_wf 
                                    (unbind_tvT a2 a'' t2) k_t2 p_a''g_t2 
                                    (unbind_tvT a3 a'' t3) k_t3 p_a''g_t3 p_a''g_t2_t3 a'
                                    ? lem_tchgFTV_unbind_tvT a2 a'' a' t2
                                    ? lem_tchgFTV_unbind_tvT a3 a'' a' t3
        p_a'g_t1_t3 = lem_sub_trans (ConsT a' k1 g) p_a'g_wf (unbind_tvT a1 a' t1) k_t1 p_a'g_t1
                                    (unbind_tvT a2 a' t2) k_t2 p_a'g_t2 (unbind_tvT a3 a' t3) 
                                    k_t3 p_a'g_t3 p_a'g_t1_t2 p_a'g_t2_t3

{-@ lem_sub_trans_switnR :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> k':Kind -> ProofOf(WFType g t' k') 
            -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t' }
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' && isSWitn p_t'_t'' }
            -> ProofOf(Subtype g t t'') / [subtypSize' p_t_t' + subtypSize' p_t'_t'', 0] @-}
lem_sub_trans_switnR :: Env -> WFEnv -> Type -> Kind -> WFType -> Type -> Kind -> WFType
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
lem_sub_trans_switnR g p_g_wf t k p_g_t t' k' p_g_t' t'' k'' p_g_t'' p_g_t_t'
                     (SWitn _ v_y s_y p_vy_sy _t' y s'' p_g_t'_s''vy)
  = SWitn g v_y s_y p_vy_sy t y s'' p_g_t_s''vy
      where
        (WFExis _ _ _ k_sy p_g_sy _ _ w p_wg_s'') 
                    = lem_wfexis_for_wf_texists g y s_y s'' k'' p_g_t''
        p_wg_wf     = WFEBind g p_g_wf w s_y k_sy p_g_sy
        p_g_s''vy   = lem_subst_wf' g Empty w v_y s_y p_vy_sy p_wg_wf (unbindT y w s'') k'' p_wg_s''
                                    ? lem_tsubFV_unbindT y w v_y s''
        p_g_t_s''vy = lem_sub_trans g p_g_wf t k p_g_t t' k' p_g_t' (tsubBV y v_y s'') k'' 
                                    p_g_s''vy p_g_t_t' p_g_t'_s''vy

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


{-@ lem_sub_trans :: g:Env -> ProofOf(WFEnv g) -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> t':Type -> k':Kind -> ProofOf(WFType g t' k') 
            -> t'':Type -> k'':Kind -> ProofOf(WFType g t'' k'')
            -> { p_t_t':Subtype   | propOf p_t_t'   == Subtype g t  t' }
            -> { p_t'_t'':Subtype | propOf p_t'_t'' == Subtype g t' t'' }
            -> ProofOf(Subtype g t t'') / [subtypSize' p_t_t' + subtypSize' p_t'_t'', 2] @-}
lem_sub_trans :: Env -> WFEnv -> Type -> Kind -> WFType -> Type -> Kind -> WFType
                     -> Type -> Kind -> WFType -> Subtype -> Subtype -> Subtype
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
