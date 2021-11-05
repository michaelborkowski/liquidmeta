{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module MainTheorems where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFTyping
import WellFormedness
import PrimitivesFTyping
import PrimitivesWFType
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
import SubstitutionLemmaWF
import DenotationsSelfify
import DenotationsSoundness
import PrimitivesSemantics
import PrimitivesDenotations
import LemmasExactness
import SubstitutionLemmaEnt
import SubstitutionLemmaTyp
import LemmasSubtypeClosed
import LemmasInvertLambda
import PrimitivesRefinements
import PrimitivesDeltaTyping

{-@ reflect foo64 @-}
foo64 x = Just x
foo64 :: a -> Maybe a

--------------------------------------------------------------------------------
--- | PROGRESS and PRESERVATION
--------------------------------------------------------------------------------

-- the big theorems                -- removed Set_emp (freeBV e) from the LHS case
{-@ thm_progress :: e:Expr -> t:Type -> ProofOf(HasType Empty e t)  
        -> Either { pf:_ | isValue e }  (Expr, Step)<{\e' pf -> propOf pf == Step e e'}> @-}
thm_progress :: Expr -> Type -> HasType -> Either Proof (Expr,Step) 
thm_progress c _b (TBC Empty _)           = Left ()
thm_progress c _b (TIC Empty _)           = Left ()
thm_progress x _t (TVar1 Empty _ _ _)     = Left ()
thm_progress x _t (TVar2 Empty _ _ _ _ _) = Left ()
thm_progress c _t (TPrm Empty _)          = Left ()
thm_progress e t  p_e_t@(TAbs {})         = Left () {-? lem_freeBV_empty Empty e t p_e_t WFEEmpty-}
thm_progress _e _t p_e_t@(TApp Empty e1 x t_x t p_e1_txt e2 p_e2_tx) = case e1 of
      (Prim p)      -> case (thm_progress e2 t_x p_e2_tx) of
          Left ()               -> Right (delta p e2_compat, EPrim p e2_compat)
            where
              e2_compat = e2 ? lem_prim_compat_in_tapp p e2 (TExists x t_x t) p_e_t
          Right (e2', p_e2_e2') -> Right (App (Prim p) e2', EApp2 e2 e2' p_e2_e2' (Prim p))  
      (Lambda x e') -> case (thm_progress e2 t_x p_e2_tx) of
          Left ()               -> Right (subBV x e2 e', EAppAbs x e' e2)
          Right (e2', p_e2_e2') -> Right (App (Lambda x e') e2', EApp2 e2 e2' p_e2_e2' (Lambda x e'))
      (_)           -> case (isValue e1) of
          False                 -> Right (App e1' e2, EApp1 e1 e1' p_e1_e1' e2)
              where
                  Right (e1', p_e1_e1') = thm_progress e1 (TFunc x t_x t) p_e1_txt
          True                  -> impossible ("by lemma" ? lemma_function_values e1 (erase t_x) (erase t)
                                                                                  p_e1_er_txt)
              where
                  p_e1_er_txt = lem_typing_hasftype Empty e1 (TFunc x t_x t) p_e1_txt WFEEmpty
thm_progress _e _t (TSub Empty e s p_e_s t p_t p_s_t)
      = case (thm_progress e s p_e_s) of
          Left ()               -> Left ()
          Right (e', p_e_e')    -> Right (e', p_e_e') 

-- Left () means the case is contradictory and cannot occur
{-@ thm_preservation :: e:Expr -> t:Type -> ProofOf(HasType Empty e t) -> e':Expr
        -> ProofOf(Step e e') -> Either { pf:_ | false } { pf:_ | propOf pf == HasType Empty e' t} @-}
thm_preservation :: Expr -> Type -> HasType -> Expr -> Step -> Either Proof HasType 
thm_preservation e t (TBC _emp b)  e' st_e_e'       = Left () ? lem_value_stuck e e' st_e_e'
thm_preservation e t (TIC _emp n)  e' st_e_e'       = Left () ? lem_value_stuck e e' st_e_e' 
thm_preservation e t (TVar1 _ _ _ _) e' st_e_e'     = Left () ? lem_value_stuck e e' st_e_e'
thm_preservation e t (TVar2 _ _ _ _ _ _) e' st_e_e' = Left () ? lem_value_stuck e e' st_e_e'
thm_preservation e t (TPrm _emp c) e' st_e_e'       = Left () ? lem_value_stuck e e' st_e_e'
thm_preservation e t (TAbs {}) e' st_e_e'           = Left () ? lem_value_stuck e e' st_e_e'
thm_preservation e t p_e_t@(TApp Empty (Prim c) x t_x t' p_c_txt' e2 p_e2_tx) e' st_e_e'
  = case (thm_progress e2 t_x p_e2_tx) of
      Left ()                -> Right p_del_ex_t' ? lem_sem_det e e' st_e_e' (delta_c_e2) (EPrim c e2)
        where
          delta_c_e2   = delta c (e2 ? lem_prim_compat_in_tapp c e2 (TExists x t_x t') p_e_t)
          p_del_t'e2   = lem_delta_typ c e2 x t_x t' p_c_txt' p_e2_tx 
          p_emp_ex_t'  = lem_typing_wf Empty e t p_e_t WFEEmpty
          (WFExis _ _ _ _ _t' y p_y_t') = p_emp_ex_t'
          p_t'e2_ex_t' = lem_witness_sub Empty e2 t_x p_e2_tx WFEEmpty x t' y p_y_t'
          p_del_ex_t'  = TSub Empty (delta_c_e2) (tsubBV x e2 t') p_del_t'e2 
                              (TExists x t_x t') p_emp_ex_t' p_t'e2_ex_t' 
      Right (e2', st_e2_e2') -> Right (TApp Empty (Prim c) x t_x t' p_c_txt' e2' p_e2'_tx)
        where
          Right p_e2'_tx  = thm_preservation e2 t_x p_e2_tx e2' st_e2_e2' 
                                ? lem_sem_det e e' st_e_e' (App (Prim c) e2') 
                                              (EApp2 e2 e2' st_e2_e2' (Prim c) )
thm_preservation e t p_e_t@(TApp Empty (Lambda w e1) x t_x t' p_lam_txt' e2 p_e2_tx) e' st_e_e'
  = case (thm_progress e2 t_x p_e2_tx) of
      Left ()                -> Right p_e1e2_ex_t' ? lem_sem_det e e' st_e_e' 
                                                         (subBV w e2 e1) (EAppAbs w e1 e2)
        where
          (y, p_e1_t')        = lem_invert_tabs Empty w e1 x t_x t' p_lam_txt' WFEEmpty
          {-(TAbs _ _ _tx p_tx _ _ y p_e1_t') = p_lam_txt' -- y:t_x |- e1 : t'-}
          p_tx                = lem_typing_wf Empty e2 t_x p_e2_tx WFEEmpty
          p_wf_ytx            = WFEBind Empty WFEEmpty y t_x p_tx
          p_e1e2_t'e2         = lem_subst_typ Empty Empty y e2 t_x p_e2_tx p_wf_ytx
                                              (unbind w y e1) (unbindT x y t') p_e1_t'
          p_emp_ex_t'         = lem_typing_wf Empty e t p_e_t WFEEmpty
          (WFExis _ _ _ _ _ y' p_y_t') = p_emp_ex_t'
          p_t'e2_ex_t'        = lem_witness_sub Empty e2 t_x p_e2_tx WFEEmpty x t' y' p_y_t'
          p_e1e2_ex_t'        = TSub Empty (subBV w e2 e1) (tsubBV x e2 t') 
                                     (p_e1e2_t'e2 ? lem_subFV_unbind w y e2 e1
                                                  ? lem_tsubFV_unbindT x y e2 t')
                                     (TExists x t_x t') p_emp_ex_t' p_t'e2_ex_t'
      Right (e2', st_e2_e2') -> Right (TApp Empty (Lambda w e1) x t_x t' p_lam_txt' e2' p_e2'_tx)
        where
          Right p_e2'_tx      = thm_preservation e2 t_x p_e2_tx e2' st_e2_e2'  
                                    ? lem_sem_det e e' st_e_e' (App (Lambda w e1) e2') 
                                                  (EApp2 e2 e2' st_e2_e2' (Lambda w e1))
thm_preservation e t p_e_t@(TApp Empty e1 x t_x t' p_e1_txt' e2 p_e2_tx) e' st_e_e' 
  = case (thm_progress e1 (TFunc x t_x t') p_e1_txt') of
      Left ()                -> impossible ("by lemma" ? lemma_function_values e1 (erase t_x) (erase t')
                                                                                  p_e1_er_txt')
        where
          p_e1_er_txt'        = lem_typing_hasftype Empty e1 (TFunc x t_x t') p_e1_txt' WFEEmpty
      Right (e1', st_e1_e1') -> Right (TApp Empty e1' x t_x t' p_e1'_txt' e2 p_e2_tx)
        where
          Right p_e1'_txt'    = thm_preservation e1 (TFunc x t_x t') p_e1_txt' e1' st_e1_e1'
                                    ? lem_sem_det e e' st_e_e' (App e1' e2)
                                                  (EApp1 e1 e1' st_e1_e1' e2)
thm_preservation e t (TSub Empty _e s p_e_s _t p_t p_s_t) e' st_e_e'
  = case (thm_preservation e s p_e_s e' st_e_e') of
      Left ()      -> Left ()
      Right p_e'_s -> Right (TSub Empty e' s p_e'_s t p_t p_s_t)

{-@ thm_soundness :: e:Expr -> e':Expr -> ProofOf(EvalsTo e e') -> t:Type 
        -> ProofOf(HasType Empty e t) -> ProofOf(HasType Empty e' t) @-}
thm_soundness :: Expr -> Expr -> EvalsTo -> Type -> HasType -> HasType
thm_soundness e e' ev_e_e' t p_e_t = case ev_e_e' of
  (Refl e)                             -> p_e_t
  (AddStep _e e1 st_e_e1 _e' ev_e1_e') -> thm_soundness e1 e' ev_e1_e' t p_e1_t
    where
      Right p_e1_t = thm_preservation e t p_e_t e1 st_e_e1 
