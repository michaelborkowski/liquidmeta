{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module MainTheorems where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof,(?))
import qualified Data.Set as S

import Basics
import Semantics
import SystemFTyping
import BasicPropsSubstitution
import BasicPropsEnvironments
import WellFormedness
import PrimitivesFTyping
import BasicPropsWellFormedness
import Typing
import LemmasTyping
import LemmasSubtyping
import SubstitutionLemmaTyp
import SubstitutionLemmaTypTV
import LemmasInversion
import PrimitivesDeltaTyping

--------------------------------------------------------------------------------
--- | PROGRESS and PRESERVATION
--------------------------------------------------------------------------------

{-@ thm_progress :: e:Expr -> t:Type -> ProofOf(HasType Empty e t)  
        -> Either { pf:_ | isValue e }  (Expr, Step)<{\e' pf -> propOf pf == Step e e'}> @-}
thm_progress :: Expr -> Type -> HasType -> Either Proof (Expr,Step) 
thm_progress c _b (TBC Empty _)             = Left ()
thm_progress c _b (TIC Empty _)             = Left ()
thm_progress x _t (TVar1 Empty _ _ _ _)     = Left ()
thm_progress x _t (TVar2 _ Empty _ _ _ _ _) = Left ()
thm_progress x _t (TVar3 _ Empty _ _ _ _ _) = Left ()
thm_progress c _t (TPrm Empty _)            = Left ()
thm_progress e t  p_e_t@(TAbs {})           = Left () 
thm_progress _e _t p_e_t@(TApp _ Empty e1 t_x t p_e1_txt e2 p_e2_tx) = case e1 of
      (Prim p)      -> case (thm_progress e2 t_x p_e2_tx) of
          Left ()               -> Right (delta p e2_compat, EPrim p e2_compat)
            where
              e2_compat = e2 ? lem_prim_compat_in_tapp p e2 (TExists t_x t) p_e_t
          Right (e2', p_e2_e2') -> Right (App (Prim p) e2', EApp2 e2 e2' p_e2_e2' (Prim p))  
      (Lambda e') -> case (thm_progress e2 t_x p_e2_tx) of
          Left ()               -> Right (subBV e2 e', EAppAbs e' e2)
          Right (e2', p_e2_e2') -> Right (App (Lambda e') e2', EApp2 e2 e2' p_e2_e2' (Lambda e'))
      (_)           -> case (isValue e1) of
          False                 -> Right (App e1' e2, EApp1 e1 e1' p_e1_e1' e2)
              where
                  Right (e1', p_e1_e1') = thm_progress e1 (TFunc t_x t) p_e1_txt
          True                  -> impossible ("by lemma" ? lemma_function_values e1 (erase t_x) (erase t)
                                                                                  p_e1_er_txt)
              where
                  p_e1_er_txt = lem_typing_hasftype Empty e1 (TFunc t_x t) p_e1_txt WFEEmpty
thm_progress e t  p_e_t@(TAbsT {})        = Left () 
thm_progress _e t p_e_t@(TAppT _ Empty e' k s p_e'_as t' p_emp_t') = case e' of
      (Prim c)         -> Right (deltaT c t'_,     EPrimT c t'_)
          where
            t'_ = t' ? lem_prim_compatT_in_tappT c t' t p_e_t 
      (LambdaT k' e'') -> Right (subBTV t' e'', EAppTAbs k' e'' t')
      _                 -> case (isValue e') of
          False         -> Right (AppT e'' t',     EAppT e' e'' p_e'_e'' t')
              where
                  Right (e'', p_e'_e'') = thm_progress e' (TPoly k s) p_e'_as
          True          -> impossible ("by lemmas" ? lemma_tfunction_values e' k (erase s) p_e'_er_as)
              where
                  p_e'_er_as = lem_typing_hasftype Empty e' (TPoly k s) p_e'_as WFEEmpty
thm_progress _e _t (TLet _ Empty e1 tx p_e1_tx e2 t _ p_t y p_e2_t)
      = case (thm_progress e1 tx p_e1_tx) of
          Left ()               -> Right (subBV e1 e2, ELetV e1 e2)
          Right (e1', p_e1_e1') -> Right (Let e1' e2,  ELet e1 e1' p_e1_e1' e2)
thm_progress _e _t (TAnn _ Empty e1 t p_e1_t)
      = case (thm_progress e1 t p_e1_t) of
          Left ()               -> Right (e1, EAnnV e1 t)
          Right (e1', p_e1_e1') -> Right (Annot e1' t, EAnn e1 e1' p_e1_e1' t)
thm_progress _e _t (TSub _ Empty e s p_e_s t k p_t p_s_t)
      = case (thm_progress e s p_e_s) of
          Left ()               -> Left ()
          Right (e', p_e_e')    -> Right (e', p_e_e') 

-- Left () means the case is contradictory and cannot occur
{-@ thm_preservation :: e:Expr -> t:Type -> ProofOf(HasType Empty e t) -> e':Expr
        -> ProofOf(Step e e') -> Either { pf:_ | false } { pf:_ | propOf pf == HasType Empty e' t} @-}
thm_preservation :: Expr -> Type -> HasType -> Expr -> Step -> Either Proof HasType 
thm_preservation e t (TBC _emp b)  e' st_e_e'         = Left () ? lem_value_stuck e e' st_e_e'
thm_preservation e t (TIC _emp n)  e' st_e_e'         = Left () ? lem_value_stuck e e' st_e_e' 
thm_preservation e t (TVar1 _ _ _ _ _) e' st_e_e'     = Left () ? lem_value_stuck e e' st_e_e'
thm_preservation e t (TVar2 _ _ _ _ _ _ _) e' st_e_e' = Left () ? lem_value_stuck e e' st_e_e'
thm_preservation e t (TVar3 _ _ _ _ _ _ _) e' st_e_e' = Left () ? lem_value_stuck e e' st_e_e'
thm_preservation e t (TPrm _emp c) e' st_e_e'         = Left () ? lem_value_stuck e e' st_e_e'
thm_preservation e t (TAbs {}) e' st_e_e'             = Left () ? lem_value_stuck e e' st_e_e'
thm_preservation e t p_e_t@(TApp _ Empty (Prim c) t_x t' p_c_txt' e2 p_e2_tx) e' st_e_e'
  = case (thm_progress e2 t_x p_e2_tx) of
      Left ()                -> Right p_del_ex_t' ? lem_sem_det e e' st_e_e' (delta_c_e2) (EPrim c e2)
        where
          delta_c_e2   = delta c (e2 ? lem_prim_compat_in_tapp c e2 (TExists t_x t') p_e_t)
          p_del_ex_t'  = lem_delta_typ c e2 t_x t' p_c_txt' p_e2_tx
      Right (e2', st_e2_e2') -> Right (TApp n Empty (Prim c) t_x t' p_c_txt' e2' p_e2'_tx)
        where
          Right p_e2'_tx  = thm_preservation e2 t_x p_e2_tx e2' st_e2_e2' 
                                ? lem_sem_det e e' st_e_e' (App (Prim c) e2') 
                                              (EApp2 e2 e2' st_e2_e2' (Prim c) )
          n               = max (typSize p_c_txt') (typSize p_e2'_tx)
thm_preservation e t p_e_t@(TApp _ Empty (Lambda e1) t_x t' p_lam_txt' e2 p_e2_tx) e' st_e_e'
  = case (thm_progress e2 t_x p_e2_tx) of
      Left ()                -> Right p_e1e2_ex_t' ? lem_sem_det e e' st_e_e' 
                                                         (subBV e2 e1) (EAppAbs e1 e2)
        where
          (TAbs _ _ _ _ _ _ _ nms mk_p_e1_t')        
                              = lem_invert_tabs Empty e1 t_x t' p_lam_txt' WFEEmpty
          y                   = fresh nms
          p_e1e2_t'e2         = lem_subst_typ Empty Empty y e2 t_x p_e2_tx WFEEmpty
                                              (unbind y e1) (unbindT y t') (mk_p_e1_t' y)
                              ? lem_subFV_unbind    y e2 (e1
                                  ? lem_fv_subset_binds Empty (Lambda e1) (TFunc t_x t') 
                                                        p_lam_txt' WFEEmpty)
                              ? lem_tsubFV_unbindT  y e2 (t' 
                                  ? lem_free_bound_in_env Empty (TExists t_x t') Star p_emp_ex_t' y)
          p_emp_ex_t'         = lem_typing_wf Empty e t p_e_t WFEEmpty
          p_t'e2_ex_t'        = lem_witness_sub Empty e2 t_x p_e2_tx t' Star p_emp_ex_t' WFEEmpty
          p_e1e2_ex_t'        = TSub n Empty (subBV e2 e1) (tsubBV e2 t') p_e1e2_t'e2
                                     (TExists t_x t') Star p_emp_ex_t' p_t'e2_ex_t'
          n                   = max (typSize p_e1e2_t'e2) (subtypSize p_t'e2_ex_t')
      Right (e2', st_e2_e2') -> Right (TApp n Empty (Lambda e1) t_x t' p_lam_txt' e2' p_e2'_tx)
        where
          Right p_e2'_tx      = thm_preservation e2 t_x p_e2_tx e2' st_e2_e2'  
                                    ? lem_sem_det e e' st_e_e' (App (Lambda e1) e2') 
                                                  (EApp2 e2 e2' st_e2_e2' (Lambda e1))
          n                   = max (typSize p_lam_txt') (typSize p_e2'_tx)
thm_preservation e t p_e_t@(TApp _ Empty e1 t_x t' p_e1_txt' e2 p_e2_tx) e' st_e_e' 
  = case (thm_progress e1 (TFunc t_x t') p_e1_txt') of
      Left ()                -> impossible ("by lemma" ? lemma_function_values e1 (erase t_x) (erase t')
                                                                                  p_e1_er_txt')
        where
          p_e1_er_txt'        = lem_typing_hasftype Empty e1 (TFunc t_x t') p_e1_txt' WFEEmpty
      Right (e1', st_e1_e1') -> Right (TApp n Empty e1' t_x t' p_e1'_txt' e2 p_e2_tx)
        where
          Right p_e1'_txt'    = thm_preservation e1 (TFunc t_x t') p_e1_txt' e1' st_e1_e1'
                                    ? lem_sem_det e e' st_e_e' (App e1' e2)
                                                  (EApp1 e1 e1' st_e1_e1' e2)
          n                   = max (typSize p_e1'_txt') (typSize p_e2_tx)
thm_preservation e t (TAbsT {}) e' st_e_e'          = Left () ? lem_value_stuck e e' st_e_e'
thm_preservation e t p_e_t@(TAppT _ Empty (Prim c) k s p_e1_as t'_ p_emp_t') e' st_e_e' 
  = Right p_delT_st' -- deltaT c t' :: tsubBTV a t' s
          ? lem_sem_det e e' st_e_e' (deltaT c t') (EPrimT c t') 
        where
          t'         = t'_ ? lem_prim_compatT_in_tappT c t'_ t p_e_t
          p_delT_st' = lem_deltaT_typ c k s p_e1_as t' p_emp_t'
thm_preservation e t (TAppT _ Empty (LambdaT k1 e2) k s p_e1_as t' p_emp_t') e' st_e_e' 
  = Right p_e2t'_st' -- subBTV a1 t' e2 :: tsubBTV a t' s      
          ? lem_sem_det e e' st_e_e' (subBTV t' e2) (EAppTAbs k1 e2 t') 
        where
          (TAbsT _ _ _ _ _ nms mk_p_e2_s)
                          = lem_invert_tabst Empty k1 e2 s (p_e1_as 
                          ? lem_lambdaT_tpoly_same_kind Empty k1 e2 k s p_e1_as WFEEmpty) WFEEmpty
          a               = fresh nms
          p_emp_ks        = lem_typing_wf Empty (LambdaT k1 e2) (TPoly k s) p_e1_as WFEEmpty
          p_e2t'_st'      = lem_subst_tv_typ Empty Empty a t' k p_emp_t' WFEEmpty
                                             (unbind_tv a e2) (unbind_tvT a s) (mk_p_e2_s a)
                          ? lem_subFTV_unbind_tv   a t' (e2
                               ? lem_fv_subset_binds Empty (LambdaT k1 e2) (TPoly k s) p_e1_as WFEEmpty)
                          ? lem_tsubFTV_unbind_tvT a t' (s
                               ? lem_free_bound_in_env Empty (TPoly k s) Star p_emp_ks a)
thm_preservation e t (TAppT _ Empty e1 k s p_e1_as t' p_emp_t') e' st_e_e' 
  = case (thm_progress e1 (TPoly k s) p_e1_as) of
        Left ()           -> impossible ("by" ? lemma_tfunction_values e1 k (erase s) p_e1_er_as)
              where
                p_e1_er_as = lem_typing_hasftype Empty e1 (TPoly k s) p_e1_as WFEEmpty
        Right (e1', st_e1_e1') -> Right (TAppT n Empty e1' k s p_e1'_as t' p_emp_t')
          where
            Right p_e1'_as = thm_preservation e1 (TPoly k s) p_e1_as e1' st_e1_e1'
                              ? lem_sem_det e e' st_e_e' (AppT e1' t') (EAppT e1 e1' st_e1_e1' t')
            n              = typSize p_e1'_as
thm_preservation e t p_e_t@(TLet n Empty e_x t_x p_ex_tx e1 _t k p_emp_t nms mk_p_e1_t) e' st_e_e'
  = case (thm_progress e_x t_x p_ex_tx) of 
      Left ()                 -> Right p_e1ex_t
                                     ? lem_sem_det e e' st_e_e' (subBV e_x e1) (ELetV e_x e1)
                                     ? lem_free_bound_in_env Empty t k p_emp_t y
        where
          y                    = fresh nms
          {-@ p_e1ex_t :: ProofOf(HasType Empty (subBV e_x e1) t) @-} -- (tsubBV x e_x t)) @- }
          p_e1ex_t             = lem_subst_typ Empty Empty y e_x t_x p_ex_tx WFEEmpty 
                                           (unbind y e1) (unbindT y t) (mk_p_e1_t y)
                                           ? lem_subFV_unbind y e_x (e1 
                                               ? lem_fv_subset_binds Empty e t p_e_t WFEEmpty)
                                           ? lem_tsubFV_unbindT y e_x (t
                                               ? lem_free_bound_in_env Empty t k p_emp_t y)
                                           ? lem_empty_concatE Empty
                                           ? lem_tsubBV_at_lct_at 0 e_x 0 0 (t 
                                               ? lem_wftype_islct Empty t k p_emp_t)
      Right (e_x', st_ex_ex') -> Right (TLet n' Empty e_x' t_x p_ex'_tx e1 t k p_emp_t nms mk_p_e1_t)
        where
          Right p_ex'_tx       = thm_preservation e_x t_x p_ex_tx e_x' st_ex_ex'
                                     ? lem_sem_det e e' st_e_e' (Let e_x' e1) 
                                                   (ELet e_x e_x' st_ex_ex' e1)
          n'                   = max n (typSize p_ex'_tx)
thm_preservation e t (TAnn _ Empty e1 t_ p_e1_t) e' st_e_e'      
  = case (thm_progress e1 t p_e1_t) of
      Left ()                -> Right p_e1_t ? lem_sem_det e e' st_e_e' e1 (EAnnV e1 t)
      Right (e1', st_e1_e1') -> Right (TAnn (typSize p_e1'_t) Empty e1' t p_e1'_t)
                                  ? lem_sem_det e e' st_e_e' (Annot e1' t) (EAnn e1 e1' st_e1_e1' t)
          where
            Right p_e1'_t = thm_preservation e1 t p_e1_t e1' st_e1_e1'
thm_preservation e t (TSub n Empty _e s p_e_s _t k p_t p_s_t) e' st_e_e'
  = case (thm_preservation e s p_e_s e' st_e_e') of
      Left ()      -> Left ()
      Right p_e'_s -> Right (TSub n' Empty e' s p_e'_s t k p_t p_s_t)
        where
          n'        = max n (typSize p_e'_s)

{-@ thm_many_preservation :: e:Expr -> e':Expr -> ProofOf(EvalsTo e e') -> t:Type 
        -> ProofOf(HasType Empty e t) -> ProofOf(HasType Empty e' t) @-}
thm_many_preservation :: Expr -> Expr -> EvalsTo -> Type -> HasType -> HasType
thm_many_preservation e e' ev_e_e' t p_e_t = case ev_e_e' of
  (Refl e)                             -> p_e_t
  (AddStep _e e1 st_e_e1 _e' ev_e1_e') -> thm_many_preservation e1 e' ev_e1_e' t p_e1_t
    where
      Right p_e1_t = thm_preservation e t p_e_t e1 st_e_e1 

{-@ thm_soundness :: e:Expr -> t:Type -> ProofOf(HasType Empty e t)
            -> e':Expr  -> ProofOf(EvalsTo e e')
            -> Either { pf:_ | isValue e' }
                      (Expr, Step)<{\e'' pf -> propOf pf == Step e' e''}> @-}
thm_soundness :: Expr -> Type -> HasType -> Expr -> EvalsTo -> Either Proof (Expr,Step)
thm_soundness e t p_e_t e' ev_e_e' = case ev_e_e' of
  (Refl _e)                            -> thm_progress e' t p_e_t
  (AddStep _e e1 st_e_e1 _e' ev_e1_e') -> thm_soundness e1 t p_e1_t e' ev_e1_e'
    where
      Right p_e1_t = thm_preservation e t p_e_t e1 st_e_e1
