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
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import PrimitivesFTyping
import PrimitivesWFType
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import Typing
import BasicPropsCSubst
import LemmasWellFormedness
import LemmasTyping
import LemmasSubtyping
import SubstitutionLemmaWF
import PrimitivesSemantics
import PrimitivesDenotations
import DenotationsSoundness
import LemmasExactness
import SubstitutionLemmaTyp
import SubstitutionLemmaTypTV
import LemmasSubtypeClosed
import LemmasInvertLambda
import PrimitivesRefinements
import PrimitivesDeltaTyping

{-@ reflect foo77 @-}
foo77 x = Just x
foo77 :: a -> Maybe a

--------------------------------------------------------------------------------
--- | PROGRESS and PRESERVATION
--------------------------------------------------------------------------------

-- the big theorems                -- removed Set_emp (freeBV e) from the LHS case
{-@ thm_progress' :: e:Term -> t:Type -> ProofOf(HasType Empty e t)  
        -> Either { pf:_ | isValue e }  (Expr, Step)<{\e' pf -> propOf pf == Step e e'}> @-}
thm_progress' :: Expr -> Type -> HasType -> Either Proof (Expr,Step) 
thm_progress' c _b (TBC Empty _)           = Left ()
thm_progress' c _b (TIC Empty _)           = Left ()
thm_progress' x _t (TVar1 Empty _ _ _ _)   = Left ()
thm_progress' x _t (TVar2 Empty _ _ _ _ _) = Left ()
thm_progress' x _t (TVar3 Empty _ _ _ _ _) = Left ()
thm_progress' c _t (TPrm Empty _)          = Left ()
thm_progress' e t  p_e_t@(TAbs {})         = Left () 
thm_progress' _e _t p_e_t@(TApp Empty e1 x t_x t p_e1_txt e2 p_e2_tx) = case e1 of
      (Prim p)      -> case (thm_progress' e2 t_x p_e2_tx) of
          Left ()               -> Right (delta p e2_compat, EPrim p e2_compat)
            where
              e2_compat = e2 ? lem_prim_compat_in_tapp p e2 (TExists x t_x t) p_e_t
          Right (e2', p_e2_e2') -> Right (App (Prim p) e2', EApp2 e2 e2' p_e2_e2' (Prim p))  
      (Lambda x e') -> case (thm_progress' e2 t_x p_e2_tx) of
          Left ()               -> Right (subBV x e2 e', EAppAbs x e' e2)
          Right (e2', p_e2_e2') -> Right (App (Lambda x e') e2', EApp2 e2 e2' p_e2_e2' (Lambda x e'))
      (_)           -> case (isValue e1) of
          False                 -> Right (App e1' e2, EApp1 e1 e1' p_e1_e1' e2)
              where
                  Right (e1', p_e1_e1') = thm_progress' e1 (TFunc x t_x t) p_e1_txt
          True                  -> impossible ("by lemma" ? lemma_function_values e1 (erase t_x) (erase t)
                                                                                  p_e1_er_txt)
              where
                  p_e1_er_txt = lem_typing_hasftype Empty e1 (TFunc x t_x t) p_e1_txt WFEEmpty
thm_progress' e t  p_e_t@(TAbsT {})        = Left () 
thm_progress' _e t p_e_t@(TAppT Empty e' a k s p_e'_as t' p_emp_t') = case e' of
      (Prim c)          -> Right (deltaT c t'_,     EPrimT c t'_)
          where
            t'_ = t' ? lem_prim_compatT_in_tappT c t' t p_e_t 
      (LambdaT a' k' e'') -> Right (subBTV a' t' e'', EAppTAbs a' k' e'' t')
      _                 -> case (isValue e') of
          False         -> Right (AppT e'' t',     EAppT e' e'' p_e'_e'' t')
              where
                  Right (e'', p_e'_e'') = thm_progress' e' (TPoly a k s) p_e'_as
          True          -> impossible ("by lemmas" ? lemma_tfunction_values e' a k (erase s) p_e'_er_as)
              where
                  p_e'_er_as = lem_typing_hasftype Empty e' (TPoly a k s) p_e'_as WFEEmpty
thm_progress' _e _t (TLet Empty e1 tx p_e1_tx x e2 t _ p_t y p_e2_t)
      = case (thm_progress' e1 tx p_e1_tx) of
          Left ()               -> Right (subBV x e1 e2, ELetV x e1 e2)
          Right (e1', p_e1_e1') -> Right (Let x e1' e2,  ELet e1 e1' p_e1_e1' x e2) 
thm_progress' _e _t (TAnn Empty e1 t p_e1_t)
      = case (thm_progress' e1 t p_e1_t) of
          Left ()               -> Right (e1, EAnnV e1 t)
          Right (e1', p_e1_e1') -> Right (Annot e1' t, EAnn e1 e1' p_e1_e1' t)
thm_progress' _e _t (TSub Empty e s p_e_s t k p_t p_s_t)
      = case (thm_progress' e s p_e_s) of
          Left ()               -> Left ()
          Right (e', p_e_e')    -> Right (e', p_e_e') 

-- Left () means the case is contradictory and cannot occur
{-@ thm_preservation' :: e:Term -> t:Type -> ProofOf(HasType Empty e t) -> e':Expr
        -> ProofOf(Step e e') -> Either { pf:_ | false } { pf:_ | propOf pf == HasType Empty e' t} @-}
thm_preservation' :: Expr -> Type -> HasType -> Expr -> Step -> Either Proof HasType 
thm_preservation' e t (TBC _emp b)  e' st_e_e'       = Left () ? lem_value_stuck e e' st_e_e'
thm_preservation' e t (TIC _emp n)  e' st_e_e'       = Left () ? lem_value_stuck e e' st_e_e' 
thm_preservation' e t (TVar1 _ _ _ _ _) e' st_e_e'   = Left () ? lem_value_stuck e e' st_e_e'
thm_preservation' e t (TVar2 _ _ _ _ _ _) e' st_e_e' = Left () ? lem_value_stuck e e' st_e_e'
thm_preservation' e t (TVar3 _ _ _ _ _ _) e' st_e_e' = Left () ? lem_value_stuck e e' st_e_e'
thm_preservation' e t (TPrm _emp c) e' st_e_e'       = Left () ? lem_value_stuck e e' st_e_e'
thm_preservation' e t (TAbs {}) e' st_e_e'           = Left () ? lem_value_stuck e e' st_e_e'
thm_preservation' e t p_e_t@(TApp Empty (Prim c) x t_x t' p_c_txt' e2 p_e2_tx) e' st_e_e'
  = case (thm_progress' e2 t_x p_e2_tx) of
      Left ()                -> Right p_del_ex_t' ? lem_sem_det e e' st_e_e' (delta_c_e2) (EPrim c e2)
        where
          delta_c_e2   = delta c (e2 ? lem_prim_compat_in_tapp c e2 (TExists x t_x t') p_e_t)
          p_del_t'e2   = lem_delta_typ c e2 x t_x t' p_c_txt' p_e2_tx 
          p_emp_ex_t'_ = lem_typing_wf Empty e t p_e_t WFEEmpty
          p_emp_ex_t'  = lem_wfexis_for_wf_texists Empty x t_x t' Star p_emp_ex_t'_
          (WFExis _ _ _ _ _ _t' k' y p_y_t') = p_emp_ex_t'
          p_t'e2_ex_t' = lem_witness_sub Empty e2 t_x p_e2_tx WFEEmpty x t' k' y p_y_t'
          p_del_ex_t'  = TSub Empty (delta_c_e2) (tsubBV x e2 t') p_del_t'e2 
                              (TExists x t_x t') k' p_emp_ex_t' p_t'e2_ex_t' 
      Right (e2', st_e2_e2') -> Right (TApp Empty (Prim c) x t_x t' p_c_txt' e2' p_e2'_tx)
        where
          Right p_e2'_tx  = thm_preservation' e2 t_x p_e2_tx e2' st_e2_e2' 
                                ? lem_sem_det e e' st_e_e' (App (Prim c) e2') 
                                              (EApp2 e2 e2' st_e2_e2' (Prim c) )
thm_preservation' e t p_e_t@(TApp Empty (Lambda w e1) x t_x t' p_lam_txt' e2 p_e2_tx) e' st_e_e'
  = case (thm_progress' e2 t_x p_e2_tx) of
      Left ()                -> Right p_e1e2_ex_t' ? lem_sem_det e e' st_e_e' 
                                                         (subBV w e2 e1) (EAppAbs w e1 e2)
        where
          (y, p_e1_t')        = lem_invert_tabs Empty w e1 x t_x t' p_lam_txt' WFEEmpty
          {-(TAbs _ _ _tx p_tx _ _ y p_e1_t') = p_lam_txt' -- y:t_x |- e1 : t'-}
          p_tx                = lem_typing_wf Empty e2 t_x p_e2_tx WFEEmpty
          p_wf_ytx            = WFEBind Empty WFEEmpty y t_x Star p_tx
          p_e1e2_t'e2         = lem_subst_typ Empty Empty y e2 t_x p_e2_tx p_wf_ytx
                                              (unbind w y e1) (unbindT x y t') p_e1_t'
          p_emp_ex_t'_        = lem_typing_wf Empty e t p_e_t WFEEmpty
          p_emp_ex_t'         = lem_wfexis_for_wf_texists Empty x t_x t' Star p_emp_ex_t'_
          (WFExis _ _ _ _ _ _ k' y' p_y_t') = p_emp_ex_t'
          p_t'e2_ex_t'        = lem_witness_sub Empty e2 t_x p_e2_tx WFEEmpty x t' k' y' p_y_t'
          p_e1e2_ex_t'        = TSub Empty (subBV w e2 e1) (tsubBV x e2 t') 
                                     (p_e1e2_t'e2 ? lem_subFV_unbind w y e2 e1
                                                  ? lem_tsubFV_unbindT x y e2 t')
                                     (TExists x t_x t') k' p_emp_ex_t' p_t'e2_ex_t'
      Right (e2', st_e2_e2') -> Right (TApp Empty (Lambda w e1) x t_x t' p_lam_txt' e2' p_e2'_tx)
        where
          Right p_e2'_tx      = thm_preservation' e2 t_x p_e2_tx e2' st_e2_e2'  
                                    ? lem_sem_det e e' st_e_e' (App (Lambda w e1) e2') 
                                                  (EApp2 e2 e2' st_e2_e2' (Lambda w e1))
thm_preservation' e t p_e_t@(TApp Empty e1 x t_x t' p_e1_txt' e2 p_e2_tx) e' st_e_e' 
  = case (thm_progress' e1 (TFunc x t_x t') p_e1_txt') of
      Left ()                -> impossible ("by lemma" ? lemma_function_values e1 (erase t_x) (erase t')
                                                                                  p_e1_er_txt')
        where
          p_e1_er_txt'        = lem_typing_hasftype Empty e1 (TFunc x t_x t') p_e1_txt' WFEEmpty
      Right (e1', st_e1_e1') -> Right (TApp Empty e1' x t_x t' p_e1'_txt' e2 p_e2_tx)
        where
          Right p_e1'_txt'    = thm_preservation' e1 (TFunc x t_x t') p_e1_txt' e1' st_e1_e1'
                                    ? lem_sem_det e e' st_e_e' (App e1' e2)
                                                  (EApp1 e1 e1' st_e1_e1' e2)
thm_preservation' e t (TAbsT {}) e' st_e_e'          = Left () ? lem_value_stuck e e' st_e_e'
thm_preservation' e t p_e_t@(TAppT Empty (Prim c) a k s p_e1_as t'_ p_emp_t') e' st_e_e' 
  = Right p_delT_st' -- deltaT c t' :: tsubBTV a t' s
          ? lem_sem_det e e' st_e_e' (deltaT c t') (EPrimT c t') 
        where
          t'         = t'_ ? lem_prim_compatT_in_tappT c t'_ t p_e_t
          p_delT_st' = lem_deltaT_typ c a k s p_e1_as t' p_emp_t'
thm_preservation' e t (TAppT Empty (LambdaT a1 k1 e2) a k s p_e1_as t' p_emp_t') e' st_e_e' 
  = Right p_e2t'_st' -- subBTV a1 t' e2 :: tsubBTV a t' s      
          ? lem_sem_det e e' st_e_e' (subBTV a1 t' e2) (EAppTAbs a1 k1 e2 t') 
        where
          (a', p_e2_s)    = lem_invert_tabst Empty a1 k1 e2 a k s p_e1_as WFEEmpty
          p_wf_a'k        = WFEBindT Empty WFEEmpty a' k
          p_e2t'_st'      = lem_subst_tv_typ Empty Empty a' t' k p_emp_t' 
                                             p_wf_a'k
                                             (unbind_tv a1 a' e2) (unbind_tvT a a' s) p_e2_s
                                ? lem_subFTV_unbind_tv   a1 a' t' e2
                                ? lem_tsubFTV_unbind_tvT a  a' t' s
thm_preservation' e t (TAppT Empty e1 a k s p_e1_as t' p_emp_t') e' st_e_e' 
  = case (thm_progress' e1 (TPoly a k s) p_e1_as) of
        Left ()                -> impossible ("by lemmas" ? lemma_tfunction_values e1 a k (erase s) p_e1_er_as)
              where
                p_e1_er_as = lem_typing_hasftype Empty e1 (TPoly a k s) p_e1_as WFEEmpty
        Right (e1', st_e1_e1') -> Right (TAppT Empty e1' a k s p_e1'_as t' p_emp_t')
          where
            Right p_e1'_as = thm_preservation' e1 (TPoly a k s) p_e1_as e1' st_e1_e1'
                              ? lem_sem_det e e' st_e_e' (AppT e1' t') (EAppT e1 e1' st_e1_e1' t')
thm_preservation' e t p_e_t@(TLet Empty e_x t_x p_ex_tx x e1 _t k p_emp_t y p_e1_t) e' st_e_e'
  = case (thm_progress' e_x t_x p_ex_tx) of 
      Left ()                 -> Right p_e1ex_t
                                     ? lem_sem_det e e' st_e_e' (subBV x e_x e1) (ELetV x e_x e1)
                                     ? lem_free_bound_in_env Empty t k p_emp_t y
        where
          p_tx                 = lem_typing_wf Empty e_x t_x p_ex_tx WFEEmpty
          p_wf_ytx             = WFEBind Empty WFEEmpty y t_x Star p_tx
          {-@ p_e1ex_t :: ProofOf(HasType Empty (subBV x e_x e1) t) @-} -- (tsubBV x e_x t)) @- }
          p_e1ex_t             = lem_subst_typ Empty Empty y e_x t_x p_ex_tx p_wf_ytx
                                           (unbind x y e1) (unbindT x y t) p_e1_t
                                           ? lem_subFV_unbind x y e_x e1 
                                           ? lem_tsubFV_unbindT x y e_x t
                                     ? lem_tfreeBV_empty Empty t k p_emp_t 
                                     ? lem_tsubBV_notin x e_x t
                                     ? toProof ( t === tsubBV x e_x t ) 
      Right (e_x', st_ex_ex') -> Right (TLet Empty e_x' t_x p_ex'_tx x e1 t k p_emp_t y p_e1_t)
        where
          Right p_ex'_tx       = thm_preservation' e_x t_x p_ex_tx e_x' st_ex_ex'
                                     ? lem_sem_det e e' st_e_e' (Let x e_x' e1) 
                                                   (ELet e_x e_x' st_ex_ex' x e1)
thm_preservation' e t (TAnn Empty e1 t_ p_e1_t) e' st_e_e'      
  = case (thm_progress' e1 t p_e1_t) of
      Left ()                -> Right p_e1_t ? lem_sem_det e e' st_e_e' e1 (EAnnV e1 t)
      Right (e1', st_e1_e1') -> Right (TAnn Empty e1' t p_e1'_t)
                                  ? lem_sem_det e e' st_e_e' (Annot e1' t) (EAnn e1 e1' st_e1_e1' t)
          where
            Right p_e1'_t = thm_preservation' e1 t p_e1_t e1' st_e1_e1'
thm_preservation' e t (TSub Empty _e s p_e_s _t k p_t p_s_t) e' st_e_e'
  = case (thm_preservation' e s p_e_s e' st_e_e') of
      Left ()      -> Left ()
      Right p_e'_s -> Right (TSub Empty e' s p_e'_s t k p_t p_s_t)

{-@ thm_progress :: e:Expr -> t:Type -> ProofOf(HasType Empty e t)  
        -> Either { pf:_ | isValue e }  (Expr, Step)<{\e' pf -> propOf pf == Step e e'}> @-}
thm_progress :: Expr -> Type -> HasType -> Either Proof (Expr,Step) 
thm_progress e t p_e_t = thm_progress' (e ? lem_typing_isterm Empty e t p_e_t) t p_e_t

{-@ thm_preservation :: e:Expr -> t:Type -> ProofOf(HasType Empty e t) -> e':Expr
        -> ProofOf(Step e e') -> Either { pf:_ | false } { pf:_ | propOf pf == HasType Empty e' t} @-}
thm_preservation :: Expr -> Type -> HasType -> Expr -> Step -> Either Proof HasType 
thm_preservation e t p_e_t e' st_e_e' 
  = thm_preservation' (e ? lem_typing_isterm Empty e t p_e_t) t p_e_t e' st_e_e'
--                      (e' ? lem_step_term e e' st_e_e') st_e_e'

{-@ lem_typing_isterm :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
        -> { pf:_ | isTerm e} @-}
lem_typing_isterm :: Env -> Expr -> Type -> HasType -> Proof
lem_typing_isterm g e t (TBC _g b) = ()
lem_typing_isterm g e t (TIC _g n) = ()
lem_typing_isterm g e t (TVar1 _g' x t' k' p_g'_t') = ()
lem_typing_isterm g e t (TVar2 g' x _t p_g'_x_t y s) = ()
lem_typing_isterm g e t (TVar3 g' x _t p_g'_x_t a k_a) = ()
lem_typing_isterm g e t (TPrm _g c) = ()
lem_typing_isterm g e t (TAbs _g x t_x k_x p_tx_wf e' t' y p_e'_t')
  =   lem_typing_isterm (Cons y t_x g) (unbind x y e') (unbindT x y t') p_e'_t'
lem_typing_isterm g e t (TApp _g e1 x t_x t' p_e1_txt' e2 p_e2_tx)
  =   lem_typing_isterm g e1 (TFunc x t_x t') p_e1_txt'
    ? lem_typing_isterm g e2 t_x              p_e2_tx
lem_typing_isterm g e t (TAbsT _g a k e' t' k_t' a' p_a'g_e'_t' p_a'g_t')
  =   lem_typing_isterm (ConsT a' k g) (unbind_tv a a' e') (unbind_tvT a a' t') p_a'g_e'_t'
lem_typing_isterm g e t (TAppT _g e' a k s p_e'_as t' p_g_t')
  =   lem_typing_isterm g e' (TPoly a k s) p_e'_as
lem_typing_isterm g e t (TLet _g e_x t_x p_ex_tx x e' _t k p_g_t y p_e'_t)
  =   lem_typing_isterm g e_x t_x p_ex_tx
    ? lem_typing_isterm (Cons y t_x g) (unbind x y e') (unbindT x y t) p_e'_t
lem_typing_isterm g e t (TAnn _g e' _t p_e'_t)
  =   lem_typing_isterm g e' t p_e'_t
lem_typing_isterm g e t (TSub _g _e s p_e_s _t k p_g_t p_s_t)
  =   lem_typing_isterm g e s p_e_s

{-@ thm_soundness :: e:Expr -> e':Expr -> ProofOf(EvalsTo e e') -> t:Type 
        -> ProofOf(HasType Empty e t) -> ProofOf(HasType Empty e' t) @-}
thm_soundness :: Expr -> Expr -> EvalsTo -> Type -> HasType -> HasType
thm_soundness e e' ev_e_e' t p_e_t = case ev_e_e' of
  (Refl e)                             -> p_e_t
  (AddStep _e e1 st_e_e1 _e' ev_e1_e') -> thm_soundness e1 e' ev_e1_e' t p_e1_t
    where
      Right p_e1_t = thm_preservation e t p_e_t e1 st_e_e1 
