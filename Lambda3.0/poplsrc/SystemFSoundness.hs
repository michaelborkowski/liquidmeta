{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SystemFSoundness where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import BasicPropsSubstitution
import BasicPropsEnvironments
import PrimitivesFTyping
import WellFormedness
import SystemFWellFormedness
import SystemFLemmasWellFormedness
import SystemFLemmasWeaken
import SystemFLemmasSubstitution

{-@ reflect foo25 @-}
foo25 x = Just x
foo25 :: a -> Maybe a

-----------------------------------------------------------------------------
----- | SOUNDNESS of the SYSTEM F LAMBDA CALCULUS
-----------------------------------------------------------------------------

-- The System F Progress Lemma   
{-@ lemma_progress :: e:Expr -> t:FType -> ProofOf(HasFType FEmpty e t)  
             -> Either { pf:_ | isValue e } 
                       (Expr, Step)<{\e' pf -> propOf pf == Step e e'}> @-}
lemma_progress :: Expr -> FType -> HasFType -> Either Proof (Expr,Step) 
lemma_progress c _b (FTBC FEmpty _)           = Left ()
lemma_progress c _b (FTIC FEmpty _)           = Left ()
lemma_progress x _t (FTVar1 FEmpty _ _)       = Left ()
lemma_progress x _t (FTVar2 FEmpty _ _ _ _ _) = Left ()
lemma_progress x _t (FTVar3 FEmpty _ _ _ _ _) = Left ()
lemma_progress c _t (FTPrm FEmpty _)          = Left ()
lemma_progress e t  p_e_t@(FTAbs {})          = Left () 
lemma_progress e t p_e_t@(FTApp FEmpty e1 t_x t' p_e1_txt' e2 p_e2_tx) 
      = case e1 of 
          (Prim p) -> case (lemma_progress e2 t_x p_e2_tx) of
              Left ()               -> Right (delta p e2_, EPrim p e2_)
                  where
                      e2_ = e2 ? lem_prim_compat_in_ftapp p e2 t p_e_t
              Right (e2', p_e2_e2') -> Right (e', p_e_e') 
                  where
                      e'     = App (Prim p) e2'
                      p_e_e' = EApp2 e2 e2' p_e2_e2' (Prim p)
          (Lambda e3) -> case (lemma_progress e2 t_x p_e2_tx) of
              Left ()               -> Right (subBV e2 e3, EAppAbs e3 e2)
              Right (e2', p_e2_e2') -> Right (e', p_e_e') 
                  where
                      e'     = App (Lambda e3) e2'
                      p_e_e' = EApp2 e2 e2' p_e2_e2' (Lambda e3)
          _ -> case (isValue e1) of
              False -> Right (e', p_e_e') 
                  where
                      Right (e1', p_e1_e1') = lemma_progress e1 (FTFunc t_x t) p_e1_txt'
                      e'     = App e1' e2
                      p_e_e' = EApp1 e1 e1' p_e1_e1' e2 
              True  -> impossible ("by lemma" ? lemma_function_values e1 t_x t' p_e1_txt')
lemma_progress e t  p_e_t@(FTAbsT {})         = Left () 
lemma_progress e t  p_e_t@(FTAppT FEmpty e1 k s  p_e1_as rt p_emp_er_rt) = case e1 of
      (Prim c)            -> Right (deltaT c rt_,     EPrimT c rt_)
          where
            rt_ = rt ? lem_prim_compatT_in_ftappt c rt t p_e_t
      (LambdaT k' e'') -> Right (subBTV rt e'', EAppTAbs  k' e'' rt)
      _                   -> case (isValue e1) of
        False             -> Right (e', p_e_e') 
          where
            Right (e2, p_e1_e2) = lemma_progress e1 (FTPoly k s) p_e1_as
            e'     = AppT e2 rt
            p_e_e' = EAppT e1 e2 p_e1_e2 rt
        True              -> impossible ("by lemma" ? lemma_tfunction_values e1 k s p_e1_as)
lemma_progress e _t (FTLet FEmpty e1 tx p_e1_tx e2 t nms make_p_e2_t)
      = case (lemma_progress e1 tx p_e1_tx) of
          Left ()               -> Right (subBV e1 e2, ELetV e1 e2)
          Right (e1', p_e1_e1') -> Right (e', p_e_e') 
            where
              e'     = Let e1' e2
              p_e_e' = ELet e1 e1' p_e1_e1' e2
lemma_progress e _t (FTAnn FEmpty e1 t liqt p_e1_t)
      = case (lemma_progress e1 t p_e1_t) of
          Left ()               -> Right (e1, EAnnV e1 liqt)
          Right (e1', p_e1_e1') -> Right (e', p_e_e') 
            where
              e'     = Annot e1' liqt
              p_e_e' = EAnn e1 e1' p_e1_e1' liqt

{-@ lemma_preservation :: e:Expr -> t:FType -> ProofOf(HasFType FEmpty e t) -> e':Expr
        -> ProofOf(Step e e') -> Either { pf:_ | false } { pf:_ | propOf pf == HasFType FEmpty e' t} @-}
lemma_preservation :: Expr -> FType -> HasFType -> Expr -> Step -> Either Proof HasFType 
lemma_preservation e t (FTBC _emp b)  e' st_e_e'       = Left () ? lem_value_stuck e e' st_e_e'
lemma_preservation e t (FTIC _emp n)  e' st_e_e'       = Left () ? lem_value_stuck e e' st_e_e' 
lemma_preservation e t (FTVar1 _ _ _) e' st_e_e'       = Left () ? lem_value_stuck e e' st_e_e'
lemma_preservation e t (FTVar2 _ _ _ _ _ _) e' st_e_e' = Left () ? lem_value_stuck e e' st_e_e'
lemma_preservation e t (FTVar3 _ _ _ _ _ _) e' st_e_e' = Left () ? lem_value_stuck e e' st_e_e'
lemma_preservation e t (FTPrm _emp c) e' st_e_e'       = Left () ? lem_value_stuck e e' st_e_e'
lemma_preservation e t (FTAbs {}) e' st_e_e'           = Left () ? lem_value_stuck e e' st_e_e'
lemma_preservation e t p_e_t@(FTApp FEmpty (Prim c) t_x t' p_c_txt' e2 p_e2_tx) e' st_e_e'
  = case (lemma_progress e2 t_x p_e2_tx) of
      Left ()                -> Right p_del_t' ? lem_sem_det e e' st_e_e' (delta c e2_) (EPrim c e2_)
        where
          e2_        = e2 ? lem_prim_compat_in_ftapp c e2 t p_e_t
          p_del_t'   = lem_delta_ftyp c e2 t_x t' p_c_txt' p_e2_tx 
      Right (e2', st_e2_e2') -> Right (FTApp FEmpty (Prim c) t_x t' p_c_txt' e2' p_e2'_tx)
        where
          Right p_e2'_tx  = lemma_preservation e2 t_x p_e2_tx e2' st_e2_e2' 
                                ? lem_sem_det e e' st_e_e' (App (Prim c) e2') 
                                              (EApp2 e2 e2' st_e2_e2' (Prim c) )
lemma_preservation e t p_e_t@(FTApp FEmpty (Lambda e1) t_x t' p_lam_txt' e2 p_e2_tx) e' st_e_e'
  = case (lemma_progress e2 t_x p_e2_tx) of
      Left ()        -> Right p_e1e2_t' ? lem_sem_det e e' st_e_e' (subBV e2 e1) (EAppAbs e1 e2)
                                        ? lem_subFV_unbind y e2 (e1
                                              ? lem_fv_bound_in_fenv FEmpty (Lambda e1) 
                                                                     (FTFunc t_x t') p_lam_txt' y)
        where
          (FTAbs _ _tx k_x pf_tx _ _ nms mk_p_e1_t') = p_lam_txt' -- y:t_x |- e1 : t'
          p_e1e2_t'           = lem_subst_ftyp FEmpty FEmpty y e2 t_x p_e2_tx 
                                               (unbind y e1) t' (mk_p_e1_t' y)
          y                   = fresh nms 
      Right (e2', st_e2_e2') -> Right (FTApp FEmpty (Lambda e1) t_x t' p_lam_txt' e2' p_e2'_tx)
        where
          Right p_e2'_tx      = lemma_preservation e2 t_x p_e2_tx e2' st_e2_e2'  
                                    ? lem_sem_det e e' st_e_e' (App (Lambda e1) e2') 
                                                  (EApp2 e2 e2' st_e2_e2' (Lambda e1))
lemma_preservation e t p_e_t@(FTApp FEmpty e1 t_x t' p_e1_txt' e2 p_e2_tx) e' st_e_e' 
  = case (lemma_progress e1 (FTFunc t_x t') p_e1_txt') of
      Left ()                -> impossible ("by Lemma" ? lemma_function_values e1 t_x t' p_e1_txt')
      Right (e1', st_e1_e1') -> Right (FTApp FEmpty e1' t_x t' p_e1'_txt' e2 p_e2_tx)
        where
          Right p_e1'_txt'    = lemma_preservation e1 (FTFunc t_x t') p_e1_txt' e1' st_e1_e1'
                                    ? lem_sem_det e e' st_e_e' (App e1' e2)
                                                  (EApp1 e1 e1' st_e1_e1' e2)
lemma_preservation e t (FTAbsT {}) e' st_e_e'          = Left () ? lem_value_stuck e e' st_e_e'
lemma_preservation e t p_e_t@(FTAppT FEmpty (Prim c) k s p_e1_as rt_ p_emp_er_rt) e' st_e_e'           
  = Right (lem_deltaT_ftyp c k s p_e1_as rt p_emp_er_rt)
          ? lem_sem_det e e' st_e_e' (deltaT c rt) (EPrimT c rt)
      where
        rt = rt_ ? lem_prim_compatT_in_ftappt c rt_ t p_e_t
lemma_preservation e t (FTAppT FEmpty (LambdaT k1 e2) k s p_e1_as rt p_emp_er_rt) e' st_e_e'
  = Right p_e2rt_srt ? lem_sem_det e e' st_e_e' (subBTV rt e2) (EAppTAbs k1 e2 rt)
      where
        (FTAbsT _ _ _ _ nms mk_p_e2_s) = p_e1_as
        p_as_star   = lem_ftyping_wfft FEmpty (LambdaT k1 e2) (FTPoly k s) p_e1_as WFFEmpty
--        p_wf_a'k    = WFFBindT FEmpty WFFEmpty a k
        p_e2rt_srt  = lem_subst_tv_ftyp FEmpty FEmpty a rt k p_emp_er_rt
                                  WFFEmpty {-p_wf_a'k-} (unbind_tv a e2) (unbindFT a s) (mk_p_e2_s a)
                                  ? lem_subFTV_unbind_tv a rt (e2
                                        ? lem_fv_bound_in_fenv FEmpty (LambdaT k1 e2) (FTPoly k s) p_e1_as a)
                                  ? lem_ftsubFV_unbindFT a (erase rt) (s  
                                        ? lem_ffreeTV_bound_in_fenv FEmpty (FTPoly k s) Star p_as_star a)
        a           = fresh nms
lemma_preservation e t (FTAppT FEmpty e1 k s p_e1_as rt p_emp_er_rt) e' st_e_e'
  = case (lemma_progress e1 (FTPoly k s) p_e1_as) of
      Left ()                -> impossible ("by lemma" ? lemma_tfunction_values e1 k s p_e1_as)
      Right (e1', st_e1_e1') -> Right (FTAppT FEmpty e1' k s p_e1'_as rt  p_emp_er_rt)
        where
          Right p_e1'_as = lemma_preservation e1 (FTPoly k s) p_e1_as e1' st_e1_e1'
                             ? lem_sem_det e e' st_e_e' (AppT e1' rt) (EAppT e1 e1' st_e1_e1' rt)
lemma_preservation e t p_e_t@(FTLet FEmpty e_x t_x p_ex_tx e1 _t nms mk_p_e1_t) e' st_e_e'
  = case (lemma_progress e_x t_x p_ex_tx) of 
      Left ()                 -> Right p_e1ex_t
                                     ? lem_sem_det e e' st_e_e' (subBV e_x e1) (ELetV e_x e1)
        where
          p_e1ex_t             = lem_subst_ftyp FEmpty FEmpty y e_x t_x p_ex_tx 
                                                (unbind y e1) t (mk_p_e1_t y) 
                                                ? lem_subFV_unbind y e_x (e1 
                                                      ? lem_fv_bound_in_fenv FEmpty e t p_e_t y)
          y                    = fresh nms
      Right (e_x', st_ex_ex') -> Right (FTLet FEmpty e_x' t_x p_ex'_tx e1 t nms mk_p_e1_t)
        where
          Right p_ex'_tx       = lemma_preservation e_x t_x p_ex_tx e_x' st_ex_ex'
                                     ? lem_sem_det e e' st_e_e' (Let e_x' e1) 
                                                   (ELet e_x e_x' st_ex_ex' e1)
lemma_preservation e t (FTAnn FEmpty e1 t_ liqt p_e1_t) e' st_e_e'      
  = case (lemma_progress e1 t p_e1_t) of
      Left ()                -> Right p_e1_t ? lem_sem_det e e' st_e_e' e1 (EAnnV e1 liqt)
      Right (e1', st_e1_e1') -> Right (FTAnn FEmpty e1' t liqt p_e1'_t)
                                  ? lem_sem_det e e' st_e_e' (Annot e1' liqt) (EAnn e1 e1' st_e1_e1' liqt)
          where
            Right p_e1'_t = lemma_preservation e1 t p_e1_t e1' st_e1_e1'

{-@ lemma_many_preservation :: e:Expr -> e':Expr -> ProofOf(EvalsTo e e') -> b:FType
                   -> ProofOf(HasFType FEmpty e b) -> ProofOf(HasFType FEmpty e' b) @-}
lemma_many_preservation :: Expr -> Expr -> EvalsTo -> FType -> HasFType -> HasFType
lemma_many_preservation e e' p_ee' b p_eb = case p_ee' of 
  (Refl _e)                          -> p_eb  
  (AddStep _e e1 st_e_e1 _e' p_e1e') -> lemma_many_preservation e1 e' p_e1e' b p_e1b
    where
      Right p_e1b = lemma_preservation e b p_eb e1 st_e_e1

-- Lemma. The underlying bare type system is sound. This is the textbook
--          soundness proof for the STLC. 
{-@ lemma_soundness :: e:Expr -> t:FType -> ProofOf(HasFType FEmpty e t)  
             -> e':Expr -> ProofOf(EvalsTo e e')
             -> Either { pf:_ | isValue e' } 
                       (Expr, Step)<{\e'' pf -> propOf pf == Step e' e''}> @-}
lemma_soundness :: Expr -> FType -> HasFType -> Expr -> EvalsTo -> Either Proof (Expr,Step) 
lemma_soundness e t p_e_t e' ev_e_e' = case ev_e_e' of
  (Refl _e)                            -> lemma_progress e' t p_e_t
  (AddStep _e e1 st_e_e1 _e' ev_e1_e') -> lemma_soundness e1 t p_e1_t e' ev_e1_e'
    where
      Right p_e1_t = lemma_preservation e t p_e_t e1 st_e_e1
