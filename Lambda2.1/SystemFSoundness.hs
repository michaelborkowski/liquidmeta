{-# LANGUAGE GADTs #-}

{-@ LIQUID "--no-termination" @-}  -- TODO assume
{-@ LIQUID "--no-totality" @-}     -- TODO assume
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
import WellFormedness
import PrimitivesFTyping
import BasicPropsSubstitution
import BasicPropsEnvironments
import SystemFWellFormedness
import SystemFLemmasWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasSubstitution

{-@ reflect foo23 @-}
foo23 x = Just x
foo23 :: a -> Maybe a

-----------------------------------------------------------------------------
----- | SOUNDNESS of the SYSTEM F LAMBDA CALCULUS
-----------------------------------------------------------------------------

-- was:           -> Either { pf:_ | isValue e && Set_emp (freeBV e) } 
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
lemma_progress e t  p_e_t@(FTAbs {})          = Left () -- ? lem_freeBV_emptyF FEmpty e t p_e_t 
lemma_progress _e _t (FTApp FEmpty e1 t_x t p_e1_txt e2 p_e2_tx) 
      = case e1 of 
          (Prim p) -> case (lemma_progress e2 t_x p_e2_tx) of
              Left ()               -> Right (delta p e2, EPrim p e2)
              Right (e2', p_e2_e2') -> Right (App (Prim p) e2', EApp2 e2 e2' p_e2_e2' (Prim p))
          (Lambda x e') -> case (lemma_progress e2 t_x p_e2_tx) of
              Left ()               -> Right (subBV x e2 e', EAppAbs x e' e2)
              Right (e2', p_e2_e2') -> Right (App (Lambda x e') e2', EApp2 e2 e2' p_e2_e2' (Lambda x e'))
          _ -> case (isValue e1) of
              False -> Right (App e1' e2, EApp1 e1 e1' p_e1_e1' e2)
                  where
                      Right (e1', p_e1_e1') = lemma_progress e1 (FTFunc t_x t) p_e1_txt
              True  -> impossible ("by lemma" ? lemma_function_values e1 t_x t p_e1_txt)
lemma_progress e t  p_e_t@(FTAbsT {})         = Left () 
lemma_progress e t  p_e_t@(FTAppT {})         
      = undefined --assume
lemma_progress _e _t (FTLet FEmpty e1 tx p_e1_tx x e2 t y p_e2_t)
      = case (lemma_progress e1 tx p_e1_tx) of
          Left ()               -> Right (subBV x e1 e2, ELetV x e1 e2)
          Right (e1', p_e1_e1') -> Right (Let x e1' e2, ELet e1 e1' p_e1_e1' x e2) 
lemma_progress _e _t (FTAnn FEmpty e1 t liqt p_e1_t)
      = case (lemma_progress e1 t p_e1_t) of
          Left ()               -> Right (e1, EAnnV e1 liqt)
          Right (e1', p_e1_e1') -> Right (Annot e1' liqt, EAnn e1 e1' p_e1_e1' liqt)


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
      Left ()                -> Right p_del_t' ? lem_sem_det e e' st_e_e' (delta c e2) (EPrim c e2)
        where
          p_del_t'   = lem_delta_ftyp c e2 t_x t' p_c_txt' p_e2_tx 
      Right (e2', st_e2_e2') -> Right (FTApp FEmpty (Prim c) t_x t' p_c_txt' e2' p_e2'_tx)
        where
          Right p_e2'_tx  = lemma_preservation e2 t_x p_e2_tx e2' st_e2_e2' 
                                ? lem_sem_det e e' st_e_e' (App (Prim c) e2') 
                                              (EApp2 e2 e2' st_e2_e2' (Prim c) )
lemma_preservation e t p_e_t@(FTApp FEmpty (Lambda w e1) t_x t' p_lam_txt' e2 p_e2_tx) e' st_e_e'
  = case (lemma_progress e2 t_x p_e2_tx) of
      Left ()                -> Right p_e1e2_t' ? lem_sem_det e e' st_e_e' 
                                                         (subBV w e2 e1) (EAppAbs w e1 e2)
                                                ? lem_subFV_unbind w y e2 e1
        where
          (FTAbs _ _ _tx k_x pf_tx _ _ y p_e1_t') = p_lam_txt' -- y:t_x |- e1 : t'
          p_e1e2_t'           = lem_subst_ftyp FEmpty FEmpty y e2 t_x p_e2_tx 
                                              (WFFBind FEmpty WFFEmpty y t_x k_x pf_tx)
                                              (unbind w y e1) t' p_e1_t'
      Right (e2', st_e2_e2') -> Right (FTApp FEmpty (Lambda w e1) t_x t' p_lam_txt' e2' p_e2'_tx)
        where
          Right p_e2'_tx      = lemma_preservation e2 t_x p_e2_tx e2' st_e2_e2'  
                                    ? lem_sem_det e e' st_e_e' (App (Lambda w e1) e2') 
                                                  (EApp2 e2 e2' st_e2_e2' (Lambda w e1))
lemma_preservation e t p_e_t@(FTApp FEmpty e1 t_x t' p_e1_txt' e2 p_e2_tx) e' st_e_e' 
  = case (lemma_progress e1 (FTFunc t_x t') p_e1_txt') of
      Left ()                -> impossible ("by Lemma" ? lemma_function_values e1 t_x t' p_e1_txt')
      Right (e1', st_e1_e1') -> Right (FTApp FEmpty e1' t_x t' p_e1'_txt' e2 p_e2_tx)
                                    ? toProof (e === App e1 e2)
        where
          Right p_e1'_txt'    = lemma_preservation e1 (FTFunc t_x t') p_e1_txt' e1' st_e1_e1'
                                    ? lem_sem_det e e' st_e_e' (App e1' e2)
                                                  (EApp1 e1 e1' st_e1_e1' e2)
lemma_preservation e t (FTAbsT {}) e' st_e_e'          = Left () ? lem_value_stuck e e' st_e_e'
lemma_preservation e t (FTAppT {}) e' st_e_e'           
  = undefined -- assume
lemma_preservation e t p_e_t@(FTLet FEmpty e_x t_x p_ex_tx x e1 _t y p_e1_t) e' st_e_e'
  = case (lemma_progress e_x t_x p_ex_tx) of 
      Left ()                 -> Right p_e1ex_t
                                     ? lem_sem_det e e' st_e_e' (subBV x e_x e1) (ELetV x e_x e1)
--                                     ? lem_free_bound_in_env Empty t p_emp_t y
        where
          {- @ p_e1ex_t :: ProofOf(HasType Empty (subBV x e_x e1) t) @-} -- (tsubBV x e_x t)) @-}
          p_tx_star            = lem_ftyping_wfft FEmpty e_x t_x p_ex_tx WFFEmpty
          p_e1ex_t             = lem_subst_ftyp FEmpty FEmpty y e_x t_x p_ex_tx 
                                           (WFFBind FEmpty WFFEmpty y t_x Star p_tx_star)
                                           (unbind x y e1) t p_e1_t
                                           ? lem_subFV_unbind x y e_x e1 
                                     -- ? lem_tfreeBV_empty Empty t p_emp_t WFEEmpty
                                     -- ? lem_tsubBV_inval x e_x t
                                     -- ? toProof ( t === tsubBV x e_x t ) 
      Right (e_x', st_ex_ex') -> Right (FTLet FEmpty e_x' t_x p_ex'_tx x e1 t y p_e1_t)
        where
          Right p_ex'_tx       = lemma_preservation e_x t_x p_ex_tx e_x' st_ex_ex'
                                     ? lem_sem_det e e' st_e_e' (Let x e_x' e1) 
                                                   (ELet e_x e_x' st_ex_ex' x e1)
lemma_preservation e t (FTAnn FEmpty e1 t_ liqt p_e1_t) e' st_e_e'      
  = case (lemma_progress e1 t p_e1_t) of
      Left ()                -> Right p_e1_t ? lem_sem_det e e' st_e_e' e1 (EAnnV e1 liqt)
      Right (e1', st_e1_e1') -> Right (FTAnn FEmpty e1' t liqt p_e1'_t)
                                  ? lem_sem_det e e' st_e_e' (Annot e1' liqt) (EAnn e1 e1' st_e1_e1' liqt)
          where
            Right p_e1'_t = lemma_preservation e1 t p_e1_t e1' st_e1_e1'

-- Lemma. The underlying bare type system is sound. This is the textbook
--          soundness proof for the STLC.
{-@ lemma_soundness :: e:Expr -> e':Expr -> ProofOf(EvalsTo e e') -> b:FType
                   -> ProofOf(HasFType FEmpty e b) -> ProofOf(HasFType FEmpty e' b) @-}
lemma_soundness :: Expr -> Expr -> EvalsTo -> FType -> HasFType -> HasFType
lemma_soundness e e' p_ee' b p_eb = case p_ee' of 
  (Refl e)                           -> p_eb  
  (AddStep _e e1 st_e_e1 _e' p_e1e') -> lemma_soundness e1 e' p_e1e' b p_e1b
    where
      Right p_e1b = lemma_preservation e b p_eb e1 st_e_e1
