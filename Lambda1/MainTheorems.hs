{-# LANGUAGE GADTs #-}

--{-@ LIQUID "--higherorder" @-}
{- @ LIQUID "--diff"        @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module MainTheorems where

--import Control.Exception (assert)
import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Syntax
import Semantics
import Typing
import Primitives
import BasicLemmas
import BasicLemmas2
import DenotationalSoundness 
import Substitution

-- force these into scope
semantics = (Step, EvalsTo)
typing = (HasBType, HasType, WFType, WFEnv, Subtype)
denotations = (Entails, Denotes, DenotesEnv)

--------------------------------------------------------------------------------
--- | PROGRESS and PRESERVATION
--------------------------------------------------------------------------------

-- need a lemma that a typed term has no loose BVs!

-- the big theorems 
{-@ thm_progress :: e:Expr -> t:Type -> ProofOf(HasType Empty e t)  
           -> Either { pf:_ | isValue e && Set_emp (freeBV e) } 
                     (Expr, Step)<{\e' pf -> propOf pf == Step e e'}> @-}
thm_progress :: Expr -> Type -> HasType -> Either Proof (Expr,Step) 
thm_progress c _b (TBC Empty _)           = Left ()
thm_progress c _b (TIC Empty _)           = Left ()
thm_progress x _t (TVar1 Empty _ _)       = Left ()
thm_progress x _t (TVar2 Empty _ _ _ _ _) = Left ()
thm_progress c _t (TPrm Empty _)          = Left ()
thm_progress e t  p_e_t@(TAbs {})               
      = Left () ? lem_freeBV_empty Empty e t p_e_t WFEEmpty 
thm_progress _e _t (TApp Empty (Prim p) x t_x t p_e1_txt e2 p_e2_tx) 
      = case (thm_progress e2 t_x p_e2_tx) of
          Left ()               -> Right (delta p e2, EPrim p e2)
          Right (e2', p_e2_e2') -> Right (App (Prim p) e2', EApp2 e2 e2' p_e2_e2' (Prim p))
thm_progress _e _t (TApp Empty (Lambda x e') _x t_x t p_e1_txt e2 p_e2_tx) 
      = case (thm_progress e2 t_x p_e2_tx) of
          Left ()               -> Right (subBV x e2 e', EAppAbs x e' e2)
          Right (e2', p_e2_e2') -> Right (App (Lambda x e') e2', EApp2 e2 e2' p_e2_e2' (Lambda x e'))
thm_progress _e _t (TApp Empty e1 x t_x t p_e1_txt e2 p_e2_tx) 
      = Right (App e1' e2, EApp1 e1 e1' p_e1_e1' e2)
        where
          Right (e1', p_e1_e1') = thm_progress e1 (TFunc x t_x t) p_e1_txt
thm_progress _e _t (TLet Empty e1 tx p_e1_tx x e2 t p_t y p_e2_t)
      = case (thm_progress e1 tx p_e1_tx) of
          Left ()               -> Right (subBV x e1 e2, ELetV x e1 e2)
          Right (e1', p_e1_e1') -> Right (Let x e1' e2, ELet e1 e1' p_e1_e1' x e2) 
thm_progress _e _t (TAnn Empty e1 t p_e1_t)
      = case (thm_progress e1 t p_e1_t) of
          Left ()               -> Right (e1, EAnnV e1 t)
          Right (e1', p_e1_e1') -> Right (Annot e1' t, EAnn e1 e1' p_e1_e1' t)
thm_progress _e _t (TSub Empty e s p_e_s t p_t p_s_t)
      = case (thm_progress e s p_e_s) of
          Left ()               -> Left ()
          Right (e', p_e_e')    -> Right (e', p_e_e') 

{-@ thm_preservation :: e:Expr -> t:Type -> ProofOf(HasType Empty e t) -> e':Expr
        -> ProofOf(Step e e') -> Either { pf:_ | false } { pf:_ | propOf pf == HasType Empty e' t} @-}
thm_preservation :: Expr -> Type -> HasType -> Expr -> Step -> Either Proof HasType 
thm_preservation e t (TBC _emp b)  e' st_e_e'       = Left () ? lem_value_stuck e e' st_e_e'
thm_preservation e t (TIC _emp n)  e' st_e_e'       = Left () ? lem_value_stuck e e' st_e_e' 
thm_preservation e t (TVar1 _ _ _) e' st_e_e'       = Left () ? lem_value_stuck e e' st_e_e'
thm_preservation e t (TVar2 _ _ _ _ _ _) e' st_e_e' = Left () ? lem_value_stuck e e' st_e_e'
thm_preservation e t (TPrm _emp c) e' st_e_e'       = Left () ? lem_value_stuck e e' st_e_e'
thm_preservation e t (TAbs {}) e' st_e_e'           = Left () ? lem_value_stuck e e' st_e_e'
{-thm_preservation e t p_e_t@(TApp Empty (Prim c) x t_x t' p_c_txt' e2 p_e2_tx) e' st_e_e'
  = case (thm_progress e2 t_x p_e2_tx) of
      Left ()                -> Right p_del_ex_t' ? lem_sem_det e e' st_e_e' (delta c e2) (EPrim c e2)
                                                  ? toProof ( ty c === TFunc x t_x t')
        where
          p_del_t'e2   = lem_delta_typ Empty c e2 x t_x t' p_e2_tx 
          p_emp_ex_t'  = lem_typing_wf Empty e t p_e_t WFEEmpty
          (WFExis _ _ _ _ _t' y p_y_t') = p_emp_ex_t'
          p_t'e2_ex_t' = lem_witness_sub Empty e2 t_x p_e2_tx x t' y p_y_t'
          p_del_ex_t'  = TSub Empty (delta c e2) (tsubBV x e2 t') p_del_t'e2 
                         (TExists x t_x t') p_emp_ex_t' p_t'e2_ex_t'
      Right (e2', st_e2_e2') -> Right (TApp Empty (Prim c) x t_x t' p_c_txt' e2' p_e2'_tx)
        where
          Right p_e2'_tx  = thm_preservation e2 t_x p_e2_tx e2' st_e2_e2' 
                                ? lem_sem_det e e' st_e_e' (App (Prim c) e2') 
                                              (EApp2 e2 e2' st_e2_e2' (Prim c) )-}
--thm_preservation e t (
--thm_preservation e t (
--thm_preservation e t (
thm_preservation e t (TAnn Empty e1 t_ p_e1_t) e' st_e_e'      
  = case (thm_progress e1 t p_e1_t) of
      Left ()                -> Right p_e1_t ? lem_sem_det e e' st_e_e' e1 (EAnnV e1 t)
      Right (e1', st_e1_e1') -> Right (TAnn Empty e1' t p_e1'_t)
                                  ? lem_sem_det e e' st_e_e' (Annot e1' t) (EAnn e1 e1' st_e1_e1' t)
          where
            Right p_e1'_t = thm_preservation e1 t p_e1_t e1' st_e1_e1'
thm_preservation e t (TSub Empty _e s p_e_s _t p_t p_s_t) e' st_e_e'
  = case (thm_preservation e s p_e_s e' st_e_e') of
      Left ()      -> Left ()
      Right p_e'_s -> Right (TSub Empty e' s p_e'_s t p_t p_s_t)
