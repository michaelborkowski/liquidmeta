{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-}
{- @ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module STLCSoundness where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Syntax
import Environments
import Semantics
import BareTyping
import WellFormedness
import Typing
import STLCLemmas

-- we must force these into scope for LH
semantics = (Step, EvalsTo)
typing = (HasBType, HasType, WFType, WFEnv, Subtype)
denotations = (Entails, Denotes, DenotesEnv, ValueDenoted)

-----------------------------------------------------------------------------
----- | SOUNDNESS of the SIMPLY-TYPED LAMBDA CALCULUS
-----------------------------------------------------------------------------

-- The STLC Progress Lemma
{-@ lemma_progress :: e:Expr -> t:BType -> ProofOf(HasBType BEmpty e t)  
           -> Either { pf:_ | isValue e && Set_emp (freeBV e) } 
                     (Expr, Step)<{\e' pf -> propOf pf == Step e e'}> @-}
lemma_progress :: Expr -> BType -> HasBType -> Either Proof (Expr,Step) 
lemma_progress c _b (BTBC BEmpty _)           = Left ()
lemma_progress c _b (BTIC BEmpty _)           = Left ()
lemma_progress x _t (BTVar1 BEmpty _ _)       = Left ()
lemma_progress x _t (BTVar2 BEmpty _ _ _ _ _) = Left ()
lemma_progress c _t (BTPrm BEmpty _)          = Left ()
lemma_progress e t  p_e_t@(BTAbs {})               
      = Left () ? lem_freeBV_emptyB BEmpty e t p_e_t 
lemma_progress _e _t (BTApp BEmpty (Prim p) t_x t p_e1_txt e2 p_e2_tx) 
      = case (lemma_progress e2 t_x p_e2_tx) of
          Left ()               -> Right (delta p e2, EPrim p e2)
          Right (e2', p_e2_e2') -> Right (App (Prim p) e2', EApp2 e2 e2' p_e2_e2' (Prim p))
lemma_progress _e _t (BTApp BEmpty (Lambda x e') t_x t p_e1_txt e2 p_e2_tx) 
      = case (lemma_progress e2 t_x p_e2_tx) of
          Left ()               -> Right (subBV x e2 e', EAppAbs x e' e2)
          Right (e2', p_e2_e2') -> Right (App (Lambda x e') e2', EApp2 e2 e2' p_e2_e2' (Lambda x e'))
lemma_progress _e _t (BTApp BEmpty e1 t_x t p_e1_txt e2 p_e2_tx) 
      = Right (App e1' e2, EApp1 e1 e1' p_e1_e1' e2)
        where
          Right (e1', p_e1_e1') = lemma_progress e1 (BTFunc t_x t) p_e1_txt
lemma_progress _e _t (BTLet BEmpty e1 tx p_e1_tx x e2 t y p_e2_t)
      = case (lemma_progress e1 tx p_e1_tx) of
          Left ()               -> Right (subBV x e1 e2, ELetV x e1 e2)
          Right (e1', p_e1_e1') -> Right (Let x e1' e2, ELet e1 e1' p_e1_e1' x e2) 
lemma_progress _e _t (BTAnn BEmpty e1 t liqt p_e1_t)
      = case (lemma_progress e1 t p_e1_t) of
          Left ()               -> Right (e1, EAnnV e1 liqt)
          Right (e1', p_e1_e1') -> Right (Annot e1' liqt, EAnn e1 e1' p_e1_e1' liqt)

{-@ assume lem_delta_btyp :: c:Prim -> v:Value -> t_x:BType -> t':BType
        -> ProofOf(HasBType BEmpty (Prim c) (BTFunc t_x t')) -> ProofOf(HasBType BEmpty v t_x)
        -> { pf:_ | propOf pf == HasBType BEmpty (delta c v) t' &&
                    not ((delta c v) == Crash) } @-}
lem_delta_btyp :: Prim -> Expr -> BType -> BType -> HasBType -> HasBType -> HasBType
lem_delta_btyp And v t_x t' p_c_txt' p_v_tx = undefined

{-@ lemma_preservation :: e:Expr -> t:BType -> ProofOf(HasBType BEmpty e t) -> e':Expr
        -> ProofOf(Step e e') -> Either { pf:_ | false } { pf:_ | propOf pf == HasBType BEmpty e' t} @-}
lemma_preservation :: Expr -> BType -> HasBType -> Expr -> Step -> Either Proof HasBType 
lemma_preservation e t (BTBC _emp b)  e' st_e_e'       = Left () ? lem_value_stuck e e' st_e_e'
lemma_preservation e t (BTIC _emp n)  e' st_e_e'       = Left () ? lem_value_stuck e e' st_e_e' 
lemma_preservation e t (BTVar1 _ _ _) e' st_e_e'       = Left () ? lem_value_stuck e e' st_e_e'
lemma_preservation e t (BTVar2 _ _ _ _ _ _) e' st_e_e' = Left () ? lem_value_stuck e e' st_e_e'
lemma_preservation e t (BTPrm _emp c) e' st_e_e'       = Left () ? lem_value_stuck e e' st_e_e'
lemma_preservation e t (BTAbs {}) e' st_e_e'           = Left () ? lem_value_stuck e e' st_e_e'
lemma_preservation e t p_e_t@(BTApp BEmpty (Prim c) t_x t' p_c_txt' e2 p_e2_tx) e' st_e_e'
  = case (lemma_progress e2 t_x p_e2_tx) of
      Left ()                -> Right p_del_t' ? lem_sem_det e e' st_e_e' (delta c e2) (EPrim c e2)
        where
          p_del_t'   = lem_delta_btyp c e2 t_x t' p_c_txt' p_e2_tx 
      Right (e2', st_e2_e2') -> Right (BTApp BEmpty (Prim c) t_x t' p_c_txt' e2' p_e2'_tx)
        where
          Right p_e2'_tx  = lemma_preservation e2 t_x p_e2_tx e2' st_e2_e2' 
                                ? lem_sem_det e e' st_e_e' (App (Prim c) e2') 
                                              (EApp2 e2 e2' st_e2_e2' (Prim c) )
lemma_preservation e t p_e_t@(BTApp BEmpty (Lambda w e1) t_x t' p_lam_txt' e2 p_e2_tx) e' st_e_e'
  = case (lemma_progress e2 t_x p_e2_tx) of
      Left ()                -> Right p_e1e2_t' ? lem_sem_det e e' st_e_e' 
                                                         (subBV w e2 e1) (EAppAbs w e1 e2)
                                                ? lem_subFV_unbind w y e2 e1
        where
          (BTAbs _ _ _tx _ _ y p_e1_t') = p_lam_txt' -- y:t_x |- e1 : t'
          p_e1e2_t'           = lem_subst_btyp BEmpty BEmpty y e2 t_x p_e2_tx 
                                              (unbind w y e1) t' p_e1_t'
      Right (e2', st_e2_e2') -> Right (BTApp BEmpty (Lambda w e1) t_x t' p_lam_txt' e2' p_e2'_tx)
        where
          Right p_e2'_tx      = lemma_preservation e2 t_x p_e2_tx e2' st_e2_e2'  
                                    ? lem_sem_det e e' st_e_e' (App (Lambda w e1) e2') 
                                                  (EApp2 e2 e2' st_e2_e2' (Lambda w e1))
lemma_preservation e t p_e_t@(BTApp BEmpty e1 t_x t' p_e1_txt' e2 p_e2_tx) e' st_e_e' 
  = case (lemma_progress e1 (BTFunc t_x t') p_e1_txt') of
      --Left ()                -> impossible "remove me later?"
      Right (e1', st_e1_e1') -> Right (BTApp BEmpty e1' t_x t' p_e1'_txt' e2 p_e2_tx)
        where
          Right p_e1'_txt'    = lemma_preservation e1 (BTFunc t_x t') p_e1_txt' e1' st_e1_e1'
                                    ? lem_sem_det e e' st_e_e' (App e1' e2)
                                                  (EApp1 e1 e1' st_e1_e1' e2)
lemma_preservation e t p_e_t@(BTLet BEmpty e_x t_x p_ex_tx x e1 _t y p_e1_t) e' st_e_e'
  = case (lemma_progress e_x t_x p_ex_tx) of 
      Left ()                 -> Right p_e1ex_t
                                     ? lem_sem_det e e' st_e_e' (subBV x e_x e1) (ELetV x e_x e1)
--                                     ? lem_free_bound_in_env Empty t p_emp_t y
        where
          {- @ p_e1ex_t :: ProofOf(HasType Empty (subBV x e_x e1) t) @-} -- (tsubBV x e_x t)) @-}
          p_e1ex_t             = lem_subst_btyp BEmpty BEmpty y e_x t_x p_ex_tx 
                                           (unbind x y e1) t p_e1_t
                                           ? lem_subFV_unbind x y e_x e1 
                                     -- ? lem_tfreeBV_empty Empty t p_emp_t WFEEmpty
                                     -- ? lem_tsubBV_inval x e_x t
                                     -- ? toProof ( t === tsubBV x e_x t ) 
      Right (e_x', st_ex_ex') -> Right (BTLet BEmpty e_x' t_x p_ex'_tx x e1 t y p_e1_t)
        where
          Right p_ex'_tx       = lemma_preservation e_x t_x p_ex_tx e_x' st_ex_ex'
                                     ? lem_sem_det e e' st_e_e' (Let x e_x' e1) 
                                                   (ELet e_x e_x' st_ex_ex' x e1)
lemma_preservation e t (BTAnn BEmpty e1 t_ liqt p_e1_t) e' st_e_e'      
  = case (lemma_progress e1 t p_e1_t) of
      Left ()                -> Right p_e1_t ? lem_sem_det e e' st_e_e' e1 (EAnnV e1 liqt)
      Right (e1', st_e1_e1') -> Right (BTAnn BEmpty e1' t liqt p_e1'_t)
                                  ? lem_sem_det e e' st_e_e' (Annot e1' liqt) (EAnn e1 e1' st_e1_e1' liqt)
          where
            Right p_e1'_t = lemma_preservation e1 t p_e1_t e1' st_e1_e1'

-- Lemma. The underlying bare type system is sound. This is the textbook
--          soundness proof for the STLC.
{-@ lemma_soundness :: e:Expr -> e':Expr -> ProofOf(EvalsTo e e') -> b:BType
                   -> ProofOf(HasBType BEmpty e b) -> ProofOf(HasBType BEmpty e' b) @-}
lemma_soundness :: Expr -> Expr -> EvalsTo -> BType -> HasBType -> HasBType
lemma_soundness e e' p_ee' b p_eb = case p_ee' of 
  (Refl e)                           -> p_eb  
  (AddStep _e e1 st_e_e1 _e' p_e1e') -> lemma_soundness e1 e' p_e1e' b p_e1b
    where
      Right p_e1b = lemma_preservation e b p_eb e1 st_e_e1

