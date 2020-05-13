{-# LANGUAGE GADTs #-}

{-@ LIQUID "--no-termination" @-} -- TODO assume
{-@ LIQUID "--no-totality" @-} -- TODO assume
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module MainTheorems where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import BasicProps
import Typing
import Primitives
import Primitives3
import STLCLemmas
import STLCSoundness
import TechLemmas
import TechLemmas2
import DenotationalSoundness 
import Substitution
import Primitives5

-- force these into scope
semantics = (Step, EvalsTo)
typing = (HasBType, HasType, WFType, WFEnv, Subtype)
denotations = (Entails, Denotes, DenotesEnv, AugmentedCSubst, lem_subst_typ)

{-@ reflect foo18 @-}
foo18 x = Just x
foo18 :: a -> Maybe a

  -- Last Lemmas
{-
{-@ lemma_function_values :: v:Value -> x:Vname -> t:Type -> t':Type
          -> { p_v_tt':HasType | propOf p_v_tt' == HasType Empty v (TFunc x t t') }
          -> { pf:_ | isLambda v || isPrim v } / [typSize p_v_tt'] @-}
lemma_function_values :: Expr -> Type -> Type -> HasType -> Proof
lemma_function_values e t t' (TPrm {})   = ()
lemma_function_values e t t' (TAbs {})   = ()
lemma_function_values e t t' (TSub 
-}

--------------------------------------------------------------------------------
--- | PROGRESS and PRESERVATION
--------------------------------------------------------------------------------

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
thm_progress _e _t (TApp Empty e1 x t_x t p_e1_txt e2 p_e2_tx) = case e1 of
      (Prim p)      -> case (thm_progress e2 t_x p_e2_tx) of
          Left ()               -> Right (delta p e2, EPrim p e2)
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
                  p_e1_er_txt = lem_typing_hasbtype Empty e1 (TFunc x t_x t) p_e1_txt WFEEmpty
{-thm_progress _e _t (TApp Empty (Prim p) x t_x t p_e1_txt e2 p_e2_tx) 
thm_progress _e _t (TApp Empty (Lambda x e') _x t_x t p_e1_txt e2 p_e2_tx) 
thm_progress _e _t (TApp Empty e1 x t_x t p_e1_txt e2 p_e2_tx) -}
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
thm_preservation e t p_e_t@(TApp Empty (Prim c) x t_x t' p_c_txt' e2 p_e2_tx) e' st_e_e'
  = case (thm_progress e2 t_x p_e2_tx) of
      Left ()                -> Right p_del_ex_t' ? lem_sem_det e e' st_e_e' (delta c e2) (EPrim c e2)
        where
          p_del_t'e2   = lem_delta_typ Empty c e2 x t_x t' p_c_txt' p_e2_tx 
          p_emp_ex_t'  = lem_typing_wf Empty e t p_e_t WFEEmpty
          (WFExis _ _ _ _ _t' y p_y_t') = p_emp_ex_t'
          p_t'e2_ex_t' = lem_witness_sub Empty e2 t_x p_e2_tx WFEEmpty x t' y p_y_t'
          p_del_ex_t'  = TSub Empty (delta c e2) (tsubBV x e2 t') p_del_t'e2 
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
          (TAbs _ _ _tx p_tx _ _ y p_e1_t') = p_lam_txt' -- y:t_x |- e1 : t'
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
      --Left ()                -> impossible "remove me later?"
      Right (e1', st_e1_e1') -> Right (TApp Empty e1' x t_x t' p_e1'_txt' e2 p_e2_tx)
        where
          Right p_e1'_txt'    = thm_preservation e1 (TFunc x t_x t') p_e1_txt' e1' st_e1_e1'
                                    ? lem_sem_det e e' st_e_e' (App e1' e2)
                                                  (EApp1 e1 e1' st_e1_e1' e2)
thm_preservation e t p_e_t@(TLet Empty e_x t_x p_ex_tx x e1 _t p_emp_t y p_e1_t) e' st_e_e'
  = case (thm_progress e_x t_x p_ex_tx) of 
      Left ()                 -> Right p_e1ex_t
                                     ? lem_sem_det e e' st_e_e' (subBV x e_x e1) (ELetV x e_x e1)
                                     ? lem_free_bound_in_env Empty t p_emp_t y
        where
          p_tx                 = lem_typing_wf Empty e_x t_x p_ex_tx WFEEmpty
          p_wf_ytx             = WFEBind Empty WFEEmpty y t_x p_tx
          {-@ p_e1ex_t :: ProofOf(HasType Empty (subBV x e_x e1) t) @-} -- (tsubBV x e_x t)) @-}
          p_e1ex_t             = lem_subst_typ Empty Empty y e_x t_x p_ex_tx p_wf_ytx
                                           (unbind x y e1) (unbindT x y t) p_e1_t
                                           ? lem_subFV_unbind x y e_x e1 
                                           ? lem_tsubFV_unbindT x y e_x t
                                     ? lem_tfreeBV_empty Empty t p_emp_t WFEEmpty
                                     ? lem_tsubBV_inval x e_x t
                                     ? toProof ( t === tsubBV x e_x t ) 
      Right (e_x', st_ex_ex') -> Right (TLet Empty e_x' t_x p_ex'_tx x e1 t p_emp_t y p_e1_t)
        where
          Right p_ex'_tx       = thm_preservation e_x t_x p_ex_tx e_x' st_ex_ex'
                                     ? lem_sem_det e e' st_e_e' (Let x e_x' e1) 
                                                   (ELet e_x e_x' st_ex_ex' x e1)
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

{-@ thm_crashfree :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t) 
                           -> { pf:_ | not (e == Crash) } @-}
thm_crashfree :: Env -> Expr -> Type -> HasType -> Proof
thm_crashfree g e t (TBC _ _)  = ()
thm_crashfree g e t (TIC _ _)  = ()
thm_crashfree g e t (TVar1 {}) = ()
thm_crashfree g e t (TVar2 {}) = ()
thm_crashfree g e t (TPrm _ _) = ()
thm_crashfree g e t (TAbs {})  = ()
thm_crashfree g e t (TApp {})  = ()
thm_crashfree g e t (TLet {})  = ()
thm_crashfree g e t (TAnn {})  = ()
thm_crashfree g e t (TSub _ _ s p_e_s _ _ _)
  = thm_crashfree g e s p_e_s

data ValueReducedP where
    ValueReduced :: Expr -> Type -> ValueReducedP

{-@ data ValueReduced where
    ValRed :: e:Expr -> t:Type -> v:Value -> ProofOf(EvalsTo e v)
                     -> ProofOf(HasType Empty v t) -> ProofOf(ValueReduced e t) @-}
data ValueReduced where
    ValRed :: Expr -> Type -> Expr -> EvalsTo -> HasType -> ValueReduced

{-@ thm_soundness :: { e:Expr | not (e == Crash) } -> t:Type -> ProofOf(HasType Empty e t)
                         -> ProofOf(ValueReduced e t) @-}
thm_soundness :: Expr -> Type -> HasType -> ValueReduced
thm_soundness e t p_e_t = case ( thm_progress e t p_e_t ) of
  Left ()             -> ValRed e t e (Refl e) p_e_t
  Right (e', st_e_e') -> ValRed e t v ev_e_v p_v_t
    where
      Right p_e'_t     = thm_preservation e t p_e_t e' st_e_e'
      ValRed _ _ v ev_e'_v p_v_t = thm_soundness (e' ? thm_crashfree Empty e' t p_e'_t) t p_e'_t 
      ev_e_v           = AddStep e e' st_e_e' v ev_e'_v

