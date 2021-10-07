{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SubtypingFromEntailments where

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
import BasicPropsWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasSubstitution
import SystemFSoundness
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import PrimitivesSemantics
import LemmasWellFormedness
import Implications
import Entailments

{-@ reflect foo40 @-}   
foo40 x = Just x 
foo40 :: a -> Maybe a 

{-@ lem_subtype_repetition :: g:Env -> ProofOf(WFFE (erase_env g)) -> b:Basic -> x:RVname ->  p:Term
        -> ProofOf(WFType g (TRefn b x p) Base) -> { p':Term | Set_sub (fv p') (binds g) }
        -> ( th':CSub -> ProofOf(DenotesEnv (Cons (fresh_var g) (TRefn b x p) g) th')
                      -> ProofOf(EvalsTo (csubst th' (unbind 0 (fresh_var g) p)) (Bc True))
                      -> ProofOf(EvalsTo (csubst th' (unbind 0 (fresh_var g) p')) (Bc True)) )
        -> ProofOf(Subtype g (TRefn b x p) (TRefn b x (Conj p' p))) @-}
lem_subtype_repetition :: Env -> WFFE -> Basic -> RVname -> Expr -> WFType 
           -> Expr -> (CSub -> DenotesEnv -> EvalsTo -> EvalsTo ) -> Subtype
lem_subtype_repetition g p_g_wf b x p_ p_g_t p'_ transf_func
  = SBase g x b p x pandp y ent_pandp
      where
        p         = p_  ? lem_term_pred p_
        p'        = p'_ ? lem_term_pred p'_
        y_        = fresh_var g 
        y         = y_ ? lem_free_bound_in_env g (TRefn b x p) Base p_g_t y_
        pf_p_bl   = lem_ftyp_for_wf_trefn' g b x p Base p_g_t p_g_wf
        pandp     = Conj p' p
        ent_pandp = lem_entails_repetition g p_g_wf b x p y pf_p_bl p_g_t p' transf_func

{-@ lem_subtype_itself :: g:Env -> ProofOf(WFFE (erase_env g)) -> b:Basic -> x:RVname ->  p:Pred
        -> ProofOf(WFType g (TRefn b x p) Base)
        -> ProofOf(Subtype g (TRefn b x p) (TRefn b x p)) @-}
lem_subtype_itself :: Env -> WFFE -> Basic -> RVname -> Expr -> WFType -> Subtype
lem_subtype_itself g p_g_wf b x p p_g_t = SBase g x b p x p y ent_p
  where
    y_      = fresh_var g
    y       = y_ ? lem_free_bound_in_env g (TRefn b x p) Base p_g_t y_
    pf_p_bl = lem_ftyp_for_wf_trefn' g b x p Base p_g_t p_g_wf
    ent_p   = lem_entails_itself g p_g_wf b x p y pf_p_bl p_g_t

{-@ lem_subtype_itself_trivial :: g:Env -> ProofOf(WFFE (erase_env g)) -> b:Basic -> x:RVname 
        -> { tt:Pred | isTrivial tt } -> ProofOf(Subtype g (TRefn b x tt) (TRefn b x tt)) @-}
lem_subtype_itself_trivial :: Env -> WFFE -> Basic -> RVname -> Expr -> Subtype
lem_subtype_itself_trivial g p_g_wf b x tt  = SBase g x b tt x tt y ent_tt
  where
    y_      = fresh_var g
    y       = y_ ? lem_trivial_nofv tt 
    ent_tt  = lem_entails_itself_trivial g p_g_wf b x tt y 

{-@ lem_self_refn_sub :: g:Env -> b:Basic -> z:RVname -> p:Pred -> ProofOf(WFEnv g)
        -> ProofOf(WFType g (TRefn b z p) Base) ->  e:Term
        -> ProofOf(HasFType (erase_env g) e (FTBasic b))
        -> ProofOf(Subtype g (self (TRefn b z p) e Base) (TRefn b z p)) @-}          
lem_self_refn_sub :: Env -> Basic -> RVname -> Expr -> WFEnv -> WFType -> Expr 
                         -> HasFType -> Subtype
lem_self_refn_sub g b z p p_g_wf p_g_t{- @(WFRefn _ _ _ _ _ _ w pf_p_bl)-} e_ p_e_t
  = SBase g z b selfp z p w ent_selfp_p
      where
        w_           = fresh_var g
        w            = w_ ? lem_free_bound_in_env g (TRefn b z p) Base p_g_t w_
        p_er_g_wf    = lem_erase_env_wfenv g p_g_wf
        pf_p_bl      = lem_ftyp_for_wf_trefn' g b z p Base p_g_t p_er_g_wf
        e            = e_ ? lem_freeBV_emptyB (erase_env g) e_ (FTBasic b) p_e_t
                          ? lem_fv_subset_bindsF (erase_env g) e_ (FTBasic b) p_e_t
                          ? lem_subBV_notin 0 (FV w) e_
        pf_q_bl      = lem_eqlPred_ftyping g b z p p_g_t p_er_g_wf w e p_e_t
        selfp        = selfify p b z e
        p_g_tpq      = lem_selfify_wf g (TRefn b z p) Base p_g_t p_er_g_wf e p_e_t
        ent_selfp_p  = lem_entails_elimination g p_er_g_wf b z (eqlPred (TRefn b z p) e) 
                           (p ? lem_freeBV_unbind_empty 0 w 
                              (p ? lem_freeBV_emptyB (FCons w (FTBasic b) (erase_env g)) (unbind 0 w p)
                                                     (FTBasic TBool) pf_p_bl))
                           (w ? lem_fv_bound_in_fenv (erase_env g) e (FTBasic b) p_e_t w)
                           pf_q_bl pf_p_bl p_g_tpq

{- NOT NEEDED anymore: remove this when finished
{ -@ lem_self_tt_sub_eql :: see Lambda 1.1 -}
