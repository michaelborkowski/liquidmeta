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

{-@ reflect foo33 @-}   
foo33 x = Just x 
foo33 :: a -> Maybe a 

{-@ lem_subtype_repetition :: g:Env -> b:Basic -> x:RVname ->  p:Pred 
        -> ProofOf(WFType g (TRefn b x p) Base)
        -> ProofOf(Subtype g (TRefn b x p) (TRefn b x (App (App (Prim Conj) p) p))) @-}
lem_subtype_repetition :: Env -> Basic -> RVname -> Pred -> WFType -> Subtype
lem_subtype_repetition g b x p p_g_t 
  = SBase g x b p x pandp y ent_pandp
      where
        (y, pf_p_bl) = lem_ftyp_for_wf_trefn g b x p Base p_g_t
        pandp     = App (App (Prim Conj) p) p
        ent_pandp = lem_entails_repetition g b x p y pf_p_bl

{-@ lem_self_refn_sub :: g:Env -> b:Basic -> z:RVname -> p:Pred -> ProofOf(WFEnv g)
        -> ProofOf(WFType g (TRefn b z p) Base) ->  e:Term
        -> ProofOf(HasFType (erase_env g) e (FTBasic b))
        -> ProofOf(Subtype g (self (TRefn b z p) e Base) (TRefn b z p)) @-}          
lem_self_refn_sub :: Env -> Basic -> RVname -> Pred -> WFEnv -> WFType -> Expr 
                         -> HasFType -> Subtype
lem_self_refn_sub g b z p p_g_wf p_g_t{- @(WFRefn _ _ _ _ _ _ w pf_p_bl)-} e_ p_e_t
  = SBase g z b selfp z p w ent_selfp_p
      where
        {-@ w :: { ww:Vname | not (in_env ww g) && not (Set_mem ww (fv p)) && not (Set_mem ww (ftv p)) } @-}
        (w, pf_p_bl) = lem_ftyp_for_wf_trefn g b z p Base p_g_t
        e            = e_ ? lem_freeBV_emptyB (erase_env g) e_ (FTBasic b) p_e_t
                          ? lem_fv_subset_bindsF (erase_env g) e_ (FTBasic b) p_e_t
                          ? lem_subBV_notin 0 (FV w) e_
        p_er_g_wf    = lem_erase_env_wfenv g p_g_wf
        pf_q_bl      = lem_eqlPred_ftyping g b z p p_g_t p_er_g_wf w e p_e_t
        selfp        = selfify p b z e
        ent_selfp_p  = lem_entails_elimination g b z (eqlPred (TRefn b z p) e) 
                           (p ? lem_freeBV_unbind_empty 0 w 
                              (p ? lem_freeBV_emptyB (FCons w (FTBasic b) (erase_env g)) (unbind 0 w p)
                                                     (FTBasic TBool) pf_p_bl))
                           (w ? lem_fv_bound_in_fenv (erase_env g) e (FTBasic b) p_e_t w)
                           pf_q_bl pf_p_bl 

{- NOT NEEDED anymore: remove this when finished
-----------------------------------replace z' with z below, only one RVname param------------------------
{-@ lem_self_tt_sub_eql :: g:Env -> b:Basic -> z:RVname -> { x:Vname | not (in_env x g) } 
        -> ProofOf(Subtype (Cons x (TRefn b z (Bc True)) g) 
             (self (TRefn b z (Bc True)) (FV x)) (TRefn b z (App (App (equals b) (BV z')) (FV x)))) @-} 
lem_self_tt_sub_eql :: Env -> Basic -> RVname -> Vname -> Subtype
lem_self_tt_sub_eql g b z z' x  
    = SBase (Cons x t g) z b ttq z' eqx' w ent_ttq_eqx'
      where
        ent_ttq_qtt  = lem_entails_and_commutes (Cons x t g) b z (Bc True) eqx w pf_tt_bl pf_eqx_bl
        ent_qtt_eqx  = lem_entails_elimination (Cons x t g) b z eqx (Bc True) w pf_eqx_bl pf_tt_bl
        ent_ttq_eqx  = lem_entails_trans (Cons x t g) b z (App (App (Prim And) (Bc True)) eqx) 
                                         z (App (App (Prim And) eqx) (Bc True)) z eqx 
                                         w ent_ttq_qtt ent_qtt_eqx
        {-@ ent_eqx_eqx' :: { ent:Entails | propOf ent == Entails (Cons w (TRefn b z eqx) (Cons x t g)) 
                                                                  (unbind z' w eqx') } @-}
        ent_eqx_eqx' = lem_entails_change_bv (Cons x t g) b z eqx z' eqx' w
        ent_ttq_eqx' = lem_entails_trans (Cons x t g) b z (App (App (Prim And) (Bc True)) eqx)
                                         z eqx z' eqx' w ent_ttq_eqx ent_eqx_eqx'
        ttq          = App (App (Prim And) (Bc True)) eqx 
                         ? toProof ( selfify (Bc True) b z (FV x)
                                 === App (App (Prim And) (Bc True)) (App (App (equals b) (BV z)) (FV x)) 
                                 === App (App (Prim And) (Bc True)) eqx)
        qtt          = App (App (Prim And) eqx) (Bc True) 
        {-@ eqx' :: { q:Expr | freeBV q == Set_sng z' && not (Set_mem w (fv q)) && fv q == Set_sng x &&
                            subBV z' (FV w) q == App (App (equals b) (FV w)) (FV x) &&
                            unbind z' w q == unbind z w eqx &&
                            selfify (Bc True) b z' (FV x) == App (App (Prim And) (Bc True)) q} @-}
        eqx'         = (App (App (equals b) (BV z')) (FV x))
        {-@ eqx :: { q:Expr | freeBV q == Set_sng z && not (Set_mem w (fv q)) && fv q == Set_sng x &&
                            subBV z (FV w) q == App (App (equals b) (FV w)) (FV x) &&
                            selfify (Bc True) b z (FV x) == App (App (Prim And) (Bc True)) q} @-}
        eqx          = (App (App (equals b) (BV z)) (FV x))

        w            = fresh_var_excluding g x
        g2           = (FCons w (FTBasic b) (erase_env (Cons x t g)))
        t            = TRefn b z (Bc True)
        pf_tt_bl     = FTBC g2 True
        (Prim c)     = equals b
        pf_eqx_bl    = FTApp g2 (App (equals b) (FV w)) (FTBasic b) (FTBasic TBool)
                         (FTApp g2 (equals b) (FTBasic b) (FTFunc (FTBasic b) (FTBasic TBool))
                                (FTPrm g2 c) (FV w) (FTVar1 (erase_env (Cons x t g)) w (FTBasic b)))
                         (FV x) (FTVar2 (erase_env (Cons x t g)) x (FTBasic b)
                                        (FTVar1 (erase_env g) x (FTBasic b)) w (FTBasic b)) 
-}
