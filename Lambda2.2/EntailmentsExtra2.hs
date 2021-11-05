{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module EntailmentsExtra2 where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Strengthenings
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
import BasicPropsEraseTyping
import LemmasWeakenWFTV
import PrimitivesSemantics
import LemmasWellFormedness
import SubstitutionWFAgain
import Implications
import Entailments
import DenotationsSoundness
import SubstitutionLemmaEntTV
import SubstitutionLemmaWFEnv
import EntailmentsExtra

{-@ reflect foo67 @-}
foo67 x = Just x 
foo67 :: a -> Maybe a 

{-@ lem_entails_strengthen :: g:Env -> ProofOf(WFFE (erase_env g)) -> b:Basic -> x:RVname -> r:Pred
        -> k1:Kind -> ProofOf(WFType g (TRefn b x r) k1)
        -> p:Pred -> q:Pred -> k2:Kind -> ProofOf(WFType g (TRefn b x (strengthen p q)) k2)
        -> { y:Vname | not (in_env y g) }
        -> ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y p))
        -> ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y q))
        -> ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y (strengthen p q))) / [esize p] @-}
lem_entails_strengthen :: Env -> WFFE -> Basic -> RVname -> Expr -> Kind -> WFType -> Expr -> Expr
                              -> Kind -> WFType -> Vname -> Entails -> Entails -> Entails
lem_entails_strengthen g p_g_wf b x r k1 p_g_t1 p q k2 p_g_tpq y ent_yenv_p ent_yenv_q
  = lem_entails_conjunction' g p_g_wf b x r k1 p_g_t1 (p ? p_nobv_pf) (q ? q_nobv_pf)
                             (y ? y_notin_pf) pf_y_p_bl pf_y_q_bl ent_yenv_p ent_yenv_q
      where 
        p_er_g_b    = lem_erase_wftype g (TRefn b x r) k1 p_g_t1
        p_er_frg_wf = WFFBind (erase_env g) p_g_wf (fresh_var g) (FTBasic b) k1 p_er_g_b
        pf_fr_pq_bl = lem_ftyp_for_wf_trefn' g b x (strengthen p q) k2 p_g_tpq p_g_wf
        pf_y_pq_bl  = lem_change_var_ftyp (erase_env g) (fresh_var g) (FTBasic b) FEmpty 
                          p_er_frg_wf (unbind 0 (fresh_var g) (strengthen p q)) 
                          (FTBasic TBool) pf_fr_pq_bl y 
                          ? lem_subFV_unbind 0 (fresh_var g) (FV y) (strengthen p q ? fr_notin_pf)
        (pf_y_p_bl, pf_y_q_bl)
                    = lem_unstrengthen_ftyping (FCons y (FTBasic b) (erase_env g)) 
                                               (unbind 0 y p) (unbind 0 y q) (pf_y_pq_bl
                                               ? lem_subBV_strengthen 0 (FV y) p q)

        p_nobv_pf   = lem_freeBV_unbind_empty 0 y 
                        (p ? lem_freeBV_emptyB (FCons y (FTBasic b) (erase_env g)) 
                                               (unbind 0 y p) (FTBasic TBool) pf_y_p_bl)
        q_nobv_pf   = lem_freeBV_unbind_empty 0 y 
                        (q ? lem_freeBV_emptyB (FCons y (FTBasic b) (erase_env g))
                                               (unbind 0 y q) (FTBasic TBool) pf_y_q_bl)
        y_notin_pf  = lem_free_bound_in_env g (TRefn b x (strengthen p q)) k2 p_g_tpq y
        fr_notin_pf = lem_free_bound_in_env g (TRefn b x (strengthen p q)) k2 p_g_tpq (fresh_var g)

{-@ lem_entails_unstrengthen :: g:Env -> ProofOf(WFFE (erase_env g)) -> b:Basic -> x:RVname -> r:Pred
        -> k1:Kind -> ProofOf(WFType g (TRefn b x r) k1)
        -> p:Pred -> q:Pred -> k2:Kind -> ProofOf(WFType g (TRefn b x (strengthen p q)) k2)
        -> { y:Vname | not (in_env y g) }
        -> ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y (strengthen p q)))
        -> (ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y p)),
            ProofOf(Entails (Cons y (TRefn b x r) g) (unbind 0 y q))) @-}
lem_entails_unstrengthen :: Env -> WFFE -> Basic -> RVname -> Expr -> Kind -> WFType -> Expr -> Expr
                              -> Kind -> WFType -> Vname -> Entails -> (Entails, Entails)
lem_entails_unstrengthen g p_g_wf b x r k1 p_g_t1 p q k2 p_g_tpq y ent_yenv_pq
  = lem_entails_disjunction' g p_g_wf b x r k1 p_g_t1 (p ? p_nobv_pf) (q ? q_nobv_pf) 
                             (y ? y_notin_pf) pf_y_p_bl pf_y_q_bl ent_yenv_pq
      where
        p_er_g_b    = lem_erase_wftype g (TRefn b x r) k1 p_g_t1
        p_er_frg_wf = WFFBind (erase_env g) p_g_wf (fresh_var g) (FTBasic b) k1 p_er_g_b
        pf_fr_pq_bl = lem_ftyp_for_wf_trefn' g b x (strengthen p q) k2 p_g_tpq p_g_wf
        pf_y_pq_bl  = lem_change_var_ftyp (erase_env g) (fresh_var g) (FTBasic b) FEmpty 
                          p_er_frg_wf (unbind 0 (fresh_var g) (strengthen p q)) 
                          (FTBasic TBool) pf_fr_pq_bl y 
                          ? lem_subFV_unbind 0 (fresh_var g) (FV y) (strengthen p q ? fr_notin_pf)
        (pf_y_p_bl, pf_y_q_bl)
                    = lem_unstrengthen_ftyping (FCons y (FTBasic b) (erase_env g)) 
                                               (unbind 0 y p) (unbind 0 y q) (pf_y_pq_bl
                                               ? lem_subBV_strengthen 0 (FV y) p q)

        p_nobv_pf   = lem_freeBV_unbind_empty 0 y 
                        (p ? lem_freeBV_emptyB (FCons y (FTBasic b) (erase_env g)) 
                                               (unbind 0 y p) (FTBasic TBool) pf_y_p_bl)
        q_nobv_pf   = lem_freeBV_unbind_empty 0 y 
                        (q ? lem_freeBV_emptyB (FCons y (FTBasic b) (erase_env g))
                                               (unbind 0 y q) (FTBasic TBool) pf_y_q_bl)
        y_notin_pf  = lem_free_bound_in_env g (TRefn b x (strengthen p q)) k2 p_g_tpq y
        fr_notin_pf = lem_free_bound_in_env g (TRefn b x (strengthen p q)) k2 p_g_tpq (fresh_var g)

{-@ binds_proof_helper :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') }
        -> b':Basic -> z:RVname -> q:Pred -> k_a:Kind -> ProofOf(WFType g (TRefn b' z q) k_a)
        -> { y:Vname | not (in_env y (concatE (ConsT a k_a g) g')) } -> s:Type
        -> { pf:_ | Set_emp (Set_cap (binds (ConsT a k_a g)) (binds g')) &&
                    Set_emp (Set_cap (binds g) (binds (Cons y s g'))) &&
                    Set_emp (Set_cap (binds (ConsT a k_a g)) (binds (Cons y s g'))) &&
                    Set_emp (Set_cap (binds g) (binds (esubFTV a (TRefn b' z q) g'))) &&
                    not (in_env y (concatE g (esubFTV a (TRefn b' z q) g'))) &&
                    not (in_env a (Cons y s g')) &&
                    (concatE g (esubFTV a (TRefn b' z q) (Cons y s g'))
                         ==  Cons y (tsubFTV a (TRefn b' z q) s)
                                    (concatE g (esubFTV a (TRefn b' z q) g'))) }  @-}
binds_proof_helper :: Env -> Env -> Vname -> Basic -> RVname -> Expr -> Kind -> WFType 
                          -> Vname -> Type -> Proof
binds_proof_helper g g' a b' z q k_a p_g_ta y s 
  = () ? binds (esubFTV a (TRefn b' z q) g') -- ? binds (esubFTV a (TRefn b' z q) (Cons y s g'))
       ? lem_in_env_concat (ConsT a k_a g) g' y
       ? lem_in_env_esubFTV g' a (TRefn b' z q) y
       ? lem_in_env_concat g  (esubFTV a (TRefn b' z q) g') y

{-@ lem_subst_tv_sub_sbase_ftv :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
      -> { a:Vname | (not (in_env a g)) && not (in_env a g') } 
      -> b':Basic -> z:RVname -> q:Pred -> k_a:Kind -> ProofOf(WFType g (TRefn b' z q) k_a) 
      -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) 
      -> z1:RVname -> p1:Pred -> k_s:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') (TRefn (FTV a) z1 p1) k_s)
      -> z2:RVname -> p2:Pred -> k_t:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') (TRefn (FTV a) z2 p2) k_t)
      -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (ConsT a k_a g) g') 
                                             (TRefn (FTV a) z1 p1) (TRefn (FTV a) z2 p2)  && isSBase p_s_t }
      -> ProofOf(Subtype (concatE g (esubFTV a (TRefn b' z q) g')) (tsubFTV a (TRefn b' z q) (TRefn (FTV a) z1 p1)) 
                                                              (tsubFTV a (TRefn b' z q) (TRefn (FTV a) z2 p2))) @-}
lem_subst_tv_sub_sbase_ftv :: Env -> Env -> Vname -> Basic -> RVname -> Expr -> Kind -> WFType -> WFEnv
      -> RVname -> Expr -> Kind -> WFType -> RVname -> Expr -> Kind -> WFType -> Subtype -> Subtype
lem_subst_tv_sub_sbase_ftv g g' a b' z q k_a p_g_ta p_env_wf z1 p1 k_s p_env_s z2 p2 k_t p_env_t 
                       (SBase env _z1 b _p1 _z2 _p2 y ent_yenv_p2) 
  = SBase (concatE g (esubFTV a t_a g')) z b' (strengthen (subFTV a t_a p1) q)
          z (strengthen (subFTV a (t_a ? noex) p2) q) (y ? fv_pf) ent_yenv'_p2taq ? t1pf ? t2pf
      where 
        t_a              = TRefn b' z q
        s                = TRefn (FTV a) z1 p1 
        p_er_g_ta        = lem_erase_wftype g t_a k_a p_g_ta
        p_yenv_wf        = WFEBind (concatE (ConsT a k_a g) (g' ? binds_pf)) p_env_wf y s k_s p_env_s
        p_er_env_wf      = lem_erase_env_wfenv env p_env_wf
        env'             = concatE g (esubFTV a t_a g')
        p_env'_wf        = lem_subst_tv_wfenv g g' a t_a k_a p_g_ta p_env_wf
        p_er_env'_wf     = lem_erase_env_wfenv env' p_env'_wf

        env              = (concatE (ConsT a k_a g) (g' ? binds_pf))
        p_er_g_t         = lem_erase_wftype (concatE (ConsT a k_a g) (g' ? binds_pf)) 
                                            (TRefn (FTV a) z2 p2) k_t p_env_t
        p_er_frg_wf      = WFFBind (erase_env env) p_er_env_wf 
                                   (fresh_var env) (FTBasic (FTV a)) k_t p_er_g_t
        pf_fr_p2_bl      = lem_ftyp_for_wf_trefn' env (FTV a) z2 p2 k_t p_env_t p_er_env_wf
        pf_y_p2_bl       = lem_change_var_ftyp (erase_env env) (fresh_var env) (FTBasic (FTV a)) FEmpty 
                               p_er_frg_wf (unbind 0 (fresh_var env) p2) 
                               (FTBasic TBool) pf_fr_p2_bl y 
                               ? lem_subFV_unbind 0 (fresh_var env) (FV y) (p2 ? fr_pf)

        {- @ t1 :: { t1_:Type | t1_ == tsubFTV a t_a s } @-}
        t1               = TRefn b' z (strengthen (subFTV a (t_a ? noex) p1) q) ? t1pf
        p_env'_t1        = lem_subst_tv_wf'   g g' a t_a k_a p_g_ta p_env_wf s k_s p_env_s
        {- @ t2 :: { t2_:Type | t2_ == tsubFTV a t_a (TRefn (FTV a) z2 p2) } @-}
        t2               = TRefn b' z (strengthen (subFTV a (t_a ? noex) p2) q) ? t2pf
        p_env'_t2        = lem_subst_tv_wf'   g g' a t_a k_a p_g_ta p_env_wf 
                                              (TRefn (FTV a) z2 p2) k_t p_env_t ? t2pf

        {- @ ent_yenv_p2     :: Entails (Cons y  s env)  (unbind 0 y p2) @-}
        {-@ ent_yenv'_p2ta  :: ProofOf(Entails (Cons y (tsubFTV a t_a s) env') 
                                               (unbind 0 y (subFTV a t_a p2))) @-}
        ent_yenv'_p2ta   = lem_subst_tv_ent g (Cons y s g') (a ? binds_pf) t_a k_a p_g_ta p_yenv_wf
                                            (unbind 0 y p2 ? free_sub) (ent_yenv_p2 {-? cons_yenv-}) ? binds_pf 
                                   ? lem_commute_subFTV_unbind a t_a -- (t_a ? noex)
                                       (0 ? lem_tfreeBV_empty g t_a k_a p_g_ta) y p2
        {-@ ent_yenv'_p1taq :: ProofOf(Entails (Cons y (tsubFTV a t_a s) env') 
                                               (unbind 0 y (strengthen (subFTV a t_a p1) q))) @-}
        ent_yenv'_p1taq  = lem_entails_itself' env' p_er_env'_wf b' z (strengthen (subFTV a t_a p1) q)
                                               k_s p_env'_t1 (y ? binds_pf)  ? t1pf
        {-@ ent_yenv'_q     :: ProofOf(Entails (Cons y (tsubFTV a t_a s) env') (unbind 0 y q)) @-}
        (_, ent_yenv'_q) = lem_entails_unstrengthen env' p_er_env'_wf  b' z
                                         (strengthen (subFTV a t_a p1) q) k_s p_env'_t1
                                         (subFTV a t_a p1) q k_s p_env'_t1 y ent_yenv'_p1taq 
        {-@ ent_yenv'_p2taq :: ProofOf(Entails (Cons y (tsubFTV a t_a s) env') 
                                               (unbind 0 y (strengthen (subFTV a t_a p2) q))) @-}
        ent_yenv'_p2taq  = lem_entails_strengthen env' p_er_env'_wf  b' z
                                         (strengthen (subFTV a t_a p1) q) k_s p_env'_t1
                                         (subFTV a t_a p2) q k_t p_env'_t2
                                         y ent_yenv'_p2ta ent_yenv'_q ? t1pf

        -- evidence needed without PLE
        binds_pf         = binds_proof_helper g g' a b' z q k_a p_g_ta y s
        fv_pf            = lem_free_bound_in_env env' t2 k_t p_env'_t2 y ? free t2
        fr_pf            = lem_free_bound_in_env (concatE (ConsT a k_a g) (g' ? binds_pf)) 
                                                 (TRefn (FTV a) z2 p2) k_t p_env_t (fresh_var env) 
                                                 ? free (TRefn (FTV a) z2 p2)
        free_sub         = lem_fv_subset_bindsF (FCons y (FTBasic (FTV a)) (erase_env env))
                                                (unbind 0 y p2) (FTBasic TBool) pf_y_p2_bl
        noex             = noExists (TRefn b' z q)
        t1pf             =   tsubFTV a (t_a ? noex) (TRefn (FTV a) z1 p1) 
                         === push (subFTV a (t_a ? noex) p1) (TRefn b' z q)
                         === TRefn b' z (strengthen (subFTV a (t_a ? noex) p1) q)
        t2pf             =   tsubFTV a (t_a ? noex) (TRefn (FTV a) z1 p2) 
                         === push (subFTV a (t_a ? noex) p2) (TRefn b' z q)
                         === TRefn b' z (strengthen (subFTV a (t_a ? noex) p2) q)
