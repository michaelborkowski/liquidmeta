{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{- @ LIQUID "--ple"   @-}
{- @ LIQUID "--ple-local"   @-}
{- @ LIQUID "--fuel=1"      @-}
{-@ LIQUID "--short-names" @-}

module SubstitutionLemmaSBase where

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

{-@ reflect foo66aa @-}   
foo66aa x = Just x 
foo66aa :: a -> Maybe a 


{- @ ple lem_subst_tv_sub_sbase_ftv' @-}
{-@ lem_subst_tv_sub_sbase_ftv' :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
      -> { a:Vname | (not (in_env a g)) && not (in_env a g') } 
      -> b':Basic -> z:RVname -> q:Pred -> k_a:Kind -> ProofOf(WFType g (TRefn b' z q) k_a) 
      -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) 
      -> z1:RVname -> p1:Pred -> k_s:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') (TRefn (FTV a) z1 p1) k_s)
      -> z2:RVname -> p2:Pred -> k_t:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') (TRefn (FTV a) z2 p2) k_t)
      -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (ConsT a k_a g) g') 
                                             (TRefn (FTV a) z1 p1) (TRefn (FTV a) z2 p2)  && isSBase p_s_t }
      -> ProofOf(Subtype (concatE g (esubFTV a (TRefn b' z q) g')) (tsubFTV a (TRefn b' z q) (TRefn (FTV a) z1 p1)) 
                                                              (tsubFTV a (TRefn b' z q) (TRefn (FTV a) z2 p2))) @-}
lem_subst_tv_sub_sbase_ftv' :: Env -> Env -> Vname -> Basic -> RVname -> Expr -> Kind -> WFType -> WFEnv
      -> RVname -> Expr -> Kind -> WFType -> RVname -> Expr -> Kind -> WFType -> Subtype -> Subtype
lem_subst_tv_sub_sbase_ftv' g g' a b' z q k_a p_g_ta p_env_wf z1 p1 k_s p_env_s z2 p2 k_t p_env_t 
                       (SBase env _z1 b _p1 _z2 _p2 y ent_yenv_p2) 
  = SBase (concatE g (esubFTV a t_a g')) z b' (strengthen (subFTV a t_a p1) q)
          z (strengthen (subFTV a (t_a) p2) q) y ent_yenv'_p2taq ? t1pf ? t2pf
      where 
        t_a              = TRefn b' z q
        s                = TRefn (FTV a) z1 p1 
  --      y                = y_  ? lem_in_env_esubFTV g' a (t_a) y_ 
  --                             ? lem_in_env_concat g  g' y_ 
  --                             ? lem_in_env_concat (ConsT a k_a g) g' y_
  --                             ? lem_free_bound_in_env g t_a k_a p_g_ta (y_ ? lem_in_env_concat (ConsT a k_a g) g' y_)
  --      p_ag_wf          = lem_truncate_wfenv (ConsT a k_a g) g' p_env_wf
--        (WFEBindT _ pg_wf _ _) = p_ag_wf
        p_er_g_ta        = lem_erase_wftype g t_a k_a p_g_ta
        p_yenv_wf        = WFEBind (concatE (ConsT a k_a g) g') p_env_wf y s k_s p_env_s
        p_er_env_wf      = lem_erase_env_wfenv env p_env_wf
        p_er_wenv_wf     = WFFBind (erase_env env) p_er_env_wf (fresh_var env) (FTBasic b) 
                                   k_s (lem_erase_wftype env s k_s p_env_s {-? er_s-}) ? concF_wenv
                                   ? lem_erase_concat (ConsT a k_a g) g'
        p_er_yenv_wf     = WFFBind (erase_env env) p_er_env_wf (y) (FTBasic b) 
                                   k_s (lem_erase_wftype env s k_s p_env_s {-? er_s-}) ? concF_yenv
                                   ? lem_erase_concat (ConsT a k_a g) g'
        env'             = concatE g (esubFTV a t_a g')
        p_env'_wf        = lem_subst_tv_wfenv g g' a t_a k_a p_g_ta p_env_wf
        p_er_env'_wf     = lem_erase_env_wfenv env' p_env'_wf
        {-@ t1 :: { t1_:Type | t1_ == tsubFTV a t_a s } @-}
        t1               = TRefn b' z (strengthen (subFTV a (t_a {-? noex-}) p1) q) ? t1pf
        p_env'_t1        = lem_subst_tv_wf'   g g' a t_a k_a p_g_ta p_env_wf s k_s p_env_s
        p_er_wenv'_wf    = WFFBind (erase_env env') p_er_env'_wf (fresh_var env' {-? binds_fr-}) (FTBasic b') 
                                   k_s (lem_erase_wftype env' t1 k_s p_env'_t1) {-? concF_wenv'-}
        pf'_p1taq_bl     = lem_ftyp_for_wf_trefn' env' b' z (strengthen (subFTV a (t_a {-? noex-}) p1) q)
                                                  k_s p_env'_t1 p_er_env'_wf ? concF_wenv'
        pf_p1taq_bl      = lem_change_var_ftyp (erase_env env') (fresh_var env') (FTBasic b') FEmpty
                                   p_er_wenv'_wf (strengthen (subFTV a t_a p1) q)
                                   (FTBasic TBool) pf'_p1taq_bl (y {-? yemp-})
--                                   {-? vonvF_yenv'-} ? lem_subFV_unbind 0 (fresh_var env') (FV y {-? val-}) 
--                                                      (strengthen (subFTV a (t_a {-? noex-}) p1) q {-? fvp1q-})
        pf'_p1_bl        = lem_ftyp_for_wf_trefn' env b z1 p1 k_s p_env_s p_er_env_wf ? concF_wenv
        pf'_p2_bl        = lem_ftyp_for_wf_trefn' env b z2 p2 k_t p_env_t p_er_env_wf ? concF_wenv
        pf_p1_bl         = lem_change_var_ftyp (erase_env env) (fresh_var env) (FTBasic b) FEmpty        
                                   p_er_wenv_wf (unbind 0 (fresh_var env) p1) (FTBasic TBool) pf'_p1_bl y
--                                   {-? concF_yenv-} ? lem_erase_concat (ConsT a k_a g) (Cons y s g' {-? er_yg'-})
--                                   ? lem_subFV_unbind 0 (fresh_var env) (FV y {-? val-}) p1
        {-@ pf_p2_bl :: ProofOf(HasFType (FCons y (FTBasic b) (erase_env env)) (unbind 0 y p2) (FTBasic TBool)) @-}
        pf_p2_bl         = lem_change_var_ftyp (erase_env env) (fresh_var env) (FTBasic b) FEmpty        
                                   p_er_wenv_wf (unbind 0 (fresh_var env) p2) (FTBasic TBool) pf'_p2_bl (y {-? yemp-})
--                                   {-? concF_yenv-} ? lem_erase_concat (ConsT a k_a g) (Cons y s g' {-? er_yg'-})
--                                   ? lem_subFV_unbind 0 (fresh_var env) (FV y {-? val-}) p2
        pf_p1ta_bl       = lem_subst_tv_ftyp (erase_env g) (FCons y (FTBasic b) (erase_env g'))
                                   a (t_a ? fvta) k_a p_er_g_ta p_er_yenv_wf (unbind 0 y p1)
                                   (FTBasic TBool) pf_p1_bl
--                                   ? lem_erase_esubFTV a (t_a {-? noex-}) (Cons y s g' {-? er_yg'-}) -- ? er_env'
--                                   ? lem_erase_concat g (esubFTV a (t_a {-? noex-}) g')
--                                   ? lem_commute_subFTV_unbind a (t_a {-? noex-})
--                                       (0 ? lem_tfreeBV_empty g t_a k_a p_g_ta) y p1
        {-@ pf_p2ta_bl :: ProofOf(HasFType (FCons y (FTBasic b') (erase_env env')) (unbind 0 y (subFTV a t_a p2)) (FTBasic TBool)) @-}
        pf_p2ta_bl       = lem_subst_tv_ftyp (erase_env g) (FCons y (FTBasic b) (erase_env g')) 
                                   (a {-? binds_a-}) (t_a ? fvta) k_a p_er_g_ta p_er_yenv_wf (unbind 0 y p2)
                                   (FTBasic TBool) pf_p2_bl
--                                   ? lem_erase_esubFTV a (t_a {-? noex-}) (Cons y s g' {-? er_yg'-}) -- ? er_env'
--                                   ? lem_erase_concat g (esubFTV a (t_a {-? noex-}) g')
--                                   ? lem_commute_subFTV_unbind a (t_a {-? noex-})
--                                       (0 ? lem_tfreeBV_empty g t_a k_a p_g_ta) y p2
        p_env'_ta        = lem_weaken_many_wf' g (esubFTV a t_a g') p_env'_wf t_a k_a p_g_ta
        pf'_q_bl         = lem_ftyp_for_wf_trefn' env' b' z q k_a p_env'_ta p_er_env'_wf
        pf_q_bl          = lem_change_var_ftyp (erase_env env') (fresh_var env' {-? binds_fr-}) (FTBasic b') (FEmpty {-? femp-})
                                   p_er_wenv'_wf (unbind 0 (fresh_var env') q) (FTBasic TBool) pf'_q_bl (y {-? yemp-})
--                                   {-? vonvF_yenv'-} ? lem_subFV_unbind 0 (fresh_var env') (FV y) q

        {- @ ent_yenv_p2     :: Entails (Cons y  s env)  (unbind 0 y p2) @-}
        {-@ ent_yenv'_p2ta  :: ProofOf(Entails (Cons y (tsubFTV a t_a s) env') (unbind 0 y (subFTV a t_a p2))) @-}
        ent_yenv'_p2ta   = lem_subst_tv_ent g (Cons y s g') a t_a k_a p_g_ta p_yenv_wf
                                            (unbind 0 y p2) (ent_yenv_p2 ? cons_yenv)
--                                   ? lem_commute_subFTV_unbind a (t_a {-? noex-})
--                                       (0 ? lem_tfreeBV_empty g t_a k_a p_g_ta) y p2
        {-@ ent_yenv'_p1taq :: ProofOf(Entails (Cons y (tsubFTV a t_a s) env') (unbind 0 y (strengthen (subFTV a t_a p1) q))) @-}
        ent_yenv'_p1taq  = lem_entails_itself' env' p_er_env'_wf b' z (strengthen (subFTV a t_a p1) q)
                                               y pf_p1taq_bl k_s p_env'_t1
        {-@ ent_yenv'_q     :: ProofOf(Entails (Cons y (tsubFTV a t_a s) env') (unbind 0 y q)) @-}
        ent_yenv'_q      = snd ( lem_entails_disjunction' env' p_er_env'_wf  b' z
                                         (strengthen (subFTV a t_a p1) q) k_s p_env'_t1
                                         (subFTV a t_a p1) q y pf_p1ta_bl pf_q_bl ent_yenv'_p1taq )
        {-@ ent_yenv'_p2taq :: ProofOf(Entails (Cons y (tsubFTV a t_a s) env') (unbind 0 y (strengthen (subFTV a t_a p2) q))) @-}
        ent_yenv'_p2taq  = lem_entails_conjunction' env' p_er_env'_wf  b' z
                                         (strengthen (subFTV a t_a p1) q) k_s p_env'_t1
                                         (subFTV a t_a p2) q (y {-? fvq-}) pf_p2ta_bl pf_q_bl 
                                         ent_yenv'_p2ta ent_yenv'_q
        -- evidence needed without PLE
{-        binds_a          = ( in_envF a (erase_env g) === in_env a g )
        binds_fr         = not (in_envF (fresh_var env') (erase_env env')) === not (in_env (fresh_var env) env)
        binds_pf         = ( in_envF y (erase_env g) === in_env y g )
                         ? ( bindsF (erase_env g) === binds g ) -}
        concF_wenv'      = concatF (FCons (fresh_var env') (FTBasic b') (erase_env env')) FEmpty
        concF_wenv       = concatF (FCons (fresh_var env) (FTBasic b) (erase_env env)) FEmpty
        concF_yenv       = concatF (FCons y (FTBasic b) (erase_env env)) FEmpty
        cons_yenv        = Cons y s env === Cons y s (concatE (ConsT a k_a g) g')
                                        === concatE (ConsT a k_a g) (Cons y s g')
{-        concF_yenv'      = concatF (FCons y (FTBasic b') (erase_env env')) FEmpty
        concF_yenv       = concatF (FCons y (FTBasic b) (erase_env env)) FEmpty
--        er_env'          = erase_env (concatE g (esubFTV a (t_a {-? noex-}) g'))
        er_yg'           = erase_env (Cons y s g') {-? er_s-} === FCons y (FTBasic b) (erase_env g')
        er_s             = erase (TRefn (FTV a) z1 p1)
        femp             = bindsF FEmpty
        fvp1q            = free t1  ? freeTV t1
        fvq              = free t_a ? freeTV t_a-}
        fvta             = lem_free_subset_binds g t_a k_a p_g_ta 
                         ? lem_tfreeBV_empty     g t_a k_a p_g_ta  
--        noex             = noExists (TRefn b' z q)
        t1pf             =   tsubFTV a (t_a {-? noex-}) (TRefn (FTV a) z1 p1) 
                         === push (subFTV a (t_a {-? noex-}) p1) (TRefn b' z q)
                         === TRefn b' z (strengthen (subFTV a (t_a {-? noex-}) p1) q)
        t2pf             =   tsubFTV a (t_a {-? noex-}) (TRefn (FTV a) z1 p2) 
                         === push (subFTV a (t_a {-? noex-}) p2) (TRefn b' z q)
                         === TRefn b' z (strengthen (subFTV a (t_a {-? noex-}) p2) q)
--        val              = isValue (FV y) ? isTerm (FV y)
--        yemp             = not (in_envF y FEmpty) === not (S.member y (bindsF FEmpty))
