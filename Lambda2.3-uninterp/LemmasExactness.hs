{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"   @-}
{-@ LIQUID "--short-names" @-}

module LemmasExactness where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
--import LocalClosure
import Strengthenings
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasWeaken
import SystemFLemmasSubstitution
import Typing
import PrimitivesWFType
--import BasicPropsCSubst
--import BasicPropsDenotes
--import BasicPropsEraseTyping
--import SubtypingFromEntailments
import LemmasWeakenWF
--import LemmasWeakenWFTV
import SubstitutionLemmaWF
import LemmasWellFormedness
import LemmasTyping
import LemmasSubtyping
--import LemmasWeakenTyp
--import LemmasWeakenTypTV
--import DenotationsSelfify
--import DenotationsSoundness
--import PrimitivesSemantics
--import PrimitivesDenotations

{-@ lem_self_idempotent_upper :: g:Env -> t:Type -> k:Kind -> ProofOf(WFType g t k)
        -> e:Expr -> ProofOf(HasFType (erase_env g) e (erase t))
        -> { pf:Subtype | propOf pf == Subtype g (self t e k) (self (self t e k) e k) &&
                          sizeOf pf <= tdepth t } / [tsize t] @-}
lem_self_idempotent_upper :: Env -> Type -> Kind -> WFType -> Expr -> HasFType ->  Subtype
lem_self_idempotent_upper g t@(TRefn b q) Base p_g_t e p_e_t 
  = SBase g b (PCons eqlP q) (PCons eqlP (PCons eqlP q)) nms p_imp_sq_ssq
      where 
        eqlP           = App (App (AppT (Prim Eql) (TRefn b PEmpty)) (BV 0)) e
        {-@ p_imp_sq_ssq :: { y:Vname | NotElem y nms}
              -> ProofOf(Implies (Cons y (TRefn b PEmpty) g) (unbindP y (PCons eqlP q)) 
                                 (unbindP y (PCons eqlP (PCons eqlP q)))) @-}
        p_imp_sq_ssq y = IRepeat (Cons y (TRefn b PEmpty) g)  (unbind y eqlP) (unbindP y q)
                              ? lem_open_at_eqlPred y b PEmpty (e
                              ? lem_ftyp_islc (erase_env g) e (erase t) p_e_t)
        nms            = unionEnv [] g
lem_self_idempotent_upper g t@(TFunc t_z t') Base p_g_t e p_e_t 
  = lem_sub_refl g t Base p_g_t  ? self (TFunc t_z t') e Base
lem_self_idempotent_upper g (TExists t_z t') Base p_g_t e p_e_t 
  = lem_subtype_in_exists (tdepth t') g t_z (self t' e Base) (self (self t' e Base) e Base)
                          p_g_self2_t nms' mk_p_st'_sst'
{-              ? toProof ( self (self (TExists t_z t') e Base) e Base
                      === self (TExists t_z (self t' e Base)) e Base
                      === TExists t_z (self (self t' e Base) e Base) )
              ? toProof ( self (TExists t_z t') e Base
                      === TExists t_z (self t' e Base) ) -}
      where
        {-@ mk_p_st'_sst' :: { y:Vname | NotElem y nms' } 
              -> { pf:Subtype | propOf pf == Subtype (Cons y t_z g) (unbindT y (self t' e Base))
                                                     (unbindT y (self (self t' e Base) e Base)) &&
                                sizeOf pf <= tdepth t' }  @-}
        mk_p_st'_sst' y = lem_self_idempotent_upper (Cons y t_z g) (unbindT y t') k'
                                                    (mk_p_yg_t' y) e p_yg_e_t'
                              ? lem_unbindT_self y t'               (e ? islc_e) Base
                              ? lem_unbindT_self y (self t' e Base) (e ? islc_e) Base
          where
            p_yg_e_t'   = lem_weaken_ftyp (erase_env g) FEmpty e (erase t') p_e_t y (erase t_z)
        p_g_self_t      = lem_selfify_wf g (TExists t_z t')               Base p_g_t      e p_e_t
        p_g_self2_t     = lem_selfify_wf g (self (TExists t_z t') e Base) Base p_g_self_t e p_e_t
        (WFExis _ _tz k_z p_g_tz _t' k' nms mk_p_yg_t') 
                        = lem_wfexis_for_wf_texists g t_z t' Base p_g_t
        islc_e          = lem_ftyp_islc (erase_env g) e (erase t') p_e_t
        nms'            = unionEnv nms g
lem_self_idempotent_upper g t@(TPoly k_a t') Base p_g_t e p_e_t 
  = lem_sub_refl g t Base p_g_t  ? self (TPoly k_a t') e Base 
lem_self_idempotent_upper g t                  Star p_g_t e p_e_t 
  = lem_sub_refl g t Star p_g_t  ? (self t e Star === t)

{-
{-@ ple lem_self_idempotent_lower @-}
{-@ lem_self_idempotent_lower :: g:Env -> t:Type -> k:Kind -> ProofOf(WFType g t k)
        -> e:Term -> ProofOf(HasFType (erase_env g) e (erase t))
        -> ProofOf(WFEnv g) -> ProofOf(Subtype g (self (self t e k) e k) (self t e k)) @-}
lem_self_idempotent_lower :: Env -> Type -> Kind -> WFType -> Expr -> HasFType -> WFEnv -> Subtype
lem_self_idempotent_lower g t k p_g_t e_ p_e_t p_g_wf 
  = lem_self_is_subtype g (self t e k) k p_g_selft e p_e_t p_g_wf
      where
        e         = e_ ? lem_fv_subset_bindsF (erase_env g) e_ (erase t) p_e_t
                       ? lem_freeBV_emptyB    (erase_env g) e_ (erase t) p_e_t
        p_er_g_wf = lem_erase_env_wfenv g p_g_wf
        p_g_selft = lem_selfify_wf g t k p_g_t p_er_g_wf e p_e_t
-}

{-@ lem_exact_subtype :: g:Env -> ProofOf(WFEnv g) -> s:Type -> k_s:Kind -> ProofOf(WFType g s k_s)
        -> t:Type -> { p_s_t:Subtype | propOf p_s_t == Subtype g s t } 
        -> k:Kind -> ProofOf(WFType g t k) -> { e:Expr | isLC e } 
        -> ProofOf(HasFType (erase_env g) e (erase t))
        -> { p_s'_t':Subtype | propOf p_s'_t' == Subtype g (self s e k) (self t e k) &&
                               sizeOf p_s'_t' == sizeOf p_s_t } / [sizeOf p_s_t] @-}
lem_exact_subtype :: Env -> WFEnv -> Type -> Kind -> WFType -> Type -> Subtype -> Kind -> WFType
                         -> Expr -> HasFType -> Subtype
lem_exact_subtype g p_g_wf s k_s p_g_s t p_s_t@(SBase _ b ps qs nms mk_imp_yg_ps_qs) Base p_g_t e p_e_t 
  = SBase g b ps' qs'  nms' mk_imp_yg_ps'_qs'
      where
        {-@ mk_imp_yg_ps'_qs' :: { y:Vname | NotElem y nms' } 
              -> ProofOf(Implies (Cons y (TRefn b PEmpty) g) (unbindP y ps') (unbindP y qs')) @-}
        mk_imp_yg_ps'_qs' y = IConj (Cons y (TRefn b PEmpty) g) (unbindP y ps') 
                                    (unbindP y (PCons (eqlPred (TRefn b qs) e) PEmpty)) (unbindP y qs)
                                    imp_yg_ps'_eql imp_yg_ps'_qs 
                                    ? lem_unbindP_strengthen y (PCons (eqlPred (TRefn b qs) e) PEmpty) qs
                                    ? toProof ( unbindP y PEmpty === PEmpty )
          where
            imp_yg_ps'_eql  = ICons1 (Cons y (TRefn b PEmpty) g) (unbind y (eqlPred (TRefn b ps) e)) 
                                     (unbindP y ps) ? toProof ( unbindP y PEmpty === PEmpty )
            imp_yg_ps'_ps   = ICons2 (Cons y (TRefn b PEmpty) g) (unbind y (eqlPred (TRefn b ps) e))
                                     (unbindP y ps)
            imp_yg_ps'_qs   = ITrans (Cons y (TRefn b PEmpty) g) (unbindP y ps') (unbindP y ps)
                                     (unbindP y qs) imp_yg_ps'_ps (mk_imp_yg_ps_qs y)
        ps'           = PCons (eqlPred (TRefn b ps) e) ps
        qs'           = PCons (eqlPred (TRefn b qs) e) qs
        nms'          = unionEnv nms g
lem_exact_subtype g p_g_wf s k_s p_g_s t p_s_t@(SFunc {}) k _ e p_e_t = p_s_t
lem_exact_subtype g p_g_wf s k_s p_g_s t p_s_t@(SWitn n _ v_x t_x p_vx_tx _s t' p_s_t'vx) 
                  Base p_g_t e p_e_t 
  = SWitn n g v_x t_x p_vx_tx (self s e Base) (self t' e Base) p_self_s_t'vx
          ? self (TExists t_x t') e Base
      where 
        (WFExis _ _tx k_x p_g_tx _ _ nms mk_p_wg_t') 
                      = lem_wfexis_for_wf_texists g t_x t' Base p_g_t
        w             = fresh_var nms g
        p_er_vx_tx    = lem_typing_hasftype g v_x t_x p_vx_tx p_g_wf
        p_g_t'vx      = lem_subst_wf g Empty w v_x t_x p_er_vx_tx (unbindT w t') Base (mk_p_wg_t' w)
                             ? lem_tsubFV_unbindT w v_x (t'
                                   ? lem_free_bound_in_env g (TExists t_x t') Base p_g_t w) 
        {-@ p_self_s_t'vx :: { pf:Subtype | propOf pf == Subtype g (self s e Base) 
                                                                   (tsubBV v_x (self t' e Base)) &&
                                            sizeOf pf <= n } @-}
        p_self_s_t'vx = lem_exact_subtype g p_g_wf s k_s p_g_s (tsubBV v_x t') p_s_t'vx Base p_g_t'vx
                                          e p_e_t 
                                          ? lem_tsubBV_self v_x t' e Base
                                          ? lem_subBV_lc    v_x    e
lem_exact_subtype g p_g_wf s k_s p_g_s t p_s_t@(SBind n _ s_x s' _t nms mk_p_s'_t) Base p_g_t e p_e_t  
  = SBind n g s_x (self s' e Base) (self t e Base ? lem_self_islct t e Base ) 
          nms'' mk_p_self_s'_t                    ? self (TExists s_x s') e Base
      where
        {-@ mk_p_self_s'_t :: { y:Vname | NotElem y nms'' }
              -> { pf:Subtype | propOf pf == Subtype (Cons y s_x g) (unbindT y (self s' e Base)) 
                                                     (self t e Base) &&
                                sizeOf pf <= n } @-}
        mk_p_self_s'_t y = lem_exact_subtype (Cons y s_x g) p_yg_wf (unbindT y s') k_s (mk_p_yg_s' y)
                                             t (mk_p_s'_t y) Base p_yg_t e p_yg_e_t
                                             ? lem_unbindT_self  y s'               e Base
                                             ? lem_unbindT_self  y (self s' e Base) e Base
                                             ? lem_unbind_lc     y                  e
          where
            p_yg_wf      = WFEBind g p_g_wf y s_x k_x p_g_sx
            p_yg_t       = lem_weaken_wf g Empty t Base p_g_t y s_x
            p_yg_e_t     = lem_weaken_ftyp (erase_env g) FEmpty e (erase t) p_e_t y (erase s_x)
        (WFExis _ _sx k_x p_g_sx _ _ nms' mk_p_yg_s') 
                    = lem_wfexis_for_wf_texists g s_x s' k_s p_g_s
        nms''            = unionEnv (union nms nms') g
lem_exact_subtype g p_g_wf s k_s p_g_s t p_s_t@(SPoly {}) k _ e p_e_t = p_s_t
lem_exact_subtype g p_g_wf s k_s p_g_s t p_s_t Star _ e p_e_t 
  = p_s_t ? toProof (self s e Star === s)
          ? toProof (self t e Star === t)

{-@ lem_exact_type :: g:Env -> v:Value -> t:Type 
        -> { p_v_t:HasType | propOf p_v_t == HasType g v t } -> k:Kind
        -> ProofOf(WFType g t k) -> ProofOf(WFEnv g) 
        -> { p_v_st:HasType | propOf p_v_st == HasType g v (self t v k) &&
                              sizeOf p_v_st <= (sizeOf p_v_t + 1) } @-}
lem_exact_type :: Env -> Expr -> Type -> HasType -> Kind -> WFType -> WFEnv -> HasType
lem_exact_type g e t p_e_t@(TBC _ b)   Base p_g_t p_g_wf 
  = TSub n g (Bc b) (tybc b) p_e_t (self (tybc b) (Bc b) Base) Base p_g_selft p_t_selft
      where
        p_g_t     = lem_wf_tybc g b
        p_g_selft = lem_selfify_wf g (tybc b) Base p_g_t (Bc b) (FTBC (erase_env g) b)
        p_t_selft = lem_tybc_exact g b 
        n         = {-max-} (typSize p_e_t) {-(subtypSize p_t_selft)-}
lem_exact_type g e t p_e_t@(TIC _ m)   Base p_g_t p_g_wf  
  = TSub n g (Ic m) (tyic m) p_e_t (self (tyic m) (Ic m) Base) Base p_g_selft p_t_selft
      where
        p_g_t     = lem_wf_tyic g m
        p_g_selft = lem_selfify_wf g (tyic m) Base p_g_t (Ic m) (FTIC (erase_env g) m)
        p_t_selft = lem_tyic_exact g m 
        n         = {-max-} (typSize p_e_t) {-(subtypSize p_t_selft)-}
lem_exact_type g e t p_e_t@(TVar1 env x t' k' p_env_t')  Base p_g_t p_g_wf = case k' of
  Base -> TSub n g (FV x) t p_e_t (self t (FV x) Base) Base p_g_slt p_t_selft
    where
      p_e_er_t  = lem_typing_hasftype g (FV x) t p_e_t p_g_wf
      p_g_slt   = lem_selfify_wf g t Base p_g_t (FV x) p_e_er_t
      p_g_t'    = lem_weaken_wf env Empty t' Base p_env_t' x t'
      p_t_selft = lem_self_idempotent_upper g t' Base {-p_env_t'-} p_g_t' (FV x) 
                              (p_e_er_t ? erase (self t' (FV x) Base)) -- p_env_wf
      n         = max (typSize p_e_t) (subtypSize p_t_selft)
  Star -> {- t == t' -} TVar1 env x t' Base p_env_t'_b ? t_is_t'
    where 
      p_env_t'_b = lem_strengthen_wftype_base env Empty x t' t' p_env_t' p_g_t
      t_is_t'    = t === self t' (FV x) Star === t'
lem_exact_type g e t p_e_t@(TVar2 _ env x _t p_env_e_t w t_w) Base p_g_t p_g_wf
  = TVar2 (typSize p_env_e_selft) env x (self t (FV x) Base) p_env_e_selft w t_w
      where
        (WFEBind _env p_env_wf _ _ _ _) = p_g_wf
        p_env_t_st    = lem_typing_wf env e t p_env_e_t p_env_wf
        p_env_t_b     = lem_strengthen_wftype_base env Empty w t_w t p_env_t_st p_g_t
        p_env_e_selft = lem_exact_type env e t p_env_e_t Base p_env_t_b p_env_wf 
lem_exact_type g e t p_e_t@(TVar3 _ env x _t p_env_e_t a k_a) Base p_g_t p_g_wf
  = TVar3 (typSize p_env_e_selft) env x (self t (FV x) Base) p_env_e_selft a k_a
      where
        (WFEBindT _env p_env_wf _ _) = p_g_wf
        p_env_t_st    = lem_typing_wf env e t p_env_e_t p_env_wf
        p_env_t_b     = lem_strengthen_tv_wftype_base env Empty a k_a t p_env_t_st p_g_t
        p_env_e_selft = lem_exact_type env e t p_env_e_t Base p_env_t_b p_env_wf 
lem_exact_type g e t p_e_t@(TPrm {})  Base _ p_g_wf  
  = case t of
      (TFunc {}) -> p_e_t 
      (TPoly {}) -> p_e_t
lem_exact_type g e t p_e_t@(TAbs {})  Base _ p_g_wf
  = case t of
      (TFunc {}) -> p_e_t 
lem_exact_type g e t (TApp {})  Base _ p_g_wf = impossible "not a value"
lem_exact_type g e t p_e_t@(TAbsT {}) Base _ p_g_wf
  = case t of
      (TPoly {}) -> p_e_t
lem_exact_type g e t (TAppT {}) Base _ p_g_wf = impossible "not a value"
lem_exact_type g e t (TLet {})  Base _ p_g_wf = impossible "not a value"
lem_exact_type g e t (TAnn {})  Base _ p_g_wf = impossible "not a value"
lem_exact_type g e t p_e_t@(TSub _ _g e_ s p_g_e_s t_ k p_g_t p_g_s_t) Base p_g_t_b p_g_wf 
  = TSub n g e (self s e Base) p_e_selfs (self t e Base) Base p_g_selft p_selfs_selft
     where
       p_e_er_t      = lem_typing_hasftype g e t p_e_t p_g_wf
       p_g_s_st      = lem_typing_wf           g e s p_g_e_s p_g_wf
       p_g_s_b       = lem_sub_pullback_wftype g p_g_wf s t p_g_s_t p_g_s_st p_g_t_b
       p_e_selfs     = lem_exact_type    g e s p_g_e_s Base p_g_s_b p_g_wf
       p_g_selft     = lem_selfify_wf    g t Base p_g_t_b e p_e_er_t
       p_selfs_selft = lem_exact_subtype g p_g_wf s Base p_g_s_b t p_g_s_t Base p_g_t_b (e 
                           ? lem_ftyp_islc (erase_env g) e (erase t) p_e_er_t) p_e_er_t
       n             = max (typSize p_e_selfs) (subtypSize p_selfs_selft)
lem_exact_type g e t p_e_t Star _ p_g_wf = p_e_t ? toProof ( self t e Star === t )
