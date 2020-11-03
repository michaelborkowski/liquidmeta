{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SubstitutionLemmaWF where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import Entailments
import LemmasChangeVarWF
import LemmasWeakenWF
import LemmasWellFormedness
import LemmasTyping
import LemmasSubtyping
import LemmasChangeVarTyp
import LemmasWeakenTyp

{-@ reflect foo39 @-}
foo39 x = Just x
foo39 :: a -> Maybe a

-- -- -- -- -- -- -- -- -- -- -- ---
-- Part of the Substitution Lemma --
-- -- -- -- -- -- -- -- -- -- -- ---

{-@ lem_subst_wf_wfrefn :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
          -> t_x:Type -> ProofOf(HasType g v_x t_x) 
          -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> t:Type -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (Cons x t_x g) g') t k && isWFRefn p_env_t}
          -> ProofOf(WFType (concatE g (esubFV x v_x g')) (tsubFV x v_x t) k) / [wftypSize p_env_t, 0] @-}
lem_subst_wf_wfrefn :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv 
                    -> Type -> Kind -> WFType -> WFType
lem_subst_wf_wfrefn g g' x v_x t_x p_vx_tx p_env_wf t k (WFRefn env z b p_env_b p y_ p_env'_p_bl)
  = WFRefn (concatE g (esubFV x v_x g')) z b p_gg'_b (subFV x v_x p) y -- _env = g'; x:tx; g
           p_ygg'_pvx_bl 
      where
        p_gg'_b       = lem_subst_wf g g' x v_x t_x p_vx_tx p_env_wf (TRefn b 1 (Bc True)) Base p_env_b
        y             = y_ ? lem_in_env_esub g' x v_x y_
                           ? lem_in_env_concat g  g' y_
                           ? lem_in_env_concat (Cons x t_x g) g' y_
                           ? lem_fv_bound_in_env g v_x t_x p_vx_tx y_
        p_xg_wf       = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _ _) = p_xg_wf
        p_env_er_b    = lem_erase_wftype env (TRefn b 1 (Bc True)) Base p_env_b
        p_vx_er_tx    = lem_typing_hasftype g v_x t_x p_vx_tx p_g_wf
        p_er_yenv_wf  = WFFBind (erase_env env) (lem_erase_env_wfenv env p_env_wf) y (FTBasic b) 
                             Base p_env_er_b -- (WFFTBasic (erase_env env) b)
        p_ygg'_pvx_bl = lem_subst_ftyp (erase_env g) (FCons y (FTBasic b) (erase_env g')) 
                           (x ? lem_in_env_concatF (erase_env g) (erase_env g') x
                              ? lem_in_env_concatF (erase_env g) (FCons y (FTBasic b) (erase_env g')) x)
                           v_x (erase t_x)  p_vx_er_tx p_er_yenv_wf (unbind z y p) (FTBasic TBool) 
                           (p_env'_p_bl ? lem_erase_concat (Cons x t_x g) g')
                           ? lem_commute_subFV_subBV1 z (FV y) x 
                               (v_x ? lem_freeBV_empty g v_x t_x p_vx_tx p_g_wf) p
                           ? lem_erase_concat g (esubFV x v_x g')
                           ? lem_erase_esubFV x v_x g'

{-@ lem_subst_wf_wfvar :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
          -> t_x:Type -> ProofOf(HasType g v_x t_x) 
          -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> t:Type -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (Cons x t_x g) g') t k && isWFVar p_env_t}
          -> ProofOf(WFType (concatE g (esubFV x v_x g')) (tsubFV x v_x t) k) / [wftypSize p_env_t, 0] @-}
lem_subst_wf_wfvar :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv 
                    -> Type -> Kind -> WFType -> WFType
lem_subst_wf_wfvar g g' x v_x t_x p_vx_tx p_env_wf t k (WFVar1 _env' a k_a)
  = case g' of
      Empty              -> impossible "x <> a"
      (ConsT _a _ka g'') -> WFVar1 (concatE g (esubFV x v_x g''))
                                   (a ? lem_in_env_esub g'' x v_x a
                                      ? lem_in_env_concat g g'' a
                                      ? lem_in_env_concat (Cons x t_x g) g'' a) k_a
lem_subst_wf_wfvar g g' x v_x t_x p_vx_tx p_env_wf t k (WFVar2 _env' a k_a p_env'_a y t_y)
  = undefined
lem_subst_wf_wfvar g g' x v_x t_x p_vx_tx p_env_wf t k (WFVar3 _env' a k_a p_env'_a a1 k_a1) 
  = undefined

{-@ lem_subst_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
          -> t_x:Type -> ProofOf(HasType g v_x t_x) 
          -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> t:Type -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (Cons x t_x g) g') t k }
          -> ProofOf(WFType (concatE g (esubFV x v_x g')) (tsubFV x v_x t) k) / [wftypSize p_env_t, 1] @-}
lem_subst_wf :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv 
                    -> Type -> Kind -> WFType -> WFType
lem_subst_wf g g' x v_x t_x p_vx_tx p_env_wf t k (WFBase _env b)
  = WFBase (concatE g (esubFV x v_x g')) b
lem_subst_wf g g' x v_x t_x p_vx_tx p_env_wf t k p_env_t@(WFRefn env z b p_env_b p y_ p_env'_p_bl)  
  = lem_subst_wf_wfrefn g g' x v_x t_x p_vx_tx p_env_wf t k p_env_t 
lem_subst_wf g g' x v_x t_x p_vx_tx p_env_wf t k p_env_t@(WFVar1 _env a k_a)
  = lem_subst_wf_wfvar g g' x v_x t_x p_vx_tx p_env_wf t k p_env_t
lem_subst_wf g g' x v_x t_x p_vx_tx p_env_wf t k p_env_t@(WFVar2 {})
  = lem_subst_wf_wfvar g g' x v_x t_x p_vx_tx p_env_wf t k p_env_t
lem_subst_wf g g' x v_x t_x p_vx_tx p_env_wf t k p_env_t@(WFVar3 {}) 
  = lem_subst_wf_wfvar g g' x v_x t_x p_vx_tx p_env_wf t k p_env_t
lem_subst_wf g g' x v_x t_x p_vx_tx p_env_wf t k (WFFunc _env z t_z k_z p_env_tz t' k' y_ p_yenv_t')
  = undefined {-
  = WFFunc (concatE g (esubFV x v_x g')) z (tsubFV x v_x t_z) k_z p_g'g_tzvx 
           (tsubFV x v_x t') k' y p_yg'g_t'vx
      where
        {- @ y :: { yy:Vname | t == TFunc z t_z t' } @-}
        y           = y_ ? lem_in_env_esub g' x v_x y_ 
                         ? lem_in_env_concat g  g' y_ 
                         ? lem_in_env_concat (Cons x t_x g) g' y_
                         ? lem_in_env_concat (Cons x t_x g) g' y_
                         ? lem_fv_bound_in_fenv (erase_env g) v_x (erase t_x) p_vx_er_tx y_
        p_xg_wf     = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _ _) = p_xg_wf
        p_yenv_wf   = WFEBind (concatE (Cons x t_x g) g') p_env_wf y t_z k_z p_env_tz
        p_vx_er_tx  = lem_typing_hasftype g v_x t_x p_vx_tx p_g_wf
        p_g'g_tzvx  = lem_subst_wf g g'              x v_x t_x p_vx_tx p_env_wf  t_z k_z p_env_tz
        p_yg'g_t'vx = lem_subst_wf g (Cons y t_z g') x v_x t_x p_vx_tx p_yenv_wf (unbindT z y t') k'
                         (p_yenv_t' ? lem_erase_concat (Cons x t_x g) g')
                         ? lem_commute_tsubFV_tsubBV1 z (FV y) x v_x t'
-}
lem_subst_wf g g' x v_x t_x p_vx_tx p_env_wf t k (WFExis _env z t_z k_z p_env_tz t' k' y_ p_yenv_t')
  = WFExis (concatE g (esubFV x v_x g')) z (tsubFV x v_x t_z) k_z p_g'g_tzvx 
           (tsubFV x v_x t') k' y p_yg'g_t'vx
      where
        y           = y_ ? lem_in_env_esub g' x v_x y_ 
                         ? lem_in_env_concat g  g' y_ 
                         ? lem_in_env_concat (Cons x t_x g) g' y_
                         ? lem_in_env_concat (Cons x t_x g) g' y_
                         ? lem_fv_bound_in_fenv (erase_env g) v_x (erase t_x) p_vx_er_tx y_
        p_xg_wf     = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _ _) = p_xg_wf
        p_yenv_wf   = WFEBind (concatE (Cons x t_x g) g') p_env_wf y t_z k_z p_env_tz
        p_vx_er_tx  = lem_typing_hasftype g v_x t_x p_vx_tx p_g_wf
        p_g'g_tzvx  = lem_subst_wf g g'              x v_x t_x p_vx_tx p_env_wf t_z k_z p_env_tz
        p_yg'g_t'vx = lem_subst_wf g (Cons y t_z g') x v_x t_x p_vx_tx p_yenv_wf (unbindT z y t') k'
                         (p_yenv_t' ? lem_erase_concat (Cons x t_x g) g')
                         ? lem_commute_tsubFV_tsubBV1 z (FV y) x 
                               (v_x ? lem_freeBV_empty g v_x t_x p_vx_tx p_g_wf) t'
lem_subst_wf g g' x v_x t_x p_vx_tx p_env_wf t k (WFPoly {})
  = undefined
lem_subst_wf g g' x v_x t_x p_vx_tx p_env_wf t k (WFKind _env _t p_env_t_base)
  = WFKind (concatE g (esubFV x v_x g')) (tsubFV x v_x t) p_gg'_tvx_base
      where
        p_gg'_tvx_base = lem_subst_wf g g' x v_x t_x p_vx_tx p_env_wf t Base p_env_t_base


{-@ lem_subst_tv_wf_wfrefn :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:Type
          -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
          -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) -> t:Type -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (ConsT a k_a g) g') t k && isWFRefn p_env_t}
          -> ProofOf(WFType (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k) / [wftypSize p_env_t, 0] @-}
lem_subst_tv_wf_wfrefn :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv 
                    -> Type -> Kind -> WFType -> WFType
lem_subst_tv_wf_wfrefn g g' a t_a k_a p_g_ta p_env_wf t k (WFRefn env z b p_env_b p y_ p_env'_p_bl)
  = case b of
      (FTV a') | (a == a') -> {-lem_push_wf (concatE g (esubFTV a t_a g')) t_a k_a p_gg'ta_ta
                                  {-p_gg'ta_wf-} z (subFTV a t_a p) y pf_pta_bl 
                                  -} undefined -- need k = k_a lemma, get rid of subst wf_env 
{-        where
          y          = y_ ? lem_in_env_esubFTV g' a t_a y_
                          ? lem_in_env_concat g  g' y_
                          ? lem_in_env_concat (ConsT a k_a g) g' y_
                          ? lem_free_bound_in_env g t_a k_a p_g_ta y_
          p_gg'ta_wf = lem_subst_tv_wfenv g g' a t_a k_a p_g_ta p_env_wf
          p_gg'ta_ta = lem_weaken_many_wf g (esubFTV a t_a g') p_gg'ta_wf t_a k_a p_g_ta
          p_ag_wf    = lem_truncate_wfenv (ConsT a k_a g) g' p_env_wf
          (WFEBindT _ p_g_wf _ _) = p_ag_wf
          p_env_er_b = lem_erase_wftype env (TRefn b 1 (Bc True)) Base p_env_b
          p_g_er_ta  = lem_erase_wftype g t_a k_a p_g_ta
          p_er_yenv_wf  = WFFBind (erase_env env) (lem_erase_env_wfenv env p_env_wf) y (FTBasic b) 
                               Base p_env_er_b -- (WFFTBasic (erase_env env) b)
          pf_pta_bl  = lem_subst_tv_ftyp (erase_env g) (FCons y (FTBasic b) (erase_env g'))
                         (a ? lem_in_env_concatF (erase_env g) (erase_env g') a
                            ? lem_in_env_concatF (erase_env g) (FCons y (FTBasic b) (erase_env g')) a)
                         t_a k_a p_g_er_ta p_er_yenv_wf (unbind z y p) (FTBasic TBool) 
                         (p_env'_p_bl ? lem_erase_concat (ConsT a k_a g) g')
                         ? lem_commute_subFTV_subBV1 z (FV y) a
                             (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta p_g_wf) p
                         ? lem_erase_concat g (esubFTV a t_a g')
                         ? lem_erase_esubFTV a t_a g' -}
      _                    -> WFRefn (concatE g (esubFTV a t_a g')) z b p_gg'_b (subFTV a t_a p) 
                                     y p_ygg'_pta_bl 
        where
          p_gg'_b       = lem_subst_tv_wf g g' a t_a k_a p_g_ta p_env_wf (TRefn b 1 (Bc True)) Base p_env_b
          y             = y_ ? lem_in_env_esubFTV g' a t_a y_
                             ? lem_in_env_concat g  g' y_
                             ? lem_in_env_concat (ConsT a k_a g) g' y_
                             ? lem_free_bound_in_env g t_a k_a p_g_ta y_
          p_ag_wf       = lem_truncate_wfenv (ConsT a k_a g) g' p_env_wf
          (WFEBindT _ p_g_wf _ _) = p_ag_wf
          p_env_er_b    = lem_erase_wftype env (TRefn b 1 (Bc True)) Base p_env_b
          p_g_er_ta     = lem_erase_wftype g t_a k_a p_g_ta
--          p_vx_er_tx    = lem_typing_hasftype g v_x t_x p_vx_tx p_g_wf
          p_er_yenv_wf  = WFFBind (erase_env env) (lem_erase_env_wfenv env p_env_wf) y (FTBasic b) 
                               Base p_env_er_b -- (WFFTBasic (erase_env env) b)
          p_ygg'_pta_bl = lem_subst_tv_ftyp (erase_env g) (FCons y (FTBasic b) (erase_env g')) 
                             (a ? lem_in_env_concatF (erase_env g) (erase_env g') a
                                ? lem_in_env_concatF (erase_env g) (FCons y (FTBasic b) (erase_env g')) a)
                             t_a k_a p_g_er_ta p_er_yenv_wf (unbind z y p) (FTBasic TBool)
                             (p_env'_p_bl ? lem_erase_concat (ConsT a k_a g) g')
                             ? lem_commute_subFTV_subBV1 z (FV y) a 
                                 (t_a ? lem_tfreeBV_empty g t_a k_a p_g_ta p_g_wf) p
                             ? lem_erase_concat g (esubFTV a t_a g')
                             ? lem_erase_esubFTV a t_a g'

{-@ lem_subst_tv_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
          -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:Type
          -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
          -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') ) -> t:Type -> k:Kind
          -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (ConsT a k_a g) g') t k }
          -> ProofOf(WFType (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k) / [wftypSize p_env_t, 1] @-}
lem_subst_tv_wf :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv 
                    -> Type -> Kind -> WFType -> WFType
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_env_wf t k (WFBase _env b)
  = undefined
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_env_wf t k p_e_t@(WFRefn {})
  = lem_subst_tv_wf_wfrefn g g' a t_a k_a p_g_ta p_env_wf t k p_e_t
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_env_wf t k (WFVar1 {})
  = undefined
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_env_wf t k (WFVar2 {})
  = undefined
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_env_wf t k (WFVar3 {})
  = undefined
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_env_wf t k (WFFunc {})
  = undefined
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_env_wf t k (WFExis {})
  = undefined
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_env_wf t k (WFPoly {})
  = undefined
lem_subst_tv_wf g g' a t_a k_a p_g_ta p_env_wf t k (WFKind _env _t p_env_t_base)
  = WFKind (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) p_gg'_tta_base
      where
        p_gg'_tta_base = lem_subst_tv_wf g g' a t_a k_a p_g_ta p_env_wf t Base p_env_t_base


{-@ lem_subst_wfenv :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> ProofOf(HasType g v_x t_x)
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') )
        -> ProofOf(WFEnv (concatE g (esubFV x v_x g')) ) / [envsize g'] @-}
lem_subst_wfenv :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv -> WFEnv
lem_subst_wfenv g Empty           x v_x t_x p_vx_tx p_xg_wf  = case p_xg_wf of
  (WFEBind  _g p_g_wf _x _tx _ _) -> p_g_wf
  (WFEBindT _g p_g_wf _  _)       -> p_g_wf
lem_subst_wfenv g (Cons z t_z g') x v_x t_x p_vx_tx p_env_wf = case p_env_wf of
  (WFEBind env' p_env'_wf _z _tz k_z p_env'_tz) 
    -> WFEBind env'' p_env''_wf z (tsubFV x v_x t_z) k_z p_env''_tzvx
      where
        env''        = concatE g (esubFV x v_x g')
        p_env''_wf   = lem_subst_wfenv g g' x v_x t_x p_vx_tx p_env'_wf
        p_env''_tzvx = lem_subst_wf g g' x v_x t_x p_vx_tx p_env'_wf t_z k_z p_env'_tz
lem_subst_wfenv g (ConsT a k_a g') x v_x t_x p_vx_tx p_env_wf = case p_env_wf of
  (WFEBindT env' p_env'_wf _a _ka)           -> WFEBindT env'' p_env''_wf a k_a
    where
      env''      = concatE g (esubFV x v_x g')
      p_env''_wf = lem_subst_wfenv g g' x v_x t_x p_vx_tx p_env'_wf

{-@ lem_subst_tv_wfenv :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:Type
        -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g') )
        -> ProofOf(WFEnv (concatE g (esubFTV a t_a g')) ) / [envsize g'] @-}
lem_subst_tv_wfenv :: Env -> Env -> Vname -> Type -> Kind -> WFType -> WFEnv -> WFEnv
lem_subst_tv_wfenv g Empty           a t_a k_a p_g_ta p_xg_wf  = case p_xg_wf of
  (WFEBind  _g p_g_wf _ _ _ _) -> p_g_wf
  (WFEBindT _g p_g_wf _ _)     -> p_g_wf
lem_subst_tv_wfenv g (Cons z t_z g') a t_a k_a p_g_ta p_env_wf = case p_env_wf of
  (WFEBind env' p_env'_wf _z _tz k_z p_env'_tz) 
    -> WFEBind env'' p_env''_wf z (tsubFTV a t_a t_z) k_z p_env''_tzta
      where
        env''        = concatE g (esubFTV a t_a g')
        p_env''_wf   = lem_subst_tv_wfenv g g' a t_a k_a p_g_ta p_env'_wf
        p_env''_tzta = lem_subst_tv_wf    g g' a t_a k_a p_g_ta p_env'_wf t_z k_z p_env'_tz
lem_subst_tv_wfenv g (ConsT a1 k1 g') a t_a k_a p_g_ta p_env_wf = case p_env_wf of
  (WFEBindT env' p_env'_wf _a1 _k1)          -> WFEBindT env'' p_env''_wf a1 k1
    where
      env''      = concatE g (esubFTV a t_a g')
      p_env''_wf = lem_subst_tv_wfenv g g' a t_a k_a p_g_ta p_env'_wf

-----------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
-----------------------------------------------------------

{-@ lem_witness_sub :: g:Env -> v_x:Value -> t_x:Type -> ProofOf(HasType g v_x t_x) 
        -> ProofOf(WFEnv g) -> x:Vname -> t':Type -> k':Kind 
        -> { y:Vname | not (in_env y g) && not (Set_mem y (free t')) && not (Set_mem y (freeTV t')) }
        -> ProofOf(WFType (Cons y t_x g) (unbindT x y t') k')
        -> ProofOf(Subtype g (tsubBV x v_x t') (TExists x t_x t')) @-}
lem_witness_sub :: Env -> Expr -> Type -> HasType -> WFEnv -> Vname -> Type -> Kind
                       -> Vname -> WFType -> Subtype
lem_witness_sub g v_x t_x p_vx_tx p_g_wf x t' k' y p_yg_t' 
  = SWitn g v_x t_x p_vx_tx (tsubBV x v_x t') x t' p_t'vx_t'vx
      where
      p_g_tx      = lem_typing_wf g v_x t_x p_vx_tx p_g_wf
      p_yg_wf     = WFEBind g p_g_wf y t_x Star p_g_tx
      p_g_t'vx    = lem_subst_wf g Empty y v_x t_x p_vx_tx p_yg_wf (unbindT x y t') k' p_yg_t'
                                 ? lem_tsubFV_unbindT x y v_x t'
      p_t'vx_t'vx = lem_sub_refl g (tsubBV x v_x t') k' p_g_t'vx p_g_wf
