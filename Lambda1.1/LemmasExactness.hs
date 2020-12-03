{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasExactness where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
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
--import SubstitutionLemmaWF
import DenotationsSelfify
import DenotationsSoundness
import PrimitivesSemantics
import PrimitivesDenotations

{-@ reflect foo52 @-}
foo52 x = Just x           
foo52 :: a -> Maybe a    

{-@ lem_subtype_in_exists :: g:Env -> x:Vname -> t_x:Type 
        -> ProofOf(WFType g t_x) -> ProofOf(WFEnv g) -> t:Type 
        -> { t':Type | not (Set_mem x (tfreeBV t')) }
        -> { y:Vname | not (in_env y g) && not (Set_mem y (free t))
                                        && not (Set_mem y (free t')) }
        -> ProofOf(Subtype (Cons y t_x g) (unbindT x y t) (unbindT x y t'))
        -> ProofOf(Subtype g (TExists x t_x t) (TExists x t_x t')) @-}
lem_subtype_in_exists :: Env -> Vname -> Type -> WFType -> WFEnv -> Type -> Type 
                           -> Vname -> Subtype -> Subtype
lem_subtype_in_exists g x t_x p_g_tx p_g_wf t t' y p_yg_t_t' 
 = undefined {- CHECKED
  = SBind g x t_x t (TExists x t_x t' ? lem_free_bound_in_env g t_x p_g_tx y
                                      ? lem_tfreeBV_empty g t_x p_g_tx 
                                      ? toProof ( free (TExists x t_x t') === S.union (free t_x) (free t') ))
          y p_t_ext'
      where
        p_yg_wf     = WFEBind g p_g_wf y t_x p_g_tx
        p_yg_tx     = lem_weaken_wf g Empty t_x p_g_tx y t_x
        -- y:t_x, g |- (self t_x y) <: tx
        p_selftx_tx = lem_self_is_subtype (Cons y t_x g) t_x p_yg_tx (FV y) p_yg_wf
        p_y_tx      = TSub (Cons y t_x g) (FV y) (self t_x (FV y)) 
                           (TVar1 g y t_x p_g_tx) t_x p_yg_tx p_selftx_tx
        p_t_ext'    = SWitn (Cons y t_x g) (FV y) t_x p_y_tx (unbindT x y t) x t' p_yg_t_t'        
-}

{-@ lem_self_idempotent_upper :: g:Env -> t:Type -> ProofOf(WFType g t)
        -> e:Expr -> ProofOf(HasFType (erase_env g) e (erase t))
        -> ProofOf(WFEnv g) -> ProofOf(Subtype g (self t e) (self (self t e) e)) / [tsize t] @-}
lem_self_idempotent_upper :: Env -> Type -> WFType -> Expr -> HasFType -> WFEnv -> Subtype
lem_self_idempotent_upper g t@(TRefn b z p) p_g_t e_ p_e_t p_g_wf 
  = SBase g z b (selfify p b z e) z (selfify (selfify p b z e) b z e) 
          (y ? lem_free_bound_in_env g (TRefn b z p) p_g_t y
             ? lem_fv_bound_in_fenv (erase_env g) e (FTBasic b) p_e_t y) p_ent_ssp
      where 
        (Prim c)  = equals b
        e         = e_ ? lem_freeBV_emptyB (erase_env g) e_ (FTBasic b) p_e_t
        (WFRefn _g _ _ _p y pf_p_bl) = p_g_t
{-
        y_        = fresh_var g
        y         = y_ ? lem_free_bound_in_env g (TRefn b z p) p_g_t y_
                       ? lem_fv_bound_in_fenv (erase_env g) e (FTBasic b) p_e_t y_ -}
        g'        = FCons y (FTBasic b) (erase_env g)
        p_g'_e_t   = lem_weaken_ftyp (erase_env g) FEmpty e (erase t) p_e_t y (FTBasic b)
        q         = App (App (equals b) (BV z)) e
        pf_eqy_bl = FTApp g' (equals b) (FTBasic b) (FTFunc (FTBasic b) (FTBasic TBool))
                          (FTPrm g' c) (FV y) (FTVar1 (erase_env g) y (FTBasic b))
        {-@ pf_q_bl :: ProofOf(HasFType g' (unbind z y q) (FTBasic TBool)) @-}
        pf_q_bl   = FTApp g' (App (equals b) (FV y)) (FTBasic b) (FTBasic TBool)
                          pf_eqy_bl e p_g'_e_t
                          ? lem_subBV_notin z (FV y) (e
                                ? lem_freeBV_emptyB g' e (erase t) p_g'_e_t)
        p_ent_ssp = lem_entails_redundancy g b z p q y pf_p_bl pf_q_bl
lem_self_idempotent_upper g t@(TFunc z t_z t') p_g_t e p_e_t p_g_wf 
  = lem_sub_refl g t p_g_t p_g_wf
lem_self_idempotent_upper g (TExists z t_z t') p_g_t e_ p_e_t p_g_wf 
  = lem_subtype_in_exists g z t_z p_g_tz p_g_wf (self t' e) 
                          (self (self t' e) e) y p_st'_sst' 
      where
        e           = e_ ? lem_freeBV_emptyB (erase_env g) e_ (erase t') p_e_t
        (WFExis _ _ _tz p_g_tz _t' y0 p_y0g_t') = p_g_t 
        y_          = fresh_var g
        y           = y_ ? lem_free_bound_in_env g (TExists z t_z t') p_g_t y_
                         -- ? lem_erase_concat g Empty
                         ? lem_fv_bound_in_fenv (erase_env g) e (erase t') p_e_t y_
        p_yg_wf     = WFEBind g p_g_wf y  t_z p_g_tz
        p_yg_t'     = lem_change_var_wf g y0 t_z Empty (unbindT z y0 t') p_y0g_t' y
                                        ? lem_tsubFV_unbindT z y0 (FV y) t'
        p_e_t'      = lem_weaken_ftyp (erase_env g) FEmpty e (erase t') p_e_t y (erase t_z)
        p_st'_sst'  = lem_self_idempotent_upper (Cons y t_z g) (unbindT z y t') p_yg_t'
                          e (p_e_t' ? lem_tsubBV_self z (FV y) (self (unbindT z y t') e) e 
                                    ? lem_tsubBV_self z (FV y) (unbindT z y t') e) p_yg_wf


{-@ lem_self_idempotent_lower :: g:Env -> t:Type -> ProofOf(WFType g t)
        -> e:Expr -> ProofOf(HasFType (erase_env g) e (erase t))
        -> ProofOf(WFEnv g) -> ProofOf(Subtype g (self (self t e) e) (self t e)) @-}
lem_self_idempotent_lower :: Env -> Type -> WFType -> Expr -> HasFType -> WFEnv -> Subtype
lem_self_idempotent_lower g t p_g_t e_ p_e_t p_g_wf 
 = undefined {- CHECKED
  = lem_self_is_subtype g (self t e) p_g_selft e p_g_wf
      where
        e         = e_ ? lem_fv_subset_bindsF (erase_env g) e_ (erase t) p_e_t
                       ? lem_freeBV_emptyB    (erase_env g) e_ (erase t) p_e_t
        p_g_selft = lem_selfify_wf g t p_g_t e p_e_t
-}

--        -> k:Kind -> { e:Expr | Set_emp (freeBV e) } -> t_e:Type -> ProofOf(HasType g e t_e) 
{-@ lem_exact_subtype :: g:Env -> s:Type -> t:Type -> ProofOf(Subtype g s t) 
        -> { e:Expr | Set_emp (freeBV e) && Set_sub (fv e) (binds g) } 
        -> ProofOf(Subtype g (self s e) (self t e)) @-}
lem_exact_subtype :: Env -> Type -> Type -> Subtype -> Expr -> Subtype
lem_exact_subtype g s t p_s_t@(SBase _ x1 b p1 x2 p2 y ent_yg_p2) e 
 = undefined {- CHECKED
  = SBase g x1 b (selfify p1 b x1 e) x2 (selfify p2 b x2 e) y ent_yg_selfp2
      where
        (EntPred _ _ reduce_thp2_tt) = ent_yg_p2
        g'            = Cons y (TRefn b x1 (selfify p1 b x1 e)) g
        ent_yg_selfp2 = lem_self_entails_self g b x1 p1 x2 p2 y ent_yg_p2 e 
-}
lem_exact_subtype g s t p_s_t@(SFunc {}) e  = p_s_t
lem_exact_subtype g s t p_s_t@(SWitn _ v_x t_x p_vx_tx _s x t' p_s_t'vx) e 
 = undefined {- CHECKED
  = SWitn g v_x t_x p_vx_tx (self s e) x (self t' e) p_self_s_t'vx
      where 
        p_self_s_t'vx = lem_exact_subtype g s (tsubBV x v_x t') p_s_t'vx e 
                                          ? lem_tsubBV_self x v_x t' e 
-}
lem_exact_subtype g s t p_s_t@(SBind _ x s_x s' _t y p_s'_t) e 
 = undefined {- CHECKED
  = SBind g x s_x (self s' e) (self t e) y p_self_s'_t
      where
        p_self_s'_t = lem_exact_subtype (Cons y s_x g) (unbindT x y s') t p_s'_t e 
                                        ? lem_tsubBV_self x (FV y) s' e 
-}

{-@ lem_exact_type :: g:Env -> v:Value -> t:Type -> ProofOf(HasType g v t) 
        -> ProofOf(WFEnv g) -> ProofOf(HasType g v (self t v)) @-}
lem_exact_type :: Env -> Expr -> Type -> HasType -> WFEnv -> HasType
lem_exact_type g e t (TBC {}) p_g_wf     = undefined -- assume this for constants
lem_exact_type g e t (TIC {}) p_g_wf     = undefined -- assume this for constants
lem_exact_type g e t (TVar1 _env z t' p_env_t) p_g_wf   = undefined
lem_exact_type g e t (TVar2 env_ z _t p_z_t w_ t_w) p_g_wf  = undefined
lem_exact_type g e t (TPrm {}) p_g_wf    = undefined -- assume this for primitives
lem_exact_type g e t p_e_t@(TAbs env_ z t_z p_env_tz e' t' y_ p_yenv_e'_t') p_g_wf
  = case t of
      (TFunc {}) -> p_e_t 
lem_exact_type g e t (TApp {}) p_g_wf  = impossible "not a value"
lem_exact_type g e t (TLet {}) p_g_wf  = impossible "not a value"
lem_exact_type g e t (TAnn {}) p_g_wf  = impossible "not a value"
lem_exact_type g e t p_e_t@(TSub _g e_ s p_g_e_s t_ p_g_t p_g_s_t) p_g_wf
  = TSub g e (self s e) p_e_selfs (self t e) p_g_selft p_selfs_selft
     where
       p_e_selfs     = lem_exact_type    g e s p_g_e_s p_g_wf
       p_g_selft     = lem_selfify_wf'   g t p_g_t p_g_wf e p_e_t
       p_selfs_selft = lem_exact_subtype g s t p_g_s_t (e
                           ? lem_freeBV_empty g e t p_e_t p_g_wf
                           ? lem_fv_subset_binds g e t p_e_t p_g_wf)
