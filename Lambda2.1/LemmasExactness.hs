{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasExactness where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import SameBinders
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
import SystemFAlphaEquivalence
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
import DenotationsSoundnessSub
import PrimitivesSemantics
import PrimitivesDenotations

{-@ reflect foo52 @-}
foo52 x = Just x           
foo52 :: a -> Maybe a    

-- do I need this?    -> ProofOf(HasType g e t)
{-@ lem_self_is_subtype :: g:Env -> t:Type -> k:Kind -> ProofOf(WFType g t k) 
        -> { e:Expr | Set_emp ( freeBV e ) && Set_sub (fv e) (binds g) }
        -> ProofOf(WFEnv g) -> ProofOf(Subtype g (self t e k) t) / [tsize t] @-}
lem_self_is_subtype :: Env -> Type -> Kind -> WFType -> Expr -> WFEnv -> Subtype 
lem_self_is_subtype = undefined {- CHECKED
lem_self_is_subtype g (TRefn b x p)        Base p_g_t e p_g_wf 
  = lem_self_refn_sub g b x p p_g_wf p_g_t e 
lem_self_is_subtype g t@(TFunc x t_x t')   Base p_g_t e p_g_wf 
  = lem_sub_refl g t Base p_g_t p_g_wf 
lem_self_is_subtype g t@(TExists x t_x t') Base p_g_t e p_g_wf 
  = SBind g x t_x (self t' e Base) (TExists x t_x t' ? lem_free_bound_in_env g t Base p_g_t y
                                                     ? lem_tfreeBV_empty g t Base p_g_t p_g_wf)
          y p_self_exis
      where
        (WFExis _ _ _tx k_x p_g_tx _t' _ y p_yg_t') 
                    = lem_wfexis_for_wf_texists g x t_x t' Base p_g_t
        p_yg_wf     = WFEBind g p_g_wf y t_x k_x p_g_tx
        p_yg_tx     = lem_weaken_wf g Empty p_g_wf t_x k_x p_g_tx y t_x
        -- y:t_x, g |- (self t_x y) <: tx
        p_selftx_tx = lem_self_is_subtype (Cons y t_x g) t_x k_x p_yg_tx (FV y) p_yg_wf
        -- y:t_x, g |- (unbindT x y (self t' e Base)) <: unbindT x y t'
        p_selft'_t' = lem_self_is_subtype (Cons y t_x g) (unbindT x y t') Base p_yg_t' 
                                          e p_yg_wf ? lem_tsubBV_self x (FV y) t' e Base
        p_y_tx      = TSub (Cons y t_x g) (FV y) (self t_x (FV y) k_x) 
                           (TVar1 g y t_x k_x p_g_tx) t_x k_x p_yg_tx p_selftx_tx
        p_self_exis = SWitn (Cons y t_x g) (FV y) t_x p_y_tx (unbindT x y (self t' e Base)) 
                            x t' p_selft'_t' -- y,g |- (Self t' e)[y/x] <: \ex x:tx. t'
lem_self_is_subtype g t@(TPoly a k_a t')   Base p_g_t e p_g_wf 
  = lem_sub_refl g t Base p_g_t p_g_wf
lem_self_is_subtype g t                    Star p_g_t e p_g_wf 
  = lem_sub_refl g t Star p_g_t p_g_wf
-}

{-@ lem_subtype_in_exists :: g:Env -> x:Vname -> t_x:Type -> k_x:Kind 
        -> ProofOf(WFType g t_x k_x) -> ProofOf(WFEnv g) -> t:Type 
        -> { t':Type | not (Set_mem x (tfreeBV t')) }
        -> { y:Vname | not (in_env y g) && not (Set_mem y (free t))
                                        && not (Set_mem y (free t')) }
        -> ProofOf(Subtype (Cons y t_x g) (unbindT x y t) (unbindT x y t'))
        -> ProofOf(Subtype g (TExists x t_x t) (TExists x t_x t')) @-}
lem_subtype_in_exists :: Env -> Vname -> Type -> Kind -> WFType -> WFEnv -> Type -> Type 
                           -> Vname -> Subtype -> Subtype
lem_subtype_in_exists g x t_x k_x p_g_tx p_g_wf t t' y p_yg_t_t' = undefined {- CHECKED
  = SBind g x t_x t (TExists x t_x t' ? lem_free_bound_in_env g t_x k_x p_g_tx y
                                      ? lem_tfreeBV_empty g t_x k_x p_g_tx p_g_wf
                                      ? toProof ( free (TExists x t_x t') === S.union (free t_x) (free t') ))
          y p_t_ext'
      where
        p_yg_wf     = WFEBind g p_g_wf y t_x k_x p_g_tx
        p_yg_tx     = lem_weaken_wf g Empty p_g_wf t_x k_x p_g_tx y t_x
        -- y:t_x, g |- (self t_x y) <: tx
        p_selftx_tx = lem_self_is_subtype (Cons y t_x g) t_x k_x p_yg_tx (FV y) p_yg_wf
        p_y_tx      = TSub (Cons y t_x g) (FV y) (self t_x (FV y) k_x) 
                           (TVar1 g y t_x k_x p_g_tx) t_x k_x p_yg_tx p_selftx_tx
        p_t_ext'    = SWitn (Cons y t_x g) (FV y) t_x p_y_tx (unbindT x y t) x t' p_yg_t_t'        
-}

{-@ lem_self_idempotent_upper :: g:Env -> t:Type -> k:Kind -> ProofOf(WFType g t k)
        -> e:Expr -> ProofOf(HasFType (erase_env g) e (erase t))
        -> ProofOf(WFEnv g) -> ProofOf(Subtype g (self t e k) (self (self t e k) e k)) / [tsize t] @-}
lem_self_idempotent_upper :: Env -> Type -> Kind -> WFType -> Expr -> HasFType -> WFEnv -> Subtype
lem_self_idempotent_upper g (TRefn b z p) Base p_g_t e_ p_e_t p_g_wf = undefined {- TODO TODO
  = SBase g z b (selfify p b z e) z (selfify (selfify p b z e) b z e) y p_ent_ssp
      where 
        e         = e_ ? lem_freeBV_emptyB (erase_env g) e_ (FTBasic b) p_e_t
        -- .... invert wfrefn
        pf_p_bl   = undefined
        y_        = fresh_var g
        y         = y_ ? lem_free_bound_in_env g (TRefn b z p) Base p_g_t y_
                       ? lem_fv_bound_in_fenv (erase_env g) e (FTBasic b) p_e_t y_
        q         = (App (App (AppT (Prim Eql) (TRefn b 1 (Bc True))) (BV z)) e)
        pf_q_bl   = undefined
        p_ent_ssp = lem_entails_redundancy g b z p q y pf_p_bl pf_q_bl
-}
lem_self_idempotent_upper g t@(TFunc z t_z t') Base p_g_t e p_e_t p_g_wf 
  = lem_sub_refl g t Base p_g_t p_g_wf
lem_self_idempotent_upper g (TExists z t_z t') Base p_g_t e_ p_e_t p_g_wf = undefined {- NOT WORKING
  = lem_subtype_in_exists g z t_z k_z p_g_tz p_g_wf (self t' e Base) 
                          (self (self t' e Base) e Base) y p_st'_sst' 
      where
        e           = e_ ? lem_freeBV_emptyB (erase_env g) e_ (erase t') p_e_t
        (WFExis _ _ _tz k_z p_g_tz _t' _ y0 p_y0g_t') = p_g_t 
--                    = lem_wfexis_for_wf_texists g z t_z t' Base p_g_t
        y_          = fresh_var g
        y           = y_ ? lem_free_bound_in_env g (TExists z t_z t') Base p_g_t y_
                         -- ? lem_erase_concat g Empty
                         ? lem_fv_bound_in_fenv (erase_env g) e (erase t') p_e_t y_
        p_y0g_wf    = WFEBind g p_g_wf y0 t_z k_z p_g_tz
        p_yg_wf     = WFEBind g p_g_wf y  t_z k_z p_g_tz
        p_yg_t'     = lem_change_var_wf g y0 t_z Empty p_y0g_wf (unbindT z y0 t') Base p_y0g_t' y
                                        ? lem_tsubFV_unbindT z y0 (FV y) t'
        p_er_g      = lem_erase_env_wfenv g p_g_wf
        p_e_t'      = lem_weaken_ftyp (erase_env g) FEmpty p_er_g e (erase t') p_e_t y (erase t_z)
        p_st'_sst'  = lem_self_idempotent_upper (Cons y t_z g) (unbindT z y t') Base p_yg_t'
                          e (p_e_t' ? lem_tsubBV_self z (FV y) (self (unbindT z y t') e Base) e Base
                                    ? lem_tsubBV_self z (FV y) (unbindT z y t') e Base ) p_yg_wf
-}
lem_self_idempotent_upper g t@(TPoly a k_a t') Base p_g_t e p_e_t p_g_wf 
  = lem_sub_refl g t Base p_g_t p_g_wf
lem_self_idempotent_upper g t                  Star p_g_t e p_e_t p_g_wf 
  = lem_sub_refl g t Star p_g_t p_g_wf

{-@ lem_self_idempotent_lower :: g:Env -> t:Type -> k:Kind -> ProofOf(WFType g t k)
        -> e:Expr -> ProofOf(HasFType (erase_env g) e (erase t))
        -> ProofOf(WFEnv g) -> ProofOf(Subtype g (self (self t e k) e k) (self t e k)) @-}
lem_self_idempotent_lower :: Env -> Type -> Kind -> WFType -> Expr -> HasFType -> WFEnv -> Subtype
lem_self_idempotent_lower g t k p_g_t e_ p_e_t p_g_wf = undefined {- CHECKED
  = lem_self_is_subtype g (self t e k) k p_g_selft e p_g_wf
      where
        e         = e_ ? lem_fv_subset_bindsF (erase_env g) e_ (erase t) p_e_t
                       ? lem_freeBV_emptyB    (erase_env g) e_ (erase t) p_e_t
        p_g_selft = lem_selfify_wf g t k p_g_t e p_e_t
-}

--        -> k:Kind -> { e:Expr | Set_emp (freeBV e) } -> t_e:Type -> ProofOf(HasType g e t_e) 
{-@ lem_exact_subtype :: g:Env -> s:Type -> t:Type -> ProofOf(Subtype g s t) 
        -> k:Kind -> { e:Expr | Set_emp (freeBV e) && Set_sub (fv e) (binds g) } 
        -> ProofOf(Subtype g (self s e k) (self t e k)) @-}
lem_exact_subtype :: Env -> Type -> Type -> Subtype -> Kind -> Expr -> Subtype
lem_exact_subtype = undefined {- recheck TODO
lem_exact_subtype g s t p_s_t@(SBase _ x1 b p1 x2 p2 y ent_yg_p2) Base e --t_e p_e_te 
  = SBase g x1 b (selfify p1 b x1 e) x2 (selfify p2 b x2 e) y ent_yg_selfp2
      where
        (EntPred _ _ reduce_thp2_tt) = ent_yg_p2
        g'            = Cons y (TRefn b x1 (selfify p1 b x1 e)) g
        ent_yg_selfp2 = lem_self_entails_self g b x1 p1 x2 p2 y ent_yg_p2 e {-t_e p_e_te-}
lem_exact_subtype g s t p_s_t@(SFunc {}) k e {-t_e p_e_te-} = p_s_t
lem_exact_subtype g s t p_s_t@(SWitn _ v_x t_x p_vx_tx _s x t' p_s_t'vx) Base e {-t_e p_e_te-}
  = SWitn g v_x t_x p_vx_tx (self s e Base) x (self t' e Base) p_self_s_t'vx
      where 
        p_self_s_t'vx = lem_exact_subtype g s (tsubBV x v_x t') p_s_t'vx Base e {-t_e p_e_te-}
                                          ? lem_tsubBV_self x v_x t' e Base
lem_exact_subtype g s t p_s_t@(SBind _ x s_x s' _t y p_s'_t) Base e {-t_e p_e_te-}
  = SBind g x s_x (self s' e Base) (self t e Base) y p_self_s'_t
      where
        p_self_s'_t = lem_exact_subtype (Cons y s_x g) (unbindT x y s') t p_s'_t Base e {-t_e p_e_te-}
                                        ? lem_tsubBV_self x (FV y) s' e Base
lem_exact_subtype g s t p_s_t@(SPoly {}) k e {-t_e p_e_te-} = p_s_t
lem_exact_subtype g s t p_s_t Star e {-t_e p_e_te-} = p_s_t ? toProof (self s e Star === s)
                                                            ? toProof (self t e Star === t)
-}

{-@ lem_exact_type :: g:Env -> v:Value -> t:Type -> ProofOf(HasType g v t) -> k:Kind
        -> ProofOf(HasType g v (self t v k)) @-}
lem_exact_type :: Env -> Expr -> Type -> HasType -> Kind -> HasType
lem_exact_type g e t (TBC {})   Base   = undefined -- assume this for constants
lem_exact_type g e t (TIC {})   Base   = undefined -- assume this for constants
lem_exact_type g e t (TVar1 _env z t' k' p_env_t)   Base = undefined
lem_exact_type g e t (TVar2 env_ z _t p_z_t w_ t_w) Base = undefined
lem_exact_type g e t (TVar3 env_ z _t p_z_t a_ k_a) Base = undefined
lem_exact_type g e t (TPrm {})  Base   = undefined -- assume this for primitives
lem_exact_type g e t p_e_t@(TAbs env_ z t_z k_z p_env_tz e' t' y_ p_yenv_e'_t') Base 
  = case t of
      (TFunc {}) -> p_e_t 
lem_exact_type g e t (TApp {})  Base  = impossible "not a value"
lem_exact_type g e t p_e_t@(TAbsT _env a k e' t' k_t' a' p_a'env_e'_t' p_a'env_t') Base 
  = case t of
      (TPoly {}) -> p_e_t
lem_exact_type g e t (TAppT {}) Base = impossible "not a value"
lem_exact_type g e t (TLet {})  Base = impossible "not a value"
lem_exact_type g e t (TAnn {})  Base = impossible "not a value"
lem_exact_type g e t p_e_t@(TSub _g e_ s p_g_e_s t_ k p_g_t p_g_s_t) Base
  = TSub g e (self s e Base) p_e_selfs (self t e Base) k p_g_selft p_selfs_selft
     where
       p_e_selfs     = lem_exact_type    g e s p_g_e_s Base
       p_g_selft     = lem_selfify_wf'   g t k p_g_t e p_e_t
       p_selfs_selft = lem_exact_subtype g s t p_g_s_t Base e
lem_exact_type g e t p_e_t Star = p_e_t
