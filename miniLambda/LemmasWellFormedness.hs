{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasWellFormedness where

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

{-@ reflect foo41 @-}
foo41 x = Just x
foo41 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------

{-@ lem_selfify_wf :: g:Env -> t:Type -> ProofOf(WFType g t) -> e:Expr
        -> ProofOf(HasFType (erase_env g) e (erase t))
        -> ProofOf(WFType g (self t e)) @-}
lem_selfify_wf :: Env -> Type -> WFType -> Expr -> HasFType -> WFType
lem_selfify_wf g t@(TRefn b z p) p_g_t e p_e_t = case p_g_t of
  (WFRefn _g _z _b _p  y pf_p_bl) {--> case b of
    TBool-} -> WFRefn g z b p' w pf_p'_bl 
      where
        Prim c      = equals b
        w_          = fresh_var g 
        w           = w_ ? lem_fv_bound_in_fenv (erase_env g) e (erase t) p_e_t w_
                         ? lem_free_subset_binds g t p_g_t
        g''         = FCons w (FTBasic b) (erase_env g)
        pf_pw_bl    = lem_change_var_ftyp (erase_env g) y (FTBasic b) FEmpty (unbind z y p) (FTBasic TBool) 
                                          pf_p_bl w ? lem_subFV_unbind z y (FV w) p
        p_g''_e_t   = lem_weaken_ftyp (erase_env g) FEmpty e (erase t) p_e_t w (FTBasic b)
        p'          = App (App (Prim And) p) (App (App (equals b) (BV z)) e)
--                                  ? lem_fv_subset_bindsF (erase_env g) e (erase t) p_e_t)
        blbl        = FTFunc (FTBasic TBool) (FTBasic TBool)
        b_bl        = FTFunc (FTBasic b) (FTBasic TBool)
        app_eqv1    = FTApp g'' (equals b) (FTBasic b) b_bl (FTPrm g'' c) 
                            (FV w) (FTVar1 (erase_env g) w (FTBasic b))
        app_eqv2    = FTApp g'' (App (equals b) (FV w)) (FTBasic b) (FTBasic TBool) app_eqv1
                            e p_g''_e_t
        app_and1    = FTApp g'' (Prim And) (FTBasic TBool) blbl (FTPrm g'' And)
                            (unbind z w p) pf_pw_bl
        {-@ pf_p'_bl :: ProofOf(HasFType g'' (unbind z w p') (FTBasic TBool)) @-}
        pf_p'_bl    = FTApp g'' (App (Prim And) (unbind z w p)) (FTBasic TBool) (FTBasic TBool) app_and1
                            (App (App (equals b) (FV w)) e) app_eqv2
                            ? lem_subBV_notin z (FV w) (e
                                    ? lem_freeBV_emptyB (erase_env g) e (erase t) p_e_t)
lem_selfify_wf g t@(TExists z t_z t') p_g_t e p_e_t = case p_g_t of
    (WFExis _ _z _tz p_tz_wf _t' y' p_y'_t'_wf) 
      -> WFExis g z t_z p_tz_wf (self t' e) (y' ? lem_fv_bound_in_fenv (erase_env g) e (erase t) p_e_t y')
                p_y'_selft'_wf
           where
             p_y'g_e_t      = lem_weaken_ftyp (erase_env g) FEmpty e (erase t) p_e_t y' (erase t_z)
             p_y'_selft'_wf = lem_selfify_wf (Cons y' t_z g) (unbindT z y' t') p_y'_t'_wf e 
                                             (p_y'g_e_t ? lem_erase_tsubBV z (FV y') t')
                                             ? lem_tsubBV_self z (FV y') t' (e
                                                   ? lem_freeBV_emptyB (erase_env g) e (erase t) p_e_t)
lem_selfify_wf g t                    p_g_t e p_e_t = p_g_t

{-@ lem_subtype_in_env_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> { x:Vname | (not (in_env x g)) && not (in_env x g') }
      -> s_x:Type -> t_x:Type -> ProofOf(Subtype g s_x t_x) -> t:Type 
      -> ProofOf(WFType (concatE (Cons x t_x g) g') t)
      -> ProofOf(WFType (concatE (Cons x s_x g) g') t) @-} 
lem_subtype_in_env_wf :: Env -> Env -> Vname -> Type -> Type -> Subtype -> Type -> WFType -> WFType
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t (WFRefn env z b p z'_ p_z'env_p_bl) 
    = WFRefn (concatE (Cons x s_x g) g') z b p z' p_z'env'_p_bl
        where
          z'            = z'_ ? lem_in_env_concat (Cons x t_x g) g' z'_ -- or lemma binds equal
                              ? lem_in_env_concat (Cons x s_x g) g' z'_
          p_z'env'_p_bl = p_z'env_p_bl ? lem_erase_concat (Cons x s_x g) g' -- (Cons z' (FTBasic b) g')
                                       ? lem_erase_concat (Cons x t_x g) g' -- (Cons z' (FTBasic b) g')
                                       ? lem_erase_subtype g s_x t_x p_sx_tx
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t (WFFunc env z t_z p_env_tz t' z'_ p_z'env_t')
    = WFFunc (concatE (Cons x s_x g) g') z t_z p_env'_tz t' z' p_z'env'_t'
        where
          z'            = z'_ ? lem_in_env_concat (Cons x t_x g) g' z'_ -- or lemma binds equal
                              ? lem_in_env_concat (Cons x s_x g) g' z'_
          p_env'_tz   = lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t_z p_env_tz
          p_z'env'_t' = lem_subtype_in_env_wf g (Cons z' t_z g') x s_x t_x p_sx_tx 
                                              (unbindT z z' t') p_z'env_t'
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t (WFExis env z t_z p_env_tz t' z'_ p_z'env_t')
    = WFExis (concatE (Cons x s_x g) g') z t_z p_env'_tz t' z' p_z'env'_t'
        where
          z'            = z'_ ? lem_in_env_concat (Cons x t_x g) g' z'_ -- or lemma binds equal
                              ? lem_in_env_concat (Cons x s_x g) g' z'_
          p_env'_tz   = lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t_z p_env_tz
          p_z'env'_t' = lem_subtype_in_env_wf g (Cons z' t_z g') x s_x t_x p_sx_tx 
                                              (unbindT z z' t') p_z'env_t'
