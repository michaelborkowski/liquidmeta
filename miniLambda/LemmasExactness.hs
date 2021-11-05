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
import PrimitivesWFType
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import Implications
import Entailments
import LemmasChangeVarWF
import LemmasWeakenWF
import LemmasWellFormedness
import LemmasTyping
import LemmasSubtyping
import LemmasChangeVarTyp
import LemmasWeakenTyp
import DenotationsSelfify
import DenotationsSoundness
import PrimitivesSemantics
import PrimitivesDenotations

{-@ reflect foo52 @-}
foo52 x = Just x           
foo52 :: a -> Maybe a    


{-@ lem_self_entails_self :: g:Env -> ProofOf(WFEnv g) -> b:Basic -> x1:Vname -> p1:Pred 
        -> x2:Vname -> p2:Pred 
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p1)) && not (Set_mem y (fv p2)) }  
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) (unbind x1 y p1) (FTBasic TBool))
        -> ProofOf(Entails (Cons y (TRefn b x1 p1) g) (unbind x2 y p2)) 
        -> e:Expr -> ProofOf(HasFType (erase_env g) e (FTBasic b))
        -> ProofOf(Entails (Cons y (TRefn b x1 (selfify p1 b x1 e)) g) (unbind x2 y (selfify p2 b x2 e))) @-}
lem_self_entails_self :: Env -> WFEnv -> Basic -> Vname -> Pred -> Vname -> Pred -> Vname 
                             -> HasFType -> Entails -> Expr -> HasFType -> Entails
lem_self_entails_self g p_g_wf b x1 p1 x2 p2 y pf_p1_bl ent_yg_p2 e_ p_e_b 
  = EntPred yg (unbind x2 y (selfify p2 b x2 e)) reduce_thselfp2_tt             
       where
         {-@ reduce_thselfp2_tt :: th:CSub -> ProofOf(DenotesEnv yg th)
                  -> ProofOf(EvalsTo (csubst th (unbind x2 y (selfify p2 b x2 e))) (Bc True)) @-}
         reduce_thselfp2_tt :: CSub -> DenotesEnv -> EvalsTo
         reduce_thselfp2_tt th den_yg_th = case den_yg_th of
           (DExt _g th' den_g_th' _y _t1 th'y den_th't1_th'y) ->
                 lemma_and_semantics (csubst th (unbind x2 y p2)) True ev_thp2_tt
                                     (csubst th (unbind x2 y r2)) True ev_thr1_tt
                                     ? lem_csubst_app th (App (Prim And) (unbind x2 y p2)) (unbind x2 y r2)
                                     ? lem_csubst_app th (Prim And) (unbind x2 y p2)
                                     ? lem_csubst_prim th And
             where
               {-@ ev_thp1r_tt :: ProofOf(EvalsTo (subBV x1 th'y (csubst th' p1andr)) (Bc True)) @-}
               {-@ p_th'y_b :: ProofOf(HasFType FEmpty th'y (FTBasic b)) @-}
               ev_thp1r_tt = get_evals_from_drefn b x1 (csubst th' (selfify p1 b x1 e)) th'y (den_th't1_th'y
                                 ? lem_ctsubst_refn th' b x1 (selfify p1 b x1 e)) 
               p_th'y_b    = get_ftyp_from_den (ctsubst th' (TRefn b x1 (selfify p1 b x1 e))) th'y  den_th't1_th'y
                                 ? lem_erase_ctsubst th' (TRefn b x1 (selfify p1 b x1 e)) 
               (ev_thp1_tt, ev_thr1_tt) = lem_implies_elimination (Cons y t1 g) th den_yg_th
                                 (unbind x1 y p1) (unbind x1 y r1) pf_p1_bl pf_r_bl 
                                 (ev_thp1r_tt ? lem_csubst_subBV x1 th'y (FTBasic b) p_th'y_b th' p1andr
                                              ? lem_subFV_unbind x1 y th'y p1andr)
                                 ? lem_binds_env_th g th' den_g_th'
               den_th'p1_th'y = lem_denote_sound_sub g t1 (TRefn b x1 p1) p_t1_t1' p_g_wf 
                                                     p_g_t1 p_g_t1' th' den_g_th' th'y den_th't1_th'y
               den_yg'_th  = DExt g th' den_g_th' y (TRefn b x1 p1) th'y den_th'p1_th'y
               ev_thp2_tt  = reduce_thp2_tt th den_yg'_th
         e             = e_ ? lem_freeBV_emptyB (erase_env g) e_ (FTBasic b) p_e_b
                            ? lem_fv_subset_bindsF (erase_env g) e_ (FTBasic b) p_e_b
                            ? lem_subBV_notin x1 (FV y) e_ 
                            ? lem_subBV_notin x2 (FV y) e_ 
         (Prim c)      = equals b
         yg            = Cons y (TRefn b x1 (selfify p1 b x1 e)) g  
         t1            =         TRefn b x1 (selfify p1 b x1 e)
         p_g_t1'       = WFRefn g x1 b p1 y pf_p1_bl
         p_g_t1        = lem_selfify_wf g (TRefn b x1 p1) p_g_t1' e p_e_b
         p_t1_t1'      = lem_self_is_subtype g (TRefn b x1 p1) p_g_t1' e p_e_b p_g_wf
         {-@ reduce_thp2_tt :: th0:CSub -> ProofOf(DenotesEnv (Cons y (TRefn b x1 p1) g) th0) 
                                        -> ProofOf(EvalsTo (csubst th0 (unbind x2 y p2)) (Bc True)) @-}
         (EntPred _ _ reduce_thp2_tt) = ent_yg_p2
         {-@ r1 :: { r1:Expr | unbind x1 y r1 ==  App (App (equals b) (FV y)) e } @-}
         r1            = App (App (equals b) (BV x1)) e 
         {-@ r2 :: { r2:Expr | unbind x2 y r2 ==  App (App (equals b) (FV y)) e } @-}
         r2            = App (App (equals b) (BV x2)) e 
         {-@ p1andr :: { pr:Expr | unbind x1 y pr == App (App (Prim And) (unbind x1 y p1)) (unbind x1 y r1) } @-}
         p1andr        = App (App (Prim And) p1) (App (App (equals b) (BV x1)) e)
         p_yg_e_b    = lem_weaken_ftyp (erase_env g) FEmpty e (FTBasic b) p_e_b y (FTBasic b)
         pf_eqb_bl   = FTApp (erase_env yg) (equals b) (FTBasic b) (FTFunc (FTBasic b) (FTBasic TBool))
                             (FTPrm (erase_env yg) c) (FV y) (FTVar1 (erase_env g) y (FTBasic b))
         {-@ pf_r_bl :: ProofOf(HasFType (erase_env yg) (unbind x1 y r1) (FTBasic TBool)) @-} 
         pf_r_bl     = FTApp (erase_env yg) (App (equals b) (FV y)) (FTBasic b) (FTBasic TBool)
                             pf_eqb_bl e p_yg_e_b  

{-@ lem_subtype_in_exists :: g:Env -> x:Vname -> t_x:Type 
        -> ProofOf(WFType g t_x) -> ProofOf(WFEnv g) -> t:Type 
        -> t':Type 
        -> { y:Vname | not (in_env y g) && not (Set_mem y (free t))
                                        && not (Set_mem y (free t')) }
        -> ProofOf(Subtype (Cons y t_x g) (unbindT x y t) (unbindT x y t'))
        -> ProofOf(Subtype g (TExists x t_x t) (TExists x t_x t')) @-}
lem_subtype_in_exists :: Env -> Vname -> Type -> WFType -> WFEnv -> Type -> Type 
                           -> Vname -> Subtype -> Subtype
lem_subtype_in_exists g x t_x p_g_tx p_g_wf t t' y p_yg_t_t' 
  = SBind g x t_x t (TExists x t_x t' ? lem_free_bound_in_env g t_x p_g_tx y
                                      ? lem_tfreeBV_empty g t_x p_g_tx 
                                      ? toProof ( free (TExists x t_x t') === S.union (free t_x) (free t') ))
          y p_t_ext'
      where
        p_yg_wf     = WFEBind g p_g_wf y t_x p_g_tx
        p_yg_tx     = lem_weaken_wf g Empty t_x p_g_tx y t_x
        -- y:t_x, g |- (self t_x y) <: tx
        p_y_er_tx   = FTVar1 (erase_env g) y (erase t_x)
        p_selftx_tx = lem_self_is_subtype (Cons y t_x g) t_x p_yg_tx (FV y) p_y_er_tx p_yg_wf
        p_y_tx      = TSub (Cons y t_x g) (FV y) (self t_x (FV y)) 
                           (TVar1 g y t_x p_g_tx) t_x p_yg_tx p_selftx_tx
        p_t_ext'    = SWitn (Cons y t_x g) (FV y) t_x p_y_tx (unbindT x y t) x t' p_yg_t_t'        

{-@ lem_self_idempotent_upper :: g:Env -> t:Type -> ProofOf(WFType g t)
        -> e:Expr -> ProofOf(HasFType (erase_env g) e (erase t))
        -> ProofOf(WFEnv g) -> ProofOf(Subtype g (self t e) (self (self t e) e)) @-}
lem_self_idempotent_upper :: Env -> Type -> WFType -> Expr -> HasFType -> WFEnv -> Subtype
lem_self_idempotent_upper g t{- @(TRefn b z p)-} p_g_t@(WFRefn _ z b p w pf_wg_p) 
                          e_ p_e_t p_g_wf  
  = SBase g z b (selfify p b z e) z (selfify (selfify p b z e) b z e) y p_ent_ssp
      where 
        (Prim c)  = equals b
        e         = e_ ? lem_freeBV_emptyB (erase_env g) e_ (FTBasic b) p_e_t
--        (WFRefn _g _ _ _p w pf_wg_p) = p_g_t
        y_        = fresh_var g
        y         = y_ ? lem_free_bound_in_env g (TRefn b z p) p_g_t y_
                       ? lem_fv_bound_in_fenv (erase_env g) e (FTBasic b) p_e_t y_ 
        pf_yg_p   = lem_change_var_ftyp (erase_env g) w (FTBasic b) FEmpty (unbind z w p) 
                                        (FTBasic TBool) pf_wg_p y
                                        ? lem_subFV_unbind z w (FV y) p
        g'        = FCons y (FTBasic b) (erase_env g)
        p_g'_e_t  = lem_weaken_ftyp (erase_env g) FEmpty e (erase t) p_e_t y (FTBasic b)
        q         = App (App (equals b) (BV z)) e
        pf_eqy_bl = FTApp g' (equals b) (FTBasic b) (FTFunc (FTBasic b) (FTBasic TBool))
                          (FTPrm g' c) (FV y) (FTVar1 (erase_env g) y (FTBasic b))
        {-@ pf_q_bl :: ProofOf(HasFType g' (unbind z y q) (FTBasic TBool)) @-}
        pf_q_bl   = FTApp g' (App (equals b) (FV y)) (FTBasic b) (FTBasic TBool)
                          pf_eqy_bl e p_g'_e_t
                          ? lem_subBV_notin z (FV y) (e
                                ? lem_freeBV_emptyB g' e (erase t) p_g'_e_t)
        p_ent_ssp = lem_entails_redundancy g b z p q y pf_yg_p pf_q_bl

lem_self_idempotent_upper g t p_g_t@(WFFunc {}) e p_e_t p_g_wf 
  = lem_sub_refl g t p_g_t p_g_wf
lem_self_idempotent_upper g t{-(TExists z t_z t')-} p_g_t@(WFExis _ z t_z p_g_tz t' y0 p_y0g_t')
                          e_ p_e_t p_g_wf  
  = lem_subtype_in_exists g z t_z p_g_tz p_g_wf (self {-(unbindT z y-} t'{-)-} e)
                          (self (self {-(unbindT z y-} t'{-)-} e) e) y p_st'_sst' 
      where
        e           = e_ ? lem_freeBV_emptyB (erase_env g) e_ (erase t') p_e_t
        y_          = fresh_var g
        y           = y_ ? lem_free_bound_in_env g (TExists z t_z t') p_g_t y_
                         ? lem_fv_bound_in_fenv (erase_env g) e (erase t') p_e_t y_
        p_yg_wf     = WFEBind g p_g_wf y  t_z p_g_tz
        p_yg_t'     = lem_change_var_wf g y0 t_z Empty (unbindT z y0 t') p_y0g_t' y
                                        ? lem_tsubFV_unbindT z y0 (FV y) t'
        p_e_t'      = lem_weaken_ftyp (erase_env g) FEmpty e (erase t') p_e_t y (erase t_z)
        p_st'_sst'  = lem_self_idempotent_upper (Cons y t_z g) (unbindT z y t') p_yg_t'
                          e (p_e_t' ? lem_erase_tsubBV z (FV y) t') p_yg_wf
                           ? lem_tsubBV_self z (FV y) (self t' e) e
                           ? lem_tsubBV_self z (FV y) t' e

{-@ lem_self_idempotent_lower :: g:Env -> t:Type -> ProofOf(WFType g t)
        -> e:Expr -> ProofOf(HasFType (erase_env g) e (erase t))
        -> ProofOf(WFEnv g) -> ProofOf(Subtype g (self (self t e) e) (self t e)) @-}
lem_self_idempotent_lower :: Env -> Type -> WFType -> Expr -> HasFType -> WFEnv -> Subtype
lem_self_idempotent_lower g t p_g_t e_ p_e_t p_g_wf 
  = lem_self_is_subtype g (self t e) p_g_selft e p_e_t p_g_wf
      where
        e         = e_ ? lem_fv_subset_bindsF (erase_env g) e_ (erase t) p_e_t
                       ? lem_freeBV_emptyB    (erase_env g) e_ (erase t) p_e_t
        p_g_selft = lem_selfify_wf g t p_g_t e p_e_t

--        -> k:Kind -> { e:Expr | Set_emp (freeBV e) } -> t_e:Type -> ProofOf(HasType g e t_e) 
{-@ lem_exact_subtype :: g:Env -> ProofOf(WFEnv g) -> s:Type -> ProofOf(WFType g s) 
        -> t:Type -> ProofOf(Subtype g s t) 
        -> { e:Expr | Set_emp (freeBV e) && Set_sub (fv e) (binds g) } 
        -> ProofOf(HasFType (erase_env g) e (erase t))
        -> ProofOf(Subtype g (self s e) (self t e)) @-}
lem_exact_subtype :: Env -> WFEnv -> Type -> WFType -> Type -> Subtype -> Expr -> HasFType -> Subtype
lem_exact_subtype g p_g_wf s p_g_s t p_s_t@(SBase _ x1 b p1 x2 p2 y_ ent_yg_p2) e p_e_t
  = case p_g_s of 
      (WFRefn  _ _ _ _p1 w pf_w_p1_bl) -> 
        SBase g x1 b (selfify p1 b x1 e) x2 (selfify p2 b x2 e) y ent_yg_selfp2
          where
            y             = y_ ? lem_free_subset_binds g s p_g_s
            pf_y_p1_bl    = lem_change_var_ftyp (erase_env g) w (FTBasic b) FEmpty 
                                                (unbind x1 w p1) (FTBasic TBool) pf_w_p1_bl y
                                                ? lem_subFV_unbind x1 w (FV y) p1
            ent_yg_selfp2 = lem_self_entails_self g p_g_wf b x1 p1 x2 p2 y pf_y_p1_bl ent_yg_p2 e p_e_t
lem_exact_subtype g p_g_wf s p_g_s t p_s_t@(SFunc {}) e p_e_t  = p_s_t
lem_exact_subtype g p_g_wf s p_g_s t p_s_t@(SWitn _ v_x t_x p_vx_tx _s x t' p_s_t'vx) e p_e_t
  = SWitn g v_x t_x p_vx_tx (self s e) x (self t' e) p_self_s_t'vx
      where 
        p_self_s_t'vx = lem_exact_subtype g p_g_wf s p_g_s (tsubBV x v_x t') p_s_t'vx e 
                                          (p_e_t ? lem_erase_tsubBV x v_x t')
                                          ? lem_tsubBV_self x v_x t' e 
lem_exact_subtype g p_g_wf s p_g_s t p_s_t@(SBind _ x s_x s' _t y p_s'_t) e p_e_t 
  = SBind g x s_x (self s' e) (self t e) y p_self_s'_t
      where
        (WFExis _ _ _sx p_g_sx _ w p_wg_s') = p_g_s
        p_yg_wf     = WFEBind g p_g_wf y s_x p_g_sx
        p_yg_e_t    = lem_weaken_ftyp (erase_env g) FEmpty e (erase t) p_e_t y (erase s_x)
        p_yg_s'     = lem_change_var_wf g w s_x Empty (unbindT x w s') p_wg_s' y
                                        ? lem_tsubFV_unbindT x w (FV y) s'
        p_self_s'_t = lem_exact_subtype (Cons y s_x g) p_yg_wf (unbindT x y s') p_yg_s' t 
                                        p_s'_t e p_yg_e_t
                                        ? lem_tsubBV_self x (FV y) s' e 

{-@ lem_exact_type :: g:Env -> v:Value -> t:Type -> ProofOf(HasType g v t) 
        -> ProofOf(WFEnv g) -> ProofOf(HasType g v (self t v)) @-}
lem_exact_type :: Env -> Expr -> Type -> HasType -> WFEnv -> HasType
lem_exact_type g e t (TBC _ b) p_g_wf     
  = TSub g (Bc b) (tybc b) (TBC g b) (self (tybc b) (Bc b)) p_g_self_tybc tybc_self_tybc
      where
        refn_tybc      = App (App (Prim Eqv) (BV 1)) (Bc b)
        p_g_tybc       = lem_wf_tybc g b
        p_g_self_tybc  = lem_selfify_wf' g (tybc b) p_g_tybc p_g_wf (Bc b) (TBC g b)
        tybc_self_tybc = lem_subtype_repetition g TBool 1 refn_tybc p_g_tybc
lem_exact_type g e t (TIC _ n) p_g_wf   
  = TSub g (Ic n) (tyic n) (TIC g n) (self (tyic n) (Ic n)) p_g_self_tyic tyic_self_tyic
      where
        refn_tyic      = App (App (Prim Eq) (BV 1)) (Ic n)
        p_g_tyic       = lem_wf_tyic g n
        p_g_self_tyic  = lem_selfify_wf' g (tyic n) p_g_tyic p_g_wf (Ic n) (TIC g n)
        tyic_self_tyic = lem_subtype_repetition g TInt 1 refn_tyic p_g_tyic
lem_exact_type g e t p_e_t@(TVar1 env z t' p_env_t) p_g_wf   
  = TSub g (FV z) (self t' (FV z)) p_e_t (self (self t' (FV z)) (FV z)) p_g_selft t_self_t 
      where
        (WFEBind _env p_env_wf _ _ p_env_t') = p_g_wf 
        p_g_t'    = lem_weaken_wf   env Empty t' p_env_t' z t'
        p_g_t     = lem_typing_wf   g e t p_e_t p_g_wf
        p_g_selft = lem_selfify_wf' g   t p_g_t p_g_wf (FV z) p_e_t
        p_g_t_t'  = lem_self_is_subtype g t' p_g_t' (FV z) p_z_t' p_g_wf
        p_z_t'    = FTVar1 (erase_env env)  z (erase t')
        t_self_t  = lem_self_idempotent_upper g t' p_g_t' (FV z) p_z_t' p_g_wf
lem_exact_type g e t (TVar2 env z _t p_z_t w t_w) p_g_wf  
  = TVar2 env z (self t e) p_z_selftz w t_w
      where
        (WFEBind _env p_env_wf _ _ p_env_tw) = p_g_wf 
        p_z_selftz = lem_exact_type env e t p_z_t p_env_wf
lem_exact_type g e t p_e_t@(TPrm {}) p_g_wf    
  = case t of
      (TFunc {}) -> p_e_t 
lem_exact_type g e t p_e_t@(TAbs env_ z t_z p_env_tz e' t' y_ p_yenv_e'_t') p_g_wf
  = case t of
      (TFunc {}) -> p_e_t 
lem_exact_type g e t (TApp {}) p_g_wf  = impossible "not a value"
lem_exact_type g e t p_e_t@(TSub _g e_ s p_g_e_s t_ p_g_t p_g_s_t) p_g_wf
  = TSub g e (self s e) p_e_selfs (self t e) p_g_selft p_selfs_selft
     where
       p_g_s         = lem_typing_wf     g e s p_g_e_s p_g_wf
       p_e_selfs     = lem_exact_type    g e s p_g_e_s p_g_wf
       p_g_selft     = lem_selfify_wf'   g t p_g_t p_g_wf e p_e_t
       p_e_er_t      = lem_typing_hasftype g e t p_e_t p_g_wf
       p_selfs_selft = lem_exact_subtype g p_g_wf s p_g_s t p_g_s_t (e
                           ? lem_freeBV_empty    g e t p_e_t p_g_wf
                           ? lem_fv_subset_binds g e t p_e_t p_g_wf) p_e_er_t
