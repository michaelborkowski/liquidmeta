{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasTyping where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFTyping
import WellFormedness
import PrimitivesWFType
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

{-@ reflect foo42 @-}
foo42 x = Just x
foo42 :: a -> Maybe a

{-@ lem_tsubFV_tybc :: x:Vname -> v_x:Value -> b:Bool
        -> { pf:_ | tsubFV x v_x (tybc b) == tybc b } @-}
lem_tsubFV_tybc :: Vname -> Expr -> Bool -> Proof
lem_tsubFV_tybc x v_x True  = ()
lem_tsubFV_tybc x v_x False = ()

{-@ lem_tsubFV_tyic :: x:Vname -> v_x:Value -> n:Int
        -> { pf:_ | tsubFV x v_x (tyic n) == tyic n } @-}
lem_tsubFV_tyic :: Vname -> Expr -> Int -> Proof
lem_tsubFV_tyic x v_x n = ()

{-@ lem_tsubFV_ty :: x:Vname -> v_x:Value -> c:Prim
        -> { pf:_ | tsubFV x v_x (ty c) == ty c } @-}
lem_tsubFV_ty :: Vname -> Expr -> Prim -> Proof
lem_tsubFV_ty x v_x And      = ()
lem_tsubFV_ty x v_x Or       = () 
lem_tsubFV_ty x v_x Not      = ()
lem_tsubFV_ty x v_x Eqv      = ()
lem_tsubFV_ty x v_x Leq      = ()
lem_tsubFV_ty x v_x (Leqn n) = ()
lem_tsubFV_ty x v_x Eq       = ()
lem_tsubFV_ty x v_x (Eqn n)  = ()

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------

{-@ lem_typing_wf :: g:Env -> e:Expr -> t:Type 
                      -> { p_e_t:HasType | propOf p_e_t == (HasType g e t) }
                      -> ProofOf(WFEnv g) -> ProofOf(WFType g t)  / [typSize p_e_t, 1] @-} 
lem_typing_wf :: Env -> Expr -> Type -> HasType -> WFEnv -> WFType
lem_typing_wf g e t (TBC _g b) p_wf_g  = lem_wf_tybc g b
lem_typing_wf g e t (TIC _g n) p_wf_g  = lem_wf_tyic g n
lem_typing_wf g e t p_e_t@(TVar1 _g' x t' p_g'_t') p_wf_g -- x:t',g |- (FV x) : t == self(t', x)
    = case p_wf_g of
        (WFEEmpty)                           -> impossible "surely"
        (WFEBind g' p_g' _x _t'  _p_g'_t')   -> lem_selfify_wf g t' p_g_t' (FV x) p_x_er_t'
            where
              p_x_er_t'  = lem_typing_hasftype g e t p_e_t p_wf_g
                               ? toProof ( erase ( self t' (FV x)) === erase t' )
              p_g_t'     = lem_weaken_wf g' Empty t' p_g'_t' x t'
lem_typing_wf g e t (TVar2 g' x _t p_g'_x_t y s) p_wf_g
    = case p_wf_g of
        (WFEEmpty)                         -> impossible "Surely"
        (WFEBind g' p_g' _y _s p_g'_s) -> lem_weaken_wf g' Empty t p_g'_t y s
          where 
            p_g'_t = lem_typing_wf g' e t p_g'_x_t p_g'
lem_typing_wf g e t (TPrm _g c) p_wf_g 
    = lem_weaken_many_wf Empty g (ty c) (lem_wf_ty c) ? lem_empty_concatE g
lem_typing_wf g e t (TAbs _g x t_x p_tx_wf e' t' y p_e'_t') p_wf_g
    = WFFunc g x t_x p_tx_wf t' y (lem_typing_wf (Cons y t_x g) (unbind x y e') 
                                               (unbindT x y t') p_e'_t'
                                               (WFEBind g p_wf_g y t_x p_tx_wf))
lem_typing_wf g e t (TApp _g e1 x t_x t' p_e1_txt' e2 p_e2_tx) p_wf_g
    = p_g_ext'
        where
          p_g_txt' = lem_typing_wf g e1 (TFunc x t_x t') p_e1_txt' p_wf_g
          (WFFunc _ _ _ p_g_tx _ y p_gx_t') = p_g_txt'
          p_g_ext' = WFExis g x t_x p_g_tx t' y p_gx_t'
lem_typing_wf g e t (TSub _g _e s p_e_s _t p_g_t p_s_t) p_wf_g 
    = p_g_t

{-@ lem_typing_hasftype :: g:Env -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == (HasType g e t) } -> ProofOf(WFEnv g)
        -> ProofOf(HasFType (erase_env g) e (erase t)) / [typSize p_e_t, 0] @-}
lem_typing_hasftype :: Env -> Expr -> Type -> HasType -> WFEnv -> HasFType
lem_typing_hasftype g e t (TBC _g b) p_g_wf      = FTBC (erase_env g) b
lem_typing_hasftype g e t (TIC _g n) p_g_wf      = FTIC (erase_env g) n
lem_typing_hasftype g e t (TVar1 g' x t' _) p_g_wf
  = FTVar1 (erase_env g') x (erase t') 
      ? toProof ( erase ( self t' (FV x)) === erase t' )
lem_typing_hasftype g e t (TVar2 g' x _ p_x_t y s) p_g_wf
    = FTVar2 (erase_env g') x (erase t) p_x_er_t y (erase s) 
        where
          (WFEBind _ p_g'_wf _ _ _) = p_g_wf
          p_x_er_t = lem_typing_hasftype g' e t p_x_t  p_g'_wf
lem_typing_hasftype g e t (TPrm _g c) p_g_wf     = FTPrm (erase_env g) c
    ? toProof ( erase (ty c) === erase_ty c )
lem_typing_hasftype g e t (TAbs _g x t_x p_g_tx e' t' y p_yg_e'_t') p_g_wf
    = FTAbs (erase_env g) x (erase t_x) e' 
            (erase t' ? lem_erase_tsubBV x (FV y) t') y p_yg_e'_er_t'
        where
          p_yg_wf       = WFEBind g p_g_wf y t_x p_g_tx
          p_yg_e'_er_t' = lem_typing_hasftype (Cons y t_x g) (unbind x y e')
                                             (unbindT x y t') p_yg_e'_t' p_yg_wf
lem_typing_hasftype g e t (TApp _g e' x t_x t' p_e'_txt' e_x p_ex_tx) p_g_wf
    = FTApp (erase_env g) e' (erase t_x) (erase t') p_e'_er_txt' e_x p_ex_er_tx
        where
          p_e'_er_txt' = lem_typing_hasftype g e' (TFunc x t_x t') p_e'_txt' p_g_wf 
          p_ex_er_tx   = lem_typing_hasftype g e_x t_x p_ex_tx p_g_wf
lem_typing_hasftype g e t (TSub _g _e s p_e_s _t p_g_t p_s_t) p_g_wf
    = lem_typing_hasftype g e s p_e_s p_g_wf ? lem_erase_subtype g s t p_s_t 

{-@ lem_selfify_wf' :: g:Env -> t:Type -> ProofOf(WFType g t) -> ProofOf(WFEnv g) -> e:Expr
        -> ProofOf(HasType g e t) -> ProofOf(WFType g (self t e)) @-}
lem_selfify_wf' :: Env -> Type -> WFType -> WFEnv -> Expr -> HasType -> WFType
lem_selfify_wf' g t{- @(TRefn b z p)-} p_g_t p_g_wf e p_e_t   -- prefer this one
  = lem_selfify_wf g t p_g_t e p_e_er_t
      where
        p_e_er_t = lem_typing_hasftype g e t p_e_t p_g_wf

-- Lemma. All free variables in a typed expression are bound in the environment
{-@ lem_fv_bound_in_env :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
                -> ProofOf(WFEnv g) -> { x:Vname | not (in_env x g) }
                -> { pf:_ | not (Set_mem x (fv e)) } @-}
lem_fv_bound_in_env :: Env -> Expr -> Type -> HasType -> WFEnv -> Vname -> Proof
lem_fv_bound_in_env g e t (TBC _g b) p_g_wf x          = ()
lem_fv_bound_in_env g e t (TIC _g n) p_g_wf x          = ()
lem_fv_bound_in_env g e t (TVar1 _ y _t _) p_g_wf x  = ()
lem_fv_bound_in_env g e t (TVar2 _ y _t p_y_t z t') p_g_wf x = ()
lem_fv_bound_in_env g e t (TPrm _g c) p_g_wf x         = ()
lem_fv_bound_in_env g e t (TAbs _g y t_y p_g_ty e' t' y' p_e'_t') p_g_wf x 
    = case ( x == y' ) of
        (True)  -> ()
        (False) -> () ? lem_fv_bound_in_env (Cons y' t_y g) (unbind y y' e') (unbindT y y' t') 
                                            p_e'_t' p_y'g_wf x
          where
            p_y'g_wf = WFEBind g p_g_wf y' t_y p_g_ty 
lem_fv_bound_in_env g e t (TApp _g e1 y t_y t' p_e1_tyt' e2 p_e2_ty) p_g_wf x 
    = () ? lem_fv_bound_in_env g e1 (TFunc y t_y t') p_e1_tyt' p_g_wf x
         ? lem_fv_bound_in_env g e2 t_y p_e2_ty p_g_wf x
lem_fv_bound_in_env g e t (TSub _g _e s p_e_s _t p_g_t p_s_t) p_g_wf x
    = () ? lem_fv_bound_in_env g e s p_e_s p_g_wf x

{-@ lem_fv_subset_binds :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
        -> ProofOf(WFEnv g) -> { pf:_ | Set_sub (fv e) (binds g) } @-}
lem_fv_subset_binds :: Env -> Expr -> Type -> HasType -> WFEnv -> Proof
lem_fv_subset_binds g e t (TBC _g b) p_g_wf        = ()
lem_fv_subset_binds g e t (TIC _g n) p_g_wf        = ()
lem_fv_subset_binds g e t (TVar1 _ y _t _) p_g_wf = ()
lem_fv_subset_binds g e t (TVar2 _ y _t p_y_t z t') p_g_wf = ()
lem_fv_subset_binds g e t (TPrm _g c) p_g_wf     = ()
lem_fv_subset_binds g e t (TAbs _g y t_y p_g_ty e' t' y' p_e'_t') p_g_wf 
    = () ? lem_fv_subset_binds (Cons y' t_y g) (unbind y y' e') (unbindT y y' t') p_e'_t' p_y'g_wf
          where
            p_y'g_wf = WFEBind g p_g_wf y' t_y p_g_ty 
lem_fv_subset_binds g e t (TApp _g e1 y t_y t' p_e1_tyt' e2 p_e2_ty) p_g_wf
    = () ? lem_fv_subset_binds g e1 (TFunc y t_y t') p_e1_tyt' p_g_wf
         ? lem_fv_subset_binds g e2 t_y p_e2_ty p_g_wf
lem_fv_subset_binds g e t (TSub _g _e s p_e_s _t p_g_t p_s_t) p_g_wf
    = () ? lem_fv_subset_binds g e s p_e_s p_g_wf


{-@ lem_freeBV_prim_empty :: c:Prim -> { pf:_ | Set_emp (freeBV (Prim c)) && Set_emp (tfreeBV (ty c)) } @-}
lem_freeBV_prim_empty :: Prim -> Proof
lem_freeBV_prim_empty And      = ()
lem_freeBV_prim_empty Or       = ()
lem_freeBV_prim_empty Not      = ()
lem_freeBV_prim_empty Eqv      = ()
lem_freeBV_prim_empty Leq      = ()
lem_freeBV_prim_empty (Leqn n) = ()
lem_freeBV_prim_empty Eq       = ()
lem_freeBV_prim_empty (Eqn n)  = ()

--                              -> { pf:_ | Set_emp (freeBV e) && Set_emp (tfreeBV t) } @-}
-- Lemma. If G |- e : t, then Set_emp (freeBV e)
{-@ lem_freeBV_empty :: g:Env -> e:Expr -> t:Type -> { p_e_t:HasType | propOf p_e_t == HasType g e t } 
      -> ProofOf(WFEnv g) -> { pf:_ | Set_emp (freeBV e) } / [typSize p_e_t] @-}
lem_freeBV_empty :: Env -> Expr -> Type -> HasType -> WFEnv -> Proof
lem_freeBV_empty g e t (TBC _g b) p_g_wf   = case e of
  (Bc _) -> ()
lem_freeBV_empty g e t (TIC _g n) p_g_wf   = case e of
  (Ic _) -> ()
lem_freeBV_empty g e t (TVar1 _ x t' _) p_g_wf = case e of
  (FV _) -> () 
lem_freeBV_empty g e t (TVar2 g' x _ p_x_t y s) p_g_wf
    = case (p_g_wf) of
        (WFEBind _g' p_g'_wf _ _s p_g'_s) -> lem_freeBV_empty g' e t p_x_t p_g'_wf
lem_freeBV_empty g e t (TPrm _g c) p_g_wf  = () ? lem_freeBV_prim_empty c
lem_freeBV_empty g e t (TAbs _g x t_x p_g_tx e' t' y p_yg_e'_t') p_g_wf = case e of
  (Lambda _ _) -> () -- ? lem_tfreeBV_empty g t_x k_x p_g_tx p_g_wf -- restore later?
         ? lem_freeBV_unbind_empty x y (e' ? pf_unbinds_empty)
         -- ? lem_tfreeBV_unbindT_empty x y (t' ? pf_unbinds_empty)
        where
          p_yg_wf = WFEBind g p_g_wf y t_x p_g_tx
          {-@ pf_unbinds_empty :: { pf:_ | Set_emp (freeBV (unbind x y e')) } @-}
          pf_unbinds_empty = lem_freeBV_empty (Cons y t_x g) (unbind x y e') (unbindT x y t') 
                                              p_yg_e'_t' p_yg_wf
lem_freeBV_empty g e t (TApp _g e' x t_x t' p_e'_txt' e_x p_ex_tx) p_g_wf = case e of
  (App _ _) -> () ? lem_freeBV_empty g e' (TFunc x t_x t') p_e'_txt' p_g_wf
                  ? lem_freeBV_empty g e_x t_x p_ex_tx p_g_wf
lem_freeBV_empty g e t (TSub _g _e s p_e_s _t p_g_t p_s_t) p_g_wf
    = () ? lem_freeBV_empty g e s p_e_s p_g_wf
