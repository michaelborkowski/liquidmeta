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
import SystemFWellFormedness
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

{-@ reflect foo35 @-}
foo35 x = Just x
foo35 :: a -> Maybe a

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
lem_tsubFV_ty x v_x Eql      = ()

{-@ lem_tsubFTV_tybc :: a:Vname -> t_a:Type -> b:Bool
        -> { pf:_ | tsubFTV a t_a (tybc b) == tybc b } @-}
lem_tsubFTV_tybc :: Vname -> Type -> Bool -> Proof
lem_tsubFTV_tybc a t_a True  = ()
lem_tsubFTV_tybc a t_a False = ()

{-@ lem_tsubFTV_tyic :: a:Vname -> t_a:Type -> n:Int
        -> { pf:_ | tsubFTV a t_a (tyic n) == tyic n } @-}
lem_tsubFTV_tyic :: Vname -> Type -> Int -> Proof
lem_tsubFTV_tyic a t_a n = ()

{-@ lem_tsubFTV_ty :: a:Vname -> t_a:Type -> c:Prim
        -> { pf:_ | tsubFTV a t_a (ty c) == ty c } @-}
lem_tsubFTV_ty :: Vname -> Type -> Prim -> Proof
lem_tsubFTV_ty a t_a And      = ()
lem_tsubFTV_ty a t_a Or       = () 
lem_tsubFTV_ty a t_a Not      = ()
lem_tsubFTV_ty a t_a Eqv      = ()
lem_tsubFTV_ty a t_a Leq      = ()
lem_tsubFTV_ty a t_a (Leqn n) = ()
lem_tsubFTV_ty a t_a Eq       = ()
lem_tsubFTV_ty a t_a (Eqn n)  = ()
lem_tsubFTV_ty a t_a Eql      = ()

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------

{-@ lem_typing_wf :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
                      -> ProofOf(WFEnv g) -> ProofOf(WFType g t Star) @-} 
lem_typing_wf :: Env -> Expr -> Type -> HasType -> WFEnv -> WFType
lem_typing_wf g e t (TBC _g b) p_wf_g  = WFKind g t (lem_wf_tybc g b)
lem_typing_wf g e t (TIC _g n) p_wf_g  = WFKind g t (lem_wf_tyic g n)
lem_typing_wf g e t (TVar1 _g' x t' k' _) p_wf_g -- x:t',g |- (FV x) : t == self(t', x)
    = case p_wf_g of
        (WFEEmpty)                          -> impossible "surely"
        (WFEBind g' p_g' _x _t' _  p_g'_t') -> undefined {-case k' of 
          Base  -> WFKind g t (lem_selfify_wf g' t' k' p_g'_t' x)
          Star  -> lem_selfify_wf g' t' k' p_g'_t' x -} -- FIXME
                                            -- lem_weaken_wf g' Empty t p_g'_t' x t -- p_g'_t
        (WFEBindT g' p_g' a k_a)            -> impossible ""
lem_typing_wf g e t (TVar2 g' x _t p_g'_x_t y s) p_wf_g
    = case p_wf_g of
        (WFEEmpty)                         -> impossible "Surely"
        (WFEBind g' p_g' _y _s k_y p_g'_s) -> undefined {-lem_weaken_wf g' Empty p_wf_g t Star
                                              (lem_typing_wf g' e t p_g'_x_t p_g')
                                              y s -- p_g'_s-}
        (WFEBindT g' p_g' a k_a)           -> impossible ""
lem_typing_wf g e t (TVar3 g' x _t p_g'_x_t a k_a) p_wf_g 
    = case p_wf_g of
        (WFEEmpty)                         -> impossible "Surely"
        (WFEBind g' p_g' _y _s k_y p_g'_s) -> impossible ""
        (WFEBindT g' p_g' _a _ka)          -> undefined {-lem_weaken_tv_wf g' Empty p_wf_g t Star
                                              (lem_typing_wf g' e t p_g'_x_t p_g')
                                              a k_a -- p_g'_s-}
lem_typing_wf g e t (TPrm _g c) p_wf_g 
    = lem_weaken_many_wf Empty g (p_wf_g ? lem_empty_concatE g) (ty c) Star (lem_wf_ty c) 
lem_typing_wf g e t (TAbs _g x t_x k_x p_tx_wf e' t' y p_e'_t') p_wf_g
    = WFFunc g x t_x k_x p_tx_wf t' Star y (lem_typing_wf (Cons y t_x g) (unbind x y e') 
                                               (unbindT x y t') p_e'_t'
                                               (WFEBind g p_wf_g y t_x k_x p_tx_wf))

lem_typing_wf g e t (TApp _g e1 x t_x t' p_e1_txt' e2 p_e2_tx) p_wf_g
    = case (lem_typing_wf g e1 (TFunc x t_x t') p_e1_txt' p_wf_g) of
        (WFFunc _ _ _ k_x p_g_tx _ k' y p_gx_t') -> case k' of 
          Base  -> WFKind g t (WFExis g x t_x Star (lem_typing_wf g e2 t_x p_e2_tx p_wf_g)
                                      t' k' y p_gx_t')
          Star  -> WFExis g x t_x Star (lem_typing_wf g e2 t_x p_e2_tx p_wf_g)
                                                      t' k' y p_gx_t'
        (_)                                      -> undefined {- -}
lem_typing_wf g e t (TAbsT {}) p_wf_g = undefined
lem_typing_wf g e t (TAppT {}) p_wf_g = undefined
lem_typing_wf g e t (TLet _g e_x t_x p_ex_tx x e' _t k p_g_t y p_e'_t) p_wf_g 
    = case k of 
        Base -> WFKind g t p_g_t
        Star -> p_g_t 
lem_typing_wf g e t (TAnn _g e' _t p_e'_t) p_wf_g
    = lem_typing_wf g e' t p_e'_t p_wf_g
lem_typing_wf g e t (TSub _g _e s p_e_s _t k p_g_t p_s_t) p_wf_g 
    = case k of 
        Base -> WFKind g t p_g_t 
        Star -> p_g_t

{-@ lem_typing_hasftype :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
        -> ProofOf(WFEnv g) -> ProofOf(HasFType (erase_env g) e (erase t)) @-}
lem_typing_hasftype :: Env -> Expr -> Type -> HasType -> WFEnv -> HasFType
lem_typing_hasftype g e t (TBC _g b) p_g_wf      = FTBC (erase_env g) b
lem_typing_hasftype g e t (TIC _g n) p_g_wf      = FTIC (erase_env g) n
lem_typing_hasftype g e t (TVar1 g' x t' _ _) p_g_wf = undefined 
-- FTVar1 (erase_env g') x (erase t') -- need erase self lemma
{-    ? toProof ( erase_env (Cons x t' g') === FCons x (erase t') (erase_env g')
            === FCons x (erase t) (erase_env g') )-}
lem_typing_hasftype g e t (TVar2 g' x _ p_x_t y s) p_g_wf
    = FTVar2 (erase_env g') x (erase t) p_x_er_t y (erase s) 
        where
          (WFEBind _ p_g'_wf _ _ _ _) = p_g_wf
          p_x_er_t = lem_typing_hasftype g' e t p_x_t p_g'_wf
lem_typing_hasftype g e t (TVar3 g' x _ p_x_t a k_a) p_g_wf
    = FTVar3 (erase_env g') x (erase t) p_x_er_t a k_a
        where
          (WFEBindT _ p_g'_wf _ _) = p_g_wf
          p_x_er_t = lem_typing_hasftype g' e t p_x_t p_g'_wf
lem_typing_hasftype g e t (TPrm _g c) p_g_wf     = undefined
--    = FTPrm (erase_env g) c
lem_typing_hasftype g e t (TAbs _g x t_x k_x p_g_tx e' t' y p_yg_e'_t') p_g_wf
    = FTAbs (erase_env g) x (erase t_x) k_x p_g_er_tx e' 
            (erase t' ? lem_erase_tsubBV x (FV y) t') y p_yg_e'_er_t'
        where
          p_g_er_tx     = lem_erase_wftype g t_x k_x p_g_tx
          p_yg_wf       = WFEBind g p_g_wf y t_x k_x p_g_tx
          p_yg_e'_er_t' = lem_typing_hasftype (Cons y t_x g) (unbind x y e')
                                             (unbindT x y t') p_yg_e'_t' p_yg_wf
lem_typing_hasftype g e t (TApp _g e' x t_x t' p_e'_txt' e_x p_ex_tx) p_g_wf
    = FTApp (erase_env g) e' (erase t_x) (erase t') p_e'_er_txt' e_x p_ex_er_tx
        where
          p_e'_er_txt' = lem_typing_hasftype g e' (TFunc x t_x t') p_e'_txt' p_g_wf
          p_ex_er_tx   = lem_typing_hasftype g e_x t_x p_ex_tx p_g_wf
lem_typing_hasftype g e t (TAbsT _g a k_a e' t' k' a' p_e'_t' p_a'g_t') p_g_wf = undefined
{-    = FTAbsT (erase_env g) a k_a e' (erase t') a' p_e'_er_t'
        where
          p_a'g_wf   = WFEBindT g p_g_wf a' k_a
          p_e'_er_t' = lem_typing_hasftype (ConsT a' k_a g) (unbind_tv a a' e') 
                           (unbind_tvT a a' t') p_e'_t' p_a'g_wf -}
lem_typing_hasftype g e t (TAppT {}) p_g_wf = undefined
lem_typing_hasftype g e t (TLet _g e_x t_x p_ex_tx x e' _t k p_g_t y p_yg_e'_t) p_g_wf
    = FTLet (erase_env g) e_x (erase t_x) p_ex_er_tx x e' (erase t ? lem_erase_tsubBV x (FV y) t) 
            y p_yg_e'_er_t
        where
          p_g_tx       = lem_typing_wf g e_x t_x p_ex_tx p_g_wf
          p_yg_wf      = WFEBind g p_g_wf y t_x Star p_g_tx
          p_yg_e'_er_t = lem_typing_hasftype (Cons y t_x g) (unbind x y e') 
                              (unbindT x y t)  p_yg_e'_t p_yg_wf
          p_ex_er_tx   = lem_typing_hasftype g e_x t_x p_ex_tx p_g_wf         
lem_typing_hasftype g e t (TAnn _g e' _ p_e'_t) p_g_wf
    = FTAnn (erase_env g) e' (erase t) (t ? lem_free_subset_binds g t Star p_t_wf)
--                                          ? lem_tfreeBV_empty g t p_t_wf p_g_wf)
            (lem_typing_hasftype g e' t p_e'_t p_g_wf)
        where
          p_t_wf = lem_typing_wf g e' t p_e'_t p_g_wf
lem_typing_hasftype g e t (TSub _g _e s p_e_s _t k p_g_t p_s_t) p_g_wf
    = undefined -- need lemma re: normalization
--    = lem_typing_hasftype g e s p_e_s p_g_wf ? lem_erase_subtype g s t p_s_t -- p_g_wf


-- Lemma. All free variables in a typed expression are bound in the environment
{-@ lem_fv_bound_in_env :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
                -> { x:Vname | not (in_env x g) }
                -> { pf:_ | not (Set_mem x (fv e)) && not (Set_mem x (ftv e)) } @-}
lem_fv_bound_in_env :: Env -> Expr -> Type -> HasType -> Vname -> Proof
lem_fv_bound_in_env g e t (TBC _g b) x          = ()
lem_fv_bound_in_env g e t (TIC _g n) x          = ()
lem_fv_bound_in_env g e t (TVar1 _ y _t _ _) x  = ()
lem_fv_bound_in_env g e t (TVar2 _ y _t p_y_t z t') x = ()
lem_fv_bound_in_env g e t (TVar3 _ y _y p_y_t z k)  x = ()
lem_fv_bound_in_env g e t (TPrm _g c) x         = ()
lem_fv_bound_in_env g e t (TAbs _g y t_y _ _ e' t' y' p_e'_t') x 
    = case ( x == y' ) of
        (True)  -> ()
        (False) -> () ? lem_fv_bound_in_env (Cons y' t_y g) (unbind y y' e') (unbindT y y' t') 
                                            p_e'_t' x
lem_fv_bound_in_env g e t (TApp _g e1 y t_y t' p_e1_tyt' e2 p_e2_ty) x 
    = () ? lem_fv_bound_in_env g e1 (TFunc y t_y t') p_e1_tyt' x
         ? lem_fv_bound_in_env g e2 t_y p_e2_ty x
lem_fv_bound_in_env g e t (TAbsT _g a k e' t' k_t' a' p_e'_t' _) x
    = case ( x == a' ) of
        True  -> ()
        False -> () ? lem_fv_bound_in_env (ConsT a' k g) (unbind_tv a a' e') 
                                           (unbind_tvT a a' t') p_e'_t' x
lem_fv_bound_in_env g e t (TAppT _g e' a k s p_e'_as t' p_g_t') x
    = () ? lem_fv_bound_in_env   g e' (TPoly a k s) p_e'_as x
         ? lem_free_bound_in_env g t' k p_g_t' x
lem_fv_bound_in_env g e t (TLet _g e_y t_y p_ey_ty y e' t' k' p_g_t' y' p_e'_t') x 
    = case ( x == y' ) of
        (True)  -> () ? lem_fv_bound_in_env g e_y t_y p_ey_ty x
        (False) -> () ? lem_fv_bound_in_env g e_y t_y p_ey_ty x
                      ? lem_fv_bound_in_env (Cons y' t_y g) (unbind y y' e') (unbindT y y' t') 
                                            p_e'_t' x
lem_fv_bound_in_env g e t (TAnn _g e' _t p_e'_t) x = undefined
{-    = () ? lem_fv_bound_in_env g e' t p_e'_t x
         ? lem_free_bound_in_env g t Star p_g_t x
       where
         p_g_t = lem_typing_wf g e' t p_e'_t-}
lem_fv_bound_in_env g e t (TSub _g _e s p_e_s _t k p_g_t p_s_t) x
    = () ? lem_fv_bound_in_env g e s p_e_s x

{-@ lem_fv_subset_binds :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
                -> { pf:_ | Set_sub (Set_cup (fv e) (ftv e)) (binds g) } @-}
lem_fv_subset_binds :: Env -> Expr -> Type -> HasType -> Proof
lem_fv_subset_binds g e t (TBC _g b)         = ()
lem_fv_subset_binds g e t (TIC _g n)         = ()
lem_fv_subset_binds g e t (TVar1 _ y _t _ _) = ()
lem_fv_subset_binds g e t (TVar2 _ y _t p_y_t z t') = ()
lem_fv_subset_binds g e t (TVar3 _ y _t p_y_t a k)  = ()
lem_fv_subset_binds g e t (TPrm _g c)      = ()
lem_fv_subset_binds g e t (TAbs _g y t_y _ _ e' t' y' p_e'_t')  
    = () ? lem_fv_subset_binds (Cons y' t_y g) (unbind y y' e') (unbindT y y' t') p_e'_t' 
lem_fv_subset_binds g e t (TApp _g e1 y t_y t' p_e1_tyt' e2 p_e2_ty) 
    = () ? lem_fv_subset_binds g e1 (TFunc y t_y t') p_e1_tyt' 
         ? lem_fv_subset_binds g e2 t_y p_e2_ty 
lem_fv_subset_binds g e t (TAbsT _g a k e' t' k_t' a' p_e'_t' _)  
    = () ? lem_fv_subset_binds (ConsT a' k g) (unbind_tv a a' e') (unbind_tvT a a' t') p_e'_t' 
lem_fv_subset_binds g e t (TAppT _g e' a k t1 p_e1_at1 t2 p_g_t2) 
    = () ? lem_fv_subset_binds g e' (TPoly a k t1)  p_e1_at1
         ? lem_free_subset_binds g t2 k p_g_t2
lem_fv_subset_binds g e t (TLet _g e_y t_y p_ey_ty y e' t' k' p_g_t' y' p_e'_t')  
    = () ? lem_fv_subset_binds g e_y t_y p_ey_ty 
         ? lem_fv_subset_binds (Cons y' t_y g) (unbind y y' e') (unbindT y y' t') p_e'_t' 
lem_fv_subset_binds g e t (TAnn _g e' _t p_e'_t) = undefined
{-    = () ? lem_fv_subset_binds g e' t p_e'_t 
         ? lem_free_subset_binds g t Star p_g_t
       where
         p_g_t = lem_typing_wf g e' t p_e'_t-}
lem_fv_subset_binds g e t (TSub _g _e s p_e_s _t k p_g_t p_s_t)
    = () ? lem_fv_subset_binds g e s p_e_s 


{-@ lem_freeBV_prim_empty :: c:Prim -> { pf:_ | Set_emp (freeBV (Prim c)) && Set_emp (freeBTV (Prim c))
                                            && Set_emp (tfreeBV (ty c)) && Set_emp (tfreeBTV (ty c)) } @-}
lem_freeBV_prim_empty :: Prim -> Proof
lem_freeBV_prim_empty And      = ()
lem_freeBV_prim_empty Or       = ()
lem_freeBV_prim_empty Not      = ()
lem_freeBV_prim_empty Eqv      = ()
lem_freeBV_prim_empty Leq      = ()
lem_freeBV_prim_empty (Leqn n) = ()
lem_freeBV_prim_empty Eq       = ()
lem_freeBV_prim_empty (Eqn n)  = ()
lem_freeBV_prim_empty Eql      = ()

--                              -> { pf:_ | Set_emp (freeBV e) && Set_emp (tfreeBV t) } @-}
-- Lemma. If G |- e : t, then Set_emp (freeBV e)
{-@ lem_freeBV_empty :: g:Env -> e:Expr -> t:Type -> { p_e_t:HasType | propOf p_e_t == HasType g e t } 
      -> ProofOf(WFEnv g) -> { pf:_ | Set_emp (freeBV e) && Set_emp (freeBTV e) } / [typSize p_e_t] @-}
lem_freeBV_empty :: Env -> Expr -> Type -> HasType -> WFEnv -> Proof
lem_freeBV_empty g e t (TBC _g b) p_g_wf   = case e of
  (Bc _) -> ()
lem_freeBV_empty g e t (TIC _g n) p_g_wf   = case e of
  (Ic _) -> ()
lem_freeBV_empty g e t (TVar1 _ x t' _ _) p_g_wf = case e of
  (FV _) -> () 
lem_freeBV_empty g e t (TVar2 g' x _ p_x_t y s) p_g_wf
    = case (p_g_wf) of
        (WFEBind _g' p_g'_wf _ _s _ p_g'_s) -> lem_freeBV_empty g' e t p_x_t p_g'_wf
lem_freeBV_empty g e t (TVar3 g' x _ p_x_t a k) p_g_wf
    = case (p_g_wf) of
        (WFEBindT _g' p_g'_wf _a _k)        -> lem_freeBV_empty g' e t p_x_t p_g'_wf
lem_freeBV_empty g e t (TPrm _g c) p_g_wf  = () ? lem_freeBV_prim_empty c
lem_freeBV_empty g e t (TAbs _g x t_x k_x 	p_g_tx e' t' y p_yg_e'_t') p_g_wf = case e of
  (Lambda _ _) -> () -- ? lem_tfreeBV_empty g t_x k_x p_g_tx p_g_wf -- restore later?
         ? lem_freeBV_unbind_empty x y (e' ? pf_unbinds_empty)
         -- ? lem_tfreeBV_unbindT_empty x y (t' ? pf_unbinds_empty)
        where
          p_yg_wf = WFEBind g p_g_wf y t_x k_x p_g_tx
          {-@ pf_unbinds_empty :: { pf:_ | Set_emp (freeBV (unbind x y e')) 
                                        && Set_emp (freeBTV (unbind x y e')) } @-}
          pf_unbinds_empty = lem_freeBV_empty (Cons y t_x g) (unbind x y e') (unbindT x y t') 
                                              p_yg_e'_t' p_yg_wf
lem_freeBV_empty g e t (TApp _g e' x t_x t' p_e'_txt' e_x p_ex_tx) p_g_wf = case e of
  (App _ _) -> () ? lem_freeBV_empty g e' (TFunc x t_x t') p_e'_txt' p_g_wf
                  ? lem_freeBV_empty g e_x t_x p_ex_tx p_g_wf
lem_freeBV_empty g e t (TAbsT {}) p_g_wf = undefined
lem_freeBV_empty g e t (TAppT {}) p_g_wf = undefined
lem_freeBV_empty g e t (TLet _g e_x t_x p_ex_tx x e' _t k p_g_t y p_yg_e'_t) p_g_wf = case e of
  (Let _ _ _) -> () 
        ? lem_freeBV_empty g e_x t_x p_ex_tx p_g_wf
        ? lem_freeBV_unbind_empty x y  (e' ? lem_freeBV_empty (Cons y t_x g) (unbind x y e')
                                                              (unbindT x y t) p_yg_e'_t p_yg_wf)
      where
        p_g_tx = lem_typing_wf g e_x t_x p_ex_tx p_g_wf
        p_yg_wf = WFEBind g p_g_wf y t_x Star p_g_tx
lem_freeBV_empty g e t (TAnn _g e' _ p_e'_t) p_g_wf = case e of
  (Annot _ _) -> () ? lem_freeBV_empty  g e' t p_e'_t p_g_wf
                    ? lem_tfreeBV_empty g t Star p_g_t p_g_wf
      where
        p_g_t = lem_typing_wf g e' t p_e'_t p_g_wf 
lem_freeBV_empty g e t (TSub _g _e s p_e_s _t k p_g_t p_s_t) p_g_wf
    = () ? lem_freeBV_empty g e s p_e_s p_g_wf
