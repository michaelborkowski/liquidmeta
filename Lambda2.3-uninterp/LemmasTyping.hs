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
--import SystemFLemmasFTyping
--import SystemFLemmasSubstitution
import Typing
--import BasicPropsEraseTyping
import LemmasWeakenWF
import LemmasWeakenWFTV
import LemmasWellFormedness
import SubstitutionLemmaWFTV

{-@ reflect foo43 @-}
foo43 x = Just x
foo43 :: a -> Maybe a

{-
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

{-@ lem_tsubFTV_tybc :: a:Vname -> t_a:UserType -> b:Bool
        -> { pf:_ | tsubFTV a t_a (tybc b) == tybc b } @-}
lem_tsubFTV_tybc :: Vname -> Type -> Bool -> Proof
lem_tsubFTV_tybc a t_a True  = ()
lem_tsubFTV_tybc a t_a False = ()

{-@ lem_tsubFTV_tyic :: a:Vname -> t_a:UserType -> n:Int
        -> { pf:_ | tsubFTV a t_a (tyic n) == tyic n } @-}
lem_tsubFTV_tyic :: Vname -> Type -> Int -> Proof
lem_tsubFTV_tyic a t_a n = ()

{-@ lem_tsubFTV_ty :: a:Vname -> t_a:UserType -> c:Prim
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

{-@ lem_tchgFTV_tybc :: a:Vname -> a':Vname -> b:Bool
        -> { pf:_ | tchgFTV a a' (tybc b) == tybc b } @-}
lem_tchgFTV_tybc :: Vname -> Vname -> Bool -> Proof
lem_tchgFTV_tybc a a' True  = ()
lem_tchgFTV_tybc a a' False = ()

{-@ lem_tchgFTV_tyic :: a:Vname -> a':Vname -> n:Int
        -> { pf:_ | tchgFTV a a' (tyic n) == tyic n } @-}
lem_tchgFTV_tyic :: Vname -> Vname -> Int -> Proof
lem_tchgFTV_tyic a a' n = ()

{-@ lem_tchgFTV_ty :: a:Vname -> a':Vname -> c:Prim
        -> { pf:_ | tchgFTV a a' (ty c) == ty c } @-}
lem_tchgFTV_ty :: Vname -> Vname -> Prim -> Proof
lem_tchgFTV_ty a a' And      = ()
lem_tchgFTV_ty a a' Or       = () 
lem_tchgFTV_ty a a' Not      = ()
lem_tchgFTV_ty a a' Eqv      = ()
lem_tchgFTV_ty a a' Leq      = ()
lem_tchgFTV_ty a a' (Leqn n) = ()
lem_tchgFTV_ty a a' Eq       = ()
lem_tchgFTV_ty a a' (Eqn n)  = ()
lem_tchgFTV_ty a a' Eql      = ()
-}

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------

{-@ lem_typing_wf :: g:Env -> e:Expr -> t:Type -> { p_e_t:HasType | propOf p_e_t == HasType g e t }
                      -> ProofOf(WFEnv g) -> ProofOf(WFType g t Star) / [esize e, envsize g] @-} 
lem_typing_wf :: Env -> Expr -> Type -> HasType -> WFEnv -> WFType
lem_typing_wf g e t (TBC _g b) p_wf_g  = WFKind g t (lem_wf_tybc g b)
lem_typing_wf g e t (TIC _g n) p_wf_g  = WFKind g t (lem_wf_tyic g n)
lem_typing_wf g e t (TVar1 _g' x t' k' p_g'_t') p_wf_g -- x:t',g |- (FV x) : t == self(t', x)
    = case p_wf_g of
        (WFEEmpty)                           -> impossible "surely"
        (WFEBind g' p_g' _x _t' _  _p_g'_t') -> case k' of 
          Base  -> WFKind g t p_g_selft'
            where
              p_g'_t'_st = WFKind g' t' p_g'_t'
              p_x_t'     = FTVar1 (erase_env g') x (erase t') --Star p_g'_t'_st
                               ? toProof ( self t' (FV x) Star === t' )
              p_g_t'     = lem_weaken_wf g' Empty t' k' p_g'_t' x t'
              p_g_selft' = lem_selfify_wf g t' k' p_g_t'  (FV x) p_x_t'
          Star  -> p_g_selft'
            where
              p_x_t'     = FTVar1 (erase_env g') x (erase t') --Star p_g'_t'
                               ? toProof ( self t' (FV x) Star === t' )
              p_g_t'     = lem_weaken_wf g' Empty t' k' p_g'_t' x t'
              p_g_selft' = lem_selfify_wf g t' k' p_g_t'  (FV x) p_x_t'
        (WFEBindT g' p_g' a k_a)            -> impossible ""
lem_typing_wf g e t (TVar2 g' x _t p_g'_x_t y s) p_wf_g
    = case p_wf_g of
        (WFEEmpty)                         -> impossible "Surely"
        (WFEBind g' p_g' _y _s k_y p_g'_s) -> lem_weaken_wf g' Empty t Star p_g'_t y s
          where 
            p_g'_t = lem_typing_wf g' e t p_g'_x_t p_g'
        (WFEBindT g' p_g' a k_a)           -> impossible ""
lem_typing_wf g e t (TVar3 g' x _t p_g'_x_t a k_a) p_wf_g 
    = case p_wf_g of
        (WFEEmpty)                         -> impossible "Surely"
        (WFEBind g' p_g' _y _s k_y p_g'_s) -> impossible ""
        (WFEBindT g' p_g' _a _ka)          -> lem_weaken_tv_wf g' Empty  t Star
                                              (lem_typing_wf g' e t p_g'_x_t p_g') a k_a  
lem_typing_wf g e t (TPrm _g c) p_wf_g 
    = lem_weaken_many_wf Empty g (ty c) Star (lem_wf_ty c)  ? lem_empty_concatE g
lem_typing_wf g e t (TAbs _g t_x k_x p_tx_wf e' t' nms mk_p_e'_t') p_wf_g
    = WFFunc g t_x k_x p_tx_wf t' Star nms' mk_yg_t'
        where
          {-@ mk_yg_t' :: { y:Vname | NotElem y nms' }
                -> ProofOf(WFType (Cons y t_x g) (unbindT y t') Star) @-}
          mk_yg_t' y = lem_typing_wf (Cons y t_x g) (unbind y e') (unbindT y t') (mk_p_e'_t' y)
                                     (WFEBind g p_wf_g y t_x k_x p_tx_wf)
          nms' = unionEnv nms g
lem_typing_wf g e t (TApp _g e1 t_x t' p_e1_txt' e2 p_e2_tx) p_wf_g
    = if k' == Base then WFKind g t p_g_ext' else p_g_ext'
        where
          p_g_txt' = lem_typing_wf g e1 (TFunc t_x t') p_e1_txt' p_wf_g
          (WFFunc _ _ k_x p_g_tx _ k' nms mk_p_yg_t') = lem_wffunc_for_wf_tfunc g t_x t' Star p_g_txt'
          p_g_ext' = WFExis g t_x k_x p_g_tx t' k' nms mk_p_yg_t'
lem_typing_wf g e t (TAbsT _g k e' t' nms mk_p_a'g_e'_t') p_wf_g 
    = WFPoly g k t' Star nms' mk_p_a'g_t' 
        where
--          p_wf_er_g = lem_erase_env_wfenv g p_wf_g
          {-@ mk_p_a'g_t' :: { a':Vname | NotElem a' nms' }
                -> ProofOf(WFType (ConsT a' k g) (unbind_tvT a' t') Star) @-}
          mk_p_a'g_t' a' = lem_typing_wf (ConsT a' k g) (unbind_tv a' e') (unbind_tvT a' t')
                                         (mk_p_a'g_e'_t' a') p_wf_a'g
            where
              p_wf_a'g   = WFEBindT g p_wf_g a' k
          nms'           = unionEnv nms g
--  = WFPoly g k t' k_t' a' p_a'g_t'
lem_typing_wf g e t (TAppT _g e' k s p_e'_as t' p_g_t') p_wf_g 
  = if k_s == Star then p_g_st' else WFKind g (tsubBTV t' s) p_g_st'
      where
        p_g_as    = lem_typing_wf g e' (TPoly k s) p_e'_as p_wf_g
        (WFPoly _ _ _ k_s nms mk_p_a'g_s) = lem_wfpoly_for_wf_tpoly g k s p_g_as
        a'        = fresh_var nms g 
        p_wf_er_g = lem_erase_env_wfenv g p_wf_g
        p_wf_a'g  = WFFBindT (erase_env g) p_wf_er_g a' k
        p_g_st'   = lem_subst_tv_wf g Empty a' t' k p_g_t' p_wf_a'g (unbind_tvT a' s) k_s 
                                    (mk_p_a'g_s a') ? lem_tsubFTV_unbind_tvT a' t' 
                                        (s ? lem_free_bound_in_env g (TPoly k s) Star p_g_as a')
lem_typing_wf g e t (TLet _g e_x t_x p_ex_tx e' _t k p_g_t nms mk_p_e'_t) p_wf_g 
    = case k of 
        Base -> WFKind g t p_g_t
        Star -> p_g_t 
lem_typing_wf g e t (TAnn _g e' _t p_e'_t) p_wf_g
    = lem_typing_wf g e' t p_e'_t p_wf_g
lem_typing_wf g e t (TSub _g _e s p_e_s _t k p_g_t p_s_t) p_wf_g 
    = case k of 
        Base -> WFKind g t p_g_t 
        Star -> p_g_t

{-
{-@ lem_selfify_wf' :: g:Env -> t:Type -> k:Kind -> ProofOf(WFType g t k) -> ProofOf(WFEnv g)
        -> e:Term -> ProofOf(HasType g e t) -> ProofOf(WFType g (self t e k) k) @-}
lem_selfify_wf' :: Env -> Type -> Kind -> WFType -> WFEnv -> Expr -> HasType -> WFType
lem_selfify_wf' g t {- @(TRefn b z p)-} k p_g_t p_g_wf e p_e_t 
  = lem_selfify_wf g t k p_g_t p_er_g_wf e p_e_er_t
      where
        p_er_g_wf = lem_erase_env_wfenv g p_g_wf
        p_e_er_t  = lem_typing_hasftype g e t p_e_t p_g_wf

{-@ lem_typing_hasftype :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
        -> ProofOf(WFEnv g) -> ProofOf(HasFType (erase_env g) e (erase t)) @-}
lem_typing_hasftype :: Env -> Expr -> Type -> HasType -> WFEnv -> HasFType
lem_typing_hasftype g e t (TBC _g b) p_g_wf      = FTBC (erase_env g) b
lem_typing_hasftype g e t (TIC _g n) p_g_wf      = FTIC (erase_env g) n
lem_typing_hasftype g e t (TVar1 g' x t' k' _) p_g_wf  
  = FTVar1 (erase_env g') x (erase t') 
      ? toProof ( erase ( self t' (FV x) k' ) === erase t' )
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
lem_typing_hasftype g e t (TPrm _g c) p_g_wf     = FTPrm (erase_env g) c
    ? toProof ( erase (ty c) === erase_ty c )
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
lem_typing_hasftype g e t (TAbsT _g a k_a e' t' k' a' p_e'_t' p_a'g_t') p_g_wf 
    = FTAbsT (erase_env g) a k_a e' (erase t') (a' ? lem_erase_freeTV t') p_e'_er_t'
        where
          p_a'g_wf   = WFEBindT g p_g_wf a' k_a
          p_e'_er_t' = lem_typing_hasftype (ConsT a' k_a g) (unbind_tv a a' e') 
                           (unbind_tvT a a' t') p_e'_t' p_a'g_wf 
                           ? lem_erase_unbind_tvT  a a' t'
lem_typing_hasftype g e t (TAppT _g e' a k s p_e'_as t' p_g_t') p_g_wf 
    = FTAppT (erase_env g) e' a k  (erase s) p_e'_er_as 
             (t' ? lem_free_subset_binds g t' k p_g_t'
                 ? lem_tfreeBV_empty g t' k p_g_t') p_g_er_t'
             ? lem_erase_tsubBTV a t' s
       where
         p_e'_er_as = lem_typing_hasftype g e' (TPoly a k s) p_e'_as p_g_wf
         p_g_er_t'  = lem_erase_wftype    g t' k p_g_t'
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
    = FTAnn (erase_env g) e' (erase t) (t ? lem_free_subset_binds g t Star p_t_wf
                                          ? lem_tfreeBV_empty g t Star p_t_wf)
            (lem_typing_hasftype g e' t p_e'_t p_g_wf)
        where
          p_t_wf = lem_typing_wf g e' t p_e'_t p_g_wf
lem_typing_hasftype g e t (TSub _g _e s p_e_s _t k p_g_t p_s_t) p_g_wf
    = lem_typing_hasftype g e s p_e_s p_g_wf ? lem_erase_subtype g s t p_s_t 

{-@ lem_csubst_hasftype :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t) 
        -> ProofOf(WFEnv g) -> th:CSub -> ProofOf(DenotesEnv g th) 
        -> ProofOf(HasFType FEmpty (csubst th e) (erase (ctsubst th t))) @-}
lem_csubst_hasftype :: Env -> Expr -> Type -> HasType -> WFEnv -> CSub -> DenotesEnv -> HasFType
lem_csubst_hasftype g e t p_e_t p_g_wf th den_g_th
  = lem_csubst_hasftype' g e t p_e_er_t p_er_g_wf th den_g_th
      where
        p_e_er_t  = lem_typing_hasftype g e t p_e_t p_g_wf
        p_er_g_wf = lem_erase_env_wfenv g p_g_wf

-- Lemma. All free variables in a typed expression are bound in the environment
{-@ lem_fv_bound_in_env :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
                -> ProofOf(WFEnv g) -> { x:Vname | not (in_env x g) }
                -> { pf:_ | not (Set_mem x (fv e)) && not (Set_mem x (ftv e)) } @-}
lem_fv_bound_in_env :: Env -> Expr -> Type -> HasType -> WFEnv -> Vname -> Proof
lem_fv_bound_in_env g e t (TBC _g b) p_g_wf x          = ()
lem_fv_bound_in_env g e t (TIC _g n) p_g_wf x          = ()
lem_fv_bound_in_env g e t (TVar1 _ y _t _ _) p_g_wf x  = ()
lem_fv_bound_in_env g e t (TVar2 _ y _t p_y_t z t') p_g_wf x = ()
lem_fv_bound_in_env g e t (TVar3 _ y _y p_y_t z k)  p_g_wf x = ()
lem_fv_bound_in_env g e t (TPrm _g c) p_g_wf x         = ()
lem_fv_bound_in_env g e t (TAbs _g y t_y k_y p_g_ty e' t' y' p_e'_t') p_g_wf x 
    = case ( x == y' ) of
        (True)  -> ()
        (False) -> () ? lem_fv_bound_in_env (Cons y' t_y g) (unbind y y' e') (unbindT y y' t') 
                                            p_e'_t' p_y'g_wf x
          where
            p_y'g_wf = WFEBind g p_g_wf y' t_y k_y p_g_ty 
lem_fv_bound_in_env g e t (TApp _g e1 y t_y t' p_e1_tyt' e2 p_e2_ty) p_g_wf x 
    = () ? lem_fv_bound_in_env g e1 (TFunc y t_y t') p_e1_tyt' p_g_wf x
         ? lem_fv_bound_in_env g e2 t_y p_e2_ty p_g_wf x
lem_fv_bound_in_env g e t (TAbsT _g a k e' t' k_t' a' p_e'_t' _) p_g_wf x
    = case ( x == a' ) of
        True  -> ()
        False -> () ? lem_fv_bound_in_env (ConsT a' k g) (unbind_tv a a' e') 
                                           (unbind_tvT a a' t') p_e'_t' p_a'g_wf x
          where
            p_a'g_wf = WFEBindT g p_g_wf a' k
lem_fv_bound_in_env g e t (TAppT _g e' a k s p_e'_as t' p_g_t') p_g_wf x
    = () ? lem_fv_bound_in_env   g e' (TPoly a k s) p_e'_as p_g_wf x
         ? lem_free_bound_in_env g t' k p_g_t' x
lem_fv_bound_in_env g e t (TLet _g e_y t_y p_ey_ty y e' t' k' p_g_t' y' p_e'_t') p_g_wf x 
    = case ( x == y' ) of
        (True)  -> () ? lem_fv_bound_in_env g e_y t_y p_ey_ty p_g_wf x
        (False) -> () ? lem_fv_bound_in_env g e_y t_y p_ey_ty p_g_wf x
                      ? lem_fv_bound_in_env (Cons y' t_y g) (unbind y y' e') (unbindT y y' t') 
                                            p_e'_t' p_y'g_wf x
          where
            p_g_ty   = lem_typing_wf g e_y t_y p_ey_ty p_g_wf
            p_y'g_wf = WFEBind g p_g_wf y' t_y Star p_g_ty
lem_fv_bound_in_env g e t (TAnn _g e' _t p_e'_t) p_g_wf x 
    = () ? lem_fv_bound_in_env g e' t p_e'_t p_g_wf x
         ? lem_free_bound_in_env g t Star p_g_t x
       where
         p_g_t = lem_typing_wf g e' t p_e'_t p_g_wf 
lem_fv_bound_in_env g e t (TSub _g _e s p_e_s _t k p_g_t p_s_t) p_g_wf x
    = () ? lem_fv_bound_in_env g e s p_e_s p_g_wf x

{-@ lem_fv_subset_binds :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
        -> ProofOf(WFEnv g) -> { pf:_ | Set_sub (Set_cup (fv e) (ftv e)) (binds g) &&
                                        Set_sub (fv e) (vbinds g) && Set_sub (ftv e) (tvbinds g) } @-}
lem_fv_subset_binds :: Env -> Expr -> Type -> HasType -> WFEnv -> Proof
lem_fv_subset_binds g e t (TBC _g b) p_g_wf        = ()
lem_fv_subset_binds g e t (TIC _g n) p_g_wf        = ()
lem_fv_subset_binds g e t (TVar1 _ y _t _ _) p_g_wf = ()
lem_fv_subset_binds g e t (TVar2 g' y _t p_y_t z t') p_g_wf 
  = () ? lem_fv_subset_binds g' e t p_y_t p_g'_wf
      where
        (WFEBind _ p_g'_wf _ _ _ _) = p_g_wf
lem_fv_subset_binds g e t (TVar3 g' y _t p_y_t a k)  p_g_wf 
  = () ? lem_fv_subset_binds g' e t p_y_t p_g'_wf
      where
        (WFEBindT _ p_g'_wf _ _) = p_g_wf
lem_fv_subset_binds g e t (TPrm _g c) p_g_wf     = ()
lem_fv_subset_binds g e t (TAbs _g y t_y k_y p_g_ty e' t' y' p_e'_t') p_g_wf 
    = () ? lem_fv_subset_binds (Cons y' t_y g) (unbind y y' e') (unbindT y y' t') p_e'_t' p_y'g_wf
          where
            p_y'g_wf = WFEBind g p_g_wf y' t_y k_y p_g_ty 
lem_fv_subset_binds g e t (TApp _g e1 y t_y t' p_e1_tyt' e2 p_e2_ty) p_g_wf
    = () ? lem_fv_subset_binds g e1 (TFunc y t_y t') p_e1_tyt' p_g_wf
         ? lem_fv_subset_binds g e2 t_y p_e2_ty p_g_wf
lem_fv_subset_binds g e t (TAbsT _g a k e' t' k_t' a' p_e'_t' _) p_g_wf 
    = () ? lem_fv_subset_binds (ConsT a' k g) (unbind_tv a a' e') (unbind_tvT a a' t') 
                               p_e'_t' p_a'g_wf
          where
            p_a'g_wf   = WFEBindT g p_g_wf a' k
lem_fv_subset_binds g e t (TAppT _g e' a k t1 p_e1_at1 t2 p_g_t2) p_g_wf
    = () ? lem_fv_subset_binds g e' (TPoly a k t1)  p_e1_at1 p_g_wf
         ? lem_free_subset_binds g t2 k p_g_t2
lem_fv_subset_binds g e t (TLet _g e_y t_y p_ey_ty y e' t' k' p_g_t' y' p_e'_t') p_g_wf
    = () ? lem_fv_subset_binds g e_y t_y p_ey_ty p_g_wf
         ? lem_fv_subset_binds (Cons y' t_y g) (unbind y y' e') (unbindT y y' t') p_e'_t' p_y'g_wf
          where
            p_g_ty   = lem_typing_wf g e_y t_y p_ey_ty p_g_wf
            p_y'g_wf = WFEBind g p_g_wf y' t_y Star p_g_ty
lem_fv_subset_binds g e t (TAnn _g e' _t p_e'_t) p_g_wf
    = () ? lem_fv_subset_binds g e' t p_e'_t p_g_wf
         ? lem_free_subset_binds g t Star p_g_t
       where
         p_g_t = lem_typing_wf g e' t p_e'_t p_g_wf
lem_fv_subset_binds g e t (TSub _g _e s p_e_s _t k p_g_t p_s_t) p_g_wf
    = () ? lem_fv_subset_binds g e s p_e_s p_g_wf


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

--                              -> { pf:_ | Set_emp (freeBV e) && Set_emp (tfreeBV t) } @- }
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
        where
          p_yg_wf = WFEBind g p_g_wf y t_x k_x p_g_tx
          {-@ pf_unbinds_empty :: { pf:_ | Set_emp (freeBV (unbind x y e')) 
                                        && Set_emp (freeBTV (unbind x y e')) } @-}
          pf_unbinds_empty = lem_freeBV_empty (Cons y t_x g) (unbind x y e') (unbindT x y t') 
                                              p_yg_e'_t' p_yg_wf
lem_freeBV_empty g e t (TApp _g e' x t_x t' p_e'_txt' e_x p_ex_tx) p_g_wf = case e of
  (App _ _) -> () ? lem_freeBV_empty g e' (TFunc x t_x t') p_e'_txt' p_g_wf
                  ? lem_freeBV_empty g e_x t_x p_ex_tx p_g_wf
lem_freeBV_empty g e t (TAbsT _g a k e' t' k_t' a' p_a'g_e'_t' p_a'g_t') p_g_wf = case e of
  (LambdaT _ _ _) -> () ? lem_freeBTV_unbind_tv_empty a a' (e' ? pf_unbinds_empty)
    where 
      p_a'g_wf         = WFEBindT g p_g_wf a' k
      {-@ pf_unbinds_empty :: { pf:_ | Set_emp (freeBV (unbind_tv a a' e'))
                                    && Set_emp (freeBTV (unbind_tv a a' e')) } @-}
      pf_unbinds_empty = lem_freeBV_empty (ConsT a' k g) (unbind_tv a a' e') (unbind_tvT a a' t')
                                         p_a'g_e'_t' p_a'g_wf
lem_freeBV_empty g e t (TAppT _g e' a k s p_e'_as t' p_g_t') p_g_wf = case e of
  (AppT _ _) -> () ? lem_freeBV_empty g e' (TPoly a k s) p_e'_as p_g_wf
                   ? lem_tfreeBV_empty g t' k p_g_t'
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
                    ? lem_tfreeBV_empty g t Star p_g_t 
      where
        p_g_t = lem_typing_wf g e' t p_e'_t p_g_wf 
lem_freeBV_empty g e t (TSub _g _e s p_e_s _t k p_g_t p_s_t) p_g_wf
    = () ? lem_freeBV_empty g e s p_e_s p_g_wf
-}
