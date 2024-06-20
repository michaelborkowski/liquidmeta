{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasTyping where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof,(?))
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
import Typing
import LemmasWeakenWF
import LemmasWeakenWFTV
import LemmasWellFormedness
import SubstitutionLemmaWFTV

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
lem_tsubFV_ty x v_x Imp      = ()
lem_tsubFV_ty x v_x Eqv      = ()
lem_tsubFV_ty x v_x Leq      = ()
lem_tsubFV_ty x v_x (Leqn n) = ()
lem_tsubFV_ty x v_x Eq       = ()
lem_tsubFV_ty x v_x (Eqn n)  = ()
lem_tsubFV_ty x v_x Eql      = ()
lem_tsubFV_ty x v_x Leql     = ()

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
lem_tsubFTV_ty a t_a Imp      = ()
lem_tsubFTV_ty a t_a Eqv      = ()
lem_tsubFTV_ty a t_a Leq      = ()
lem_tsubFTV_ty a t_a (Leqn n) = ()
lem_tsubFTV_ty a t_a Eq       = ()
lem_tsubFTV_ty a t_a (Eqn n)  = ()
lem_tsubFTV_ty a t_a Eql      = ()
lem_tsubFTV_ty a t_a Leql     = ()

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
          {-@ mk_p_a'g_t' :: { a':Vname | NotElem a' nms' }
                -> ProofOf(WFType (ConsT a' k g) (unbind_tvT a' t') Star) @-}
          mk_p_a'g_t' a' = lem_typing_wf (ConsT a' k g) (unbind_tv a' e') (unbind_tvT a' t')
                                         (mk_p_a'g_e'_t' a') p_wf_a'g
            where
              p_wf_a'g   = WFEBindT g p_wf_g a' k
          nms'           = unionEnv nms g
lem_typing_wf g e t (TAppT _g e' k s p_e'_as t' p_g_t') p_wf_g 
  = if k_s == Star then p_g_st' else WFKind g (tsubBTV t' s) p_g_st'
      where
        p_g_as    = lem_typing_wf g e' (TPoly k s) p_e'_as p_wf_g
        (WFPoly _ _ _ k_s nms mk_p_a'g_s) = lem_wfpoly_for_wf_tpoly g k s p_g_as
        a'        = fresh_var nms g 
        p_wf_er_g = lem_erase_env_wfenv g p_wf_g
        p_g_st'   = lem_subst_tv_wf g Empty a' t' k p_g_t' p_wf_er_g (unbind_tvT a' s) k_s 
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

{-@ lem_typing_hasftype :: g:Env -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType g e t }
        -> ProofOf(WFEnv g) -> ProofOf(HasFType (erase_env g) e (erase t)) / [sizeOf p_e_t] @-}
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
lem_typing_hasftype g e t (TAbs _g t_x k_x p_g_tx e' t' nms mk_p_yg_e'_t') p_g_wf
    = FTAbs (erase_env g) (erase t_x) k_x p_g_er_tx e' 
            (erase t') nms' mk_p_yg_e'_er_t'
        where
          p_g_er_tx     = lem_erase_wftype g t_x k_x p_g_tx
          {-@ mk_p_yg_e'_er_t' :: { y:Vname | NotElem y nms' }
                -> ProofOf(HasFType (FCons y (erase t_x) (erase_env g)) (unbind y e') (erase t')) @-}
          mk_p_yg_e'_er_t' y = lem_typing_hasftype (Cons y t_x g) (unbind y e')
                                   (unbindT y t') (mk_p_yg_e'_t' y) p_yg_wf
            where
              p_yg_wf       = WFEBind g p_g_wf y t_x k_x p_g_tx
          nms' = unionFEnv nms (erase_env g)
lem_typing_hasftype g e t (TApp _g e' t_x t' p_e'_txt' e_x p_ex_tx) p_g_wf
    = FTApp (erase_env g) e' (erase t_x) (erase t') p_e'_er_txt' e_x p_ex_er_tx
        where
          p_e'_er_txt' = lem_typing_hasftype g e' (TFunc t_x t') p_e'_txt' p_g_wf
          p_ex_er_tx   = lem_typing_hasftype g e_x t_x p_ex_tx p_g_wf

lem_typing_hasftype g e t (TAbsT _g k_a e' t' nms mk_p_e'_t') p_g_wf 
    = FTAbsT (erase_env g) k_a e' (erase t') nms' mk_p_e'_er_t'
        where
          {-@ mk_p_e'_er_t' :: { a:Vname | NotElem a nms' }
                -> ProofOf(HasFType (FConsT a k_a (erase_env g)) (unbind_tv a e') 
                                    (unbindFT a (erase t'))) @-}
          mk_p_e'_er_t' a = lem_typing_hasftype (ConsT a k_a g) (unbind_tv a e') 
                              (unbind_tvT a t') (mk_p_e'_t' a) p_ag_wf 
                              ? lem_erase_unbind_tvT  a  t'
            where
              p_ag_wf   = WFEBindT g p_g_wf a k_a
          nms' = unionFEnv nms (erase_env g)
lem_typing_hasftype g e t (TAppT _g e' k s p_e'_as t' p_g_t') p_g_wf 
    = FTAppT (erase_env g) e' k  (erase s) p_e'_er_as 
             (t' ? lem_free_subset_binds g t' k p_g_t'
                 ? lem_wftype_islct g t' k p_g_t') p_g_er_t'
             ? lem_erase_tsubBTV t' s
       where
         p_e'_er_as = lem_typing_hasftype g e' (TPoly k s) p_e'_as p_g_wf
         p_g_er_t'  = lem_erase_wftype    g t' k p_g_t'
lem_typing_hasftype g e t (TLet _g e_x t_x p_ex_tx e' _t k p_g_t nms mk_p_yg_e'_t) p_g_wf
    = FTLet (erase_env g) e_x (erase t_x) p_ex_er_tx e' (erase t) 
            nms' mk_p_yg_e'_er_t
        where
          p_ex_er_tx   = lem_typing_hasftype g e_x t_x p_ex_tx p_g_wf         
          p_g_tx       = lem_typing_wf g e_x t_x p_ex_tx p_g_wf
          {-@ mk_p_yg_e'_er_t :: { y:Vname | NotElem y nms' }
                -> ProofOf(HasFType (FCons y (erase t_x) (erase_env g)) (unbind y e') (erase t)) @-}
          mk_p_yg_e'_er_t y = lem_typing_hasftype (Cons y t_x g) (unbind y e') 
                                  (unbindT y t) (mk_p_yg_e'_t y) p_yg_wf
            where
              p_yg_wf      = WFEBind g p_g_wf y t_x Star p_g_tx
          nms' = unionFEnv nms (erase_env g)
lem_typing_hasftype g e t (TAnn _g e' _ p_e'_t) p_g_wf
    = FTAnn (erase_env g) e' (erase t) (t ? lem_free_subset_binds g t Star p_t_wf
                                          ? lem_wftype_islct      g t Star p_t_wf)
            (lem_typing_hasftype g e' t p_e'_t p_g_wf)
        where
          p_t_wf = lem_typing_wf g e' t p_e'_t p_g_wf
lem_typing_hasftype g e t (TSub _g _e s p_e_s _t k p_g_t p_s_t) p_g_wf
    = lem_typing_hasftype g e s p_e_s p_g_wf 
          ? lem_erase_subtype g s  t  p_s_t

{-@ lem_fv_subset_binds :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
        -> ProofOf(WFEnv g) -> { pf:_ | Set_sub (fv e) (binds g)  && Set_sub (ftv e) (binds g) &&
                                        Set_sub (fv e) (vbinds g) && Set_sub (ftv e) (tvbinds g) } @-}
lem_fv_subset_binds :: Env -> Expr -> Type -> HasType -> WFEnv -> Proof
lem_fv_subset_binds g e t p_e_t p_g_wf = lem_fv_subset_bindsF (erase_env g) e (erase t) p_e_er_t
  where
    p_e_er_t = lem_typing_hasftype g e t p_e_t p_g_wf

{-@ lem_typ_islc :: g:Env -> e:Expr -> t:Type -> { p_e_t:HasType | propOf p_e_t == HasType g e t } 
      -> ProofOf(WFEnv g) -> { pf:_ | isLC e } @-}
lem_typ_islc :: Env -> Expr -> Type -> HasType -> WFEnv -> Proof
lem_typ_islc g e t p_e_t p_g_wf  = lem_ftyp_islc (erase_env g) e (erase t) p_e_er_t
  where
    p_e_er_t = lem_typing_hasftype g e t p_e_t p_g_wf
