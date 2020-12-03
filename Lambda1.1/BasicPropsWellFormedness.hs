{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module BasicPropsWellFormedness where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import SystemFTyping
import WellFormedness
import BasicPropsSubstitution
import BasicPropsEnvironments

{-@ reflect foo21 @-}
foo21 :: a -> Maybe a
foo21 x = Just x

-------------------------------------------------------------------------------------------
-- | TECHNICAL LEMMAS relating to the abscence of dangling BOUND VARIABLES without a binder
-------------------------------------------------------------------------------------------

{-@ lem_freeBV_unbind_empty :: x:Vname -> y:Vname 
        -> { e:Expr | Set_emp (freeBV (unbind x y e)) }
        -> { pf:_ | (Set_emp (freeBV e) || freeBV e == Set_sng x) } @-}
lem_freeBV_unbind_empty :: Vname -> Vname -> Expr -> Proof
lem_freeBV_unbind_empty x y e = toProof ( S.empty === freeBV (unbind x y e)
                                      === S.difference (freeBV e) (S.singleton x) )

{-@ lem_tfreeBV_unbindT_empty :: x:Vname -> y:Vname 
         -> { t:Type | Set_emp (tfreeBV (unbindT x y t)) }
         -> { pf:_ | (Set_emp (tfreeBV t) || tfreeBV t == Set_sng x) } @-}
lem_tfreeBV_unbindT_empty :: Vname -> Vname -> Type -> Proof
lem_tfreeBV_unbindT_empty x y t = toProof ( S.empty === tfreeBV (unbindT x y t)
                                        === S.difference (tfreeBV t) (S.singleton x) )

{-@ lem_freeBV_emptyB :: g:FEnv -> e:Expr -> t:FType -> ProofOf(HasFType g e t)
                              -> { pf:_ | Set_emp (freeBV e) } @-}
lem_freeBV_emptyB :: FEnv -> Expr ->  FType -> HasFType -> Proof 
lem_freeBV_emptyB g e t (FTBC _g b)    = case e of
  (Bc _) -> ()
lem_freeBV_emptyB g e t (FTIC _g n)    = case e of
  (Ic _) -> ()
lem_freeBV_emptyB g e t (FTVar1 _ x _) = case e of 
  (FV _) -> ()
lem_freeBV_emptyB g e t (FTVar2 g' x _ p_x_t y s) = case e of
  (FV _) -> () ? lem_freeBV_emptyB g' e t p_x_t
lem_freeBV_emptyB g e t (FTPrm _g c)   = case e of
  (Prim _) -> ()
lem_freeBV_emptyB g e t (FTAbs _g x t_x e' t' y p_yg_e'_t') = case e of
  (Lambda _ _) -> () ? lem_freeBV_unbind_empty x y (e' ? lem_freeBV_emptyB (FCons y t_x g) (unbind x y e')
                                                               t' p_yg_e'_t')
lem_freeBV_emptyB g e t (FTApp _g e' t_x t' p_e'_txt' e_x p_ex_tx) = case e of
  (App _ _) -> () ? lem_freeBV_emptyB g e' (FTFunc t_x t') p_e'_txt'
                  ? lem_freeBV_emptyB g e_x t_x p_ex_tx
lem_freeBV_emptyB g e t (FTLet _g e_x t_x p_ex_tx x e' t' y p_yg_e'_t') = case e of
  (Let {}) -> () ? lem_freeBV_emptyB g e_x t_x p_ex_tx
                 ? lem_freeBV_unbind_empty x y (e' ? lem_freeBV_emptyB (FCons y t_x g) (unbind x y e')
                                                               t' p_yg_e'_t')
lem_freeBV_emptyB g e t (FTAnn _g e' _t t1 p_e'_t) = case e of
  (Annot _ _)  -> () ? lem_freeBV_emptyB g e' t p_e'_t

{-@ lem_tfreeBV_empty :: g:Env -> t:Type -> { p_g_t:WFType | propOf p_g_t == WFType g t }
        -> { pf:Proof | Set_emp (tfreeBV t) } / [wftypSize p_g_t] @-}
lem_tfreeBV_empty :: Env -> Type -> WFType -> Proof
lem_tfreeBV_empty g t p_g_t@(WFRefn _g x b p y p_yg_p_bl) = case t of
  (TRefn _ _ _) -> () ? lem_freeBV_unbind_empty x y (p ? pf_unbinds_empty)
      where
        {-@ pf_unbinds_empty :: { pf:_ | Set_emp (freeBV (unbind x y p)) } @-} 
        pf_unbinds_empty = lem_freeBV_emptyB (FCons y (FTBasic b) (erase_env g)) (unbind x y p) 
                                             (FTBasic TBool) p_yg_p_bl
lem_tfreeBV_empty g t (WFFunc _g x t_x p_g_tx t' y p_yg_t')  = case t of
  (TFunc _ _ _) -> () 
        ? lem_tfreeBV_empty g t_x p_g_tx  
        ? lem_tfreeBV_unbindT_empty x y (t' ? lem_tfreeBV_empty (Cons y t_x g) (unbindT x y t') 
                                                                p_yg_t' )
lem_tfreeBV_empty g t (WFExis _g x t_x p_g_tx t' y p_yg_t')  = case t of
  (TExists _ _ _) -> () 
        ? lem_tfreeBV_empty g t_x p_g_tx 
        ? lem_tfreeBV_unbindT_empty x y (t' ? lem_tfreeBV_empty (Cons y t_x g) (unbindT x y t') 
                                                                p_yg_t' )
