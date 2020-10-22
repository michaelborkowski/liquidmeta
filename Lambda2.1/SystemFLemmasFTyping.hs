{-# LANGUAGE GADTs #-}

{-@ LIQUID "--no-termination" @-}  -- TODO: assume
{-@ LIQUID "--no-totality" @-}     -- TODO: assume
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SystemFLemmasFTyping where

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
import SystemFLemmasWellFormedness

{-@ reflect foo22 @-}
foo22 x = Just x
foo22 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development for the Underlying STLC :: Technical LEMMAS
------------------------------------------------------------------------------

{-@ lem_freeBV_unbind_empty :: x:Vname -> y:Vname 
        -> { e:Expr | Set_emp (freeBV (unbind x y e)) && Set_emp (freeBTV (unbind x y e)) }
        -> { pf:_ | (Set_emp (freeBV e) || freeBV e == Set_sng x) && Set_emp (freeBTV e) } @-}
lem_freeBV_unbind_empty :: Vname -> Vname -> Expr -> Proof
lem_freeBV_unbind_empty x y e = toProof ( S.empty === freeBV (unbind x y e)
                                      === S.difference (freeBV e) (S.singleton x) )

{-@ lem_freeBTV_unbind_tv_empty :: a:Vname -> a':Vname 
        -> { e:Expr | Set_emp (freeBTV (unbind_tv a a' e)) && Set_emp (freeBV (unbind_tv a a' e)) }
        -> { pf:_ | (Set_emp (freeBTV e) || freeBTV e == Set_sng a) && Set_emp (freeBV e) } @-}
lem_freeBTV_unbind_tv_empty :: Vname -> Vname -> Expr -> Proof
lem_freeBTV_unbind_tv_empty a a' e = toProof ( S.empty === freeBTV (unbind_tv a a' e)
                                      === S.difference (freeBTV e) (S.singleton a) )

{-@ lem_freeBV_emptyB :: g:FEnv -> e:Expr -> t:FType -> ProofOf(HasFType g e t)
                              -> { pf:_ | Set_emp (freeBV e) && Set_emp (freeBTV e) } @-}
lem_freeBV_emptyB :: FEnv -> Expr ->  FType -> HasFType -> Proof 
lem_freeBV_emptyB g e t (FTBC _g b)    = case e of
  (Bc _) -> ()
lem_freeBV_emptyB g e t (FTIC _g n)    = case e of
  (Ic _) -> ()
lem_freeBV_emptyB g e t (FTVar1 _ x _) = case e of 
  (FV _) -> ()
lem_freeBV_emptyB g e t (FTVar2 g' x _ p_x_t y s) = case e of
  (FV _) -> () ? lem_freeBV_emptyB g' e t p_x_t
lem_freeBV_emptyB g e t (FTVar3 g' x _ p_x_t a k) = case e of
  (FV _) -> () ? lem_freeBV_emptyB g' e t p_x_t
lem_freeBV_emptyB g e t (FTPrm _g c)   = case e of
  (Prim _) -> ()
lem_freeBV_emptyB g e t (FTAbs _g x t_x k_x p_g_tx e' t' y p_yg_e'_t') = case e of
  (Lambda _ _) -> () ? lem_freeBV_unbind_empty x y (e' ? lem_freeBV_emptyB (FCons y t_x g) (unbind x y e')
                                                               t' p_yg_e'_t')
lem_freeBV_emptyB g e t (FTApp _g e' t_x t' p_e'_txt' e_x p_ex_tx) = case e of
  (App _ _) -> () ? lem_freeBV_emptyB g e' (FTFunc t_x t') p_e'_txt'
                  ? lem_freeBV_emptyB g e_x t_x p_ex_tx
lem_freeBV_emptyB g e t (FTAbsT _g a k e' t' a' p_e'_t') = case e of 
  (LambdaT {}) -> () ? lem_freeBV_emptyB (FConsT a' k g) (unbind_tv a a' e') (unbindFT a a' t') p_e'_t'
{-lem_freeBV_emptyB g e t (FTAppT _g e' a k t' p_e_at' liqt p_g_ert)
    = () ? lem_freeBV_emptyB g e' (FTPoly a k t') p_e_at'
         ? undefined -}
lem_freeBV_emptyB g e t (FTLet _g e_x t_x p_ex_tx x e' t' y p_yg_e'_t') = case e of
  (Let {}) -> () ? lem_freeBV_emptyB g e_x t_x p_ex_tx
                 ? lem_freeBV_unbind_empty x y (e' ? lem_freeBV_emptyB (FCons y t_x g) (unbind x y e')
                                                               t' p_yg_e'_t')
{- lem_freeBV_emptyB g e t (FTAnn _g e' _t t1 p_e'_t) 
    = () ? lem_freeBV_emptyB g e' t p_e'_t
          undefined -}
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 
-- Consequences of the System F Typing Judgments -
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 

{-@ lem_ftyping_wfft :: g:FEnv -> e:Expr -> t:FType -> ProofOf(HasFType g e t)
                      -> ProofOf(WFFE g) -> ProofOf(WFFT g t Star) @-} 
lem_ftyping_wfft :: FEnv -> Expr -> FType -> HasFType -> WFFE -> WFFT
lem_ftyping_wfft g e t (FTBC _g b) p_wf_g  = WFFTKind g (FTBasic TBool) (WFFTBasic g TBool)
lem_ftyping_wfft g e t (FTIC _g n) p_wf_g  = WFFTKind g (FTBasic TInt)  (WFFTBasic g TInt)
lem_ftyping_wfft g e t (FTVar1 _g' x t') p_wf_g 
    = undefined
{-    = case p_wf_g of
        (WFFEmpty)                       -> impossible "in_envF x g"
        (WFFBind g' p_g' _x _t' k' p_g'_t') -> lem_weaken_wfft g' FEmpty t k' p_g'_t' x t-}
lem_ftyping_wfft g e t (FTVar2 g' x _t p_g'_x_t y s) p_wf_g
    = undefined
{-    = case p_wf_g of
        (WFFEmpty)                       -> impossible "in_envF y g"
        (WFFBind g' p_g' _y _s k_s p_g'_s) -> lem_weaken_wfft g' Empty t 
                                              (lem_ftyping_wfft g' e t p_g'_x_t p_g') y s-}
lem_ftyping_wfft g e t (FTVar3 g' x _t p_g'_x_t a k) p_wf_g
    = undefined
{-    = case p_wf_g of
        (WFFEmpty)                     -> impossible "in_envF a g"
        (WFFBindT g' p_g' _a _k)       -> lem_weaken_tv_wfft g' Empty t 
                                            (lem_ftyping_wfft g' e t p_g'_x_t p_g') a k-}
lem_ftyping_wfft g e t (FTPrm _g c) p_wf_g 
    = undefined
{- = lem_erase_wftype g (ty c) Star pf_tyc_wf
  where
    pf_tyc_wf = lem_weaken_many_wfft Empty g (ty c) (lem_wf_ty c) ? lem_empty_concatE g-}
lem_ftyping_wfft g e t (FTAbs _g x t_x k_x pf_g_tx e' t' y pf_e'_t') pf_wf_g
    = undefined
{-    = WFFTFunc g t_x Star pf_g_tx t' Star pf_g_t'
        where
          pf_wf_yg = WFFBind g pf_wf_g y t_x k_x pf_g_tx  
          pf_yg_t' = lem_ftyping_wfft (FCons y t_x g) (unbind x y e') t' pf_e'_t' pf_wf_yg
          pf_g_t'  = lem_strengthen_wfft g y t_x FEmpty t' Star pf_yg_t'-}
lem_ftyping_wfft g e t (FTApp _g e1 t_x t' p_e1_txt' e2 p_e2_tx) p_wf_g
    = undefined
{-    = case (lem_ftyping_wfft g e1 (FTFunc t_x t') p_e1_txt' p_wf_g) of
        (WFFTFunc _ _ _ p_g_tx _ _ p_g_t') -> p_g_t'
        (_)                                -> impossible "needs lemma" -- is WFFTKind possible?-}
lem_ftyping_wfft g e t (FTAbsT _g a k e' t' a' pf_a'g_e'_t') pf_wf_g
    = WFFTPoly g a k t' Star a' pf_a'g_t'
        where
          pf_wf_a'g = WFFBindT g pf_wf_g a' k
          pf_a'g_t' = lem_ftyping_wfft (FConsT a' k g) (unbind_tv a a' e') (unbindFT a a' t')
                                       pf_a'g_e'_t' pf_wf_a'g
lem_ftyping_wfft g e t (FTAppT _g e' a k t' pf_e'_at' liqt pf_g_erliqt) pf_wf_g
    = undefined
{-    = pf_g_t'liqt
       where
         (FTAbsT _ _a _k e'' _t' a' pf_a'g_e''_t') = pf_e'_at'
         pf_wf_a'g   = WFEBindT g pf_wf_g a' k
         pf_a'g_t'   = lem_ftyping_wfft (FConsT a' k g) (unbind_tv a a' e'') (unbindFT a a' t')
                                        pf_a'g_e''_t' pf_wf_a'g 
         pf_g_t'liqt = lem_subst_tv_wfft g FEmpty a' (erase (unbind_tvT a a' liqt)) k 
                                      pf_g_erliqt pf_wf_a'g t' pf_a'g_t' -}
lem_ftyping_wfft g e t (FTLet _g e_x t_x p_ex_tx x e' _t {-p_g_t-} y p_e'_t) p_wf_g  
    = undefined
{-    = lem_ftyping_wfft (FCons y t_x g) (unbind x y e') t p_e'_t p_wf_yg 
        where 
          pf_g_tx = lem_ftyping_wfft g e_x t_x p_ex_tx p_wf_g
          p_wf_yg = WFFBind g p_wf_g y t_x Star pf_g_tx-}
lem_ftyping_wfft g e t (FTAnn _g e' _t liqt p_e'_t) p_wf_g
    = lem_ftyping_wfft g e' t p_e'_t p_wf_g

--        -> e:Expr -> { t:FType | Set_sub (ffreeTV t) (bindsF (concatF (FCons x t_x g) g')) }
-- We can alpha-rename a variable anywhere in the environment and recursively alter the type
--   derivation tree. NB this is the base type judgement so there are no variables in the 
--   types to worry about
{-@ lem_change_var_ftyp :: g:FEnv -> { x:Vname | not (in_envF x g) } -> t_x:FType
        -> { g':FEnv | not (in_envF x g') && Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> ProofOf(WFFE (concatF (FCons x t_x g) g')) -> e:Expr -> t:FType 
        -> { p_e_t:HasFType | propOf p_e_t == HasFType (concatF (FCons x t_x g) g') e t }
        -> { y:Vname | not (in_envF y g) && not (in_envF y g') }
        -> { pf:HasFType | propOf pf == (HasFType (concatF (FCons y t_x g) g') (subFV x (FV y) e) t) 
                           && ftypSize pf == ftypSize p_e_t } / [ftypSize p_e_t] @-}
lem_change_var_ftyp :: FEnv -> Vname -> FType -> FEnv -> WFFE -> Expr -> FType 
                -> HasFType ->  Vname -> HasFType
{- CHECKED -}
lem_change_var_ftyp g x t_x g' pf_wf_env e t (FTBC _ b) y
    = FTBC (concatF (FCons y t_x g) g') b
lem_change_var_ftyp g x t_x g' pf_wf_env e t (FTIC _ n) y
    = FTIC (concatF (FCons y t_x g) g') n 
lem_change_var_ftyp g x t_x g' pf_wf_env e t p_z_t@(FTVar1 _ z _t) y
    = case g' of 
        (FEmpty)           -> FTVar1 g y t_x 
        (FCons  _z _ g'')  -> FTVar1 (concatF (FCons y t_x g) g'') z t
        (FConsT a k g'')   -> impossible ""
lem_change_var_ftyp g x t_x g' pf_wf_env e t (FTVar2 _ z _t p_z_t w t_w) y
    = case g' of             -- g''=Emp so x=w and p_z_t :: HasFType(g (FV z) t)
        (FEmpty)           -> case (x == z) of
                                (True)  -> impossible "it is"
                                (False) -> FTVar2 g z t p_z_t y t_x 
        (FCons _w _tw g'') -> case (x == z) of
                    (True)  -> FTVar2 (concatF (FCons y t_x g) g'') 
                                 (y `withProof` lem_in_env_concatF (FCons y t_x g) g'' y)
                                 t (lem_change_var_ftyp g x t_x g'' pf_wf_env' (FV z) t p_z_t y) w t_w
                    (False) -> FTVar2 (concatF (FCons y t_x g) g'')
                                 (z `withProof` lem_in_env_concatF (FCons y t_x g) g'' z
                                    `withProof` lem_in_env_concatF (FCons x t_x g) g'' z)
                                 t (lem_change_var_ftyp g x t_x g'' pf_wf_env' (FV z) t p_z_t y) w t_w
          where
            (WFFBind _ pf_wf_env' _ _ _ _) = pf_wf_env
        (FConsT a k g'')   -> impossible ""
lem_change_var_ftyp g x t_x g' pf_wf_env e t (FTVar3 _ z _t p_z_t a k) y
    = case g' of
        (FEmpty)           -> impossible ""
        (FCons w t_w g'')  -> impossible ""
        (FConsT _a _k g'') -> case (x == z) of
                    (True)   -> FTVar3 (concatF (FCons y t_x g) g'') 
                                  (y `withProof` lem_in_env_concatF (FCons y t_x g) g'' y)
                                  t (lem_change_var_ftyp g x t_x g'' pf_wf_env' (FV z) t p_z_t y) a k
                    (False)  -> FTVar3 (concatF (FCons y t_x g) g'')
                                  (z `withProof` lem_in_env_concatF (FCons y t_x g) g'' z
                                     `withProof` lem_in_env_concatF (FCons x t_x g) g'' z)
                                  t (lem_change_var_ftyp g x t_x g'' pf_wf_env' (FV z) t p_z_t y) a k
          where
            (WFFBindT _ pf_wf_env' _ _) = pf_wf_env
lem_change_var_ftyp g x t_x g' pf_wf_env e t (FTPrm _ c) y
    = FTPrm (concatF (FCons y t_x g) g') c
{- -}
lem_change_var_ftyp g x t_x g' pf_wf_env e t p_e_t@(FTAbs gg z b k p_gg_b e' b' z' p_z'_e'_b') y
    = undefined 
{- = FTAbs (concatF (FCons y t_x g) g') z b (subFV x (FV y) e') b' 
            (z'' `withProof` lem_fv_bound_in_fenv (concatF (FCons x t_x g) g') e t p_e_t z'')
            (lem_change_var_ftyp g x t_x (FCons z'' b g') ______ (unbind z z'' e') b' 
                (p_z''_e'_b' `withProof` lem_subFV_unbind z z' (FV z'')
                        (e' `withProof` lem_fv_bound_in_fenv (concatF (FCons x t_x g) g')
                                                          e t p_e_t z'))
                y `withProof` lem_commute_subFV_unbind x y z z'' e')
        where
            z''_         = fresh_var_excludingF (concatF (FCons x t_x g) g') y
            z''          = z''_ ? lem_in_env_concatF g g' z''_
                               ? lem_in_env_concatF (FCons x t_x g) g' z''_
            pf_wf_z'env  = WFFBind (concatF (FCons x t_x g) g') pf_wf_env z' b 
            pf_wf_z''env =
            p_z''_e'_b'  = lem_change_var_ftyp  (concatF (FCons x t_x g) g') z' b FEmpty _____
                                    (unbind z z' e') b' p_z'_e'_b' z'' -}
lem_change_var_ftyp g x t_x g' pf_wf_env e t (FTApp _ e1 t1 t2 p_e1_t1t2 e2 p_e2_t1) y
    = FTApp (concatF (FCons y t_x g) g') (subFV x (FV y) e1) t1 t2 
            (lem_change_var_ftyp g x t_x g' pf_wf_env e1 (FTFunc t1 t2) p_e1_t1t2 y)
            (subFV x (FV y) e2) (lem_change_var_ftyp g x t_x g' pf_wf_env e2 t1 p_e2_t1 y)
lem_change_var_ftyp g x t_x g' pf_wf_env e t p_e_t@(FTAbsT _g a k e' t' a' p_a'_e'_t') y
    = undefined
{-    = FTAbsT (concatF (FCons y t_x g) g') a k (subFV x (FV y) e') t' a''
             {-(a'' ? lem_fv_bound_in_fenv (concatF (FCons x t_x g) g') e t p_e_t a'')-}
             (lem_change_var_ftyp g x t_x (FConsT a'' k g') (unbind_tv a a'' e') 
                 (unbindFT a a'' t') p_a''_e'_t' y)
        where
          a''_         = fresh_var_excludingF (concatF (FCons x t_x g) g') y 
          a''          = a''_ ? lem_in_env_concatF g g' a''_
                              ? lem_in_env_concatF (FCons x t_x g) g' a''_
                              ? lem_in_env_concatF (FCons y t_x g) g' a''_
                              ? lem_fv_bound_in_fenv (concatF (FCons x t_x g) g') e t p_e_t a''_
          p_a''_e'_t'  = lem_change_tvar_ftyp (concatF (FCons x t_x g) g') a' k FEmpty 
                                    (unbind_tv a a' e') (unbindFT a a' t') p_a'_e'_t' a''
                           ? lem_subFTV_unbind_tv a a' (FTV a'')
                                (e' ? lem_fv_bound_in_fenv (concatF (FCons x t_x g) g') e t p_e_t a')
                           ? lem_ftsubFV_unbindFT a a' (FTFV a'')  t' -}
lem_change_var_ftyp g x t_x g' pf_wf_env e t (FTAppT _ e' a k t' p_e'_at' rt pf_g_rt) y
    = undefined
{-    = FTAppT (concatF (FCons y t_x g) g') (subFV x (FV y) e') a k t'
             (lem_change_var_ftyp g x t_x g' pf_wf_env e' (FTPoly a k t') p_e'_at' y)
             (tsubFV x (FV y) rt ? lem_erase_tsubFV x (FV y) rt 
                                 ? lem_binds_cons_concatF g g' x t_x
--                                 ? lem_binds_cons_concatF g g' y t_x) -- ? free bound env with y
                                 ? lem_binds_cons_concatF g g' y t_x) -- ? free bound env with y
             -- ? lem_binds_cons_concatF g g' x t_x
--}

lem_change_var_ftyp g x t_x g' pf_wf_env e t p_e_t@(FTLet gg e_z t_z p_ez_tz z e' t' z' p_z'_e'_t') y
    = undefined -- assume
{-    = FTLet (concatF (FCons y t_x g) g') (subFV x (FV y) e_z) t_z
            (lem_change_var_ftyp g x t_x g' e_z t_z p_ez_tz y) z (subFV x (FV y) e') t' 
            (z'' `withProof` lem_fv_bound_in_fenv (concatF (FCons x t_x g) g') e t p_e_t z'')
            (lem_change_var_ftyp g x t_x (FCons z'' t_z g') (unbind z z'' e') t' 
                (p_z''_e'_t' `withProof` lem_subFV_unbind z z' (FV z'')
                        (e' `withProof` lem_fv_bound_in_fenv (concatF (FCons x t_x g) g')
                                                          e t p_e_t z'))
                y `withProof` lem_commute_subFV_unbind x y z z'' e')
        where
            z''         = fresh_var_excludingF (concatF (FCons x t_x g) g') y
            p_z''_e'_t' = lem_change_var_ftyp  (concatF (FCons x t_x g) g') z' t_z FEmpty 
                                    (unbind z z' e') t' p_z'_e'_t' 
                                    (z'' `withProof` lem_in_env_concatF g g' z''
                                         `withProof` lem_in_env_concatF (FCons x t_x g) g' z'') -}
lem_change_var_ftyp g x t_x g' pf_wf_env e t (FTAnn _ e' _t t' p_e'_t) y
    = undefined -- assume
{-
    = FTAnn (concatF (FCons y t_x g) g') (subFV x (FV y) e') t 
            (tsubFV x (FV y) t' `withProof` lem_erase_tsubFV x (FV y) t'
                                `withProof` lem_binds_cons_concatF g g' x t_x)
            (lem_change_var_ftyp g x t_x g' e' t p_e'_t y)
-}

-- delete this later
{-
lem_change_var_ftyp g x t_x g' e t p_e_t@(FTAbsT _g a k e' t' a' p_a'_e'_t') y
    = FTAbsT (concatF (FCons y t_x g) g') a k (subFV x (FV y) e') t'
             (a'' ? lem_fv_bound_in_fenv (concatF (FCons x t_x g) g') e t p_e_t a'')
             (lem_change_var_ftyp g x t_x (FConsT a'' k g') (unbind_tv a a'' e') (unbindFT a a'' t')
                 (p_a''_e'_t' {-? lem_subFTV_unbind_tv a a' (FTV a'') 
                         (e' ? lem_fv_bound_in_fenv (concatF (FCons x t_x g) g') e t p_e_t a')-})
                 y) -- TODO: check which lemmas needed
        where
          a''_         = fresh_var_excludingF (concatF (FCons x t_x g) g') y 
          a''          = a''_ ? lem_in_env_concatF g g' a''_
                              ? lem_in_env_concatF (FCons x t_x g) g' a''_
          p_a''_e'_t'  = lem_change_tvar_ftyp (concatF (FCons x t_x g) g') a' k FEmpty 
                                    (unbind_tv a a' e') (unbindFT a a' t') p_a'_e'_t' a''
                           ? lem_subFTV_unbind_tv a a' (FTV a'')
                                (e' ? lem_fv_bound_in_fenv (concatF (FCons x t_x g) g') e t p_e_t a')
                           ? lem_ftsubFV_unbindFT a a' (FTFV a'')  t'
-}

--        -> e:Expr -> { t:FType | Set_sub (ffreeTV t) (bindsF (concatF (FConsT a k g) g')) }
{-@ lem_change_tvar_ftyp :: g:FEnv -> { a:Vname | not (in_envF a g) } -> k:Kind 
        -> { g':FEnv | not (in_envF a g') && Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> ProofOf(WFFE (concatF (FConsT a k g) g')) -> e:Expr -> t:FType 
        -> { p_e_t:HasFType | propOf p_e_t == HasFType (concatF (FConsT a k g) g') e t }
        -> { a':Vname | not (in_envF a' g) && not (in_envF a' g') }
        -> { pf:HasFType | propOf pf == (HasFType (concatF (FConsT a' k g) 
                                                     (fesubFV a (FTBasic (FTV a')) g')) 
                                           (chgFTV a a' e) (ftsubFV a (FTBasic (FTV a')) t)) && 
                             ftypSize pf == ftypSize p_e_t } / [ftypSize p_e_t] @-}
lem_change_tvar_ftyp :: FEnv -> Vname -> Kind -> FEnv -> WFFE -> Expr -> FType 
                -> HasFType ->  Vname -> HasFType
{- -}
lem_change_tvar_ftyp g a k g' pf_wf_env e t (FTBC _ b) a'
    = FTBC (concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g')) b
lem_change_tvar_ftyp g a k g' pf_wf_env e t (FTIC _ n) a'
    = FTIC (concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g')) n 
lem_change_tvar_ftyp g a k g' pf_wf_env e t p_z_t@(FTVar1 _ z _t) a'
    = undefined -- assume
{-    = case g' of 
        (FEmpty)           -> impossible ""
        (FCons  _z _ g'')  -> FTVar1 (concatF (FConsT a' k g) (fesubFV a (FTBasic (FTV a')) g'')) z 
                                     (ftsubFV a (FTBasic (FTV a')) t)
        (FConsT a k g'')   -> impossible ""
{ - -}
lem_change_tvar_ftyp g a k g' pf_wf_env e t (FTVar2 _ z _t p_z_t w t_w) a'
    = undefined -- assume
lem_change_tvar_ftyp g a k g' pf_wf_env e t (FTVar3 _ z _t p_z_t a1 k1) a'
    = undefined -- assume
lem_change_tvar_ftyp g a k g' pf_wf_env e t (FTPrm _ c) y
    = undefined -- assume
{- -}
lem_change_tvar_ftyp g a k g' pf_wf_env e t p_e_t@(FTAbs gg z b e' b' _ _ z' p_z'_e'_b') a'
    = undefined -- assume
lem_change_tvar_ftyp g a k g' pf_wf_env e t (FTApp _ e1 t1 t2 p_e1_t1t2 e2 p_e2_t1) a'
    = undefined -- assume
lem_change_tvar_ftyp g a k g' pf_wf_env e t p_e_t@(FTAbsT _g a1 k1 e' t' a1' p_a1'_e'_t') a'
    = undefined -- assume
lem_change_tvar_ftyp g a k g' pf_wf_env e t (FTAppT _ e' a1 k1 t' p_e'_a1t' rt _) a'
    = undefined -- assume
lem_change_tvar_ftyp g a k g' pf_wf_env e t p_e_t@(FTLet gg e_z t_z p_ez_tz z e' t' z' p_z'_e'_t') a'
    = undefined -- assume
lem_change_tvar_ftyp g a k g' pf_wf_env e t (FTAnn _ e' _t t' p_e'_t) a'
    = undefined -- assume



{-@ assume lem_weaken_ftyp :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> ProofOf(WFFE (concatF g g')) -> e:Expr -> t:FType 
        -> { p_e_t:HasFType | propOf p_e_t == HasFType (concatF g g') e t }
        -> { x:Vname | not (in_envF x g) && not (in_envF x g') } -> t_x:FType
        -> { pf:HasFType | propOf pf == (HasFType (concatF (FCons x t_x g) g') e t) 
                           && ftypSize pf == ftypSize p_e_t } @-} -- / [ftypSize p_e_t] @-}
lem_weaken_ftyp :: FEnv -> FEnv -> WFFE -> Expr -> FType 
                -> HasFType ->  Vname -> FType -> HasFType
lem_weaken_ftyp g g' pf_wf_env e t (FTBC _env b) x t_x  = undefined -- assume
lem_weaken_ftyp g g' pf_wf_env e t (FTIC _env n) x t_X  = undefined -- assume
lem_weaken_ftyp g g' pf_wf_env e t (FTVar1 _env y t_y) x t_x = undefined -- assume
lem_weaken_ftyp g g' pf_wf_env e t (FTVar2 {}) x t_x  = undefined -- assume
lem_weaken_ftyp g g' pf_wf_env e t (FTVar3 {}) x t_x  = undefined -- assume
lem_weaken_ftyp g g' pf_wf_env e t (FTPrm {})  x t_x  = undefined -- assume
lem_weaken_ftyp g g' pf_wf_env e t (FTAbs {})  x t_x  = undefined -- assume
lem_weaken_ftyp g g' pf_wf_env e t (FTApp {})  x t_x  = undefined -- assume
lem_weaken_ftyp g g' pf_wf_env e t (FTAbsT {}) x t_x  = undefined -- assume
lem_weaken_ftyp g g' pf_wf_env e t (FTAppT {}) x t_x  = undefined -- assume
lem_weaken_ftyp g g' pf_wf_env e t (FTLet {})  x t_x  = undefined -- assume
lem_weaken_ftyp g g' pf_wf_env e t (FTAnn {})  x t_x  = undefined -- assume
{-
{-@ lem_weaken_ftyp :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> e:Expr -> bt:FType -> { p_e_bt:HasFType | propOf p_e_bt == HasFType (concatF g g') e bt }
        -> { x:Vname | (not (in_envF x g)) && (not (in_envF x g')) }
        -> t_x:FType -> ProofOf(HasFType (concatF (FCons x t_x g) g') e bt) / [ftypSize p_e_bt] @-}
lem_weaken_ftyp :: FEnv -> FEnv -> Expr -> FType -> HasFType -> Vname -> FType -> HasFType
lem_weaken_ftyp g g' e t (FTBC _g b)      x t_x = FTBC  (concatF (FCons x t_x g) g') b
lem_weaken_ftyp g g' e t (FTIC _g n)      x t_x = FTIC  (concatF (FCons x t_x g) g') n
lem_weaken_ftyp g g' e t p_y_ty@(FTVar1 gg y t_y) x t_x 
    = case g' of 
        (FEmpty)           -> FTVar2 (FCons y t_y gg) y t_y p_y_ty x t_x
        (FCons _y _ty g'') -> FTVar1 (concatF (FCons x t_x g) g'') y t_y 
                                    -- (g; g' == _g, z:t_z) |- y : t_y
lem_weaken_ftyp g g' e t p_y_ty@(FTVar2 gg y t_y p_gg'_y_ty z t_z) x t_x
    = case g' of
        (FEmpty)           -> FTVar2 (FCons z t_z gg) y t_y p_y_ty x t_x
        (FCons _z _tz g'') -> FTVar2 (concatF (FCons x t_x g) g'') 
                                  (y `withProof` lem_in_env_concatF g g'' y
                                     `withProof` lem_in_env_concatF (FCons x t_x g) g'' y) t_y
                                     (lem_weaken_ftyp g g'' e t p_gg'_y_ty x t_x)
                                     z t_z
lem_weaken_ftyp g g' e t (FTPrm _g c)     x t_x = FTPrm (concatF (FCons x t_x g) g') c
lem_weaken_ftyp g g' e t p_e_t@(FTAbs gg y t_y e' t' y' p_y'_e'_t') x t_x
    = FTAbs (concatF (FCons x t_x g) g') y t_y e' t' 
               (y'' `withProof` lem_fv_bound_in_fenv (concatF g g') e t p_e_t y'')
               (lem_weaken_ftyp g (FCons y'' t_y g') (unbind y y'' e') t' 
                       (p_y''_e'_t' `withProof` lem_subFV_unbind y y' (FV y'') e')
                       x t_x) 
        where
            y''         = fresh_varF (concatF (FCons x t_x g) g')
            p_y''_e'_t' = lem_change_var_ftyp (concatF g g') y' t_y FEmpty (unbind y y' e') 
                                   t' p_y'_e'_t' 
                                   (y'' `withProof` lem_in_env_concatF g g' y''
                                        `withProof` lem_in_env_concatF (FCons x t_x g) g' y'')
lem_weaken_ftyp g g' e t (FTApp _g e1 s s' p_e1_ss' e2 p_e2_s) x t_x 
    = FTApp (concatF (FCons x t_x g) g') e1 s s' 
               (lem_weaken_ftyp g g' e1 (FTFunc s s') p_e1_ss' x t_x)
                e2 (lem_weaken_ftyp g g' e2 s p_e2_s x t_x)
lem_weaken_ftyp g g' e t p_e_t@(FTLet gg e_y t_y p_ey_ty y e' t' y' p_y'_e'_t') x t_x
    = FTLet (concatF (FCons x t_x g) g') e_y t_y 
               (lem_weaken_ftyp g g' e_y t_y p_ey_ty x t_x) y e' t' 
               (y'' `withProof` lem_fv_bound_in_fenv (concatF g g') e t p_e_t y'')
               (lem_weaken_ftyp g (FCons y'' t_y g') (unbind y y'' e') t' 
                       (p_y''_e'_t' `withProof` lem_subFV_unbind y y' (FV y'') e')
                       x t_x)
        where
            y''         = fresh_varF (concatF (FCons x t_x g) g')
            p_y''_e'_t' = lem_change_var_ftyp (concatF g g') y' t_y FEmpty (unbind y y' e') 
                              t' p_y'_e'_t' (y'' `withProof` lem_in_env_concatF g g' y''
                                        `withProof` lem_in_env_concatF (FCons x t_x g) g' y'')
lem_weaken_ftyp g g' e bt (FTAnn _g e' _bt lt p_e'_bt) x t_x
    = FTAnn (concatF (FCons x t_x g) g') e' bt 
            (lt `withProof` lem_binds_cons_concatF g g' x t_x)
            (lem_weaken_ftyp g g' e' bt p_e'_bt x t_x)
-}

{-@ assume lem_weaken_tv_ftyp :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> ProofOf(WFFE (concatF g g')) -> e:Expr -> t:FType 
        -> { p_e_t:HasFType | propOf p_e_t == HasFType (concatF g g') e t }
        -> { a:Vname | not (in_envF a g) && not (in_envF a g') } -> k:Kind
        -> { pf:HasFType | propOf pf == (HasFType (concatF (FConsT a k g) g') e t)
                           && ftypSize pf == ftypSize p_e_t } @-} -- / [ftypSize p_e_t] @-}
lem_weaken_tv_ftyp :: FEnv -> FEnv -> WFFE -> Expr -> FType 
                -> HasFType -> Vname -> Kind -> HasFType
lem_weaken_tv_ftyp g g' pf_wf_env e t (FTBC _env b) a k  = undefined -- assume
lem_weaken_tv_ftyp g g' pf_wf_env e t (FTIC _env n) a k  = undefined -- assume
lem_weaken_tv_ftyp g g' pf_wf_env e t (FTVar1 _env x t_x) a k  = undefined -- assume
lem_weaken_tv_ftyp g g' pf_wf_env e t (FTVar2 {}) a k  = undefined -- assume
lem_weaken_tv_ftyp g g' pf_wf_env e t (FTVar3 {}) a k  = undefined -- assume
lem_weaken_tv_ftyp g g' pf_wf_env e t (FTPrm {}) a k  = undefined -- assume
lem_weaken_tv_ftyp g g' pf_wf_env e t (FTAbs {}) a k  = undefined -- assume
lem_weaken_tv_ftyp g g' pf_wf_env e t (FTApp {}) a k  = undefined -- assume
lem_weaken_tv_ftyp g g' pf_wf_env e t (FTAbsT {}) a k  = undefined -- assume
lem_weaken_tv_ftyp g g' pf_wf_env e t (FTAppT {}) a k  = undefined -- assume
lem_weaken_tv_ftyp g g' pf_wf_env e t (FTLet {}) a k  = undefined -- assume
lem_weaken_tv_ftyp g g' pf_wf_env e t (FTAnn {}) a k  = undefined -- assume

{-@ lem_weaken_many_ftyp :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> ProofOf(WFFE (concatF g g')) -> e:Expr -> t:FType -> ProofOf(HasFType g e t)
        -> ProofOf(HasFType (concatF g g') e t) @-}
lem_weaken_many_ftyp :: FEnv -> FEnv -> WFFE -> Expr -> FType -> HasFType -> HasFType
lem_weaken_many_ftyp g FEmpty           p_g_wf    e t p_g_e_t = p_g_e_t
lem_weaken_many_ftyp g (FCons x t_x g') p_xenv_wf e t p_g_e_t
  = lem_weaken_ftyp (concatF g g') FEmpty p_env_wf e t p_g'g_e_t x t_x
      where
        (WFFBind _ p_env_wf _ _ _ _) = p_xenv_wf
        p_g'g_e_t = lem_weaken_many_ftyp g g' p_env_wf e t p_g_e_t
lem_weaken_many_ftyp g (FConsT a k g') p_xenv_wf e t p_g_e_t
  = lem_weaken_tv_ftyp (concatF g g') FEmpty p_env_wf e t p_g'g_e_t a k
      where
        (WFFBindT _ p_env_wf _ _) = p_xenv_wf
        p_g'g_e_t = lem_weaken_many_ftyp g g' p_env_wf e t p_g_e_t

