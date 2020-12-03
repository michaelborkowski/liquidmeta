{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SystemFLemmasFTyping where

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

{-@ reflect foo23 @-}
foo23 x = Just x
foo23 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development for the Underlying STLC :: Technical LEMMAS
------------------------------------------------------------------------------

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 
-- Consequences of the System F Typing Judgments -
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 

--        -> e:Expr -> { t:FType | Set_sub (ffreeTV t) (bindsF (concatF (FCons x t_x g) g')) }
-- We can alpha-rename a variable anywhere in the environment and recursively alter the type
--   derivation tree. NB this is the base type judgement so there are no variables in the 
--   types to worry about
{-@ lem_change_var_ftyp :: g:FEnv -> { x:Vname | not (in_envF x g) } -> t_x:FType
        -> { g':FEnv | not (in_envF x g') && Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> e:Expr -> t:FType 
        -> { p_e_t:HasFType | propOf p_e_t == HasFType (concatF (FCons x t_x g) g') e t }
        -> { y:Vname | not (in_envF y g) && not (in_envF y g') }
        -> { pf:HasFType | propOf pf == (HasFType (concatF (FCons y t_x g) g') (subFV x (FV y) e) t) 
                           && ftypSize pf == ftypSize p_e_t } / [ftypSize p_e_t] @-}
lem_change_var_ftyp :: FEnv -> Vname -> FType -> FEnv -> Expr -> FType 
                -> HasFType ->  Vname -> HasFType
lem_change_var_ftyp g x t_x g' e t (FTBC _ b) y
    = FTBC (concatF (FCons y t_x g) g') b
lem_change_var_ftyp g x t_x g' e t (FTIC _ n) y
    = FTIC (concatF (FCons y t_x g) g') n 
lem_change_var_ftyp g x t_x g' e t p_z_t@(FTVar1 _ z _t) y
    = case g' of 
        (FEmpty)           -> FTVar1 g y t_x 
        (FCons  _z _ g'')  -> FTVar1 (concatF (FCons y t_x g) g'') z t
lem_change_var_ftyp g x t_x g' e t (FTVar2 _ z _t p_z_t w t_w) y
    = case g' of             -- g''=Emp so x=w and p_z_t :: HasFType(g (FV z) t)
        (FEmpty)           -> case (x == z) of
                                (True)  -> impossible "it is"
                                (False) -> FTVar2 g z t p_z_t y t_x 
        (FCons _w _tw g'') -> case (x == z) of
                    (True)  -> FTVar2 (concatF (FCons y t_x g) g'') 
                                 (y `withProof` lem_in_env_concatF (FCons y t_x g) g'' y)
                                 t (lem_change_var_ftyp g x t_x g'' (FV z) t p_z_t y) w t_w
                    (False) -> FTVar2 (concatF (FCons y t_x g) g'')
                                 (z `withProof` lem_in_env_concatF (FCons y t_x g) g'' z
                                    `withProof` lem_in_env_concatF (FCons x t_x g) g'' z)
                                 t (lem_change_var_ftyp g x t_x g'' (FV z) t p_z_t y) w t_w
lem_change_var_ftyp g x t_x g' e t (FTPrm _ c) y
    = FTPrm (concatF (FCons y t_x g) g') c
lem_change_var_ftyp g x t_x g' e t p_e_t@(FTAbs gg z b e' b' z' p_z'_e'_b') y
    = FTAbs (concatF (FCons y t_x g) g') z b (subFV x (FV y) e') b' z'' p_z''y_e'_b'
        where
            z''_         = fresh_var_excludingF (concatF (FCons x t_x g) g') y
            z''          = z''_ ? lem_in_env_concatF g g' z''_
                                ? lem_in_env_concatF (FCons x t_x g) g' z''_
                                ? lem_fv_bound_in_fenv (concatF (FCons x t_x g) g') e t p_e_t z''_
            p_z''_e'_b'  = lem_change_var_ftyp  (concatF (FCons x t_x g) g') z' b FEmpty 
                                    (unbind z z' e') b' p_z'_e'_b' z'' 
                                    ? lem_subFV_unbind z z' (FV z'') e'
            p_z''y_e'_b' = lem_change_var_ftyp g x t_x (FCons z'' b g') 
                                    (unbind z z'' e') b' p_z''_e'_b' y
                                    ? lem_commute_subFV_unbind x y z z'' e'
lem_change_var_ftyp g x t_x g' e t (FTApp _ e1 t1 t2 p_e1_t1t2 e2 p_e2_t1) y
    = FTApp (concatF (FCons y t_x g) g') (subFV x (FV y) e1) t1 t2 
            (lem_change_var_ftyp g x t_x g' e1 (FTFunc t1 t2) p_e1_t1t2 y)
            (subFV x (FV y) e2) (lem_change_var_ftyp g x t_x g' e2 t1 p_e2_t1 y)
lem_change_var_ftyp g x t_x g' e t p_e_t@(FTLet env e_z t_z p_ez_tz z e' t' z' p_z'_e'_t') y
    = FTLet (concatF (FCons y t_x g) g') (subFV x (FV y) e_z) t_z p_env'_ez_tz z
            (subFV x (FV y) e') t' z'' p_z''y_e'_t'
        where
          z''_         = fresh_var_excludingF (concatF (FCons x t_x g) g') y
          z''          = z''_ ? lem_in_env_concatF g g' z''_
                              ? lem_in_env_concatF (FCons x t_x g) g' z''_
                              ? lem_fv_bound_in_fenv (concatF (FCons x t_x g) g') e t p_e_t z''_
          p_env'_ez_tz = lem_change_var_ftyp g x t_x g' e_z t_z p_ez_tz y
          p_z''_e'_t'  = lem_change_var_ftyp (concatF (FCons x t_x g) g') z' t_z FEmpty 
                                             (unbind z z' e')  t' p_z'_e'_t'  z''
                                             ? lem_subFV_unbind z z' (FV z'') e'
          p_z''y_e'_t' = lem_change_var_ftyp g x t_x (FCons z'' t_z g') 
                                             (unbind z z'' e') t' p_z''_e'_t' y
                                             ? lem_commute_subFV_unbind x y z z'' e'
lem_change_var_ftyp g x t_x g' e t (FTAnn _ e' _t liqt p_e'_t) y
    = FTAnn (concatF (FCons y t_x g) g') (subFV x (FV y) e') t liqt' p_env'_e'_t
     --                                         ? lem_binds_cons_concatF g g' x t_x
       --                                       ? lem_binds_cons_concatF g g' y t_x
        where
          liqt'       = tsubFV x (FV y) (liqt ? lem_erase_tsubFV x (FV y) liqt)
                                              ? lem_binds_cons_concatF g g' x t_x
                                              ? lem_binds_cons_concatF g g' y t_x
          p_env'_e'_t = lem_change_var_ftyp g x t_x g' e' t p_e'_t y
  
 
{-@ lem_weaken_ftyp :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> e:Expr -> t:FType 
        -> { p_e_t:HasFType | propOf p_e_t == HasFType (concatF g g') e t }
        -> { x:Vname | not (in_envF x g) && not (in_envF x g') } -> t_x:FType
        -> { pf:HasFType | propOf pf == (HasFType (concatF (FCons x t_x g) g') e t) }
           / [ftypSize p_e_t] @-}
lem_weaken_ftyp :: FEnv -> FEnv -> Expr -> FType -> HasFType ->  Vname -> FType -> HasFType
lem_weaken_ftyp g g' e t (FTBC _env b) x t_x  
    = FTBC  (concatF (FCons x t_x g) g') b
lem_weaken_ftyp g g' e t (FTIC _env n) x t_x  
    = FTIC  (concatF (FCons x t_x g) g') n
lem_weaken_ftyp g g' e t p_y_ty@(FTVar1 env y t_y) x t_x 
    = case g' of 
        (FEmpty)           -> FTVar2 (FCons y t_y env) y t_y p_y_ty x t_x
        (FCons _y _ty g'') -> FTVar1 (concatF (FCons x t_x g) g'') y t_y 
                                    -- (g; g' == _g, z:t_z) |- y : t_y
lem_weaken_ftyp g g' e t p_y_ty@(FTVar2 gg y t_y p_gg'_y_ty z t_z) x t_x
    = case g' of
        (FEmpty)           -> FTVar2 (FCons z t_z gg) y t_y p_y_ty x t_x
        (FCons _z _tz g'') -> FTVar2 (concatF (FCons x t_x g) g'') 
                                  (y `withProof` lem_in_env_concatF g g'' y
                                     `withProof` lem_in_env_concatF (FCons x t_x g) g'' y) t_y
                                     (lem_weaken_ftyp g g'' e t p_gg'_y_ty x t_x) z t_z
lem_weaken_ftyp g g' e t (FTPrm _env c)  x t_x 
    = FTPrm (concatF (FCons x t_x g) g') c
lem_weaken_ftyp g g' e t p_e_t@(FTAbs env y t_y e' t' y' p_y'_e'_t') x t_x 
    = FTAbs (concatF (FCons x t_x g) g') y t_y e' t' y'' p_y''x_e'_t'
        where
            y''_         = fresh_varF (concatF (FCons x t_x g) g')
            y''          = y''_ ? lem_in_env_concatF g g' y''_
                                ? lem_in_env_concatF (FCons x t_x g) g' y''_
                                ? lem_fv_bound_in_fenv (concatF g g') e t p_e_t y''_
            p_y''_e'_t'  = lem_change_var_ftyp (concatF g g') y' t_y FEmpty 
                                (unbind y y' e') t' p_y'_e'_t' y''
                                ? lem_subFV_unbind y y' (FV y'') e'
            p_y''x_e'_t' = lem_weaken_ftyp g (FCons y'' t_y g') 
                                (unbind y y'' e') t' p_y''_e'_t' x t_x
lem_weaken_ftyp g g' e t (FTApp env e1 s s' p_e1_ss' e2 p_e2_s)  x t_x  
    = FTApp (concatF (FCons x t_x g) g') e1 s s' p_env'_e1_ss' e2 p_env'_e2_s
        where
          p_env'_e1_ss' = lem_weaken_ftyp g g' e1 (FTFunc s s') p_e1_ss' x t_x
          p_env'_e2_s   = lem_weaken_ftyp g g' e2 s             p_e2_s   x t_x
lem_weaken_ftyp g g' e t p_e_t@(FTLet env e_y t_y p_ey_ty y e' t' y' p_y'_e'_t') x t_x
    = FTLet (concatF (FCons x t_x g) g') e_y t_y p_env'_ey_ty y e' t' y'' p_y''x_e'_t'
        where
            y''_         = fresh_varF (concatF (FCons x t_x g) g')
            y''          = y''_ ? lem_in_env_concatF g g' y''_
                                ? lem_in_env_concatF (FCons x t_x g) g' y''_
                                ? lem_fv_bound_in_fenv (concatF g g') e t p_e_t y''_
            p_env'_ey_ty = lem_weaken_ftyp g g' e_y t_y p_ey_ty x t_x
            p_y''_e'_t'  = lem_change_var_ftyp (concatF g g') y' t_y FEmpty 
                                               (unbind y y' e') t' p_y'_e'_t' y'' 
                                               ? lem_subFV_unbind y y' (FV y'') e'
            p_y''x_e'_t' = lem_weaken_ftyp g (FCons y'' t_y g') 
                                           (unbind y y'' e') t' p_y''_e'_t' x t_x
lem_weaken_ftyp g g' e t (FTAnn _ e' _t liqt p_e'_t)  x t_x  
    = FTAnn (concatF (FCons x t_x g) g') e' t (liqt ? lem_binds_cons_concatF g g' x t_x)
            (lem_weaken_ftyp g g' e' t p_e'_t x t_x)

{-@ lem_weaken_many_ftyp :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> e:Expr -> t:FType -> ProofOf(HasFType g e t)
        -> ProofOf(HasFType (concatF g g') e t) @-}
lem_weaken_many_ftyp :: FEnv -> FEnv -> Expr -> FType -> HasFType -> HasFType
lem_weaken_many_ftyp g FEmpty           e t p_g_e_t = p_g_e_t
lem_weaken_many_ftyp g (FCons x t_x g') e t p_g_e_t
  = lem_weaken_ftyp (concatF g g') FEmpty e t p_g'g_e_t x t_x
      where
        p_g'g_e_t = lem_weaken_many_ftyp g g' e t p_g_e_t
