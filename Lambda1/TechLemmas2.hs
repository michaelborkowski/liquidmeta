{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-} 
{- @ LIQUID "--no-totality" @-} 
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module TechLemmas2 where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import BasicProps
import Typing
import Primitives
import Primitives3
import STLCLemmas
import STLCSoundness
import TechLemmas

-- force these into scope
semantics = (Step, EvalsTo)
typing = (HasBType, HasType, Subtype, WFType, WFEnv)
denotations = (Entails, Denotes, DenotesEnv)

{-@ reflect foo13 @-}
foo13 x = Just x
foo13 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   Mon PM: 476 lines, 431, 
------------------------------------------------------------------------------

-- Note: The technical lemmas lem_change_var_btyp, lem_weaken_btyp
--   are found in STLCLemmas.hs

-- We can alpha-rename a variable anywhere in the environment and recursively alter the type
--   derivation tree. This is the type judgement so there are variables in the types to worry about
{-@ lem_change_var_typ :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
        -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
        -> e:Expr -> t:Type -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t }
        -> { y:Vname | not (in_env y g) && not (in_env y g') }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                           (subFV x (FV y) e) (tsubFV x (FV y) t) &&
                           typSize p_e_t == typSize p'_e_t } / [typSize p_e_t] @-}
lem_change_var_typ :: Env -> Vname -> Type -> Env -> WFEnv -> Expr -> Type 
                -> HasType ->  Vname -> HasType
lem_change_var_typ g x t_x g' p_env_wf e t (TBC _ b) y  
    = TBC (concatE (Cons y t_x g) (esubFV x (FV y) g')) b ? lem_tsubFV_tybc x (FV y) b
lem_change_var_typ g x t_x g' p_env_wf e t (TIC _ n) y  
    = TIC (concatE (Cons y t_x g) (esubFV x (FV y) g')) n ? lem_tsubFV_tyic x (FV y) n
lem_change_var_typ g x t_x g' p_env_wf e t (TVar1 _ z _t) y
    = case g' of 
        (Empty)           -> TVar1 g y t_x ? lem_free_bound_in_env g t_x p_g_tx x
                                           ? toProof ( tsubFV x (FV y) t === t_x )
          where
            (WFEBind _g p_g_wf _x _tx p_g_tx) = p_env_wf
        (Cons _z _ g'')   -> TVar1 (concatE (Cons y t_x g) (esubFV x (FV y) g'')) z (tsubFV x (FV y) t)
lem_change_var_typ g x t_x g' p_env_wf e t (TVar2 _ z _t p_z_t w t_w) y
    = case g' of             -- g''=Emp so x=w and p_z_t :: HasBType(g (FV z) t)
        (Empty)           -> case (x == z) of
                                (True)  -> impossible "it is"
                                (False) -> TVar2 g z t p_z_t  
                                             (y ? lem_free_bound_in_env g t p_g_t y ) t_x
                                             ? toProof ( tsubFV x (FV y) t === t )
                                  where
                                   -- p_z_er_t = lem_typing_hasbtype g (FV z) t p_z_t p_g_wf
                                   (WFEBind g_ p_g_wf _ _ _) = p_env_wf
                                   p_g_t = lem_typing_wf g (FV z) t p_z_t p_g_wf
        (Cons _w _tw g'') -> case (x == z) of
                    (True)  -> TVar2 (concatE (Cons y t_x g) (esubFV x (FV y) g'')) 
                                 (y `withProof` lem_in_env_concat (Cons y t_x g) g'' y)
                                 (tsubFV x (FV y) t) 
                                 (lem_change_var_typ g x t_x g'' p_env'_wf (FV z) t p_z_t y) 
                                 w (tsubFV x (FV y) t_w)
                      where
                        (WFEBind env' p_env'_wf _ _ _) = p_env_wf
                    (False) -> TVar2 (concatE (Cons y t_x g) (esubFV x (FV y) g''))
                                 (z `withProof` lem_in_env_concat (Cons y t_x g) g'' z
                                    `withProof` lem_in_env_concat (Cons x t_x g) g'' z)
                                 (tsubFV x (FV y) t)
                                 (lem_change_var_typ g x t_x g'' p_env'_wf (FV z) t p_z_t y) 
                                 w (tsubFV x (FV y) t_w)
                      where
                        (WFEBind env' p_env'_wf _ _ _) = p_env_wf
lem_change_var_typ g x t_x g' p_env_wf e t (TPrm _ c) y  
    = TPrm (concatE (Cons y t_x g) (esubFV x (FV y) g')) c ? lem_tsubFV_ty x (FV y) c
lem_change_var_typ g x t_x g' p_env_wf e t p_e_t@(TAbs env z t_z p_env_tz e' t' z' p_z'_e'_t') y
    = TAbs (concatE (Cons y t_x g) (esubFV x (FV y) g')) z (tsubFV x (FV y) t_z) 
           p_env'_tz (subFV x (FV y) e') (tsubFV x (FV y) t')  z'' p_z''y_e'_t'
        where
          p_env_t      = lem_typing_wf env e t p_e_t p_env_wf
          p_env'_tz    = lem_change_var_wf g x t_x g' t_z p_env_tz y
          p_e_er_t     = lem_typing_hasbtype env e t p_e_t p_env_wf
          z''_         = fresh_var_excluding (concatE (Cons x t_x g) g') y
          z''          = z''_ ? lem_in_env_concat g g' z''_
                              ? lem_in_env_concat (Cons x t_x g) g' z''_
                              ? lem_fv_bound_in_benv (erase_env (concatE (Cons x t_x g) g')) e (erase t)
                                                      p_e_er_t z''_
                              ? lem_free_bound_in_env env t p_env_t z''_
          p_z'env_wf   = WFEBind env p_env_wf z'  t_z p_env_tz
          p_z''env_wf  = WFEBind env p_env_wf z'' t_z p_env_tz
          p_z''_e'_t'  = lem_change_var_typ (concatE (Cons x t_x g) g') z' t_z Empty p_z'env_wf
                                 (unbind z z' e') (unbindT z z' t') p_z'_e'_t' z''
                                 ? lem_subFV_unbind z z' (FV z'') e'                                  
                                 ? lem_tsubFV_unbindT z z' (FV z'') t'
          p_z''y_e'_t' = lem_change_var_typ g x t_x (Cons z'' t_z g') p_z''env_wf (unbind z z'' e') 
                                 (unbindT z z'' t') p_z''_e'_t' y 
                                 ? lem_commute_subFV_unbind x y z z'' e'
                                 ? lem_commute_tsubFV_unbindT x y z z'' t'
lem_change_var_typ g x t_x g' p_env_wf e t (TApp env e1 z t1 t2 p_env_e1_t1t2 e2 p_env_e2_t1) y
    = TApp (concatE (Cons y t_x g) (esubFV x (FV y) g')) (subFV x (FV y) e1) 
           z (tsubFV x (FV y) t1) (tsubFV x (FV y) t2) p_env'_e1_t1t2 
           (subFV x (FV y) e2) p_env'_e2_t1
        where
          p_env'_e1_t1t2 = lem_change_var_typ g x t_x g' p_env_wf e1 (TFunc z t1 t2) p_env_e1_t1t2 y
          p_env'_e2_t1   = lem_change_var_typ g x t_x g' p_env_wf e2 t1 p_env_e2_t1 y 
lem_change_var_typ g x t_x g' p_env_wf e t 
                   p_e_t@(TLet env e_z t_z p_env_ez_tz z e' t' p_env_t' z' p_z'env_e'_t') y
    = TLet (concatE (Cons y t_x g) (esubFV x (FV y) g')) (subFV x (FV y) e_z) (tsubFV x (FV y) t_z)
           p_env'_ez_tz z (subFV x (FV y) e') (tsubFV x (FV y) t') p_env'_t' z'' p_z''env'_e'_t'
        where
          p_env_t         = lem_typing_wf env e t p_e_t p_env_wf
          p_env_tz        = lem_typing_wf env e_z t_z p_env_ez_tz p_env_wf
          p_env'_t'       = lem_change_var_wf g x t_x g' t' p_env_t' y
          p_e_er_t        = lem_typing_hasbtype env e t p_e_t p_env_wf
          z''_            = fresh_var_excluding (concatE (Cons x t_x g) g') y
          z''             = z''_ ? lem_in_env_concat g g' z''_
                                 ? lem_in_env_concat (Cons x t_x g) g' z''_
                                 ? lem_fv_bound_in_benv (erase_env (concatE (Cons x t_x g) g')) e (erase t) 
                                                        p_e_er_t z''_
                                 ? lem_free_bound_in_env env t p_env_t z''_
          p_z'env_wf      = WFEBind env p_env_wf z'  t_z p_env_tz
          p_z''env_wf     = WFEBind env p_env_wf z'' t_z p_env_tz
          p_env'_ez_tz    = lem_change_var_typ g x t_x g' p_env_wf e_z t_z p_env_ez_tz y 
          p_z''env_e'_t'  = lem_change_var_typ (concatE (Cons x t_x g) g') z' t_z Empty p_z'env_wf
                                    (unbind z z' e') (unbindT z z' t') p_z'env_e'_t' z''
                                    ? lem_subFV_unbind z z' (FV z'') e'
                                    ? lem_tsubFV_unbindT z z' (FV z'') t'
          p_z''env'_e'_t' = lem_change_var_typ g x t_x (Cons z'' t_z g') p_z''env_wf (unbind z z'' e') 
                                    (unbindT z z'' t') p_z''env_e'_t' y
                                    ? lem_commute_subFV_unbind x y z z'' e'
                                    ? lem_commute_tsubFV_unbindT x y z z'' t'
lem_change_var_typ g x t_x g' p_env_wf e t (TAnn env e' _t p_env_e'_t) y
    = TAnn (concatE (Cons y t_x g) (esubFV x (FV y) g')) (subFV x (FV y) e')  
           (tsubFV x (FV y) t) p_env'_e'_t
        where
          p_env'_e'_t = lem_change_var_typ g x t_x g' p_env_wf e' t p_env_e'_t y
lem_change_var_typ g x t_x g' p_env_wf e t p_e_t@(TSub env _e s p_env_e_s _t p_env_t p_env_s_t) y
    = TSub (concatE (Cons y t_x g) (esubFV x (FV y) g')) (subFV x (FV y) e) (tsubFV x (FV y) s) 
           p_env'_e_s (tsubFV x (FV y) t) p_env'_t p_env'_s_t
        where
          p_env_s    = lem_typing_wf env e s p_env_e_s p_env_wf
          p_env'_e_s = lem_change_var_typ g x t_x g' p_env_wf e s p_env_e_s y
          p_env'_t   = lem_change_var_wf g x t_x g' t p_env_t y
          p_env'_s_t = lem_change_var_subtype g x t_x g' p_env_wf s p_env_s t p_env_t p_env_s_t y


{-@ lem_weaken_typ :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE g g') e t }
        -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) } -> t_x:Type 
        -> { p'_e_t:HasType | (propOf p'_e_t == HasType (concatE (Cons x t_x g) g') e t) } / [typSize p_e_t] @-}
--                              typSize p'_e_t == typSize p_e_t } @-}
lem_weaken_typ :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> Vname -> Type -> HasType          
lem_weaken_typ g g' p_env_wf e t (TBC _g b)      x t_x = TBC  (concatE (Cons x t_x g) g') b
lem_weaken_typ g g' p_env_wf e t (TIC _g n)      x t_x = TIC  (concatE (Cons x t_x g) g') n
lem_weaken_typ g g' p_env_wf e t p_y_ty@(TVar1 gg y t_y) x_ t_x -- env == concatE g (Cons y t_y g'') = g;g' 
    = case g' of 
        (Empty)           -> TVar2 (Cons y t_y gg) (y ? lem_free_bound_in_env gg t p_gg_ty y) t_y p_y_ty x t_x 
          where
            x = x_ ? lem_in_env_concat g g' x_
                   ? lem_in_env_concat gg (Cons y t_y Empty) x_
                   ? lem_free_bound_in_env gg t_y p_gg_ty x_
            (WFEBind _gg p_gg_wf _y _ty p_gg_ty) = p_env_wf
        (Cons _y _ty g'') -> TVar1 (concatE (Cons x_ t_x g) g'') y t_y 
-- (g; g' == _g, z:t_z) |- y : t_y
lem_weaken_typ g g' p_env_wf e t p_y_ty@(TVar2 gg y t_y p_gg_y_ty z t_z) x_ t_x
    = case g' of
        (Empty)           -> TVar2 (concatE g g') y t_y p_y_ty x t_x 
          where
            x = x_ ? lem_in_env_concat g g' x_ 
                   ? lem_in_env_concat gg (Cons z t_z Empty) x_
                   ? lem_free_bound_in_env gg t_y p_gg_ty x_
            (WFEBind _gg p_gg_wf _ _ _) = p_env_wf
            p_gg_ty = lem_typing_wf gg (FV y) t_y p_gg_y_ty p_gg_wf
        (Cons _z _tz g'') -> TVar2 (concatE (Cons x t_x g) g'') 
                                   (y `withProof` lem_in_env_concat g g'' y
                                      `withProof` lem_in_env_concat (Cons x t_x g) g'' y) 
                                   t_y p_gxg_y_ty z t_z
          where
            x = x_ ? lem_in_env_concat gg (Cons z t_z Empty) x_
            (WFEBind _gg p_gg_wf _ _ _) = p_env_wf 
            p_gxg_y_ty = lem_weaken_typ g g'' p_gg_wf e t p_gg_y_ty x t_x
lem_weaken_typ g g' p_env_wf e t (TPrm _g c)     x t_x = TPrm (concatE (Cons x t_x g) g') c
lem_weaken_typ g g' p_env_wf e t p_e_t@(TAbs env y t_y p_gg'_ty e' t' y' p_y'_e'_t') x t_x
    = TAbs (concatE (Cons x t_x g) g') y t_y p_gxg'_ty e' t' y'' p_y''x_e'_t'
        where
            p_env_t      = lem_typing_wf env e t p_e_t p_env_wf
            p_gxg'_ty    = lem_weaken_wf g g' t_y p_gg'_ty x t_x -- p_g_tx
            p_e_er_t     = lem_typing_hasbtype env e t p_e_t p_env_wf
            y''_         = fresh_var (concatE (Cons x t_x g) g')
            y''          = y''_ ? lem_in_env_concat g g' y''_
                                ? lem_in_env_concat (Cons x t_x g) g' y''_
                                ? lem_fv_bound_in_benv (erase_env (concatE g g')) e (erase t) 
                                                       p_e_er_t y''_
                                ? lem_free_bound_in_env env t p_env_t y''_
            p_y'env_wf   = WFEBind env p_env_wf y'  t_y p_gg'_ty
            p_y''env_wf  = WFEBind env p_env_wf y'' t_y p_gg'_ty
            p_y''_e'_t'  = lem_change_var_typ (concatE g g') y' t_y Empty p_y'env_wf (unbind y y' e') 
                                              (unbindT y y' t') p_y'_e'_t' y'' 
                                              ? lem_subFV_unbind   y y' (FV y'') e' 
                                              ? lem_tsubFV_unbindT y y' (FV y'') t'
            p_y''x_e'_t' = lem_weaken_typ g (Cons y'' t_y g') p_y''env_wf (unbind y y'' e') 
                                          (unbindT y y'' t') p_y''_e'_t' x t_x
lem_weaken_typ g g' p_env_wf e t (TApp env e1 z s s' p_env_e1_ss' e2 p_env_e2_s) x t_x 
    = TApp (concatE (Cons x t_x g) g') e1 z s s' p_env'_e1_ss' e2 p_env'_e2_s
        where
          p_env'_e1_ss' = lem_weaken_typ g g' p_env_wf e1 (TFunc z s s') p_env_e1_ss' x t_x
          p_env'_e2_s   = lem_weaken_typ g g' p_env_wf e2 s              p_env_e2_s   x t_x
lem_weaken_typ g g' p_env_wf e t 
               p_e_t@(TLet env e_y t_y p_env_ey_ty y e' t' p_env_t' y' p_y'env_e'_t') x t_x
    = TLet (concatE (Cons x t_x g) g') e_y t_y p_env'_ey_ty y e' t' p_env'_t' y'' p_y''env'_e'_t'
        where
          p_env_t         = lem_typing_wf env e t p_e_t p_env_wf
          p_env_ty        = lem_typing_wf env e_y t_y p_env_ey_ty p_env_wf
          p_env'_t'       = lem_weaken_wf g g' t' p_env_t' x t_x
          p_e_er_t        = lem_typing_hasbtype env e t p_e_t p_env_wf
          y''_            = fresh_var (concatE (Cons x t_x g) g') 
          y''             = y''_ ? lem_in_env_concat g g' y''_
                                 ? lem_in_env_concat (Cons x t_x g) g' y''_
                                 ? lem_fv_bound_in_benv (erase_env (concatE g g')) e (erase t) 
                                                        p_e_er_t y''_
                                 ? lem_free_bound_in_env env t p_env_t y''_
          p_y'env_wf      = WFEBind env p_env_wf y'  t_y p_env_ty
          p_y''env_wf     = WFEBind env p_env_wf y'' t_y p_env_ty
          p_env'_ey_ty    = lem_weaken_typ g g' p_env_wf e_y t_y p_env_ey_ty x t_x
          p_y''env_e'_t'  = lem_change_var_typ (concatE g g') y' t_y Empty p_y'env_wf (unbind y y' e') 
                                               (unbindT y y' t') p_y'env_e'_t' y''
                                               ? lem_subFV_unbind   y y' (FV y'') e' 
                                               ? lem_tsubFV_unbindT y y' (FV y'') t'
          p_y''env'_e'_t' = lem_weaken_typ g (Cons y'' t_y g') p_y''env_wf (unbind y y'' e') 
                                           (unbindT y y'' t') p_y''env_e'_t' x t_x 
lem_weaken_typ g g' p_env_wf e t (TAnn env e' _t p_env_e'_t) x t_x
    = TAnn (concatE (Cons x t_x g) g') e' t p_env'_e'_t
        where
          p_env'_e'_t = lem_weaken_typ g g' p_env_wf e' t p_env_e'_t x t_x
lem_weaken_typ g g' p_env_wf e t (TSub env _e s p_env_e_s _t p_env_t p_env_s_t) x t_x
    = TSub (concatE (Cons x t_x g) g') e s p_env'_e_s t p_env'_t p_env'_s_t 
        where
          p_env_s    = lem_typing_wf      env e s p_env_e_s p_env_wf
          p_env'_e_s = lem_weaken_typ     g g' p_env_wf e s p_env_e_s x t_x
          p_env'_t   = lem_weaken_wf      g g' t p_env_t x t_x 
          p_env'_s_t = lem_weaken_subtype g g' p_env_wf s p_env_s t p_env_t p_env_s_t x t_x

{-@ lem_weaken_many_typ :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE g g')) -> e:Expr -> t:Type -> ProofOf(HasType g e t) 
      -> ProofOf(HasType (concatE g g') e t) @-}
lem_weaken_many_typ :: Env -> Env -> WFEnv -> Expr -> Type -> HasType -> HasType
lem_weaken_many_typ g Empty           p_g_wf    e t p_g_e_t = p_g_e_t
lem_weaken_many_typ g (Cons x t_x g') p_xenv_wf e t p_g_e_t 
  = lem_weaken_typ (concatE g g') Empty p_env_wf e t p_gg'_e_t x t_x
      where
        (WFEBind _ p_env_wf _ _ _) = p_xenv_wf
        p_gg'_e_t = lem_weaken_many_typ g g' p_env_wf e t p_g_e_t 

{-@ lem_change_var_subtype :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
      -> t:Type  -> ProofOf(WFType (concatE (Cons x t_x g) g') t) 
      -> t':Type -> ProofOf(WFType (concatE (Cons x t_x g) g') t')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE (Cons x t_x g) g') t t' } 
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                         (tsubFV x (FV y) t) (tsubFV x (FV y) t') &&
                         subtypSize p_t_t' == subtypSize p'_t_t' } / [subtypSize p_t_t'] @-}
lem_change_var_subtype :: Env -> Vname -> Type -> Env -> WFEnv -> Type -> WFType -> Type -> WFType
                              -> Subtype -> Vname -> Subtype
lem_change_var_subtype g x t_x g' p_env_wf t p_env_t t' p_env_t' 
                       (SBase env z1 b p1 z2 p2 w pf_wenv_ent_p2) y_
    = SBase env' z1 b p1' z2 p2' w' pf_w'env'_ent_p2 
        where
          w'               = fresh_var_excluding (concatE (Cons x t_x g) g') y_
          y                = y_ ? lem_in_env_concat g g' y_
                                ? lem_in_env_concat g (Cons w' t g') y_
                                ? lem_in_env_concat (Cons x t_x g) g' y_
          env'             = (concatE (Cons y t_x g) (esubFV x (FV y) g'))
          p1'              = subFV x (FV y) p1
          p2'              = subFV x (FV y) p2
          p_wenv_wf        = WFEBind env p_env_wf w  t p_env_t
          p_w'env_wf       = WFEBind env p_env_wf w' t p_env_t
          pf_w'env_ent_p2  = lem_change_var_ent (concatE (Cons x t_x g) g') w t Empty p_wenv_wf
                                 (unbind z2 w p2 ? lem_free_subset_binds env t' p_env_t') 
                                 pf_wenv_ent_p2 
                                 (w' ? lem_free_bound_in_env env t' p_env_t' w')
                                 ? lem_subFV_unbind z2 w (FV w') p2
          pf_w'env'_ent_p2 = lem_change_var_ent g x t_x (Cons w' t g') 
                                 p_w'env_wf (unbind z2 w' p2) pf_w'env_ent_p2 y 
                                 ? lem_commute_subFV_unbind x y z2 w' p2 
lem_change_var_subtype g x t_x g' p_env_wf ft1 p_env_ft1 ft2 p_env_ft2 
                       (SFunc env z1 s1 z2 s2 p_env_s2_s1 t1 t2 w p_wenv_t1_t2) y_
    = case p_env_ft1 of
        (WFFunc _ _ _ p_env_s1 _ w1 p_w1'env_t1) -> case p_env_ft2 of
          (WFFunc _ _ _ p_env_s2 _ w2 p_w2env_t2) 
            -> SFunc env' z1 (tsubFV x (FV y) s1) z2 (tsubFV x (FV y) s2) p_env'_s2_s1 
                     (tsubFV x (FV y) t1) (tsubFV x (FV y) t2) w'
                     p_w'env'_t1_t2
                 where
                   w'             = fresh_var_excluding (concatE (Cons x t_x g) g') y_
                   y              = y_ ? lem_in_env_concat g g' y_
                                       ? lem_in_env_concat g (Cons w' s2 g') y_
                                       ? lem_in_env_concat (Cons x t_x g) g' y_
                   env'           = (concatE (Cons y t_x g) (esubFV x (FV y) g'))
                   p_wenv_wf      = WFEBind env p_env_wf w  s2 p_env_s2
                   p_w'env_wf     = WFEBind env p_env_wf w' s2 p_env_s2
                   p_w1env_t1     = lem_subtype_in_env_wf env Empty w1 s2 s1 p_env_s2_s1 
                                            (unbindT z1 w1 t1) p_w1'env_t1
                   p_wenv_t1      = lem_change_var_wf (concatE (Cons x t_x g) g') w1 s2 Empty
                                            (unbindT z1 w1 t1) p_w1env_t1 w
                                            ? lem_tsubFV_unbindT z1 w1 (FV w) t1
                   p_wenv_t2      = lem_change_var_wf (concatE (Cons x t_x g) g') w2 s2 Empty 
                                            (unbindT z2 w2 t2) p_w2env_t2 w
                                            ? lem_tsubFV_unbindT z2 w2 (FV w) t2
                   p_w'env_t1     = lem_change_var_wf (concatE (Cons x t_x g) g') w1 s2 Empty
                                            (unbindT z1 w1 t1) p_w1env_t1 w'
                                            ? lem_tsubFV_unbindT z1 w1 (FV w') t1
                   p_w'env_t2     = lem_change_var_wf (concatE (Cons x t_x g) g') w2 s2 Empty 
                                            (unbindT z2 w2 t2) p_w2env_t2 w'
                                            ? lem_tsubFV_unbindT z2 w2 (FV w') t2
                   p_env'_s2_s1   = lem_change_var_subtype g x t_x g' p_env_wf s2 p_env_s2 s1 p_env_s1
                                                           p_env_s2_s1 y
                   p_w'env_t1_t2  = lem_change_var_subtype (concatE (Cons x t_x g) g') w s2 Empty p_wenv_wf
                                            (unbindT z1 w t1) p_wenv_t1 (unbindT z2 w t2) p_wenv_t2
                                            p_wenv_t1_t2 
                                            ( w' ? lem_free_bound_in_env env ft1 p_env_ft1 w'
                                                 ? lem_free_bound_in_env env ft2 p_env_ft2 w' )
                                            ? lem_tsubFV_unbindT z1 w (FV w') t1
                                            ? lem_tsubFV_unbindT z2 w (FV w') t2
                   p_w'env'_t1_t2 = lem_change_var_subtype g x t_x (Cons w' s2 g') p_w'env_wf
                                            (unbindT z1 w' t1) p_w'env_t1 (unbindT z2 w' t2) p_w'env_t2
                                            p_w'env_t1_t2 y
                                            ? lem_commute_tsubFV_unbindT x y z1 w' t1
                                            ? lem_commute_tsubFV_unbindT x y z2 w' t2
lem_change_var_subtype g x t_x g' p_env_wf t p_env_t t2 p_env_t2
                       (SWitn env v_z t_z p_env_vz_tz _t z t' p_env_t_t'vz) y_ 
    = case p_env_t2 of
        (WFExis _ _ _ p_env_tz _ z' p_z'env_t')
          -> SWitn env' (subFV x (FV y) v_z) (tsubFV x (FV y) t_z) p_env'_vz_tz
                   (tsubFV x (FV y) t) z (tsubFV x (FV y) t') p_env'_t_t'vz
               where
                   y             = y_ ? lem_in_env_concat g g' y_
                                      ? lem_in_env_concat (Cons x t_x g) g' y_
                   env'          = (concatE (Cons y t_x g) (esubFV x (FV y) g'))
                   p_z'env_wf    = WFEBind env p_env_wf z' t_z p_env_tz
                   p_env_t'vz    = lem_subst_wf (concatE (Cons x t_x g) g') Empty 
                                                z' v_z t_z p_env_vz_tz p_z'env_wf 
                                                (unbindT z z' t') p_z'env_t'
                   p_env'_vz_tz  = lem_change_var_typ g x t_x g' p_env_wf v_z t_z p_env_vz_tz y    
                                                ? lem_tsubFV_unbindT z z' v_z t'
                   p_env'_t_t'vz = lem_change_var_subtype g x t_x g' p_env_wf t p_env_t
                                                (tsubBV z v_z t') p_env_t'vz p_env_t_t'vz y
                                                ? lem_commute_tsubFV_tsubBV z v_z x (FV y) t'
lem_change_var_subtype g x t_x g' p_env_wf t1 p_env_t1 t' p_env_t'
                       (SBind env z t_z t _t' z' p_z'env_t_t') y_
    = case p_env_t1 of 
        (WFExis _ _ _ p_env_tz _ w p_wenv_t)
          -> SBind env' z (tsubFV x (FV y) t_z) (tsubFV x (FV y) t) (tsubFV x (FV y) t') 
                   z'' p_z''env'_t_t'
               where
                   z''_           = fresh_var_excluding (concatE (Cons x t_x g) g') y_
                   z''            = z''_ ? lem_free_bound_in_env env t1 p_env_t1 z''_
                                         ? lem_free_bound_in_env env t' p_env_t' z''_
                   y              = y_ ? lem_in_env_concat g g' y_
                                       -- ? lem_in_env_concat g (Cons z'' t_z g') y_
                                       ? lem_in_env_concat (Cons x t_x g) g' y_
                   env'           = (concatE (Cons y t_x g) (esubFV x (FV y) g'))
                   p_z'env_wf     = WFEBind env p_env_wf z'  t_z p_env_tz
                   p_z''env_wf    = WFEBind env p_env_wf z'' t_z p_env_tz
                   p_z'env_t      = lem_change_var_wf env w t_z Empty (unbindT z w t) p_wenv_t z'
                                            ? lem_tsubFV_unbindT z w (FV z') t
                   p_z''env_t     = lem_change_var_wf env w t_z Empty (unbindT z w t) p_wenv_t z''
                                            ? lem_tsubFV_unbindT z w (FV z'') t
                   p_z'env_t'     = lem_weaken_wf env Empty t' p_env_t' z'  t_z
                   p_z''env_t'    = lem_weaken_wf env Empty t' p_env_t' z'' t_z
                   p_z''env_t_t'  = lem_change_var_subtype (concatE (Cons x t_x g) g') z' t_z Empty
                                            p_z'env_wf (unbindT z z' t) p_z'env_t t' p_z'env_t' 
                                            p_z'env_t_t' z'' 
                                            ? lem_tsubFV_unbindT z z' (FV z'') t
                                            ? lem_free_bound_in_env env t' p_env_t' z'
                                            ? toProof ( tsubFV z' (FV z'') t' === t' )
                   p_z''env'_t_t' = lem_change_var_subtype g x t_x (Cons z'' t_z g') p_z''env_wf
                                            (unbindT z z'' t) p_z''env_t t' p_z''env_t' p_z''env_t_t' y
                                            ? lem_commute_tsubFV_unbindT x y z z'' t

{-@ lem_weaken_subtype :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE g g'))
      -> t:Type  -> ProofOf(WFType (concatE g g') t) 
      -> t':Type -> ProofOf(WFType (concatE g g') t')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE g g') t t' }
      -> { x:Vname | not (in_env x g) && not (in_env x g') } -> t_x:Type
      -> ProofOf(Subtype (concatE (Cons x t_x g) g') t t') / [subtypSize p_t_t'] @-}
lem_weaken_subtype :: Env -> Env -> WFEnv -> Type -> WFType -> Type -> WFType
                              -> Subtype -> Vname -> Type -> Subtype
lem_weaken_subtype g g' p_env_wf t p_env_t t' p_env_t' 
                       (SBase env z1 b p1 z2 p2 w pf_wenv_ent_p2) x_ t_x
    = SBase env' z1 b p1 z2 p2 w' pf_w'env'_ent_p2 
        where
          x                = x_ ? lem_in_env_concat g g' x_
          env'             = concatE (Cons x t_x g) g'
          w'               = fresh_var (concatE (Cons x t_x g) g')
          p_wenv_wf        = WFEBind env p_env_wf w  t p_env_t
          p_w'env_wf       = WFEBind env p_env_wf 
                                 (w' ? lem_in_env_concat g g' w'
                                     ? lem_in_env_concat (Cons x t_x g) g' w')
                                 t p_env_t
          pf_w'env_ent_p2  = lem_change_var_ent (concatE g g') w t Empty p_wenv_wf
                                 (unbind z2 w p2 ? lem_free_subset_binds env t' p_env_t') 
                                 pf_wenv_ent_p2 
                                 (w' ? lem_free_bound_in_env env t' p_env_t' w')
                                 ? lem_subFV_unbind z2 w (FV w') p2
          pf_w'env'_ent_p2 = lem_weaken_ent g (Cons w' t g') 
                                 p_w'env_wf (unbind z2 w' p2) pf_w'env_ent_p2 x t_x
lem_weaken_subtype g g' p_env_wf ft1 p_env_ft1 ft2 p_env_ft2 
                       (SFunc env z1 s1 z2 s2 p_env_s2_s1 t1 t2 w p_wenv_t1_t2) x_ t_x
    = case p_env_ft1 of       -- env == concatE g g'
        (WFFunc _ _ _ p_env_s1 _ w1 p_w1'env_t1) -> case p_env_ft2 of
          (WFFunc _ _ _ p_env_s2 _ w2 p_w2env_t2) 
            -> SFunc env' z1 s1 z2 s2 p_env'_s2_s1 t1 t2 w' p_w'env'_t1_t2
                 where
                   x              = x_ ? lem_in_env_concat g g' x_
                   env'           = concatE (Cons x t_x g) g'
                   w'_            = fresh_var (concatE (Cons x t_x g) g') 
                   w'             = w'_ ? lem_in_env_concat g g' w'_
                                        ? lem_in_env_concat (Cons x t_x g) g' w'_
                   p_wenv_wf      = WFEBind env p_env_wf w  s2 p_env_s2
                   p_w'env_wf     = WFEBind env p_env_wf  w'
                                            s2 p_env_s2
                   p_w1env_t1     = lem_subtype_in_env_wf env Empty w1 s2 s1 p_env_s2_s1 
                                            (unbindT z1 w1 t1) p_w1'env_t1
                   p_wenv_t1      = lem_change_var_wf env w1 s2 Empty
                                            (unbindT z1 w1 t1) p_w1env_t1 w
                                            ? lem_tsubFV_unbindT z1 w1 (FV w) t1
                   p_wenv_t2      = lem_change_var_wf env w2 s2 Empty 
                                            (unbindT z2 w2 t2) p_w2env_t2 w
                                            ? lem_tsubFV_unbindT z2 w2 (FV w) t2
                   p_w'env_t1     = lem_change_var_wf env w1 s2 Empty
                                            (unbindT z1 w1 t1) p_w1env_t1 w'
                                            ? lem_tsubFV_unbindT z1 w1 (FV w') t1
                   p_w'env_t2     = lem_change_var_wf env w2 s2 Empty 
                                            (unbindT z2 w2 t2) p_w2env_t2 w'
                                            ? lem_tsubFV_unbindT z2 w2 (FV w') t2
                   p_env'_s2_s1   = lem_weaken_subtype g g' p_env_wf s2 p_env_s2 s1 p_env_s1
                                                           p_env_s2_s1 x t_x
                   p_w'env_t1_t2  = lem_change_var_subtype env w s2 Empty p_wenv_wf
                                            (unbindT z1 w t1) p_wenv_t1 (unbindT z2 w t2) p_wenv_t2
                                            p_wenv_t1_t2 
                                            ( w' ? lem_free_bound_in_env env ft1 p_env_ft1 w'
                                                 ? lem_free_bound_in_env env ft2 p_env_ft2 w' )
                                            ? lem_tsubFV_unbindT z1 w (FV w') t1
                                            ? lem_tsubFV_unbindT z2 w (FV w') t2
                   p_w'env'_t1_t2 = lem_weaken_subtype g (Cons w' s2 g') p_w'env_wf
                                            (unbindT z1 w' t1) p_w'env_t1 (unbindT z2 w' t2) p_w'env_t2
                                            p_w'env_t1_t2 x t_x
lem_weaken_subtype g g' p_env_wf t p_env_t t2 p_env_t2
                   (SWitn env v_z t_z p_env_vz_tz _t z t' p_env_t_t'vz) x_ t_x 
    = case p_env_t2 of
        (WFExis _ _ _ p_env_tz _ z' p_z'env_t')
          -> SWitn env' v_z t_z p_env'_vz_tz t z t' p_env'_t_t'vz
               where
                   x             = x_ ? lem_in_env_concat g g' x_
                   env'          = concatE (Cons x t_x g) g'
                   p_z'env_wf    = WFEBind env p_env_wf z' t_z p_env_tz
                   p_env_t'vz    = lem_subst_wf (concatE g g') Empty z' v_z t_z p_env_vz_tz p_z'env_wf 
                                                (unbindT z z' t') p_z'env_t'
                   p_env'_vz_tz  = lem_weaken_typ g g' p_env_wf v_z t_z p_env_vz_tz x t_x
                                                ? lem_tsubFV_unbindT z z' v_z t'
                   p_env'_t_t'vz = lem_weaken_subtype g g' p_env_wf t p_env_t
                                                (tsubBV z v_z t') p_env_t'vz p_env_t_t'vz x t_x
lem_weaken_subtype g g' p_env_wf t1 p_env_t1 t' p_env_t'
                   (SBind env z t_z t _t' z' p_z'env_t_t') x_ t_x
    = case p_env_t1 of 
        (WFExis _ _ _ p_env_tz _ w p_wenv_t)
          -> SBind env' z t_z t t' z'' p_z''env'_t_t'
               where
                   x              = x_ ? lem_in_env_concat g g' x_
                   z''_           = fresh_var (concatE (Cons x t_x g) g') 
                   z''            = z''_ ? lem_in_env_concat g g' z''_
                                         ? lem_in_env_concat (Cons x t_x g) g' z''_
                                         ? lem_free_bound_in_env env t1 p_env_t1 z''_
                                         ? lem_free_bound_in_env env t' p_env_t' z''_
                   env'           = concatE (Cons x t_x g) g'
                   p_z'env_wf     = WFEBind env p_env_wf z'  t_z p_env_tz
                   p_z''env_wf    = WFEBind env p_env_wf z'' t_z p_env_tz
                   p_z'env_t      = lem_change_var_wf env w t_z Empty (unbindT z w t) p_wenv_t z'
                                            ? lem_tsubFV_unbindT z w (FV z') t
                   p_z''env_t     = lem_change_var_wf env w t_z Empty (unbindT z w t) p_wenv_t z''
                                            ? lem_tsubFV_unbindT z w (FV z'') t
                   p_z'env_t'     = lem_weaken_wf env Empty t' p_env_t' z'  t_z
                   p_z''env_t'    = lem_weaken_wf env Empty t' p_env_t' z'' t_z
                   p_z''env_t_t'  = lem_change_var_subtype (concatE g g') z' t_z Empty
                                            p_z'env_wf (unbindT z z' t) p_z'env_t t' p_z'env_t' 
                                            p_z'env_t_t' z'' 
                                            ? lem_tsubFV_unbindT z z' (FV z'') t
                                            ? lem_free_bound_in_env env t' p_env_t' z'
                                            ? toProof ( tsubFV z' (FV z'') t' === t' )
                   p_z''env'_t_t' = lem_weaken_subtype g (Cons z'' t_z g') p_z''env_wf
                                            (unbindT z z'' t) p_z''env_t t' p_z''env_t' p_z''env_t_t' x t_x

{-@ lem_sub_refl :: g:Env -> t:Type -> ProofOf(WFType g t) -> ProofOf(WFEnv g) -> ProofOf(Subtype g t t) @-}
lem_sub_refl :: Env -> Type -> WFType -> WFEnv -> Subtype
lem_sub_refl g t (WFRefn _g x b p y pf_p_bl) p_g_wf-- t = b{x:p}
    = SBase g x b p x p y (EntPred (Cons y (TRefn b x p) g) (unbind x y p) eval_thp_func)
        where
          {-@ eval_thp_func :: th':CSubst -> ProofOf(DenotesEnv (Cons y (TRefn b x p) g) th') 
                                          -> ProofOf(EvalsTo (csubst th' (unbind x y p)) (Bc True)) @-}
          eval_thp_func :: CSubst -> DenotesEnv -> EvalsTo
          eval_thp_func th' den_yg_th' = case den_yg_th' of 
            (DEmp)                                 -> impossible "Cons y t g != Empty"
            (DExt g th den_g_th _y _t v den_tht_v) -> case den_tht_v of 
              (DRefn _b _x _thp _v pf_v_b ev_thpv_tt) -> ev_thpv_tt 
                ? lem_subFV_unbind x y v p
                ? lem_ctsubst_refn th b x p
                ? lem_csubst_subBV x v (BTBase b) pf_v_b th p
              (_)                                     -> impossible ("by lemma" ? lem_ctsubst_refn th b x p)
lem_sub_refl g t (WFFunc _g x t_x p_g_tx t' y p_yg_t') p_g_wf -- t = (x:t_x -> t')
    = SFunc g x t_x x t_x p_tx_tx t' t' y p_t'_t'
        where
          p_yg_wf = WFEBind g p_g_wf y t_x p_g_tx
          p_tx_tx = lem_sub_refl g t_x p_g_tx p_g_wf
          p_t'_t' = lem_sub_refl (Cons y t_x g) (unbindT x y t') p_yg_t' p_yg_wf
lem_sub_refl g t p_g_t@(WFExis _g x t_x p_g_tx t' y p_yg_t') p_g_wf -- t = (\exists x:t_x. t')
    = SBind g x t_x t' (TExists x t_x t' ? lem_tfreeBV_empty g t p_g_t p_g_wf)
            (y ? lem_free_bound_in_env g t p_g_t y) p_yg_t'_ext'
        where
          p_y_tx       = TVar1 g y t_x
          p_yg_wf      = WFEBind g p_g_wf y t_x p_g_tx
          p_yg_t'_t'   = lem_sub_refl (Cons y t_x g) (unbindT x y t') p_yg_t' p_yg_wf
          p_yg_t'_ext' = SWitn (Cons y t_x g) (FV y) t_x p_y_tx (unbindT x y t') 
                               x t' p_yg_t'_t'
          

{-@ lem_witness_sub :: g:Env -> v_x:Value -> t_x:Type -> ProofOf(HasType g v_x t_x) -> ProofOf(WFEnv g)
        -> x:Vname -> t':Type -> { y:Vname | not (in_env y g) && not (Set_mem y (free t')) }
        -> ProofOf(WFType (Cons y t_x g) (unbindT x y t'))
        -> ProofOf(Subtype g (tsubBV x v_x t') (TExists x t_x t')) @-}
lem_witness_sub :: Env -> Expr -> Type -> HasType -> WFEnv -> Vname -> Type 
                       -> Vname -> WFType -> Subtype
lem_witness_sub g v_x t_x p_vx_tx p_g_wf x t' y p_yg_t' 
  = SWitn g v_x t_x p_vx_tx (tsubBV x v_x t') x t' p_t'vx_t'vx
      where
      p_g_tx      = lem_typing_wf g v_x t_x p_vx_tx p_g_wf
      p_yg_wf     = WFEBind g p_g_wf y t_x p_g_tx
      p_g_t'vx    = lem_subst_wf g Empty y v_x t_x p_vx_tx p_yg_wf (unbindT x y t') p_yg_t'
                                 ? lem_tsubFV_unbindT x y v_x t'
      p_t'vx_t'vx = lem_sub_refl g (tsubBV x v_x t') p_g_t'vx p_g_wf

-- -- -- -- -- -- -- -- -- -- -- ---
-- Part of the Substitution Lemma --
-- -- -- -- -- -- -- -- -- -- -- ---

{-@ lem_subst_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
            -> t_x:Type -> ProofOf(HasType g v_x t_x) 
            -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> t:Type 
            -> { p_env_t:WFType | propOf p_env_t == WFType (concatE (Cons x t_x g) g') t }
            -> ProofOf(WFType (concatE g (esubFV x v_x g')) (tsubFV x v_x t)) / [wftypSize p_env_t] @-}
lem_subst_wf :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv -> Type -> WFType -> WFType
lem_subst_wf g g' x v_x t_x p_vx_tx p_env_wf t (WFRefn _env z b p y_ p_env'_p_bl) -- _env = g'; x:tx; g
  = WFRefn (concatE g (esubFV x v_x g')) z b (subFV x v_x p) y 
           p_ygg'_pvx_bl 
      where
        y             = y_ ? lem_in_env_esub g' x v_x y_
                           ? lem_in_env_concat g  g' y_
                           ? lem_in_env_concat (Cons x t_x g) g' y_
                           ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx y_
        p_xg_wf       = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _) = p_xg_wf
        p_vx_er_tx    = (lem_typing_hasbtype g v_x t_x p_vx_tx p_g_wf)
        p_ygg'_pvx_bl = lem_subst_btyp (erase_env g) (BCons y (BTBase b) (erase_env g')) 
                           (x ? lem_in_env_concatB (erase_env g) (erase_env g') x
                              ? lem_in_env_concatB (erase_env g) (BCons y (BTBase b) (erase_env g')) x)
                           v_x (erase t_x)  p_vx_er_tx (unbind z y p) (BTBase TBool) 
                           (p_env'_p_bl ? lem_erase_concat (Cons x t_x g) g')
                           ? lem_commute_subFV_subBV1 z (FV y) x v_x p
                           ? lem_erase_concat g (esubFV x v_x g')
                           ? lem_erase_esubFV x v_x g'
lem_subst_wf g g' x v_x t_x p_vx_tx p_env_wf t (WFFunc _env z t_z p_env_tz t' y_ p_yenv_t')
  = WFFunc (concatE g (esubFV x v_x g')) z (tsubFV x v_x t_z) p_g'g_tzvx (tsubFV x v_x t') y p_yg'g_t'vx
      where
        {- @ y :: { yy:Vname | t == TFunc z t_z t' } @-}
        y           = y_ ? lem_in_env_esub g' x v_x y_ 
                         ? lem_in_env_concat g  g' y_ 
                         ? lem_in_env_concat (Cons x t_x g) g' y_
                         ? lem_in_env_concat (Cons x t_x g) g' y_
                         ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx y_
                         ---- ? lem_binds_esubFV g' x v_x  ---- if I can erase this, then delete??
        p_xg_wf     = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _) = p_xg_wf
        p_yenv_wf   = WFEBind (concatE (Cons x t_x g) g') p_env_wf y t_z p_env_tz
        p_vx_er_tx  = lem_typing_hasbtype g v_x t_x p_vx_tx p_g_wf
        p_g'g_tzvx  = lem_subst_wf g g'              x v_x t_x p_vx_tx p_env_wf  t_z p_env_tz
        p_yg'g_t'vx = lem_subst_wf g (Cons y t_z g') x v_x t_x p_vx_tx p_yenv_wf (unbindT z y t')  
                         (p_yenv_t' ? lem_erase_concat (Cons x t_x g) g')
                         ? lem_commute_tsubFV_tsubBV1 z (FV y) x v_x t'
                         -- ? toProof ( t === TFunc z t_z t' ) --
                         -- ? lem_erase_concat g (esubFV x v_x g') --
                         -- ? lem_erase_esubFV x v_x g' --
lem_subst_wf g g' x v_x t_x p_vx_tx p_env_wf t (WFExis _env z t_z p_env_tz t' y_ p_yenv_t')
  = WFExis (concatE g (esubFV x v_x g')) z (tsubFV x v_x t_z) p_g'g_tzvx (tsubFV x v_x t') y p_yg'g_t'vx
      where
        y           = y_ ? lem_in_env_esub g' x v_x y_ 
                         ? lem_in_env_concat g  g' y_ 
                         ? lem_in_env_concat (Cons x t_x g) g' y_
                         ? lem_in_env_concat (Cons x t_x g) g' y_
                         ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx y_
        p_xg_wf     = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _) = p_xg_wf
        p_yenv_wf   = WFEBind (concatE (Cons x t_x g) g') p_env_wf y t_z p_env_tz
        p_vx_er_tx  = lem_typing_hasbtype g v_x t_x p_vx_tx p_g_wf
        p_g'g_tzvx  = lem_subst_wf g g'              x v_x t_x p_vx_tx p_env_wf t_z p_env_tz
        p_yg'g_t'vx = lem_subst_wf g (Cons y t_z g') x v_x t_x p_vx_tx p_yenv_wf (unbindT z y t')  
                         (p_yenv_t' ? lem_erase_concat (Cons x t_x g) g')
                         ? lem_commute_tsubFV_tsubBV1 z (FV y) x v_x t'
  
{-
{-@ lem_bad :: v:Int -> { w:Int | v > 1 } @-}
lem_bad :: Int -> Int
lem_bad y = _y
  where
    y = _y
-}      
{- @ assu me lem_binds_esubFV :: g:Env -> x:Vname -> v_x:Value 
                                 -> { pf:_ | binds g == binds (esubFV x v_x g) } @-}
-- lem_binds_esubFV :: Env -> Vname -> Expr -> Proof
-- lem_binds_esubFV g x v_x = undefined
