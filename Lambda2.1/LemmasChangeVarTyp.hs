{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasChangeVarTyp where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
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
import BasicPropsEraseTyping
import LemmasChangeVarWF
import LemmasChangeVarEnt
import LemmasWeakenWF
import LemmasWeakenWFTV
import LemmasWellFormedness
import LemmasTyping
import SubstitutionWFAgain

{-@ reflect foo45 @-}
foo45 x = Just x
foo45 :: a -> Maybe a

-----------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
-----------------------------------------------------------

-- We can alpha-rename a variable anywhere in the environment and recursively alter the type
--   derivation tree. This is the type judgement so there are variables in the types to worry about
{-@ lem_change_var_typ_tvar1 :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
        -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t && isTVar1 p_e_t }
        -> { y:Vname | not (in_env y g) && not (in_env y g') }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                           (subFV x (FV y) e) (tsubFV x (FV y) t) &&
                           typSize p_e_t == typSize p'_e_t } / [typSize p_e_t, 0] @-}
lem_change_var_typ_tvar1 :: Env -> Vname -> Type -> Env -> WFEnv -> Expr -> Type 
                -> HasType ->  Vname -> HasType
lem_change_var_typ_tvar1 g x t_x g' p_env_wf e t (TVar1 _ z t' k' p_env'_t') y  -- t == self t' (FV z)
    = case g' of 
        (Empty)           -> TVar1 g y (tsubFV x (FV y) t_x) k' 
                                   (p_env'_t' ? lem_tsubFV_notin x (FV y) (t_x
                                                              ? lem_free_bound_in_env g t_x k_x p_g_tx x))
        {- x = z and t_x = t' -}   ? lem_tsubFV_self1 x y t' z k'
          where
            (WFEBind _g p_g_wf _x _tx k_x p_g_tx) = p_env_wf
        (Cons _z _ g'')   -> TVar1 (concatE (Cons y t_x g) (esubFV x (FV y) g'')) 
                                   (z ? lem_in_env_esub g'' x (FV y) z 
                                      ? lem_in_env_concat g g'' z
                                      ? lem_in_env_concat (Cons x t_x g) g'' z)
                                   (tsubFV x (FV y) t') k' p'_env'_t'
                                                              ? lem_tsubFV_self2 x (FV y) t' z k'
          where
            (WFEBind env' p_env'_wf _z _t' k_z _) = p_env_wf
            p'_env'_t' = lem_change_var_wf' g x t_x g'' p_env'_wf t' k' p_env'_t' y

{-@ lem_change_var_typ_tvar2 :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
        -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t && isTVar2 p_e_t }
        -> { y:Vname | not (in_env y g) && not (in_env y g') }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                           (subFV x (FV y) e) (tsubFV x (FV y) t) &&
                           typSize p_e_t == typSize p'_e_t } / [typSize p_e_t, 0] @-}
lem_change_var_typ_tvar2 :: Env -> Vname -> Type -> Env -> WFEnv -> Expr -> Type 
                -> HasType ->  Vname -> HasType
lem_change_var_typ_tvar2 g x t_x g' p_env_wf e t (TVar2 _ z _t p_z_t w_ t_w) y
    = case g' of             -- g''=Emp so x=w and p_z_t :: HasBType(g (FV z) t)
        (Empty)           -> case (x == z) of
                               (True)  -> impossible "it is"
                               (False) -> TVar2 g z t p_z_t  
                                             (y ? lem_free_bound_in_env g t Star p_g_t y ) t_x
                                             ? toProof ( tsubFV x (FV y) t === t )
                                 where
                                   (WFEBind g_ p_g_wf _ _ _ _ ) = p_env_wf
                                   p_g_t = lem_typing_wf g (FV z) t p_z_t p_g_wf
        (Cons _w _tw g'') -> case (x == z) of
                (True)  -> TVar2 (concatE (Cons y t_x g) (esubFV x (FV y) g'')) 
                                 (y `withProof` lem_in_env_concat (Cons y t_x g) g'' y)
                                 (tsubFV x (FV y) t) 
                                 (lem_change_var_typ g x t_x g'' p_env'_wf (FV z) t p_z_t y) 
                                 w (tsubFV x (FV y) t_w)     
                (False) -> TVar2 (concatE (Cons y t_x g) (esubFV x (FV y) g''))
                                 (z `withProof` lem_in_env_concat (Cons y t_x g) g'' z
                                    `withProof` lem_in_env_concat (Cons x t_x g) g'' z)
                                 (tsubFV x (FV y) t)
                                 (lem_change_var_typ g x t_x g'' p_env'_wf (FV z) t p_z_t y) 
                                 w (tsubFV x (FV y) t_w)  
            where
              w = w_ ? lem_in_env_concat (Cons x t_x g) g'' w_
                     ? lem_in_env_esub g'' x (FV y) w_
                     ? lem_in_env_concat (Cons y t_x g) (esubFV x (FV y) g'') w_
              (WFEBind env' p_env'_wf _ _ _ _) = p_env_wf

{-@ lem_change_var_typ_tvar3 :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
        -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t && isTVar3 p_e_t }
        -> { y:Vname | not (in_env y g) && not (in_env y g') }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                           (subFV x (FV y) e) (tsubFV x (FV y) t) &&
                           typSize p_e_t == typSize p'_e_t } / [typSize p_e_t, 0] @-}
lem_change_var_typ_tvar3 :: Env -> Vname -> Type -> Env -> WFEnv -> Expr -> Type 
                -> HasType ->  Vname -> HasType
lem_change_var_typ_tvar3 g x t_x g' p_env_wf e t (TVar3 _ z _t p_z_t a'_ k_a') y 
    = case g' of             -- g''=Emp so x=w and p_z_t :: HasBType(g (FV z) t)
        (Empty)           -> impossible "a' <> x"
        (ConsT _a' _ g'') -> case (x == z) of
                (True)  -> TVar3 (concatE (Cons y t_x g) (esubFV x (FV y) g'')) 
                                 (y `withProof` lem_in_env_concat (Cons y t_x g) g'' y)
                                 (tsubFV x (FV y) t) 
                                 (lem_change_var_typ g x t_x g'' p_env'_wf (FV z) t p_z_t y) 
                                 a' k_a'
                (False) -> TVar3 (concatE (Cons y t_x g) (esubFV x (FV y) g''))
                                 (z `withProof` lem_in_env_concat (Cons y t_x g) g'' z
                                    `withProof` lem_in_env_concat (Cons x t_x g) g'' z)
                                 (tsubFV x (FV y) t)
                                 (lem_change_var_typ g x t_x g'' p_env'_wf (FV z) t p_z_t y) 
                                 a' k_a'
            where
              a' = a'_ ? lem_in_env_concat (Cons x t_x g) g'' a'_
                       ? lem_in_env_esub g'' x (FV y) a'_
                       ? lem_in_env_concat (Cons y t_x g) (esubFV x (FV y) g'') a'_
              (WFEBindT env' p_env'_wf _ _) = p_env_wf

{-@ lem_change_var_typ_tabs :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
        -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t && isTAbs p_e_t }
        -> { y:Vname | not (in_env y g) && not (in_env y g') }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                           (subFV x (FV y) e) (tsubFV x (FV y) t) &&
                           typSize p_e_t == typSize p'_e_t } / [typSize p_e_t, 0] @-}
lem_change_var_typ_tabs :: Env -> Vname -> Type -> Env -> WFEnv -> Expr -> Type 
                -> HasType ->  Vname -> HasType
lem_change_var_typ_tabs g x t_x g' p_env_wf e t p_e_t@(TAbs env z t_z k_z p_env_tz e' t' z' p_z'_e'_t') y
    = TAbs (concatE (Cons y t_x g) (esubFV x (FV y) g')) z (tsubFV x (FV y) t_z) k_z 
           p_env'_tz (subFV x (FV y) e') (tsubFV x (FV y) t')  z'' p_z''y_e'_t'
        where
          p_env_t      = lem_typing_wf env e t p_e_t p_env_wf
          p_env'_tz    = lem_change_var_wf' g x t_x g' p_env_wf t_z k_z p_env_tz y
          z''_         = fresh_var_excluding (concatE (Cons x t_x g) g') y
          z''          = z''_ ? lem_in_env_concat g g' z''_
                              ? lem_in_env_concat (Cons x t_x g) g' z''_
                              ? lem_fv_bound_in_env (concatE (Cons x t_x g) g') e t p_e_t p_env_wf z''_
                              ? lem_free_bound_in_env env t Star p_env_t z''_
          p_z'env_wf   = WFEBind env p_env_wf z'  t_z k_z p_env_tz
          p_z''env_wf  = WFEBind env p_env_wf z'' t_z k_z p_env_tz
          p_z''_e'_t'  = lem_change_var_typ (concatE (Cons x t_x g) g') z' t_z Empty p_z'env_wf
                                 (unbind z z' e') (unbindT z z' t') p_z'_e'_t' z''
                                 ? lem_subFV_unbind z z' (FV z'') e'                                  
                                 ? lem_tsubFV_unbindT z z' (FV z'') t'
          p_z''y_e'_t' = lem_change_var_typ g x t_x (Cons z'' t_z g') p_z''env_wf (unbind z z'' e') 
                                 (unbindT z z'' t') p_z''_e'_t' y 
                                 ? lem_commute_subFV_unbind x y z z'' e'
                                 ? lem_commute_tsubFV_unbindT x y z z'' t'

{-@ lem_change_var_typ_tapp :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
        -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t && isTApp p_e_t }
        -> { y:Vname | not (in_env y g) && not (in_env y g') }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                           (subFV x (FV y) e) (tsubFV x (FV y) t) &&
                           typSize p_e_t == typSize p'_e_t } / [typSize p_e_t, 0] @-}
lem_change_var_typ_tapp :: Env -> Vname -> Type -> Env -> WFEnv -> Expr -> Type 
                -> HasType ->  Vname -> HasType
lem_change_var_typ_tapp g x t_x g' p_env_wf e t (TApp env e1 z t1 t2 p_env_e1_t1t2 e2 p_env_e2_t1) y
    = TApp (concatE (Cons y t_x g) (esubFV x (FV y) g')) (subFV x (FV y) e1) 
           z (tsubFV x (FV y) t1) (tsubFV x (FV y) t2) p_env'_e1_t1t2 
           (subFV x (FV y) e2) p_env'_e2_t1
        where
          p_env'_e1_t1t2 = lem_change_var_typ g x t_x g' p_env_wf e1 (TFunc z t1 t2) p_env_e1_t1t2 y
          p_env'_e2_t1   = lem_change_var_typ g x t_x g' p_env_wf e2 t1 p_env_e2_t1 y 

{-@ lem_change_var_typ_tabst :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
        -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t && isTAbsT p_e_t }
        -> { y:Vname | not (in_env y g) && not (in_env y g') }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                           (subFV x (FV y) e) (tsubFV x (FV y) t) &&
                           typSize p_e_t == typSize p'_e_t } / [typSize p_e_t, 0] @-}
lem_change_var_typ_tabst :: Env -> Vname -> Type -> Env -> WFEnv -> Expr -> Type 
                -> HasType ->  Vname -> HasType
lem_change_var_typ_tabst g x t_x g' p_env_wf e t 
                         p_e_t@(TAbsT env a1 k1 e' t' k_t' a' p_a'g_e'_t' p_a'g_t') y 
    = TAbsT (concatE (Cons y t_x g) (esubFV x (FV y) g')) a1 k1 (subFV x (FV y) e')
            (tsubFV x (FV y) t') k_t' a'' p_a''y_e'_t' p_a''y_t'
        where
          p_env_t      = lem_typing_wf env e t p_e_t p_env_wf 
          a''_         = fresh_var_excluding (concatE (Cons x t_x g) g') y  
          a''          = a''_ ? lem_in_env_concat g g' a''_
                              ? lem_in_env_concat (Cons x t_x g) g' a''_
                              ? lem_in_env_concat (Cons y t_x g) g' a''_
                              ? lem_fv_bound_in_env env e t p_e_t p_env_wf a''_
                              ? lem_free_bound_in_env env t Star p_env_t a''_
          p_a'env_wf   = WFEBindT env p_env_wf a'  k1
          p_a''env_wf  = WFEBindT env p_env_wf a'' k1
          p_a''_e'_t'  = lem_change_tvar_typ (concatE (Cons x t_x g) g') a' k1 Empty p_a'env_wf
                              (unbind_tv a1 a' e') (unbind_tvT a1 a' t') p_a'g_e'_t' a''
                              ? lem_chgFTV_unbind_tv a1 a' a''
                                    (e' ? lem_fv_bound_in_env env e t p_e_t p_env_wf a')
                              ? lem_tchgFTV_unbind_tvT a1 a' a''
                                    (t' ? lem_free_bound_in_env env t Star p_env_t a')
          p_a''y_e'_t' = lem_change_var_typ g x t_x (ConsT a'' k1 g') p_a''env_wf
                              (unbind_tv a1 a'' e') (unbind_tvT a1 a'' t') p_a''_e'_t' y
                              ? lem_commute_subFV_unbind_tv x (FV y) a1 a'' e'
                              ? lem_commute_tsubFV_unbind_tvT x (FV y) a1 a'' t'
          p_a''g_t'    = lem_change_tvar_wf' (concatE (Cons x t_x g) g') a' k1 Empty p_a'env_wf
                              (unbind_tvT a1 a' t') k_t' p_a'g_t' a''
                              ? lem_tchgFTV_unbind_tvT a1 a' a''
                                    (t' ? lem_free_bound_in_env env t Star p_env_t a')
          p_a''y_t'    = lem_change_var_wf' g x t_x (ConsT a'' k1 g') p_a''env_wf
                              (unbind_tvT a1 a'' t') k_t' p_a''g_t' y
                              ? lem_tchgFTV_unbind_tvT a1 a' a''   
                                    (t' ? lem_free_bound_in_env env t Star p_env_t a')

{-@ lem_change_var_typ_tappt :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
        -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t && isTAppT p_e_t }
        -> { y:Vname | not (in_env y g) && not (in_env y g') }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                           (subFV x (FV y) e) (tsubFV x (FV y) t) &&
                           typSize p_e_t == typSize p'_e_t } / [typSize p_e_t, 0] @-}
lem_change_var_typ_tappt :: Env -> Vname -> Type -> Env -> WFEnv -> Expr -> Type 
                -> HasType ->  Vname -> HasType
lem_change_var_typ_tappt g x t_x g' p_env_wf e t (TAppT _g e' a1 k1 s p_e'_a1s t' p_g_t') y 
    = TAppT (concatE (Cons y t_x g) (esubFV x (FV y) g')) (subFV x (FV y) e') 
            a1 k1 (tsubFV x (FV y) s) p_env'_e'_a1s (tsubFV x (FV y) t') p_env'_t'
            ? lem_commute_tsubFV_tsubBTV a1 t' x (FV y) s
        where
          p_env'_e'_a1s = lem_change_var_typ g x t_x g' p_env_wf e' (TPoly a1 k1 s) p_e'_a1s y
          p_env'_t'     = lem_change_var_wf' g x t_x g' p_env_wf t' k1 p_g_t' y

{-@ lem_change_var_typ_tlet :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
        -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t && isTLet p_e_t }
        -> { y:Vname | not (in_env y g) && not (in_env y g') }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                           (subFV x (FV y) e) (tsubFV x (FV y) t) &&
                           typSize p_e_t == typSize p'_e_t } / [typSize p_e_t, 0] @-}
lem_change_var_typ_tlet :: Env -> Vname -> Type -> Env -> WFEnv -> Expr -> Type 
                -> HasType ->  Vname -> HasType
lem_change_var_typ_tlet g x t_x g' p_env_wf e t 
                   p_e_t@(TLet env e_z t_z p_env_ez_tz z e' t' k' p_env_t' z' p_z'env_e'_t') y
    = TLet (concatE (Cons y t_x g) (esubFV x (FV y) g')) (subFV x (FV y) e_z) (tsubFV x (FV y) t_z)
           p_env'_ez_tz z (subFV x (FV y) e') (tsubFV x (FV y) t') k' p_env'_t' z'' p_z''env'_e'_t'
        where
          p_env_t         = lem_typing_wf env e t p_e_t p_env_wf
          p_env_tz        = lem_typing_wf env e_z t_z p_env_ez_tz p_env_wf
          p_env'_t'       = lem_change_var_wf' g x t_x g' p_env_wf t' k' p_env_t' y
          z''_            = fresh_var_excluding (concatE (Cons x t_x g) g') y
          z''             = z''_ ? lem_in_env_concat g g' z''_
                                 ? lem_in_env_concat (Cons x t_x g) g' z''_
                                 ? lem_fv_bound_in_env (concatE (Cons x t_x g) g') e t p_e_t p_env_wf z''_
                                 ? lem_free_bound_in_env env t Star p_env_t z''_
          p_z'env_wf      = WFEBind env p_env_wf z'  t_z Star p_env_tz
          p_z''env_wf     = WFEBind env p_env_wf z'' t_z Star p_env_tz
          p_env'_ez_tz    = lem_change_var_typ g x t_x g' p_env_wf e_z t_z p_env_ez_tz y 
          p_z''env_e'_t'  = lem_change_var_typ (concatE (Cons x t_x g) g') z' t_z Empty p_z'env_wf
                                    (unbind z z' e') (unbindT z z' t') p_z'env_e'_t' z''
                                    ? lem_subFV_unbind z z' (FV z'') e'
                                    ? lem_tsubFV_unbindT z z' (FV z'') t'
          p_z''env'_e'_t' = lem_change_var_typ g x t_x (Cons z'' t_z g') p_z''env_wf (unbind z z'' e') 
                                    (unbindT z z'' t') p_z''env_e'_t' y
                                    ? lem_commute_subFV_unbind x y z z'' e'
                                    ? lem_commute_tsubFV_unbindT x y z z'' t'

{-@ lem_change_var_typ_tann :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
        -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t && isTAnn p_e_t }
        -> { y:Vname | not (in_env y g) && not (in_env y g') }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                           (subFV x (FV y) e) (tsubFV x (FV y) t) &&
                           typSize p_e_t == typSize p'_e_t } / [typSize p_e_t, 0] @-}
lem_change_var_typ_tann :: Env -> Vname -> Type -> Env -> WFEnv -> Expr -> Type 
                -> HasType ->  Vname -> HasType
lem_change_var_typ_tann g x t_x g' p_env_wf e t (TAnn env e' _t p_env_e'_t) y
    = TAnn (concatE (Cons y t_x g) (esubFV x (FV y) g')) (subFV x (FV y) e')  
           (tsubFV x (FV y) t) p_env'_e'_t
        where
          p_env'_e'_t = lem_change_var_typ g x t_x g' p_env_wf e' t p_env_e'_t y

{-@ lem_change_var_typ_tsub :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
        -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t && isTSub p_e_t }
        -> { y:Vname | not (in_env y g) && not (in_env y g') }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                           (subFV x (FV y) e) (tsubFV x (FV y) t) &&
                           typSize p_e_t == typSize p'_e_t } / [typSize p_e_t, 0] @-}
lem_change_var_typ_tsub :: Env -> Vname -> Type -> Env -> WFEnv -> Expr -> Type 
                -> HasType ->  Vname -> HasType
lem_change_var_typ_tsub g x t_x g' p_env_wf e t p_e_t@(TSub env _e s p_env_e_s _t k p_env_t p_env_s_t) y
    = TSub (concatE (Cons y t_x g) (esubFV x (FV y) g')) (subFV x (FV y) e) (tsubFV x (FV y) s) 
           p_env'_e_s (tsubFV x (FV y) t) k p_env'_t p_env'_s_t
        where
          p_env_s    = lem_typing_wf env e s p_env_e_s p_env_wf
          p_env'_e_s = lem_change_var_typ g x t_x g' p_env_wf e s p_env_e_s y
          p_env'_t   = lem_change_var_wf' g x t_x g' p_env_wf t k p_env_t y
          p_env'_s_t = lem_change_var_subtype g x t_x g' p_env_wf s Star p_env_s t k p_env_t p_env_s_t y


{-@ lem_change_var_typ :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
        -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t }
        -> { y:Vname | not (in_env y g) && not (in_env y g') }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                           (subFV x (FV y) e) (tsubFV x (FV y) t) &&
                           typSize p_e_t == typSize p'_e_t } / [typSize p_e_t, 1] @-}
lem_change_var_typ :: Env -> Vname -> Type -> Env -> WFEnv -> Expr -> Type 
                -> HasType ->  Vname -> HasType
lem_change_var_typ g x t_x g' p_env_wf e t (TBC _ b) y  
    = TBC (concatE (Cons y t_x g) (esubFV x (FV y) g')) b ? lem_tsubFV_tybc x (FV y) b
lem_change_var_typ g x t_x g' p_env_wf e t (TIC _ n) y  
    = TIC (concatE (Cons y t_x g) (esubFV x (FV y) g')) n ? lem_tsubFV_tyic x (FV y) n
lem_change_var_typ g x t_x g' p_env_wf e t p_e_t@(TVar1 _ z t' k' p_env'_t') y  -- t == self t' (FV z)
    = lem_change_var_typ_tvar1 g x t_x g' p_env_wf e t p_e_t y
lem_change_var_typ g x t_x g' p_env_wf e t p_e_t@(TVar2 _ z _t p_z_t w t_w) y
    = lem_change_var_typ_tvar2 g x t_x g' p_env_wf e t p_e_t y
lem_change_var_typ g x t_x g' p_env_wf e t p_e_t@(TVar3 _ z _t p_z_t a' k_a') y 
    = lem_change_var_typ_tvar3 g x t_x g' p_env_wf e t p_e_t y
lem_change_var_typ g x t_x g' p_env_wf e t (TPrm _ c) y  
    = TPrm (concatE (Cons y t_x g) (esubFV x (FV y) g')) c ? lem_tsubFV_ty x (FV y) c
lem_change_var_typ g x t_x g' p_env_wf e t p_e_t@(TAbs env z t_z k_z p_env_tz e' t' z' p_z'_e'_t') y
    = lem_change_var_typ_tabs g x t_x g' p_env_wf e t p_e_t y
lem_change_var_typ g x t_x g' p_env_wf e t p_e_t@(TApp env e1 z t1 t2 p_env_e1_t1t2 e2 p_env_e2_t1) y
    = lem_change_var_typ_tapp g x t_x g' p_env_wf e t p_e_t y
lem_change_var_typ g x t_x g' p_env_wf e t p_e_t@(TAbsT {}) y 
    = lem_change_var_typ_tabst g x t_x g' p_env_wf e t p_e_t y
lem_change_var_typ g x t_x g' p_env_wf e t p_e_t@(TAppT {}) y 
    = lem_change_var_typ_tappt g x t_x g' p_env_wf e t p_e_t y
lem_change_var_typ g x t_x g' p_env_wf e t 
                   p_e_t@(TLet env e_z t_z p_env_ez_tz z e' t' k' p_env_t' z' p_z'env_e'_t') y
    = lem_change_var_typ_tlet g x t_x g' p_env_wf e t p_e_t y
lem_change_var_typ g x t_x g' p_env_wf e t p_e_t@(TAnn env e' _t p_env_e'_t) y
    = lem_change_var_typ_tann g x t_x g' p_env_wf e t p_e_t y
lem_change_var_typ g x t_x g' p_env_wf e t p_e_t@(TSub env _e s p_env_e_s _t k p_env_t p_env_s_t) y
    = lem_change_var_typ_tsub g x t_x g' p_env_wf e t p_e_t y


{-@ lem_change_tvar_typ_tvar1 :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
        -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTVar1 p_e_t }
        -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
                                                       (chgFTV a a' e) (tchgFTV a a' t) && 
                              typSize p_e_t == typSize p'_e_t } / [typSize p_e_t, 0] @-}
lem_change_tvar_typ_tvar1 :: Env -> Vname -> Kind -> Env -> WFEnv -> Expr -> Type 
                -> HasType ->  Vname -> HasType
lem_change_tvar_typ_tvar1 g a k_a g' p_env_wf e t (TVar1 _ z t' k' p_env'_t') a'  -- t == self t' (FV z)
    = case g' of 
        (Empty)           -> impossible "a <> z"
        (Cons _z _ g'')   -> TVar1 (concatE (ConsT a' k_a g) (echgFTV a a' g''))
                                   (z ? lem_in_env_echgFTV g'' a a' z 
                                      ? lem_in_env_concat g g'' z
                                      ? lem_in_env_concat (ConsT a k_a g) g'' z)
                                   (tchgFTV a a' t') k' p'_env'_t'
                                   ? lem_tchgFTV_self a a' t' (FV z) k'
          where
            (WFEBind env' p_env'_wf _z _t' k_z _) = p_env_wf
            p'_env'_t' = lem_change_tvar_wf' g a k_a g'' p_env'_wf t' k' p_env'_t' a'

{-@ lem_change_tvar_typ_tvar2 :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
        -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTVar2 p_e_t }
        -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
                                                       (chgFTV a a' e) (tchgFTV a a' t) && 
                              typSize p_e_t == typSize p'_e_t } / [typSize p_e_t, 0] @-}
lem_change_tvar_typ_tvar2 :: Env -> Vname -> Kind -> Env -> WFEnv -> Expr -> Type 
                -> HasType ->  Vname -> HasType
lem_change_tvar_typ_tvar2 g a k_a g' p_env_wf e t p_env_z_t@(TVar2 _ z _t p_z_t w_ t_w) a'
    = case g' of             
        (Cons _w _tw g'') -> case (a == z) of
            True  -> impossible ("by lemma" ? lem_tvar_v_in_env (concatE (ConsT a k_a g) g') 
                                                                z t p_env_z_t
                                            ? lem_binds_invariants (concatE (ConsT a k_a g) g''))               
            False -> TVar2 (concatE (ConsT a' k_a g) (echgFTV a a' g''))
                                 (z `withProof` lem_in_env_concat (ConsT a' k_a g) g'' z
                                    `withProof` lem_in_env_concat (ConsT a  k_a g) g'' z)
                                 (tchgFTV a a' t)
                                 (lem_change_tvar_typ g a k_a g'' p_env'_wf (FV z) t p_z_t a') 
                                 w (tchgFTV a a' t_w)
              where
                w = w_ ? lem_in_env_concat (ConsT a k_a g) g'' w_
                       ? lem_in_env_echgFTV g'' a a' w_
                       ? lem_in_env_concat (ConsT a' k_a g) (echgFTV a a' g'') w_
                (WFEBind env' p_env'_wf _ _ _ _) = p_env_wf

{-@ lem_change_tvar_typ_tvar3 :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
        -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTVar3 p_e_t }
        -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
                                                       (chgFTV a a' e) (tchgFTV a a' t) && 
                              typSize p_e_t == typSize p'_e_t } / [typSize p_e_t, 0] @-}
lem_change_tvar_typ_tvar3 :: Env -> Vname -> Kind -> Env -> WFEnv -> Expr -> Type 
                -> HasType ->  Vname -> HasType
lem_change_tvar_typ_tvar3 g a k_a g' p_env_wf e t p_env_z_t@(TVar3 _ z _t p_z_t a1_ k_a1) a'
    = case g' of             
        (Empty)           -> case (a == z) of
            (True)  -> impossible ("by lemma" ? lem_tvar_v_in_env (concatE (ConsT a k_a g) g')
                                                                  z t p_env_z_t)
            (False) -> TVar3 g z t p_z_t (a' ? lem_free_bound_in_env g t Star p_g_t a') k_a
                             ? lem_tchgFTV_notin a a' t
              where
                (WFEBindT g_ p_g_wf _ _) = p_env_wf
                p_g_t = lem_typing_wf g (FV z) t p_z_t p_g_wf
        (ConsT _a' _ g'') -> case (a == z) of
            (True)  -> impossible ("by lemma" ? lem_tvar_v_in_env (concatE (ConsT a k_a g) g') 
                                                                  z t p_env_z_t
                                              ? lem_binds_invariants (concatE (ConsT a k_a g) g''))
            (False) -> TVar3 (concatE (ConsT a' k_a g) (echgFTV a a' g''))
                             (z `withProof` lem_in_env_concat (ConsT a' k_a g) g'' z
                                `withProof` lem_in_env_concat (ConsT a  k_a g) g'' z)
                             (tchgFTV a a' t)
                             (lem_change_tvar_typ g a k_a g'' p_env'_wf (FV z) t p_z_t a') a1 k_a1 
              where
                a1 = a1_ ? lem_in_env_concat (ConsT a k_a g) g'' a1_
                         ? lem_in_env_echgFTV g'' a a' a1_
                         ? lem_in_env_concat (ConsT a' k_a g) (echgFTV a a' g'') a1_
                (WFEBindT env' p_env'_wf _ _) = p_env_wf

{-@ lem_change_tvar_typ_tabs :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
        -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTAbs p_e_t }
        -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
                                                       (chgFTV a a' e) (tchgFTV a a' t) && 
                              typSize p_e_t == typSize p'_e_t } / [typSize p_e_t, 0] @-}
lem_change_tvar_typ_tabs :: Env -> Vname -> Kind -> Env -> WFEnv -> Expr -> Type 
                -> HasType ->  Vname -> HasType
lem_change_tvar_typ_tabs g a k_a g' p_env_wf e t p_e_t@(TAbs env z t_z k_z p_env_tz e' t' z' p_z'_e'_t') a'
    = TAbs (concatE (ConsT a' k_a g) (echgFTV a a' g')) z (tchgFTV a a' t_z) k_z 
           p_env'_tz (chgFTV a a' e') (tchgFTV a a' t')  z'' p_z''a'_e'_t'
        where
          p_env_t      = lem_typing_wf env e t p_e_t p_env_wf
          p_env'_tz    = lem_change_tvar_wf' g a k_a g' p_env_wf t_z k_z p_env_tz a'
          z''_         = fresh_var_excluding (concatE (ConsT a k_a g) g') a'
          z''          = z''_ ? lem_in_env_concat g g' z''_
                              ? lem_in_env_concat (ConsT a k_a g) g' z''_
                              ? lem_fv_bound_in_env (concatE (ConsT a k_a g) g') e t p_e_t p_env_wf z''_
                              ? lem_free_bound_in_env env t Star p_env_t z''_
          p_z'env_wf   = WFEBind env p_env_wf z'  t_z k_z p_env_tz
          p_z''env_wf  = WFEBind env p_env_wf z'' t_z k_z p_env_tz
          p_z''_e'_t'  = lem_change_var_typ (concatE (ConsT a k_a g) g') z' t_z Empty p_z'env_wf
                                 (unbind z z' e') (unbindT z z' t') p_z'_e'_t' z''
                                 ? lem_subFV_unbind z z' (FV z'') e'                                  
                                 ? lem_tsubFV_unbindT z z' (FV z'') t'
          p_z''a'_e'_t' = lem_change_tvar_typ g a k_a (Cons z'' t_z g') p_z''env_wf (unbind z z'' e') 
                                 (unbindT z z'' t') p_z''_e'_t' a'
                                 ? lem_commute_chgFTV_unbind a a' z z'' e'
                                 ? lem_commute_tchgFTV_unbindT a a' z z'' t'

{-@ lem_change_tvar_typ_tapp :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
        -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTApp p_e_t }
        -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
                                                       (chgFTV a a' e) (tchgFTV a a' t) && 
                              typSize p_e_t == typSize p'_e_t } / [typSize p_e_t, 0] @-}
lem_change_tvar_typ_tapp :: Env -> Vname -> Kind -> Env -> WFEnv -> Expr -> Type 
                -> HasType ->  Vname -> HasType
lem_change_tvar_typ_tapp g a k_a g' p_env_wf e t (TApp env e1 z t1 t2 p_env_e1_t1t2 e2 p_env_e2_t1) a'
    = TApp (concatE (ConsT a' k_a g) (echgFTV a a' g')) (chgFTV a a' e1) 
           z (tchgFTV a a' t1) (tchgFTV a a' t2) p_env'_e1_t1t2 
           (chgFTV a a' e2) p_env'_e2_t1
        where
          p_env'_e1_t1t2 = lem_change_tvar_typ g a k_a g' p_env_wf e1 (TFunc z t1 t2) p_env_e1_t1t2 a'
          p_env'_e2_t1   = lem_change_tvar_typ g a k_a g' p_env_wf e2 t1 p_env_e2_t1 a'

{-@ lem_change_tvar_typ_tabst :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
        -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTAbsT p_e_t }
        -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
                                                       (chgFTV a a' e) (tchgFTV a a' t) && 
                              typSize p_e_t == typSize p'_e_t } / [typSize p_e_t, 0] @-}
lem_change_tvar_typ_tabst :: Env -> Vname -> Kind -> Env -> WFEnv -> Expr -> Type 
                -> HasType ->  Vname -> HasType
lem_change_tvar_typ_tabst g a k_a g' p_env_wf e t 
                          p_e_t@(TAbsT env a1 k1 e' t' k_t' a' p_a'g_e'_t' p_a'g_t') aa
    = TAbsT (concatE (ConsT aa k_a g) (echgFTV a aa g')) a1 k1 (chgFTV a aa e')
            (tchgFTV a aa t') k_t' a'' p_a''aa_e'_t' p_a''aa_t'
        where
          p_env_t      = lem_typing_wf env e t p_e_t p_env_wf 
          a''_         = fresh_var_excluding (concatE (ConsT a k_a g) g') aa 
          a''          = a''_ ? lem_in_env_concat g g' a''_
                              ? lem_in_env_concat (ConsT a  k_a g) g' a''_
                              ? lem_in_env_concat (ConsT aa k_a g) g' a''_
                              ? lem_fv_bound_in_env env e t p_e_t p_env_wf a''_
                              ? lem_free_bound_in_env env t Star p_env_t a''_
          p_a'env_wf   = WFEBindT env p_env_wf a'  k1
          p_a''env_wf  = WFEBindT env p_env_wf a'' k1
          p_a''_e'_t'  = lem_change_tvar_typ (concatE (ConsT a k_a g) g') a' k1 Empty p_a'env_wf
                              (unbind_tv a1 a' e') (unbind_tvT a1 a' t') p_a'g_e'_t' a''
                              ? lem_chgFTV_unbind_tv a1 a' a''
                                    (e' ? lem_fv_bound_in_env env e t p_e_t p_env_wf a')
                              ? lem_tchgFTV_unbind_tvT a1 a' a''
                                    (t' ? lem_free_bound_in_env env t Star p_env_t a')
          p_a''aa_e'_t' = lem_change_tvar_typ g a k_a (ConsT a'' k1 g') p_a''env_wf
                              (unbind_tv a1 a'' e') (unbind_tvT a1 a'' t') p_a''_e'_t' aa
                              ? lem_commute_chgFTV_unbind_tv a aa a1 a'' e'
                              ? lem_commute_tchgFTV_unbind_tvT a aa a1 a'' t'
          p_a''g_t'    = lem_change_tvar_wf' (concatE (ConsT a k_a g) g') a' k1 Empty p_a'env_wf
                              (unbind_tvT a1 a' t') k_t' p_a'g_t' a''
                              ? lem_tchgFTV_unbind_tvT a1 a' a''
                                    (t' ? lem_free_bound_in_env env t Star p_env_t a')
          p_a''aa_t'    = lem_change_tvar_wf' g a k_a (ConsT a'' k1 g') p_a''env_wf
                              (unbind_tvT a1 a'' t') k_t' p_a''g_t' aa
                              ? lem_tchgFTV_unbind_tvT a1 a' a''   
                                    (t' ? lem_free_bound_in_env env t Star p_env_t a')

{-@ lem_change_tvar_typ_tappt :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
        -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTAppT p_e_t }
        -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
                                                       (chgFTV a a' e) (tchgFTV a a' t) && 
                              typSize p_e_t == typSize p'_e_t } / [typSize p_e_t, 0] @-}
lem_change_tvar_typ_tappt :: Env -> Vname -> Kind -> Env -> WFEnv -> Expr -> Type 
                -> HasType ->  Vname -> HasType
lem_change_tvar_typ_tappt g a k_a g' p_env_wf e t (TAppT _g e' a1 k1 s p_e'_a1s t' p_g_t') a'
    = TAppT (concatE (ConsT a' k_a g) (echgFTV a a' g')) (chgFTV a a' e') 
            a1 k1 (tchgFTV a a' s) p_env'_e'_a1s (tchgFTV a a' t') p_env'_t'
            ? lem_commute_tchgFTV_tsubBTV a1 t' a a' s
        where
          p_env'_e'_a1s = lem_change_tvar_typ g a k_a g' p_env_wf e' (TPoly a1 k1 s) p_e'_a1s a'
          p_env'_t'     = lem_change_tvar_wf' g a k_a g' p_env_wf t' k1 p_g_t' a'

{-@ lem_change_tvar_typ_tlet :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
        -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTLet p_e_t }
        -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
                                                       (chgFTV a a' e) (tchgFTV a a' t) && 
                              typSize p_e_t == typSize p'_e_t } / [typSize p_e_t, 0] @-}
lem_change_tvar_typ_tlet :: Env -> Vname -> Kind -> Env -> WFEnv -> Expr -> Type 
                -> HasType ->  Vname -> HasType
lem_change_tvar_typ_tlet g a k_a g' p_env_wf e t 
                   p_e_t@(TLet env e_z t_z p_env_ez_tz z e' t' k' p_env_t' z' p_z'env_e'_t') a'
    = TLet (concatE (ConsT a' k_a g) (echgFTV a a' g')) (chgFTV a a' e_z) (tchgFTV a a' t_z)
           p_env'_ez_tz z (chgFTV a a' e') (tchgFTV a a' t') k' p_env'_t' z'' p_z''env'_e'_t'
        where
          p_env_t         = lem_typing_wf env e t p_e_t p_env_wf
          p_env_tz        = lem_typing_wf env e_z t_z p_env_ez_tz p_env_wf
          p_env'_t'       = lem_change_tvar_wf' g a k_a g' p_env_wf t' k' p_env_t' a'
          z''_            = fresh_var_excluding (concatE (ConsT a k_a g) g') a'
          z''             = z''_ ? lem_in_env_concat g g' z''_
                                 ? lem_in_env_concat (ConsT a k_a g) g' z''_
                                 ? lem_fv_bound_in_env (concatE (ConsT a k_a g) g') e t p_e_t p_env_wf z''_
                                 ? lem_free_bound_in_env env t Star p_env_t z''_
          p_z'env_wf      = WFEBind env p_env_wf z'  t_z Star p_env_tz
          p_z''env_wf     = WFEBind env p_env_wf z'' t_z Star p_env_tz
          p_env'_ez_tz    = lem_change_tvar_typ g a k_a g' p_env_wf e_z t_z p_env_ez_tz a' 
          p_z''env_e'_t'  = lem_change_var_typ (concatE (ConsT a k_a g) g') z' t_z Empty p_z'env_wf
                                    (unbind z z' e') (unbindT z z' t') p_z'env_e'_t' z''
                                    ? lem_subFV_unbind z z' (FV z'') e'
                                    ? lem_tsubFV_unbindT z z' (FV z'') t'
          p_z''env'_e'_t' = lem_change_tvar_typ g a k_a (Cons z'' t_z g') p_z''env_wf (unbind z z'' e') 
                                    (unbindT z z'' t') p_z''env_e'_t' a'
                                    ? lem_commute_chgFTV_unbind   a a' z z'' e'
                                    ? lem_commute_tchgFTV_unbindT a a' z z'' t'

{-@ lem_change_tvar_typ_tann :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
        -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTAnn p_e_t }
        -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
                                                       (chgFTV a a' e) (tchgFTV a a' t) && 
                              typSize p_e_t == typSize p'_e_t } / [typSize p_e_t, 0] @-}
lem_change_tvar_typ_tann :: Env -> Vname -> Kind -> Env -> WFEnv -> Expr -> Type 
                -> HasType ->  Vname -> HasType
lem_change_tvar_typ_tann g a k_a g' p_env_wf e t (TAnn env e' _t p_env_e'_t) a'
    = TAnn (concatE (ConsT a' k_a g) (echgFTV a a' g')) (chgFTV a a' e')  
           (tchgFTV a a' t) p_env'_e'_t
        where
          p_env'_e'_t = lem_change_tvar_typ g a k_a g' p_env_wf e' t p_env_e'_t a'

{-@ lem_change_tvar_typ_tsub :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
        -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g')) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t && isTSub p_e_t }
        -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
                                                       (chgFTV a a' e) (tchgFTV a a' t) && 
                              typSize p_e_t == typSize p'_e_t } / [typSize p_e_t, 0] @-}
lem_change_tvar_typ_tsub :: Env -> Vname -> Kind -> Env -> WFEnv -> Expr -> Type 
                -> HasType ->  Vname -> HasType
lem_change_tvar_typ_tsub g a k_a g' p_env_wf e t p_e_t@(TSub env _e s p_env_e_s _t k p_env_t p_env_s_t) a'
    = TSub (concatE (ConsT a' k_a g) (echgFTV a a' g')) (chgFTV a a' e) (tchgFTV a a' s) 
           p_env'_e_s (tchgFTV a a' t) k p_env'_t p_env'_s_t
        where
          p_env_s    = lem_typing_wf env e s p_env_e_s p_env_wf
          p_env'_e_s = lem_change_tvar_typ     g a k_a g' p_env_wf e s p_env_e_s a'
          p_env'_t   = lem_change_tvar_wf'     g a k_a g' p_env_wf t k p_env_t a'
          p_env'_s_t = lem_change_tvar_subtype g a k_a g' p_env_wf s Star p_env_s t k p_env_t p_env_s_t a'


{-@ lem_change_tvar_typ :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
        -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE (ConsT a k_a g) g'))
        -> e:Expr -> t:Type -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (ConsT a k_a g) g') e t }
        -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
                                                       (chgFTV a a' e) (tchgFTV a a' t) && 
                              typSize p_e_t == typSize p'_e_t } / [typSize p_e_t, 1] @-}
lem_change_tvar_typ :: Env -> Vname -> Kind -> Env -> WFEnv -> Expr -> Type 
                -> HasType ->  Vname -> HasType
lem_change_tvar_typ g a k_a g' p_env_wf e t (TBC _ b) a' 
    = TBC (concatE (ConsT a' k_a g) (echgFTV a a' g')) b ? lem_tchgFTV_tybc a a' b
lem_change_tvar_typ g a k_a g' p_env_wf e t (TIC _ n) a' 
    = TIC (concatE (ConsT a' k_a g) (echgFTV a a' g')) n ? lem_tchgFTV_tyic a a' n
lem_change_tvar_typ g a k_a g' p_env_wf e t p_e_t@(TVar1 {}) a' 
    = lem_change_tvar_typ_tvar1 g a k_a g' p_env_wf e t p_e_t a'
lem_change_tvar_typ g a k_a g' p_env_wf e t p_e_t@(TVar2 {}) a' 
    = lem_change_tvar_typ_tvar2 g a k_a g' p_env_wf e t p_e_t a'
lem_change_tvar_typ g a k_a g' p_env_wf e t p_e_t@(TVar3 {}) a' 
    = lem_change_tvar_typ_tvar3 g a k_a g' p_env_wf e t p_e_t a'
lem_change_tvar_typ g a k_a g' p_env_wf e t (TPrm _ c) a' 
    = TPrm (concatE (ConsT a' k_a g) (echgFTV a a' g')) c ? lem_tchgFTV_ty a a' c
lem_change_tvar_typ g a k_a g' p_env_wf e t p_e_t@(TAbs {}) a' 
    = lem_change_tvar_typ_tabs g a k_a g' p_env_wf e t p_e_t a'
lem_change_tvar_typ g a k_a g' p_env_wf e t p_e_t@(TApp {}) a' 
    = lem_change_tvar_typ_tapp g a k_a g' p_env_wf e t p_e_t a'
lem_change_tvar_typ g a k_a g' p_env_wf e t p_e_t@(TAbsT {}) a'
    = lem_change_tvar_typ_tabst g a k_a g' p_env_wf e t p_e_t a'
lem_change_tvar_typ g a k_a g' p_env_wf e t p_e_t@(TAppT {}) a' 
    = lem_change_tvar_typ_tappt g a k_a g' p_env_wf e t p_e_t a'
lem_change_tvar_typ g a k_a g' p_env_wf e t p_e_t@(TLet {}) a' 
    = lem_change_tvar_typ_tlet g a k_a g' p_env_wf e t p_e_t a'
lem_change_tvar_typ g a k_a g' p_env_wf e t p_e_t@(TAnn {}) a' 
    = lem_change_tvar_typ_tann g a k_a g' p_env_wf e t p_e_t a'
lem_change_tvar_typ g a k_a g' p_env_wf e t p_e_t@(TSub {}) a' 
    = lem_change_tvar_typ_tsub g a k_a g' p_env_wf e t p_e_t a'


{-@ lem_change_var_subtype_sbase :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
      -> t:Type  -> k:Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE (Cons x t_x g) g') t t' && isSBase p_t_t'} 
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                         (tsubFV x (FV y) t) (tsubFV x (FV y) t') &&
                         subtypSize p_t_t'  == subtypSize p'_t_t' &&
                         subtypSize' p_t_t' == subtypSize' p'_t_t' } / [subtypSize p_t_t', 0] @-}
lem_change_var_subtype_sbase :: Env -> Vname -> Type -> Env -> WFEnv -> Type -> Kind -> WFType 
                              -> Type -> Kind -> WFType -> Subtype -> Vname -> Subtype
lem_change_var_subtype_sbase g x t_x g' p_env_wf t k p_env_t t' k' p_env_t' 
                       (SBase env z1 b p1 z2 p2 w pf_wenv_ent_p2) y_ 
    = SBase env' z1 b p1' z2 p2' w' pf_w'env'_ent_p2 
        where
          w'               = fresh_var_excluding (concatE (Cons x t_x g) g') y_
          y                = y_ ? lem_in_env_concat g g' y_
                                ? lem_in_env_concat g (Cons w' t g') y_
                                ? lem_in_env_concat (Cons x t_x g) g' y_
          env'             = concatE (Cons y t_x g) (esubFV x (FV y) g')
          p1'              = subFV x (FV y) p1
          p2'              = subFV x (FV y) p2
          p_wenv_wf        = WFEBind env p_env_wf w  t k p_env_t
          p_w'env_wf       = WFEBind env p_env_wf w' t k p_env_t
          pf_w'env_ent_p2  = lem_change_var_ent (concatE (Cons x t_x g) g') w t Empty p_wenv_wf
                                 (unbind 0 w p2 ? lem_free_subset_binds env t' k' p_env_t') 
                                 pf_wenv_ent_p2 
                                 (w' ? lem_free_bound_in_env env t' k' p_env_t' w')
                                 ? lem_subFV_unbind 0 w (FV w') p2
          pf_w'env'_ent_p2 = lem_change_var_ent g x t_x (Cons w' t g') 
                                 p_w'env_wf (unbind 0 w' p2) pf_w'env_ent_p2 y 
                                 ? lem_commute_subFV_unbind x y 0 w' p2 

{-@ lem_change_var_subtype_sfunc :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
      -> t:Type  -> k:Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE (Cons x t_x g) g') t t' && isSFunc p_t_t'} 
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                         (tsubFV x (FV y) t) (tsubFV x (FV y) t') &&
                         subtypSize p_t_t'  == subtypSize p'_t_t' &&
                         subtypSize' p_t_t' == subtypSize' p'_t_t' } / [subtypSize p_t_t', 0] @-}
lem_change_var_subtype_sfunc :: Env -> Vname -> Type -> Env -> WFEnv -> Type -> Kind -> WFType 
                              -> Type -> Kind -> WFType -> Subtype -> Vname -> Subtype
lem_change_var_subtype_sfunc g x t_x g' p_env_wf ft1 k1 p_env_ft1 ft2 k2 p_env_ft2 
                       (SFunc env z1 s1 z2 s2 p_env_s2_s1 t1 t2 w p_wenv_t1_t2) y_ 
    = SFunc env' z1 (tsubFV x (FV y) s1) z2 (tsubFV x (FV y) s2) p_env'_s2_s1 
                    (tsubFV x (FV y) t1) (tsubFV x (FV y) t2) w' p_w'env'_t1_t2
        where
          (WFFunc _ _ _ k_s1 p_env_s1 _ k_t1 w1 p_w1'env_t1) 
                         = lem_wffunc_for_wf_tfunc (concatE (Cons x t_x g) g') z1 s1 t1 k1 p_env_ft1
          (WFFunc _ _ _ k_s2 p_env_s2 _ k_t2 w2 p_w2env_t2)  
                         = lem_wffunc_for_wf_tfunc (concatE (Cons x t_x g) g') z2 s2 t2 k2 p_env_ft2
          w'             = fresh_var_excluding (concatE (Cons x t_x g) g') y_
          y              = y_ ? lem_in_env_concat g g' y_
                              ? lem_in_env_concat g (Cons w' s2 g') y_
                              ? lem_in_env_concat (Cons x t_x g) g' y_
          env'           = (concatE (Cons y t_x g) (esubFV x (FV y) g'))
          p_wenv_wf      = WFEBind env p_env_wf w  s2 k_s2 p_env_s2
          p_w1env_wf     = WFEBind env p_env_wf w1 s2 k_s2 p_env_s2
          p_w2env_wf     = WFEBind env p_env_wf w2 s2 k_s2 p_env_s2
          p_w'env_wf     = WFEBind env p_env_wf w' s2 k_s2 p_env_s2
          p_w1env_t1     = lem_subtype_in_env_wf env Empty w1 s2 s1 p_env_s2_s1 
                                                 (unbindT z1 w1 t1) k_t1 p_w1'env_t1
          p_wenv_t1      = lem_change_var_wf' (concatE (Cons x t_x g) g') w1 s2 Empty p_w1env_wf
                                              (unbindT z1 w1 t1) k_t1 p_w1env_t1 w
                                              ? lem_tsubFV_unbindT z1 w1 (FV w) t1
          p_wenv_t2      = lem_change_var_wf' (concatE (Cons x t_x g) g') w2 s2 Empty p_w2env_wf
                                              (unbindT z2 w2 t2) k_t2 p_w2env_t2 w
                                              ? lem_tsubFV_unbindT z2 w2 (FV w) t2
          p_w'env_t1     = lem_change_var_wf' (concatE (Cons x t_x g) g') w1 s2 Empty p_w1env_wf
                                              (unbindT z1 w1 t1) k_t1 p_w1env_t1 w'
                                              ? lem_tsubFV_unbindT z1 w1 (FV w') t1
          p_w'env_t2     = lem_change_var_wf' (concatE (Cons x t_x g) g') w2 s2 Empty p_w2env_wf
                                              (unbindT z2 w2 t2) k_t2 p_w2env_t2 w'
                                              ? lem_tsubFV_unbindT z2 w2 (FV w') t2
          p_env'_s2_s1   = lem_change_var_subtype g x t_x g' p_env_wf s2 k_s2 p_env_s2 s1 k_s1 
                                                  p_env_s1  p_env_s2_s1 y

          p_w'env_t1_t2  = lem_change_var_subtype (concatE (Cons x t_x g) g') w s2 Empty p_wenv_wf
                                   (unbindT z1 w t1) k_t1 p_wenv_t1 (unbindT z2 w t2) k_t2 p_wenv_t2
                                   p_wenv_t1_t2 
                                   ( w' ? lem_free_bound_in_env env ft1 k1 p_env_ft1 w'
                                        ? lem_free_bound_in_env env ft2 k2 p_env_ft2 w' )
                                   ? lem_tsubFV_unbindT z1 w (FV w') t1
                                   ? lem_tsubFV_unbindT z2 w (FV w') t2
          p_w'env'_t1_t2 = lem_change_var_subtype g x t_x (Cons w' s2 g') p_w'env_wf
                                   (unbindT z1 w' t1) k_t1 p_w'env_t1 (unbindT z2 w' t2) k_t2 p_w'env_t2
                                   p_w'env_t1_t2 y
                                   ? lem_commute_tsubFV_unbindT x y z1 w' t1
                                   ? lem_commute_tsubFV_unbindT x y z2 w' t2

{-@ lem_change_var_subtype_switn :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
      -> t:Type  -> k:Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE (Cons x t_x g) g') t t' && isSWitn p_t_t'} 
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                         (tsubFV x (FV y) t) (tsubFV x (FV y) t') &&
                         subtypSize p_t_t'  == subtypSize p'_t_t' &&
                         subtypSize' p_t_t' == subtypSize' p'_t_t' } / [subtypSize p_t_t', 0] @-}
lem_change_var_subtype_switn :: Env -> Vname -> Type -> Env -> WFEnv -> Type -> Kind -> WFType 
                              -> Type -> Kind -> WFType -> Subtype -> Vname -> Subtype
lem_change_var_subtype_switn g x t_x g' p_env_wf t k p_env_t t2 k2 p_env_t2
                       (SWitn env v_z t_z p_env_vz_tz _t z t' p_env_t_t'vz) y_ 
    = SWitn env' (subFV x (FV y) v_z) (tsubFV x (FV y) t_z) p_env'_vz_tz
                 (tsubFV x (FV y) t) z (tsubFV x (FV y) t') p_env'_t_t'vz
        where
          (WFExis _ _ _ k_z p_env_tz _ k' z' p_z'env_t') 
                        = lem_wfexis_for_wf_texists (concatE (Cons x t_x g) g') z t_z t' k2 p_env_t2
          y             = y_ ? lem_in_env_concat g g' y_
                             ? lem_in_env_concat (Cons x t_x g) g' y_
          env'          = concatE (Cons y t_x g) (esubFV x (FV y) g')
          p_z'env_wf    = WFEBind env p_env_wf z' t_z k_z p_env_tz
          p_env_t'vz    = lem_subst_wf' (concatE (Cons x t_x g) g') Empty z' v_z t_z p_env_vz_tz 
                                        p_z'env_wf (unbindT z z' t') k' p_z'env_t'
          p_env'_vz_tz  = lem_change_var_typ g x t_x g' p_env_wf v_z t_z p_env_vz_tz y    
                                             ? lem_tsubFV_unbindT z z' v_z t'
          p_env'_t_t'vz = lem_change_var_subtype g x t_x g' p_env_wf t k p_env_t
                                                 (tsubBV z v_z t') k' p_env_t'vz p_env_t_t'vz y
                                                 ? lem_commute_tsubFV_tsubBV z v_z x (FV y) t' 

{-@ lem_change_var_subtype_sbind :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
      -> t:Type  -> k:Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE (Cons x t_x g) g') t t' && isSBind p_t_t'} 
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                         (tsubFV x (FV y) t) (tsubFV x (FV y) t') &&
                         subtypSize p_t_t'  == subtypSize p'_t_t' &&
                         subtypSize' p_t_t' == subtypSize' p'_t_t' } / [subtypSize p_t_t', 0] @-}
lem_change_var_subtype_sbind :: Env -> Vname -> Type -> Env -> WFEnv -> Type -> Kind -> WFType 
                              -> Type -> Kind -> WFType -> Subtype -> Vname -> Subtype
lem_change_var_subtype_sbind g x t_x g' p_env_wf t1 k1 p_env_t1 t' k' p_env_t'
                       (SBind env z t_z t _t' z' p_z'env_t_t') y_  
    = SBind env' z (tsubFV x (FV y) t_z) (tsubFV x (FV y) t) (tsubFV x (FV y) t') z'' p_z''env'_t_t'
        where
          (WFExis _ _ _ k_z p_env_tz _ k w p_wenv_t) 
                         = lem_wfexis_for_wf_texists (concatE (Cons x t_x g) g') z t_z t k1 p_env_t1
          z''_           = fresh_var_excluding (concatE (Cons x t_x g) g') y_
          z''            = z''_ ? lem_free_bound_in_env env t1 k1 p_env_t1 z''_
                                ? lem_free_bound_in_env env t' k' p_env_t' z''_
          y              = y_ ? lem_in_env_concat g g' y_
                              ? lem_in_env_concat (Cons x t_x g) g' y_
          env'           = concatE (Cons y t_x g) (esubFV x (FV y) g')
          p_wenv_wf      = WFEBind env p_env_wf w   t_z k_z p_env_tz
          p_z'env_wf     = WFEBind env p_env_wf z'  t_z k_z p_env_tz
          p_z''env_wf    = WFEBind env p_env_wf z'' t_z k_z p_env_tz
          p_z'env_t      = lem_change_var_wf' env w t_z Empty p_wenv_wf (unbindT z w t) k p_wenv_t z'
                                              ? lem_tsubFV_unbindT z w (FV z') t
          p_z''env_t     = lem_change_var_wf' env w t_z Empty p_wenv_wf (unbindT z w t) k p_wenv_t z''
                                              ? lem_tsubFV_unbindT z w (FV z'') t
          p_z'env_t'     = lem_weaken_wf' env Empty p_env_wf t' k' p_env_t' z'  t_z
          p_z''env_t'    = lem_weaken_wf' env Empty p_env_wf t' k' p_env_t' z'' t_z
          p_z''env_t_t'  = lem_change_var_subtype (concatE (Cons x t_x g) g') z' t_z Empty
                                   p_z'env_wf (unbindT z z' t) k p_z'env_t t' k' p_z'env_t' 
                                   p_z'env_t_t' z'' 
                                   ? lem_tsubFV_unbindT z z' (FV z'') t
                                   ? lem_free_bound_in_env env t' k' p_env_t' z'
                                   ? lem_tsubFV_notin z' (FV z'') t'
          p_z''env'_t_t' = lem_change_var_subtype g x t_x (Cons z'' t_z g') p_z''env_wf
                                   (unbindT z z'' t) k p_z''env_t t' k' p_z''env_t' p_z''env_t_t' y
                                   ? lem_commute_tsubFV_unbindT x y z z'' t

{-@ lem_change_var_subtype_spoly :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
      -> t:Type  -> k:Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE (Cons x t_x g) g') t t' && isSPoly p_t_t'} 
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                         (tsubFV x (FV y) t) (tsubFV x (FV y) t') &&
                         subtypSize p_t_t'  == subtypSize p'_t_t' &&
                         subtypSize' p_t_t' == subtypSize' p'_t_t' } / [subtypSize p_t_t', 0] @-}
lem_change_var_subtype_spoly :: Env -> Vname -> Type -> Env -> WFEnv -> Type -> Kind -> WFType 
                              -> Type -> Kind -> WFType -> Subtype -> Vname -> Subtype
lem_change_var_subtype_spoly g x t_x g' p_env_wf t1 Star p_env_t1 t2 Star p_env_t2 
                             (SPoly env a1 k' t1' a2 t2' a1' p_a1'g_t1'_t2') y 
    = SPoly (concatE (Cons y t_x g) (esubFV x (FV y) g')) a1 k' (tsubFV x (FV y) t1')
            a2 (tsubFV x (FV y) t2') a1'' p_a1''y_t1'_t2'
        where
          (WFPoly _ _ _ _ k_t1' aa1 p_aa1env_t1')
                          = lem_wfpoly_for_wf_tpoly env a1 k' t1' p_env_t1
          (WFPoly _ _ _ _ k_t2' aa2 p_aa2env_t2')
                          = lem_wfpoly_for_wf_tpoly env a2 k' t2' p_env_t2
          a1''_           = fresh_var_excluding (concatE (Cons x t_x g) g') y
          a1''            = a1''_ ? lem_in_env_concat g g' a1''_
                                  ? lem_in_env_concat (Cons x t_x g) g' a1''_
                                  ? lem_in_env_concat (Cons y t_x g) g' a1''_
                                  ? lem_free_bound_in_env env t1 Star p_env_t1 a1''_
                                  ? lem_free_bound_in_env env t2 Star p_env_t2 a1''_
          p_aa1env_wf     = WFEBindT env p_env_wf aa1  k'
          p_aa2env_wf     = WFEBindT env p_env_wf aa2  k'
          p_a1'env_wf     = WFEBindT env p_env_wf a1'  k'
          p_a1''env_wf    = WFEBindT env p_env_wf a1'' k'
          p_a1'env_t1'    = lem_change_tvar_wf' (concatE (Cons x t_x g) g') aa1 k' Empty p_aa1env_wf
                                  (unbind_tvT a1 aa1 t1') k_t1' p_aa1env_t1' a1'
                                  ? lem_tchgFTV_unbind_tvT a1 aa1 a1' t1'
          p_a1'env_t2'    = lem_change_tvar_wf' (concatE (Cons x t_x g) g') aa2 k' Empty p_aa2env_wf
                                  (unbind_tvT a2 aa2 t2') k_t2' p_aa2env_t2' a1'
                                  ? lem_tchgFTV_unbind_tvT a2 aa2 a1' t2'
          p_a1''env_t1'   = lem_change_tvar_wf' (concatE (Cons x t_x g) g') aa1 k' Empty p_aa1env_wf
                                  (unbind_tvT a1 aa1 t1') k_t1' p_aa1env_t1' a1''
                                  ? lem_tchgFTV_unbind_tvT a1 aa1 a1'' t1'
          p_a1''env_t2'   = lem_change_tvar_wf' (concatE (Cons x t_x g) g') aa2 k' Empty p_aa2env_wf
                                  (unbind_tvT a2 aa2 t2') k_t2' p_aa2env_t2' a1''
                                  ? lem_tchgFTV_unbind_tvT a2 aa2 a1'' t2'
          p_a1''_t1'_t2'  = lem_change_tvar_subtype (concatE (Cons x t_x g) g') a1' k' Empty p_a1'env_wf
                                  (unbind_tvT a1 a1' t1') k_t1' p_a1'env_t1'
                                  (unbind_tvT a2 a1' t2') k_t2' p_a1'env_t2' p_a1'g_t1'_t2' a1''
                                  ? lem_tchgFTV_unbind_tvT a1 a1' a1'' t1'
                                  ? lem_tchgFTV_unbind_tvT a2 a1' a1'' t2'
          p_a1''y_t1'_t2' = lem_change_var_subtype g x t_x (ConsT a1'' k' g') p_a1''env_wf
                                  (unbind_tvT a1 a1'' t1') k_t1' p_a1''env_t1'
                                  (unbind_tvT a2 a1'' t2') k_t2' p_a1''env_t2' p_a1''_t1'_t2' y
                                  ? lem_commute_tsubFV_unbind_tvT x (FV y) a1 a1'' t1'
                                  ? lem_commute_tsubFV_unbind_tvT x (FV y) a2 a1'' t2'
lem_change_var_subtype_spoly g x t_x g' p_env_wf t1 Base p_env_t1 t2 k2 p_env_t2
                             (SPoly env a1 k' t1' a2 t2' a1' p_a1'g_t1'_t2') y
    = impossible ("by lemma" ? lem_wf_tpoly_star env a1 k' t1' p_env_t1)
lem_change_var_subtype_spoly g x t_x g' p_env_wf t1 k1 p_env_t1 t2 Base p_env_t2
                             (SPoly env a1 k' t1' a2 t2' a1' p_a1'g_t1'_t2') y
    = impossible ("by lemma" ? lem_wf_tpoly_star env a2 k' t2' p_env_t2)

{-@ lem_change_var_subtype :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
      -> t:Type  -> k:Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE (Cons x t_x g) g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE (Cons x t_x g) g') t t' } 
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                         (tsubFV x (FV y) t) (tsubFV x (FV y) t') &&
                         subtypSize p_t_t'  == subtypSize p'_t_t' &&
                         subtypSize' p_t_t' == subtypSize' p'_t_t' } / [subtypSize p_t_t', 1] @-}
lem_change_var_subtype :: Env -> Vname -> Type -> Env -> WFEnv -> Type -> Kind -> WFType 
                              -> Type -> Kind -> WFType -> Subtype -> Vname -> Subtype
lem_change_var_subtype g x t_x g' p_env_wf t k p_env_t t' k' p_env_t' 
                       p_t_t'@(SBase env z1 b p1 z2 p2 w pf_wenv_ent_p2) y_ 
  = lem_change_var_subtype_sbase g x t_x g' p_env_wf t k p_env_t t' k' p_env_t' p_t_t' y_ 
lem_change_var_subtype g x t_x g' p_env_wf ft1 k1 p_env_ft1 ft2 k2 p_env_ft2 
                       p_ft1_ft2@(SFunc env z1 s1 z2 s2 p_env_s2_s1 t1 t2 w p_wenv_t1_t2) y_ 
  = lem_change_var_subtype_sfunc g x t_x g' p_env_wf ft1 k1 p_env_ft1 ft2 k2 p_env_ft2 p_ft1_ft2 y_ 
lem_change_var_subtype g x t_x g' p_env_wf t k p_env_t t2 k2 p_env_t2
                       p_t_t2@(SWitn env v_z t_z p_env_vz_tz _t z t' p_env_t_t'vz) y_ 
  = lem_change_var_subtype_switn g x t_x g' p_env_wf t k p_env_t t2 k2 p_env_t2 p_t_t2 y_
lem_change_var_subtype g x t_x g' p_env_wf t1 k1 p_env_t1 t' k' p_env_t'
                       p_t1_t'@(SBind env z t_z t _t' z' p_z'env_t_t') y_ 
  = lem_change_var_subtype_sbind g x t_x g' p_env_wf t1 k1 p_env_t1 t' k' p_env_t' p_t1_t' y_
lem_change_var_subtype g x t_x g' p_env_wf t1 k1 p_env_t1 t2 k2 p_env_t2 p_t1_t2@(SPoly {}) y_ 
  = lem_change_var_subtype_spoly g x t_x g' p_env_wf t1 k1 p_env_t1 t2 k2 p_env_t2 p_t1_t2 y_


{-@ lem_change_tvar_subtype_sbase :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
      -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (ConsT a k_a g) g'))
      -> t:Type  -> k:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE (ConsT a k_a g) g') t t' && isSBase p_t_t'} 
      -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
                                                       (tchgFTV a a' t) (tchgFTV a a' t') &&
                         subtypSize p_t_t'  == subtypSize p'_t_t' &&
                         subtypSize' p_t_t' == subtypSize' p'_t_t' } / [subtypSize p_t_t', 0] @-}
lem_change_tvar_subtype_sbase :: Env -> Vname -> Kind -> Env -> WFEnv -> Type -> Kind -> WFType 
                              -> Type -> Kind -> WFType -> Subtype -> Vname -> Subtype
lem_change_tvar_subtype_sbase g a k_a g' p_env_wf t k p_env_t t' k' p_env_t' 
                       (SBase env z1 b p1 z2 p2 w pf_wenv_ent_p2) a'_ 
    = case b of 
          (FTV a1) | a1 == a  -> SBase env' z1 (FTV a') p1' z2 p2' w' pf_w'env'_ent_p2 
          _                   -> SBase env' z1 b        p1' z2 p2' w' pf_w'env'_ent_p2
        where
          w'               = fresh_var_excluding (concatE (ConsT a k_a g) g') a'_
          a'               = a'_ ? lem_in_env_concat g g' a'_
                                 ? lem_in_env_concat g (Cons w' t g') a'_
                                 ? lem_in_env_concat (ConsT a k_a g) g' a'_
          env'             = concatE (ConsT a' k_a g) (echgFTV a a' g')
          p1'              = chgFTV a a' p1
          p2'              = chgFTV a a' p2
          p_wenv_wf        = WFEBind env p_env_wf w  t k p_env_t
          p_w'env_wf       = WFEBind env p_env_wf w' t k p_env_t
          pf_w'env_ent_p2  = lem_change_var_ent (concatE (ConsT a k_a g) g') w t Empty p_wenv_wf
                                 (unbind 0 w p2 ? lem_free_subset_binds env t' k' p_env_t') 
                                 pf_wenv_ent_p2 
                                 (w' ? lem_free_bound_in_env env t' k' p_env_t' w')
                                 ? lem_subFV_unbind 0 w (FV w') p2
          pf_w'env'_ent_p2 = lem_change_tvar_ent g a k_a (Cons w' t g') 
                                 p_w'env_wf (unbind 0 w' p2) pf_w'env_ent_p2 a' 
                                 ? lem_commute_chgFTV_unbind a a' 0 w' p2 

{-@ lem_change_tvar_subtype_sfunc :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
      -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (ConsT a k_a g) g'))
      -> t:Type  -> k:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE (ConsT a k_a g) g') t t' && isSFunc p_t_t' } 
      -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
                                                       (tchgFTV a a' t) (tchgFTV a a' t') &&
                         subtypSize p_t_t'  == subtypSize p'_t_t' &&
                         subtypSize' p_t_t' == subtypSize' p'_t_t' } / [subtypSize p_t_t', 0] @-}
lem_change_tvar_subtype_sfunc :: Env -> Vname -> Kind -> Env -> WFEnv -> Type -> Kind -> WFType 
                              -> Type -> Kind -> WFType -> Subtype -> Vname -> Subtype
lem_change_tvar_subtype_sfunc g a k_a g' p_env_wf ft1 k1 p_env_ft1 ft2 k2 p_env_ft2 
                       (SFunc env z1 s1 z2 s2 p_env_s2_s1 t1 t2 w p_wenv_t1_t2) a'_
    = SFunc env' z1 (tchgFTV a a' s1) z2 (tchgFTV a a' s2)    p_env'_s2_s1 
                    (tchgFTV a a' t1)    (tchgFTV a a' t2) w' p_w'env'_t1_t2
        where
          (WFFunc _ _ _ k_s1 p_env_s1 _ k_t1 w1 p_w1'env_t1) 
                         = lem_wffunc_for_wf_tfunc (concatE (ConsT a k_a g) g') z1 s1 t1 k1 p_env_ft1
          (WFFunc _ _ _ k_s2 p_env_s2 _ k_t2 w2 p_w2env_t2)  
                         = lem_wffunc_for_wf_tfunc (concatE (ConsT a k_a g) g') z2 s2 t2 k2 p_env_ft2
          w'             = fresh_var_excluding (concatE (ConsT a k_a g) g') a'_
          a'             = a'_ ? lem_in_env_concat g g' a'_
                               ? lem_in_env_concat g (Cons w' s2 g') a'_
                               ? lem_in_env_concat (ConsT a k_a g) g' a'_
          env'           = concatE (ConsT a' k_a g) (echgFTV a a' g')
          p_wenv_wf      = WFEBind env p_env_wf w  s2 k_s2 p_env_s2
          p_w1env_wf     = WFEBind env p_env_wf w1 s2 k_s2 p_env_s2
          p_w2env_wf     = WFEBind env p_env_wf w2 s2 k_s2 p_env_s2
          p_w'env_wf     = WFEBind env p_env_wf w' s2 k_s2 p_env_s2
          p_w1env_t1     = lem_subtype_in_env_wf env Empty w1 s2 s1 p_env_s2_s1 
                                                 (unbindT z1 w1 t1) k_t1 p_w1'env_t1
          p_wenv_t1      = lem_change_var_wf' (concatE (ConsT a k_a g) g') w1 s2 Empty p_w1env_wf
                                              (unbindT z1 w1 t1) k_t1 p_w1env_t1 w
                                              ? lem_tsubFV_unbindT z1 w1 (FV w) t1
          p_wenv_t2      = lem_change_var_wf' (concatE (ConsT a k_a g) g') w2 s2 Empty p_w2env_wf
                                              (unbindT z2 w2 t2) k_t2 p_w2env_t2 w
                                              ? lem_tsubFV_unbindT z2 w2 (FV w) t2
          p_w'env_t1     = lem_change_var_wf' (concatE (ConsT a k_a g) g') w1 s2 Empty p_w1env_wf
                                              (unbindT z1 w1 t1) k_t1 p_w1env_t1 w'
                                              ? lem_tsubFV_unbindT z1 w1 (FV w') t1
          p_w'env_t2     = lem_change_var_wf' (concatE (ConsT a k_a g) g') w2 s2 Empty p_w2env_wf
                                              (unbindT z2 w2 t2) k_t2 p_w2env_t2 w'
                                              ? lem_tsubFV_unbindT z2 w2 (FV w') t2
          p_env'_s2_s1   = lem_change_tvar_subtype g a k_a g' p_env_wf s2 k_s2 p_env_s2 s1 k_s1 
                                                   p_env_s1  p_env_s2_s1 a'

          p_w'env_t1_t2  = lem_change_var_subtype (concatE (ConsT a k_a g) g') w s2 Empty p_wenv_wf
                                   (unbindT z1 w t1) k_t1 p_wenv_t1 (unbindT z2 w t2) k_t2 p_wenv_t2
                                   p_wenv_t1_t2 
                                   ( w' ? lem_free_bound_in_env env ft1 k1 p_env_ft1 w'
                                        ? lem_free_bound_in_env env ft2 k2 p_env_ft2 w' )
                                   ? lem_tsubFV_unbindT z1 w (FV w') t1
                                   ? lem_tsubFV_unbindT z2 w (FV w') t2
          p_w'env'_t1_t2 = lem_change_tvar_subtype g a k_a (Cons w' s2 g') p_w'env_wf
                                   (unbindT z1 w' t1) k_t1 p_w'env_t1 (unbindT z2 w' t2) k_t2 p_w'env_t2
                                   p_w'env_t1_t2 a'
                                   ? lem_commute_tchgFTV_unbindT a a' z1 w' t1
                                   ? lem_commute_tchgFTV_unbindT a a' z2 w' t2

{-@ lem_change_tvar_subtype_switn :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
      -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (ConsT a k_a g) g'))
      -> t:Type  -> k:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE (ConsT a k_a g) g') t t' && isSWitn p_t_t' } 
      -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
                                                       (tchgFTV a a' t) (tchgFTV a a' t') &&
                         subtypSize p_t_t'  == subtypSize p'_t_t' &&
                         subtypSize' p_t_t' == subtypSize' p'_t_t' } / [subtypSize p_t_t', 0] @-}
lem_change_tvar_subtype_switn :: Env -> Vname -> Kind -> Env -> WFEnv -> Type -> Kind -> WFType 
                              -> Type -> Kind -> WFType -> Subtype -> Vname -> Subtype
lem_change_tvar_subtype_switn g a k_a g' p_env_wf t k p_env_t t2 k2 p_env_t2
                       (SWitn env v_z t_z p_env_vz_tz _t z t' p_env_t_t'vz) a'_ 
    = SWitn env' (chgFTV a a' v_z) (tchgFTV a a' t_z) p_env'_vz_tz
                 (tchgFTV a a' t) z (tchgFTV a a' t') p_env'_t_t'vz
        where
          (WFExis _ _ _ k_z p_env_tz _ k' z' p_z'env_t') 
                        = lem_wfexis_for_wf_texists (concatE (ConsT a k_a g) g') z t_z t' k2 p_env_t2
          a'            = a'_ ? lem_in_env_concat g g' a'_
                              ? lem_in_env_concat (ConsT a k_a g) g' a'_
          env'          = concatE (ConsT a' k_a g) (echgFTV a a' g')
          p_z'env_wf    = WFEBind env p_env_wf z' t_z k_z p_env_tz
          p_env_t'vz    = lem_subst_wf' (concatE (ConsT a k_a g) g') Empty z' v_z t_z p_env_vz_tz 
                                        p_z'env_wf (unbindT z z' t') k' p_z'env_t'
          p_env'_vz_tz  = lem_change_tvar_typ g a k_a g' p_env_wf v_z t_z p_env_vz_tz a'
                                              ? lem_tsubFV_unbindT z z' v_z t'
          p_env'_t_t'vz = lem_change_tvar_subtype g a k_a g' p_env_wf t k p_env_t
                                                  (tsubBV z v_z t') k' p_env_t'vz p_env_t_t'vz a'
                                                  ? lem_commute_tchgFTV_tsubBV z v_z a a' t' 

{-@ lem_change_tvar_subtype_sbind :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
      -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (ConsT a k_a g) g'))
      -> t:Type  -> k:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE (ConsT a k_a g) g') t t' && isSBind p_t_t' } 
      -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
                                                       (tchgFTV a a' t) (tchgFTV a a' t') &&
                         subtypSize p_t_t'  == subtypSize p'_t_t' &&
                         subtypSize' p_t_t' == subtypSize' p'_t_t' } / [subtypSize p_t_t', 0] @-}
lem_change_tvar_subtype_sbind :: Env -> Vname -> Kind -> Env -> WFEnv -> Type -> Kind -> WFType 
                              -> Type -> Kind -> WFType -> Subtype -> Vname -> Subtype
lem_change_tvar_subtype_sbind g a k_a g' p_env_wf t1 k1 p_env_t1 t' k' p_env_t'
                       (SBind env z t_z t _t' z' p_z'env_t_t') a'_
    = SBind env' z (tchgFTV a a' t_z) (tchgFTV a a' t) (tchgFTV a a' t') z'' p_z''env'_t_t'
        where
          (WFExis _ _ _ k_z p_env_tz _ k w p_wenv_t) 
                         = lem_wfexis_for_wf_texists (concatE (ConsT a k_a g) g') z t_z t k1 p_env_t1
          z''_           = fresh_var_excluding (concatE (ConsT a k_a g) g') a'_
          z''            = z''_ ? lem_free_bound_in_env env t1 k1 p_env_t1 z''_
                                ? lem_free_bound_in_env env t' k' p_env_t' z''_
          a'             = a'_ ? lem_in_env_concat g g' a'_
                               ? lem_in_env_concat (ConsT a k_a g) g' a'_
          env'           = concatE (ConsT a' k_a g) (echgFTV a a' g')
          p_wenv_wf      = WFEBind env p_env_wf w   t_z k_z p_env_tz
          p_z'env_wf     = WFEBind env p_env_wf z'  t_z k_z p_env_tz
          p_z''env_wf    = WFEBind env p_env_wf z'' t_z k_z p_env_tz
          p_z'env_t      = lem_change_var_wf' env w t_z Empty p_wenv_wf (unbindT z w t) k p_wenv_t z'
                                              ? lem_tsubFV_unbindT z w (FV z') t
          p_z''env_t     = lem_change_var_wf' env w t_z Empty p_wenv_wf (unbindT z w t) k p_wenv_t z''
                                              ? lem_tsubFV_unbindT z w (FV z'') t
          p_z'env_t'     = lem_weaken_wf' env Empty p_env_wf t' k' p_env_t' z'  t_z
          p_z''env_t'    = lem_weaken_wf' env Empty p_env_wf t' k' p_env_t' z'' t_z
          p_z''env_t_t'  = lem_change_var_subtype (concatE (ConsT a k_a g) g') z' t_z Empty
                                   p_z'env_wf (unbindT z z' t) k p_z'env_t t' k' p_z'env_t' 
                                   p_z'env_t_t' z'' 
                                   ? lem_tsubFV_unbindT z z' (FV z'') t
                                   ? lem_free_bound_in_env env t' k' p_env_t' z'
                                   ? lem_tsubFV_notin z' (FV z'') t'
          p_z''env'_t_t' = lem_change_tvar_subtype g a k_a (Cons z'' t_z g') p_z''env_wf
                                   (unbindT z z'' t) k p_z''env_t t' k' p_z''env_t' p_z''env_t_t' a'
                                   ? lem_commute_tchgFTV_unbindT a a' z z'' t

{-@ lem_change_tvar_subtype_spoly :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
      -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (ConsT a k_a g) g'))
      -> t:Type  -> k:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE (ConsT a k_a g) g') t t' && isSPoly p_t_t' } 
      -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
                                                       (tchgFTV a a' t) (tchgFTV a a' t') &&
                         subtypSize p_t_t'  == subtypSize p'_t_t' &&
                         subtypSize' p_t_t' == subtypSize' p'_t_t' } / [subtypSize p_t_t', 0] @-}
lem_change_tvar_subtype_spoly :: Env -> Vname -> Kind -> Env -> WFEnv -> Type -> Kind -> WFType 
                              -> Type -> Kind -> WFType -> Subtype -> Vname -> Subtype
lem_change_tvar_subtype_spoly g a k_a g' p_env_wf t1 Star p_env_t1 t2 Star p_env_t2 
                             (SPoly env a1 k' t1' a2 t2' a1' p_a1'g_t1'_t2') a'
    = SPoly (concatE (ConsT a' k_a g) (echgFTV a a' g')) a1 k' (tchgFTV a a' t1')
            a2 (tchgFTV a a' t2') a1'' p_a1''y_t1'_t2'
        where
          (WFPoly _ _ _ _ k_t1' aa1 p_aa1env_t1')
                          = lem_wfpoly_for_wf_tpoly env a1 k' t1' p_env_t1
          (WFPoly _ _ _ _ k_t2' aa2 p_aa2env_t2')
                          = lem_wfpoly_for_wf_tpoly env a2 k' t2' p_env_t2
          a1''_           = fresh_var_excluding (concatE (ConsT a k_a g) g') a'
          a1''            = a1''_ ? lem_in_env_concat g g' a1''_
                                  ? lem_in_env_concat (ConsT a  k_a g) g' a1''_
                                  ? lem_in_env_concat (ConsT a' k_a g) g' a1''_
                                  ? lem_free_bound_in_env env t1 Star p_env_t1 a1''_
                                  ? lem_free_bound_in_env env t2 Star p_env_t2 a1''_
          p_aa1env_wf     = WFEBindT env p_env_wf aa1  k'
          p_aa2env_wf     = WFEBindT env p_env_wf aa2  k'
          p_a1'env_wf     = WFEBindT env p_env_wf a1'  k'
          p_a1''env_wf    = WFEBindT env p_env_wf a1'' k'
          p_a1'env_t1'    = lem_change_tvar_wf' (concatE (ConsT a k_a g) g') aa1 k' Empty p_aa1env_wf
                                  (unbind_tvT a1 aa1 t1') k_t1' p_aa1env_t1' a1'
                                  ? lem_tchgFTV_unbind_tvT a1 aa1 a1' t1'
          p_a1'env_t2'    = lem_change_tvar_wf' (concatE (ConsT a k_a g) g') aa2 k' Empty p_aa2env_wf
                                  (unbind_tvT a2 aa2 t2') k_t2' p_aa2env_t2' a1'
                                  ? lem_tchgFTV_unbind_tvT a2 aa2 a1' t2'
          p_a1''env_t1'   = lem_change_tvar_wf' (concatE (ConsT a k_a g) g') aa1 k' Empty p_aa1env_wf
                                  (unbind_tvT a1 aa1 t1') k_t1' p_aa1env_t1' a1''
                                  ? lem_tchgFTV_unbind_tvT a1 aa1 a1'' t1'
          p_a1''env_t2'   = lem_change_tvar_wf' (concatE (ConsT a k_a g) g') aa2 k' Empty p_aa2env_wf
                                  (unbind_tvT a2 aa2 t2') k_t2' p_aa2env_t2' a1''
                                  ? lem_tchgFTV_unbind_tvT a2 aa2 a1'' t2'
          p_a1''_t1'_t2'  = lem_change_tvar_subtype (concatE (ConsT a k_a g) g') a1' k' Empty p_a1'env_wf
                                  (unbind_tvT a1 a1' t1') k_t1' p_a1'env_t1'
                                  (unbind_tvT a2 a1' t2') k_t2' p_a1'env_t2' p_a1'g_t1'_t2' a1''
                                  ? lem_tchgFTV_unbind_tvT a1 a1' a1'' t1'
                                  ? lem_tchgFTV_unbind_tvT a2 a1' a1'' t2'
          p_a1''y_t1'_t2' = lem_change_tvar_subtype g a k_a (ConsT a1'' k' g') p_a1''env_wf
                                  (unbind_tvT a1 a1'' t1') k_t1' p_a1''env_t1'
                                  (unbind_tvT a2 a1'' t2') k_t2' p_a1''env_t2' p_a1''_t1'_t2' a'
                                  ? lem_commute_tchgFTV_unbind_tvT a a' a1 a1'' t1'
                                  ? lem_commute_tchgFTV_unbind_tvT a a' a2 a1'' t2'
lem_change_tvar_subtype_spoly g a k_a g' p_env_wf t1 Base p_env_t1 t2 k2 p_env_t2 
                              (SPoly env a1 k' t1' a2 t2' a1' p_a1'g_t1'_t2') a'
    = impossible ("by lemma" ? lem_wf_tpoly_star env a1 k' t1' p_env_t1)
lem_change_tvar_subtype_spoly g a k_a g' p_env_wf t1 k1   p_env_t1 t2 Base p_env_t2 
                              (SPoly env a1 k' t1' a2 t2' a1' p_a1'g_t1'_t2') a'
    = impossible ("by lemma" ? lem_wf_tpoly_star env a2 k' t2' p_env_t2)


{-@ lem_change_tvar_subtype :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
      -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (ConsT a k_a g) g'))
      -> t:Type  -> k:Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') t k) 
      -> t':Type -> k':Kind -> ProofOf(WFType (concatE (ConsT a k_a g) g') t' k')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE (ConsT a k_a g) g') t t' } 
      -> { a':Vname | not (in_env a' g) && not (in_env a' g') }
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (ConsT a' k_a g) (echgFTV a a' g')) 
                                                       (tchgFTV a a' t) (tchgFTV a a' t') &&
                         subtypSize p_t_t'  == subtypSize p'_t_t' &&
                         subtypSize' p_t_t' == subtypSize' p'_t_t' } / [subtypSize p_t_t', 1] @-}
lem_change_tvar_subtype :: Env -> Vname -> Kind -> Env -> WFEnv -> Type -> Kind -> WFType 
                              -> Type -> Kind -> WFType -> Subtype -> Vname -> Subtype
lem_change_tvar_subtype g a k_a g' p_env_wf t k p_env_t t' k' p_env_t' p_t_t'@(SBase {}) a' 
    = lem_change_tvar_subtype_sbase g a k_a g' p_env_wf t k p_env_t t' k' p_env_t' p_t_t' a'
lem_change_tvar_subtype g a k_a g' p_env_wf t k p_env_t t' k' p_env_t' p_t_t'@(SFunc {}) a' 
    = lem_change_tvar_subtype_sfunc g a k_a g' p_env_wf t k p_env_t t' k' p_env_t' p_t_t' a'
lem_change_tvar_subtype g a k_a g' p_env_wf t k p_env_t t' k' p_env_t' p_t_t'@(SWitn {}) a' 
    = lem_change_tvar_subtype_switn g a k_a g' p_env_wf t k p_env_t t' k' p_env_t' p_t_t' a'
lem_change_tvar_subtype g a k_a g' p_env_wf t k p_env_t t' k' p_env_t' p_t_t'@(SBind {}) a' 
    = lem_change_tvar_subtype_sbind g a k_a g' p_env_wf t k p_env_t t' k' p_env_t' p_t_t' a'
lem_change_tvar_subtype g a k_a g' p_env_wf t k p_env_t t' k' p_env_t' p_t_t'@(SPoly {}) a' 
    = lem_change_tvar_subtype_spoly g a k_a g' p_env_wf t k p_env_t t' k' p_env_t' p_t_t' a'
