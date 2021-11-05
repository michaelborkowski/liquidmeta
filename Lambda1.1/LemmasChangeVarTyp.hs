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
import Entailments
import LemmasChangeVarWF
import LemmasChangeVarEnt
import LemmasWeakenWF
import LemmasWellFormedness
import LemmasTyping
import SubstitutionLemmaWF

{-@ reflect foo44 @-}
foo44 x = Just x
foo44 :: a -> Maybe a

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
lem_change_var_typ_tvar1 g x t_x g' p_env_wf e t (TVar1 _ z t' p_env'_t') y  -- t == self t' (FV z)
    = case g' of 
        (Empty)           -> TVar1 g y (tsubFV x (FV y) t_x)  
                                   (p_env'_t' ? lem_tsubFV_notin x (FV y) (t_x
                                                              ? lem_free_bound_in_env g t_x p_g_tx x))
        {- x = z and t_x = t' -}   ? lem_tsubFV_self1 x y t' z 
          where
            (WFEBind _g p_g_wf _x _tx p_g_tx) = p_env_wf
        (Cons _z _ g'')   -> TVar1 (concatE (Cons y t_x g) (esubFV x (FV y) g'')) 
                                   (z ? lem_in_env_esub g'' x (FV y) z 
                                      ? lem_in_env_concat g g'' z
                                      ? lem_in_env_concat (Cons x t_x g) g'' z)
                                   (tsubFV x (FV y) t') p'_env'_t'
                                                              ? lem_tsubFV_self2 x (FV y) t' z 
          where
            p'_env'_t' = lem_change_var_wf g x t_x g'' t' p_env'_t' y

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
lem_change_var_typ_tvar2 g x t_x g' p_env_wf e t (TVar2 _ z _t p_z_t w t_w) y
    = case g' of             -- g''=Emp so x=w and p_z_t :: HasBType(g (FV z) t)
        (Empty)           -> case (x == z) of
                                (True)  -> impossible "it is"
                                (False) -> TVar2 g z t p_z_t  
                                             (y ? lem_free_bound_in_env g t p_g_t y ) t_x
                                             ? toProof ( tsubFV x (FV y) t === t )
                                  where
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
lem_change_var_typ_tabs g x t_x g' p_env_wf e t p_e_t@(TAbs env z t_z p_env_tz e' t' z' p_z'_e'_t') y
    = TAbs (concatE (Cons y t_x g) (esubFV x (FV y) g')) z (tsubFV x (FV y) t_z) 
           p_env'_tz (subFV x (FV y) e') (tsubFV x (FV y) t')  z'' p_z''y_e'_t'
        where
          p_env_t      = lem_typing_wf env e t p_e_t p_env_wf
          p_env'_tz    = lem_change_var_wf g x t_x g' t_z  p_env_tz y
          z''_         = fresh_var_excluding (concatE (Cons x t_x g) g') y
          z''          = z''_ ? lem_in_env_concat g g' z''_
                              ? lem_in_env_concat (Cons x t_x g) g' z''_
                              ? lem_fv_bound_in_env (concatE (Cons x t_x g) g') e t p_e_t p_env_wf z''_
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
                   p_e_t@(TLet env e_z t_z p_env_ez_tz z e' t' p_env_t' z' p_z'env_e'_t') y
    = TLet (concatE (Cons y t_x g) (esubFV x (FV y) g')) (subFV x (FV y) e_z) (tsubFV x (FV y) t_z)
           p_env'_ez_tz z (subFV x (FV y) e') (tsubFV x (FV y) t') p_env'_t' z'' p_z''env'_e'_t'
        where
          p_env_t         = lem_typing_wf env e t p_e_t p_env_wf
          p_env_tz        = lem_typing_wf env e_z t_z p_env_ez_tz p_env_wf
          p_env'_t'       = lem_change_var_wf g x t_x g' t' p_env_t' y
          z''_            = fresh_var_excluding (concatE (Cons x t_x g) g') y
          z''             = z''_ ? lem_in_env_concat g g' z''_
                                 ? lem_in_env_concat (Cons x t_x g) g' z''_
                                 ? lem_fv_bound_in_env (concatE (Cons x t_x g) g') e t p_e_t p_env_wf z''_
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
lem_change_var_typ_tsub g x t_x g' p_env_wf e t p_e_t@(TSub env _e s p_env_e_s _t p_env_t p_env_s_t) y
    = TSub (concatE (Cons y t_x g) (esubFV x (FV y) g')) (subFV x (FV y) e) (tsubFV x (FV y) s) 
           p_env'_e_s (tsubFV x (FV y) t) p_env'_t p_env'_s_t
        where
          p_env_s    = lem_typing_wf env e s p_env_e_s p_env_wf
          p_env'_e_s = lem_change_var_typ g x t_x g' p_env_wf e s p_env_e_s y
          p_env'_t   = lem_change_var_wf  g x t_x g' t p_env_t y
          p_env'_s_t = lem_change_var_subtype g x t_x g' p_env_wf s p_env_s t p_env_t p_env_s_t y

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
lem_change_var_typ g x t_x g' p_env_wf e t p_e_t@(TVar1 _ z t' p_env'_t') y  -- t == self t' (FV z)
    = lem_change_var_typ_tvar1 g x t_x g' p_env_wf e t p_e_t y
lem_change_var_typ g x t_x g' p_env_wf e t p_e_t@(TVar2 _ z _t p_z_t w t_w) y
    = lem_change_var_typ_tvar2 g x t_x g' p_env_wf e t p_e_t y
lem_change_var_typ g x t_x g' p_env_wf e t (TPrm _ c) y  
    = TPrm (concatE (Cons y t_x g) (esubFV x (FV y) g')) c ? lem_tsubFV_ty x (FV y) c
lem_change_var_typ g x t_x g' p_env_wf e t p_e_t@(TAbs env z t_z p_env_tz e' t' z' p_z'_e'_t') y
    = lem_change_var_typ_tabs g x t_x g' p_env_wf e t p_e_t y
lem_change_var_typ g x t_x g' p_env_wf e t p_e_t@(TApp env e1 z t1 t2 p_env_e1_t1t2 e2 p_env_e2_t1) y
    = lem_change_var_typ_tapp g x t_x g' p_env_wf e t p_e_t y
lem_change_var_typ g x t_x g' p_env_wf e t 
                   p_e_t@(TLet env e_z t_z p_env_ez_tz z e' t' p_env_t' z' p_z'env_e'_t') y
    = lem_change_var_typ_tlet g x t_x g' p_env_wf e t p_e_t y
lem_change_var_typ g x t_x g' p_env_wf e t p_e_t@(TAnn env e' _t p_env_e'_t) y
    = lem_change_var_typ_tann g x t_x g' p_env_wf e t p_e_t y
lem_change_var_typ g x t_x g' p_env_wf e t p_e_t@(TSub env _e s p_env_e_s _t p_env_t p_env_s_t) y
    = lem_change_var_typ_tsub g x t_x g' p_env_wf e t p_e_t y


{-@ lem_change_var_subtype_sbase :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
      -> t:Type  -> ProofOf(WFType (concatE (Cons x t_x g) g') t ) 
      -> t':Type -> ProofOf(WFType (concatE (Cons x t_x g) g') t')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE (Cons x t_x g) g') t t' && isSBase p_t_t'} 
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                         (tsubFV x (FV y) t) (tsubFV x (FV y) t') &&
                         subtypSize  p_t_t' == subtypSize  p'_t_t' &&
                         subtypSize' p_t_t' == subtypSize' p'_t_t' } / [subtypSize p_t_t', 0] @-}
lem_change_var_subtype_sbase :: Env -> Vname -> Type -> Env -> WFEnv -> Type -> WFType 
                              -> Type -> WFType -> Subtype -> Vname -> Subtype
lem_change_var_subtype_sbase g x t_x g' p_env_wf t p_env_t t' p_env_t' 
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

{-@ lem_change_var_subtype_sfunc :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
      -> t:Type  -> ProofOf(WFType (concatE (Cons x t_x g) g') t ) 
      -> t':Type -> ProofOf(WFType (concatE (Cons x t_x g) g') t')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE (Cons x t_x g) g') t t' && isSFunc p_t_t'} 
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                         (tsubFV x (FV y) t) (tsubFV x (FV y) t') &&
                         subtypSize  p_t_t' == subtypSize  p'_t_t' &&
                         subtypSize' p_t_t' == subtypSize' p'_t_t' } / [subtypSize p_t_t', 0] @-}
lem_change_var_subtype_sfunc :: Env -> Vname -> Type -> Env -> WFEnv -> Type -> WFType 
                              -> Type -> WFType -> Subtype -> Vname -> Subtype
lem_change_var_subtype_sfunc g x t_x g' p_env_wf ft1 p_env_ft1 ft2 p_env_ft2 
                       (SFunc env z1 s1 z2 s2 p_env_s2_s1 t1 t2 w p_wenv_t1_t2) y_ 
    = SFunc env' z1 (tsubFV x (FV y) s1) z2 (tsubFV x (FV y) s2) p_env'_s2_s1 
                    (tsubFV x (FV y) t1) (tsubFV x (FV y) t2) w' p_w'env'_t1_t2
        where
          (WFFunc _ _ _ p_env_s1 _ w1 p_w1'env_t1) = p_env_ft1
          (WFFunc _ _ _ p_env_s2 _ w2 p_w2env_t2)  = p_env_ft2
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
          p_env'_s2_s1   = lem_change_var_subtype g x t_x g' p_env_wf s2 p_env_s2 s1 
                                                  p_env_s1  p_env_s2_s1 y
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

{-@ lem_change_var_subtype_switn :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
      -> t:Type  -> ProofOf(WFType (concatE (Cons x t_x g) g') t ) 
      -> t':Type -> ProofOf(WFType (concatE (Cons x t_x g) g') t')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE (Cons x t_x g) g') t t' && isSWitn p_t_t'} 
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                         (tsubFV x (FV y) t) (tsubFV x (FV y) t') &&
                         subtypSize  p_t_t' == subtypSize  p'_t_t' &&
                         subtypSize' p_t_t' == subtypSize' p'_t_t' } / [subtypSize p_t_t', 0] @-}
lem_change_var_subtype_switn :: Env -> Vname -> Type -> Env -> WFEnv -> Type -> WFType 
                              -> Type -> WFType -> Subtype -> Vname -> Subtype
lem_change_var_subtype_switn g x t_x g' p_env_wf t p_env_t t2 p_env_t2
                       (SWitn env v_z t_z p_env_vz_tz _t z t' p_env_t_t'vz) y_ 
    = SWitn env' (subFV x (FV y) v_z) (tsubFV x (FV y) t_z) p_env'_vz_tz
                 (tsubFV x (FV y) t) z (tsubFV x (FV y) t') p_env'_t_t'vz
        where
          (WFExis _ _ _ p_env_tz _ z' p_z'env_t') = p_env_t2
          y             = y_ ? lem_in_env_concat g g' y_
                             ? lem_in_env_concat (Cons x t_x g) g' y_
          env'          = concatE (Cons y t_x g) (esubFV x (FV y) g')
          p_z'env_wf    = WFEBind env p_env_wf z' t_z p_env_tz
          p_env_t'vz    = lem_subst_wf' (concatE (Cons x t_x g) g') Empty z' v_z t_z p_env_vz_tz 
                                        p_z'env_wf (unbindT z z' t') p_z'env_t'
                                        ? lem_tsubFV_unbindT z z' v_z t'
          p_env'_vz_tz  = lem_change_var_typ g x t_x g' p_env_wf v_z t_z p_env_vz_tz y    
                                             ? lem_tsubFV_unbindT z z' v_z t'
          p_env'_t_t'vz = lem_change_var_subtype g x t_x g' p_env_wf t p_env_t
                                                 (tsubBV z v_z t') p_env_t'vz p_env_t_t'vz y
                                                 ? lem_commute_tsubFV_tsubBV z v_z x (FV y) t' 

{-@ lem_change_var_subtype_sbind :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
      -> t:Type  -> ProofOf(WFType (concatE (Cons x t_x g) g') t ) 
      -> t':Type -> ProofOf(WFType (concatE (Cons x t_x g) g') t')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE (Cons x t_x g) g') t t' && isSBind p_t_t'} 
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                         (tsubFV x (FV y) t) (tsubFV x (FV y) t') &&
                         subtypSize  p_t_t' == subtypSize  p'_t_t' &&
                         subtypSize' p_t_t' == subtypSize' p'_t_t' } / [subtypSize p_t_t', 0] @-}
lem_change_var_subtype_sbind :: Env -> Vname -> Type -> Env -> WFEnv -> Type -> WFType 
                              -> Type -> WFType -> Subtype -> Vname -> Subtype
lem_change_var_subtype_sbind g x t_x g' p_env_wf t1 p_env_t1 t' p_env_t'
                       (SBind env z t_z t _t' z' p_z'env_t_t') y_  
    = SBind env' z (tsubFV x (FV y) t_z) (tsubFV x (FV y) t) (tsubFV x (FV y) t') z'' p_z''env'_t_t'
        where
          (WFExis _ _ _ p_env_tz _  w p_wenv_t) = p_env_t1
          z''_           = fresh_var_excluding (concatE (Cons x t_x g) g') y_
          z''            = z''_ ? lem_free_bound_in_env env t1 p_env_t1 z''_
                                ? lem_free_bound_in_env env t' p_env_t' z''_
          y              = y_ ? lem_in_env_concat g g' y_
                              ? lem_in_env_concat (Cons x t_x g) g' y_
          env'           = concatE (Cons y t_x g) (esubFV x (FV y) g')
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
                                   ? lem_tsubFV_notin z' (FV z'') t'
          p_z''env'_t_t' = lem_change_var_subtype g x t_x (Cons z'' t_z g') p_z''env_wf
                                   (unbindT z z'' t) p_z''env_t t' p_z''env_t' p_z''env_t_t' y
                                   ? lem_commute_tsubFV_unbindT x y z z'' t

{-@ lem_change_var_subtype :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
      -> t:Type  -> ProofOf(WFType (concatE (Cons x t_x g) g') t) 
      -> t':Type -> ProofOf(WFType (concatE (Cons x t_x g) g') t')
      -> { p_t_t':Subtype | propOf p_t_t' == Subtype (concatE (Cons x t_x g) g') t t' } 
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { p'_t_t':Subtype | propOf p'_t_t' == Subtype (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                         (tsubFV x (FV y) t) (tsubFV x (FV y) t') &&
                         subtypSize  p_t_t' == subtypSize  p'_t_t' &&
                         subtypSize' p_t_t' == subtypSize' p'_t_t' } / [subtypSize p_t_t', 1] @-}
lem_change_var_subtype :: Env -> Vname -> Type -> Env -> WFEnv -> Type -> WFType 
                              -> Type -> WFType -> Subtype -> Vname -> Subtype
lem_change_var_subtype g x t_x g' p_env_wf t p_env_t t' p_env_t' 
                       p_t_t'@(SBase env z1 b p1 z2 p2 w pf_wenv_ent_p2) y_ 
  = lem_change_var_subtype_sbase g x t_x g' p_env_wf t p_env_t t' p_env_t' p_t_t' y_ 
lem_change_var_subtype g x t_x g' p_env_wf ft1 p_env_ft1 ft2 p_env_ft2 
                       p_ft1_ft2@(SFunc env z1 s1 z2 s2 p_env_s2_s1 t1 t2 w p_wenv_t1_t2) y_ 
  = lem_change_var_subtype_sfunc g x t_x g' p_env_wf ft1 p_env_ft1 ft2 p_env_ft2 p_ft1_ft2 y_ 
lem_change_var_subtype g x t_x g' p_env_wf t p_env_t t2 p_env_t2
                       p_t_t2@(SWitn env v_z t_z p_env_vz_tz _t z t' p_env_t_t'vz) y_ 
  = lem_change_var_subtype_switn g x t_x g' p_env_wf t p_env_t t2 p_env_t2 p_t_t2 y_
lem_change_var_subtype g x t_x g' p_env_wf t1 p_env_t1 t' p_env_t'
                       p_t1_t'@(SBind env z t_z t _t' z' p_z'env_t_t') y_ 
  = lem_change_var_subtype_sbind g x t_x g' p_env_wf t1 p_env_t1 t' p_env_t' p_t1_t' y_
