{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module BasicPropsEnvironments where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import SystemFWellFormedness
import SystemFTyping
import BasicPropsSubstitution

----------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of ENVIRONMENTS / BARE-TYPED ENVIRONMENTS
----------------------------------------------------------------------------

{-@ reflect concatE @-}
{-@ concatE :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
                     -> { h:Env | binds h   == (Set_cup (binds g)   (binds g')) &&
                                  vbinds h  == (Set_cup (vbinds g)  (vbinds g')) &&
                                  tvbinds h == (Set_cup (tvbinds g) (tvbinds g')) } @-}
concatE :: Env -> Env -> Env
concatE g Empty          = g
concatE g (Cons  x t g') = Cons x t  (concatE g g')
concatE g (ConsT a k g') = ConsT a k (concatE g g')

{-@ lem_empty_concatE :: g:Env -> { pf:_ | concatE Empty g == g } @-}
lem_empty_concatE :: Env -> Proof
lem_empty_concatE Empty         = ()
lem_empty_concatE (Cons  x t g) = () ? lem_empty_concatE g
lem_empty_concatE (ConsT a k g) = () ? lem_empty_concatE g

{-@ lem_in_env_concat :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
      ->  x:Vname -> {pf:_ | (in_env x (concatE g g')) <=> ((in_env x g) || (in_env x g'))} @-}
lem_in_env_concat :: Env -> Env -> Vname -> Proof
lem_in_env_concat g Empty          x = ()
lem_in_env_concat g (Cons  y s g') x = () ? lem_in_env_concat g g' x 
lem_in_env_concat g (ConsT a k g') x = () ? lem_in_env_concat g g' x

{-@ lem_erase_tsubFV :: x:Vname -> v:Value -> t:Type 
                                -> { pf:_ | erase (tsubFV x v t) == erase t } @-}
lem_erase_tsubFV :: Vname -> Expr -> Type -> Proof
lem_erase_tsubFV x v (TRefn   b  ps) = ()
lem_erase_tsubFV x v (TFunc   t_z t) = () ? lem_erase_tsubFV x v t_z
                                          ? lem_erase_tsubFV x v t
lem_erase_tsubFV x v (TExists t_z t) = () ? lem_erase_tsubFV x v t
lem_erase_tsubFV x v (TPoly   k   t) = () ? lem_erase_tsubFV x v t

{-@ lem_erase_unbind_tvT :: a':Vname -> t:Type 
	-> { pf:_ | erase (unbind_tvT a' t) == unbindFT a' (erase t) } @-}
lem_erase_unbind_tvT :: Vname -> Type -> Proof
lem_erase_unbind_tvT a' t = lem_erase_open_tvT_at 0 a' t

{-@ lem_erase_open_tvT_at :: j:Index -> a:Vname -> t:Type 
        -> { pf:_ | erase (open_tvT_at j a t) == openFT_at j a (erase t) } @-}
lem_erase_open_tvT_at :: Index -> Vname -> Type -> Proof
lem_erase_open_tvT_at j a (TRefn   b  ps) = case b of
  (BTV a') -> () 
  _        -> ()
lem_erase_open_tvT_at j a (TFunc   t_z t) = () ? lem_erase_open_tvT_at j a t_z
                                               ? lem_erase_open_tvT_at j a t
lem_erase_open_tvT_at j a (TExists t_z t) = () ? lem_erase_open_tvT_at j a t
lem_erase_open_tvT_at j a (TPoly    k1 t) = () ? lem_erase_open_tvT_at (j+1) a t

{-@ lem_erase_push :: ps:Preds -> t:UserType -> { pf:_ | erase (push ps t) == erase t } @-}
lem_erase_push :: Preds -> Type -> Proof
lem_erase_push ps (TRefn   b  rs) = ()
lem_erase_push ps (TFunc   t_y t) = () -- ? lem_erase_push p t_y ? lem_erase_push p t
lem_erase_push ps (TPoly   k_a t) = () -- ? lem_erase_push p t

{-@ lem_erase_tsubFTV :: a:Vname -> t_a:UserType -> t:Type
        -> { pf:_ | erase (tsubFTV a t_a t) == ftsubFV a (erase t_a) (erase t) } @-}
lem_erase_tsubFTV :: Vname -> Type -> Type -> Proof
lem_erase_tsubFTV a t_a (TRefn   b   ps) = case b of
  (FTV a') | a == a' -> () ? lem_erase_push (psubFTV a t_a ps) t_a 
  _                  -> ()
lem_erase_tsubFTV a t_a (TFunc    t_z t) = () ? lem_erase_tsubFTV a t_a t_z
                                              ? lem_erase_tsubFTV a t_a t
lem_erase_tsubFTV a t_a (TExists  t_z t) = () ? lem_erase_tsubFTV a t_a t
lem_erase_tsubFTV a t_a (TPoly     k' t) = () ? lem_erase_tsubFTV a t_a t

{-@ lem_erase_tsubBTV :: t_a:UserType -> t:Type
        -> { pf:_ | erase (tsubBTV t_a t) == ftsubBV (erase t_a) (erase t) } @-}
lem_erase_tsubBTV :: Type -> Type -> Proof
lem_erase_tsubBTV t_a t = lem_erase_tsubBTV_at 0 t_a t

{-@ lem_erase_tsubBTV_at :: j:Index -> t_a:UserType -> t:Type
        -> { pf:_ | erase (tsubBTV_at j t_a t) == ftsubBV_at j (erase t_a) (erase t) } @-}
lem_erase_tsubBTV_at :: Index -> Type -> Type -> Proof
lem_erase_tsubBTV_at j t_a (TRefn   b   p) = case b of
  (BTV i) | i == j -> () ? lem_erase_push (psubBTV_at j t_a p) t_a 
  _                -> ()
lem_erase_tsubBTV_at j t_a (TFunc   t_z t) = () ? lem_erase_tsubBTV_at j t_a t_z
                                                ? lem_erase_tsubBTV_at j t_a t
lem_erase_tsubBTV_at j t_a (TExists t_z t) = () ? lem_erase_tsubBTV_at j t_a t
lem_erase_tsubBTV_at j t_a (TPoly    k' t) = () ? lem_erase_tsubBTV_at (j+1) t_a t

{-@ reflect concatF @-}
{-@ concatF :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) } 
                      -> { h:FEnv  | bindsF h   == Set_cup (bindsF g)   (bindsF g') &&
                                     vbindsF h  == Set_cup (vbindsF g)  (vbindsF g') &&
                                     tvbindsF h == Set_cup (tvbindsF g) (tvbindsF g') } @-}
concatF :: FEnv -> FEnv -> FEnv
concatF g FEmpty          = g
concatF g (FCons  x t g') = FCons  x t (concatF g g')
concatF g (FConsT a k g') = FConsT a k (concatF g g')

{-@ lem_in_env_concatF :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) } 
      ->  x:Vname -> {pf:_ | (in_envF x (concatF g g')) <=> ((in_envF x g) || (in_envF x g'))} @-}
lem_in_env_concatF :: FEnv -> FEnv -> Vname -> Proof
lem_in_env_concatF g FEmpty          x = ()
lem_in_env_concatF g (FCons  y s g') x = () ? lem_in_env_concatF g g' x 
lem_in_env_concatF g (FConsT a k g') x = () ? lem_in_env_concatF g g' x 

{-@ lem_empty_concatF :: g:FEnv -> { pf:_ | concatF FEmpty g == g } @-}
lem_empty_concatF :: FEnv -> Proof
lem_empty_concatF FEmpty         = ()
lem_empty_concatF (FCons  x t g) = () ? lem_empty_concatF g
lem_empty_concatF (FConsT a k g) = () ? lem_empty_concatF g

{-@ lem_binds_cons_concatF :: g:FEnv -> g':FEnv -> x:Vname -> t_x:FType
      -> { pf:_ | Set_sub (bindsF (concatF g g'))   (bindsF (concatF (FCons x t_x g) g')) && 
                  Set_sub (vbindsF (concatF g g'))  (vbindsF (concatF (FCons x t_x g) g')) && 
                  Set_sub (tvbindsF (concatF g g')) (tvbindsF (concatF (FCons x t_x g) g')) && 
             bindsF (concatF (FCons x t_x g) g') == Set_cup (Set_cup (bindsF g) (Set_sng x)) (bindsF g') &&
             Set_sub (vbindsF (concatF g g')) (vbindsF (concatF (FCons x t_x g) g')) && 
             vbindsF (concatF (FCons x t_x g) g') == Set_cup (Set_cup (vbindsF g) (Set_sng x)) (vbindsF g') &&
             tvbindsF (concatF (FCons x t_x g) g') == Set_cup (tvbindsF g) (tvbindsF g') } @-}
lem_binds_cons_concatF :: FEnv -> FEnv -> Vname -> FType -> Proof
lem_binds_cons_concatF g FEmpty          x t = ()
lem_binds_cons_concatF g (FCons  y s g') x t = () ? lem_binds_cons_concatF g g' x t
lem_binds_cons_concatF g (FConsT a k g') x t = () ? lem_binds_cons_concatF g g' x t

{-@ lem_binds_consT_concatF :: g:FEnv -> g':FEnv -> a:Vname -> k:Kind
      -> { pf:_ | Set_sub (bindsF (concatF g g'))   (bindsF (concatF (FConsT a k g) g')) && 
                  Set_sub (vbindsF (concatF g g'))  (vbindsF (concatF (FConsT a k g) g')) && 
                  Set_sub (tvbindsF (concatF g g')) (tvbindsF (concatF (FConsT a k g) g')) && 
             bindsF (concatF (FConsT a k g) g') == Set_cup (Set_cup (bindsF g) (Set_sng a)) (bindsF g') &&
             vbindsF (concatF (FConsT a k g) g') == Set_cup (vbindsF g) (vbindsF g') &&
             Set_sub (tvbindsF (concatF g g')) (tvbindsF (concatF (FConsT a k g) g')) && 
             tvbindsF (concatF (FConsT a k g) g') == Set_cup (Set_cup (tvbindsF g) (Set_sng a)) (tvbindsF g') } @-}
lem_binds_consT_concatF :: FEnv -> FEnv -> Vname -> Kind -> Proof
lem_binds_consT_concatF g FEmpty            a k = ()
lem_binds_consT_concatF g (FCons  y  s  g') a k = () ? lem_binds_consT_concatF g g' a k
lem_binds_consT_concatF g (FConsT a' k' g') a k = () ? lem_binds_consT_concatF g g' a k

{-@ lem_erase_concat :: g:Env -> g':Env 
           -> { pf:_ |  erase_env (concatE g g') == concatF (erase_env g) (erase_env g') } @-}
lem_erase_concat :: Env -> Env -> Proof
lem_erase_concat g Empty          = ()
lem_erase_concat g (Cons  x t g') = () ? lem_erase_concat g g'
lem_erase_concat g (ConsT a k g') = () ? lem_erase_concat g g'

-- -- -- -- -- -- -- -- -- -- -- --
-- Substitutions in Environments --
-- -- -- -- -- -- -- -- -- -- -- --

{-@ reflect esubFV @-}
{-@ esubFV :: x:Vname -> v:Value -> g:Env 
      -> { g':Env | binds g == binds g' && vbinds g == vbinds g' && tvbinds g == tvbinds g' } @-}
esubFV :: Vname -> Expr -> Env -> Env
esubFV x e_x Empty           = Empty
esubFV x e_x (Cons  z t_z g) = Cons z (tsubFV x e_x t_z) (esubFV x e_x g)
esubFV x e_x (ConsT a k   g) = ConsT a k                 (esubFV x e_x g)

{-@ lem_in_env_esub :: g:Env -> x:Vname -> v_x:Value -> y:Vname
        -> { pf:_ | in_env y (esubFV x v_x g) <=> in_env y g } @-}
lem_in_env_esub :: Env -> Vname -> Expr -> Vname -> Proof
lem_in_env_esub Empty           x v_x y = ()
lem_in_env_esub (Cons  z t_z g) x v_x y = () ? lem_in_env_esub g x v_x y
lem_in_env_esub (ConsT a k   g) x v_x y = () ? lem_in_env_esub g x v_x y

{-@ lem_erase_esubFV :: x:Vname -> v:Value -> g:Env
        -> { pf:_ | erase_env (esubFV x v g) == erase_env g } @-}
lem_erase_esubFV :: Vname -> Expr -> Env -> Proof
lem_erase_esubFV x e (Empty)       = ()
lem_erase_esubFV x e (Cons  y t g) = () ? lem_erase_esubFV x e g
                                        ? lem_erase_tsubFV x e t
lem_erase_esubFV x e (ConsT a k g) = () ? lem_erase_esubFV x e g

{-@ reflect esubFTV @-}
{-@ esubFTV :: a:Vname -> t_a:UserType -> g:Env 
      -> { g':Env | binds g == binds g' && vbinds g == vbinds g' && tvbinds g == tvbinds g' } @-}
esubFTV :: Vname -> Type -> Env -> Env
esubFTV a t_a Empty           = Empty
esubFTV a t_a (Cons  z t_z g) = Cons z (tsubFTV a t_a t_z) (esubFTV a t_a g)
esubFTV a t_a (ConsT a' k' g) = ConsT a' k'                (esubFTV a t_a g)

{-@ lem_in_env_esubFTV :: g:Env -> a:Vname -> t_a:UserType -> y:Vname
        -> { pf:_ | in_env y (esubFTV a t_a g) <=> in_env y g } @-}
lem_in_env_esubFTV :: Env -> Vname -> Type -> Vname -> Proof
lem_in_env_esubFTV Empty           a t_a y = ()
lem_in_env_esubFTV (Cons  z t_z g) a t_a y = () ? lem_in_env_esubFTV g a t_a y
lem_in_env_esubFTV (ConsT a' k' g) a t_a y = () ? lem_in_env_esubFTV g a t_a y

{-@ lem_erase_esubFTV :: a:Vname -> t_a:UserType -> g:Env
        -> { pf:_ | erase_env (esubFTV a t_a g) == fesubFV a (erase t_a) (erase_env g) } @-}
lem_erase_esubFTV :: Vname -> Type -> Env -> Proof
lem_erase_esubFTV a t_a (Empty)        = ()
lem_erase_esubFTV a t_a (Cons  y t g)  = () ? lem_erase_esubFTV a t_a g
                                            ? lem_erase_tsubFTV a t_a t
lem_erase_esubFTV a t_a (ConsT a' k g) = () ? lem_erase_esubFTV a t_a g

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Substitutions in Systen F Environments --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --

{-@ reflect fesubFV @-}
{-@ fesubFV :: a:Vname -> t_a:FType -> g:FEnv 
      -> { g':FEnv | bindsF g == bindsF g' && vbindsF g == vbindsF g' && tvbindsF g == tvbindsF g' } @-}
fesubFV :: Vname -> FType -> FEnv -> FEnv
fesubFV a t_a  FEmpty          = FEmpty
fesubFV a t_a (FCons  z t_z g) = FCons z (ftsubFV a t_a t_z) (fesubFV a t_a g)
fesubFV a t_a (FConsT a1  k g) = FConsT a1 k                 (fesubFV a t_a g)

{-@ lem_in_fenv_fesub :: g:FEnv -> a:Vname -> t_a:FType -> y:Vname
        -> { pf:_ | in_envF y (fesubFV a t_a g) <=> in_envF y g } @-}
lem_in_fenv_fesub :: FEnv -> Vname -> FType -> Vname -> Proof
lem_in_fenv_fesub FEmpty           a t_a y = ()
lem_in_fenv_fesub (FCons  z t_z g) a t_a y = () ? lem_in_fenv_fesub g a t_a y
lem_in_fenv_fesub (FConsT a1 k  g) a t_a y = () ? lem_in_fenv_fesub g a t_a y

-----------------------------------------------------------------------------------------
----- | TECHNICAL LEMMAS relating to FREE VARIABLES and SYSTEM F judgments
-----------------------------------------------------------------------------------------

-- Lemma. All free variables in a (bare) typed expression are bound in the (bare) environment
{-@ lem_fv_bound_in_fenv :: g:FEnv -> e:Expr -> t:FType -> ProofOf(HasFType g e t)
                -> { x:Vname | not (in_envF x g) }
                -> { pf:_ | not (Set_mem x (fv e)) && not (Set_mem x (ftv e)) } / [esize e] @-}
lem_fv_bound_in_fenv :: FEnv -> Expr -> FType -> HasFType -> Vname -> Proof
lem_fv_bound_in_fenv g e t (FTBC _g b) x      = ()
lem_fv_bound_in_fenv g e t (FTIC _g n) x      = ()
lem_fv_bound_in_fenv g e t (FTVar1 _ y _t) x  = ()
lem_fv_bound_in_fenv g e t (FTVar2 _ y _t p_y_t z t') x = ()
lem_fv_bound_in_fenv g e t (FTVar3 _ y _y p_y_t z k)  x = ()
lem_fv_bound_in_fenv g e t (FTPrm _g c) x     = ()
lem_fv_bound_in_fenv g e t (FTAbs _g t_y _ _ e' t' nms mk_p_e'_t') x 
  = () ? lem_fv_bound_in_fenv (FCons y t_y g) (unbind y e') t' (mk_p_e'_t' y) x
      where 
        y = fresh_var_excludingF nms g x
lem_fv_bound_in_fenv g e t (FTApp _g e1 t_y t' p_e1_tyt' e2 p_e2_ty) x  
  = () ? lem_fv_bound_in_fenv g e1 (FTFunc t_y t') p_e1_tyt' x
       ? lem_fv_bound_in_fenv g e2 t_y p_e2_ty x
lem_fv_bound_in_fenv g e t (FTAbsT _g k e' t' nms mk_p_e'_t') x
  = () ? lem_fv_bound_in_fenv (FConsT a k g) (unbind_tv a e') (unbindFT a t') (mk_p_e'_t' a) x  
      where
        a = fresh_var_excludingF nms g x
lem_fv_bound_in_fenv g e t (FTAppT _g e' k t' p_e'_at' ref_t' _) x 
  = () ? lem_fv_bound_in_fenv g e' (FTPoly k t') p_e'_at' x
       ? toProof ( S.isSubsetOf (free ref_t')   (vbindsF g)  && S.isSubsetOf (vbindsF g)  (bindsF g) )
       ? toProof ( S.isSubsetOf (freeTV ref_t') (tvbindsF g) && S.isSubsetOf (tvbindsF g) (bindsF g) )
lem_fv_bound_in_fenv g e t (FTLet _g e_y t_y p_ey_ty e' t' nms mk_p_e'_t') x 
  = () ? lem_fv_bound_in_fenv g e_y t_y p_ey_ty x
       ? lem_fv_bound_in_fenv (FCons y t_y g) (unbind y e') t' (mk_p_e'_t' y) x
      where
        y = fresh_var_excludingF nms g x 
lem_fv_bound_in_fenv g e t (FTAnn _g e' _t ann_t p_e'_t) x 
  = () ? lem_fv_bound_in_fenv g e' t p_e'_t x
       ? toProof ( S.isSubsetOf (free ann_t)   (vbindsF g)  && S.isSubsetOf (vbindsF g)  (bindsF g) )
       ? toProof ( S.isSubsetOf (freeTV ann_t) (tvbindsF g) && S.isSubsetOf (tvbindsF g) (bindsF g) )

{-@ lem_fv_subset_bindsF :: g:FEnv -> e:Expr -> t:FType -> ProofOf(HasFType g e t)
                -> { pf:_ | Set_sub (fv e) (bindsF g) && Set_sub (ftv e) (bindsF g) &&
                            Set_sub (fv e) (vbindsF g) && Set_sub (ftv e) (tvbindsF g) } 
                 / [esize e, fenvsize g] @-}
lem_fv_subset_bindsF :: FEnv -> Expr -> FType -> HasFType -> Proof
lem_fv_subset_bindsF g e t (FTBC _g b)       = ()
lem_fv_subset_bindsF g e t (FTIC _g n)       = ()
lem_fv_subset_bindsF g e t (FTVar1 _ y _t)   = ()
lem_fv_subset_bindsF g e t (FTVar2 g' y _t p_y_t z t') = ()
         ? lem_fv_subset_bindsF g' e t p_y_t
lem_fv_subset_bindsF g e t (FTVar3 g' y _t p_y_t a k)  = ()
         ? lem_fv_subset_bindsF g' e t p_y_t
lem_fv_subset_bindsF g e t (FTPrm _g c)      = ()
lem_fv_subset_bindsF g e t p_e_t@(FTAbs _g t_y _ _ e' t' nms mk_p_e'_t')  
    = () ? lem_fv_subset_bindsF (FCons y' t_y g) (unbind y' e') t' (mk_p_e'_t' y')
         ? lem_fv_bound_in_fenv g                e              t  p_e_t           y'
        where 
          y' = fresh_varF nms g
lem_fv_subset_bindsF g e t (FTApp _g e1 t_y t' p_e1_tyt' e2 p_e2_ty) 
    = () ? lem_fv_subset_bindsF g e1 (FTFunc t_y t') p_e1_tyt' 
         ? lem_fv_subset_bindsF g e2 t_y p_e2_ty 
lem_fv_subset_bindsF g e t p_e_t@(FTAbsT _g k e' t' nms mk_p_e'_t')  
    = () ? lem_fv_subset_bindsF (FConsT a' k g) (unbind_tv a' e') 
                                (unbindFT a' t') (mk_p_e'_t' a')
         ? lem_fv_bound_in_fenv g e t p_e_t a'
        where 
          a' = fresh_varF nms g
lem_fv_subset_bindsF g e t (FTAppT _g e' k t1 p_e1_at1 t2 _) 
    = () ? lem_fv_subset_bindsF g e' (FTPoly k t1)  p_e1_at1
         ? toProof ( S.isSubsetOf (free t2)   (vbindsF g)  && S.isSubsetOf (vbindsF g)  (bindsF g) )
         ? toProof ( S.isSubsetOf (freeTV t2) (tvbindsF g) && S.isSubsetOf (tvbindsF g) (bindsF g) )
lem_fv_subset_bindsF g e t p_e_t@(FTLet _g e_y t_y p_ey_ty e' t' nms mk_p_e'_t')  
    = () ? lem_fv_subset_bindsF g e_y t_y p_ey_ty 
         ? lem_fv_subset_bindsF (FCons y' t_y g) (unbind y' e') t' (mk_p_e'_t' y')
         ? lem_fv_bound_in_fenv g e t p_e_t y'
        where 
          y' = fresh_varF nms g
lem_fv_subset_bindsF g e t (FTAnn _g e' _t ann_t p_e'_t) 
    = () ? lem_fv_subset_bindsF g e' t p_e'_t 
         ? toProof ( S.isSubsetOf (free ann_t)   (vbindsF g)  && S.isSubsetOf (vbindsF g)  (bindsF g) )
         ? toProof ( S.isSubsetOf (freeTV ann_t) (tvbindsF g) && S.isSubsetOf (tvbindsF g) (bindsF g) )

{-@ lem_fvp_bound_in_fenv :: g:FEnv -> ps:Preds -> ProofOf(PHasFType g ps)
        -> { x:Vname | not (in_envF x g) }
        -> { pf:_ | not (Set_mem x (fvP ps)) && not (Set_mem x (ftvP ps)) } / [predsize ps] @-}
lem_fvp_bound_in_fenv :: FEnv -> Preds -> PHasFType -> Vname -> Proof
lem_fvp_bound_in_fenv g ps (PFTEmp  _) x      = ()
lem_fvp_bound_in_fenv g ps (PFTCons _ p pf_p_bl ps' pf_ps'_bl) x      
    = () ? lem_fv_bound_in_fenv  g p (FTBasic TBool) pf_p_bl x
         ? lem_fvp_bound_in_fenv g ps' pf_ps'_bl x

{-@ lem_fvp_subset_bindsF :: g:FEnv -> ps:Preds -> ProofOf(PHasFType g ps)
        -> { pf:_ | Set_sub (fvP ps) (bindsF g)  && Set_sub (ftvP ps) (bindsF g) &&
                    Set_sub (fvP ps) (vbindsF g) && Set_sub (ftvP ps) (tvbindsF g) } 
         / [predsize ps] @-}
lem_fvp_subset_bindsF :: FEnv -> Preds -> PHasFType -> Proof
lem_fvp_subset_bindsF g ps (PFTEmp _)                          = ()
lem_fvp_subset_bindsF g ps (PFTCons _ p pf_p_bl ps' pf_ps'_bl)
    = () ? lem_fv_subset_bindsF  g p (FTBasic TBool) pf_p_bl
         ? lem_fvp_subset_bindsF g ps' pf_ps'_bl

{-@ lem_ffreeTV_bound_in_fenv :: g:FEnv -> t:FType -> k:Kind -> ProofOf(WFFT g t k)
                -> { a:Vname | not (in_envF a g) }
                -> { pf:_ | not (Set_mem a (ffreeTV t)) } / [ftsize t, fenvsize g, ksize k] @-}
lem_ffreeTV_bound_in_fenv :: FEnv -> FType -> Kind -> WFFT -> Vname -> Proof
lem_ffreeTV_bound_in_fenv g t k (WFFTBasic _g b) x = case t of
  (FTBasic _)  -> ()
lem_ffreeTV_bound_in_fenv g t k (WFFTFV1 g' a _k) x = case t of
  (FTBasic _)  -> ()
lem_ffreeTV_bound_in_fenv g t k (WFFTFV2 g' a _k p_a_k y t') x = case t of
  (FTBasic _)  -> () ? lem_ffreeTV_bound_in_fenv g' t k p_a_k x
lem_ffreeTV_bound_in_fenv g t k (WFFTFV3 g' a _k p_a_k a' k') x = case t of
  (FTBasic _)  -> () ? lem_ffreeTV_bound_in_fenv g' t k p_a_k x
lem_ffreeTV_bound_in_fenv g t k (WFFTFunc _g t1 k1 p_t1_wf t2 k2 p_t2_wf) a = case t of
  (FTFunc _ _) -> () ? lem_ffreeTV_bound_in_fenv g t1 k1 p_t1_wf a
                     ? lem_ffreeTV_bound_in_fenv g t2 k2 p_t2_wf a
lem_ffreeTV_bound_in_fenv g t k (WFFTPoly _g k' t' k_t' nms mk_p_a'g_t'_kt') a = case t of
  (FTPoly _ _) -> () ? lem_ffreeTV_bound_in_fenv (FConsT a' k' g) (unbindFT a' t') 
                                                  k_t' (mk_p_a'g_t'_kt' a') a
    where
      a' = fresh_var_excludingF nms g a
lem_ffreeTV_bound_in_fenv g t k (WFFTKind _g _t p_t_B) a 
                = () ? lem_ffreeTV_bound_in_fenv g t Base p_t_B a
