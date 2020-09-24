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
import WellFormedness
import BasicPropsSubstitution

{-@ reflect foo17 @-}
foo17 x = Just x 
foo17 :: a -> Maybe a 

----------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of ENVIRONMENTS / BARE-TYPED ENVIRONMENTS
----------------------------------------------------------------------------

{-@ reflect concatE @-}
{-@ concatE :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
                     -> { h:Env | (binds h) == (Set_cup (binds g) (binds g')) } @-}
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

{-@ lem_erase_tsubFV :: x:Vname -> e:Expr -> t:Type 
                                -> { pf:_ | erase (tsubFV x e t) == erase t } @-}
lem_erase_tsubFV :: Vname -> Expr -> Type -> Proof
lem_erase_tsubFV x e (TRefn   b   z p) = ()
lem_erase_tsubFV x e (TFunc   z t_z t) = () ? lem_erase_tsubFV x e t_z
                                            ? lem_erase_tsubFV x e t
lem_erase_tsubFV x e (TExists z t_z t) = () ? lem_erase_tsubFV x e t
lem_erase_tsubFV x e (TPoly   a k   t) = () ? lem_erase_tsubFV x e t

{-@ lem_erase_tsubBV :: x:Vname -> e:Expr -> t:Type 
                                -> { pf:_ | erase (tsubBV x e t) == erase t } @-}
lem_erase_tsubBV :: Vname -> Expr -> Type -> Proof
lem_erase_tsubBV x e (TRefn   b   z p) = ()
lem_erase_tsubBV x e (TFunc   z t_z t) = () ? lem_erase_tsubBV x e t_z
                                            ? lem_erase_tsubBV x e t
lem_erase_tsubBV x e (TExists z t_z t) = () ? lem_erase_tsubBV x e t
lem_erase_tsubBV x e (TPoly   a k   t) = () ? lem_erase_tsubBV x e t


{-@ lem_erase_tsubBTV :: a:Vname -> t_a:Type -> t:Type 
        -> { pf:_ | erase (tsubBTV a t_a t) == ftsubBV a (erase t_a) (erase t) } @-}
lem_erase_tsubBTV :: Vname -> Type -> Type -> Proof
lem_erase_tsubBTV a t_a (TRefn   b   z p) = case b of
  (BTV a') -> () ? toProof ( erase (push z (subBTV a t_a p) t_a) === erase t_a )
  _        -> ()
lem_erase_tsubBTV a t_a (TFunc   z t_z t) = () ? lem_erase_tsubBTV a t_a t_z
                                               ? lem_erase_tsubBTV a t_a t
lem_erase_tsubBTV a t_a (TExists z t_z t) = () ? lem_erase_tsubBTV a t_a t
lem_erase_tsubBTV a t_a (TPoly   a' k' t) = () ? lem_erase_tsubBTV a t_a t

{-@ lem_erase_freeTV :: t:Type -> { pf:_ | Set_sub (ffreeTV (erase t)) (freeTV t) } @-}
lem_erase_freeTV :: Type -> Proof
lem_erase_freeTV (TRefn   b   z p) = ()
lem_erase_freeTV (TFunc   z t_z t) = () ? lem_erase_freeTV t_z
                                        ? lem_erase_freeTV t
lem_erase_freeTV (TExists z t_z t) = () ? lem_erase_freeTV t
lem_erase_freeTV (TPoly   a' k' t) = () ? lem_erase_freeTV t




{-@ reflect concatF @-}
{-@ concatF :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) } 
                      -> { h:FEnv  | bindsF h == Set_cup (bindsF g) (bindsF g') } @-}
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
  -> { pf:_ | Set_sub (bindsF (concatF g g')) (bindsF (concatF (FCons x t_x g) g')) && 
              bindsF (concatF (FCons x t_x g) g') == Set_cup (Set_cup (bindsF g) (Set_sng x)) (bindsF g') } @-}
lem_binds_cons_concatF :: FEnv -> FEnv -> Vname -> FType -> Proof
lem_binds_cons_concatF g FEmpty          x t = ()
lem_binds_cons_concatF g (FCons  y s g') x t = () ? lem_binds_cons_concatF g g' x t
lem_binds_cons_concatF g (FConsT a k g') x t = () ? lem_binds_cons_concatF g g' x t

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
{-@ esubFV :: x:Vname -> v:Value -> g:Env -> { g':Env | binds g == binds g' } @-}
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


{-@ lem_erase_esubFV :: x:Vname -> v:Expr -> g:Env
        -> { pf:_ | erase_env (esubFV x v g) == erase_env g } @-}
lem_erase_esubFV :: Vname -> Expr -> Env -> Proof
lem_erase_esubFV x e (Empty)       = ()
lem_erase_esubFV x e (Cons  y t g) = () ? lem_erase_esubFV x e g
                                        ? lem_erase_tsubFV x e t
lem_erase_esubFV x e (ConsT a k g) = () ? lem_erase_esubFV x e g


{-@ lem_esubFV_inverse :: g0:Env -> { x:Vname | not (in_env x g0) } -> t_x:Type
        -> { g:Env | Set_emp (Set_cap (binds g0) (binds g)) && not (in_env x g) } 
        -> ProofOf(WFEnv (concatE (Cons x t_x g0) g))
        -> { y:Vname | not (in_env y g) && not (in_env y g0) } 
        -> { pf:Proof | esubFV y (FV x) (esubFV x (FV y) g) == g } @-}
lem_esubFV_inverse :: Env -> Vname -> Type -> Env -> WFEnv -> Vname -> Proof
lem_esubFV_inverse g0 x t_x Empty           p_g0g_wf y = ()
lem_esubFV_inverse g0 x t_x (Cons z t_z g') p_g0g_wf y = case p_g0g_wf of
  (WFEBind env' p_env'_wf _z _tz k_z p_env'_tz) -> case ( x == y ) of
    (True)  -> () ? lem_esubFV_inverse g0 x t_x g' p_env'_wf y
                  ? lem_tsubFV_id x t_z
    (False) -> () {- toProof (
          esubFV y (FV x) (esubFV x (FV y) (Cons z t_z g'))
      === esubFV y (FV x) (Cons z (tsubFV x (FV y) t_z) (esubFV x (FV y) g'))
      === Cons z (tsubFV y (FV x) (tsubFV x (FV y) t_z)) (esubFV y (FV x) (esubFV x (FV y) g')) -}
        ? lem_esubFV_inverse g0 x t_x g' p_env'_wf y 
   {- === Cons z (tsubFV y (FV x) (tsubFV x (FV y) t_z)) g' -}
        ? lem_chain_tsubFV x y (FV x) (t_z ? lem_free_bound_in_env env' t_z k_z p_env'_tz (y ? lem_in_env_concat (Cons x t_x g0) (Cons z t_z g') y ? lem_in_env_concat (Cons x t_x g0) g'))
        ? lem_tsubFV_id x t_z
   {- === Cons z t_z g'  ) -}
lem_esubFV_inverse g0 x t_x (ConsT a k g') p_g0g_wf y = case p_g0g_wf of
  (WFEBindT env' p_env'_wf _a _k)  -> () ? lem_esubFV_inverse g0 x t_x g' p_env'_wf y


-- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Substitutions in Systen F Environments --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --

{-@ reflect fesubFV @-}
{-@ fesubFV :: a:Vname -> t_a:FType -> g:FEnv 
       -> { g':FEnv | Set_sub (bindsF g) (bindsF g') && Set_sub (bindsF g') (bindsF g) } @-}
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
----- | Properties of JUDGEMENTS : the Bare-Typing Relation and Well-Formedness of Types
-----------------------------------------------------------------------------------------

-- Lemma. All free variables in a (bare) typed expression are bound in the (bare) environment
{-@ lem_fv_bound_in_fenv :: g:FEnv -> e:Expr -> t:FType -> ProofOf(HasFType g e t)
                -> { x:Vname | not (in_envF x g) }
                -> { pf:_ | not (Set_mem x (fv e)) && not (Set_mem x (ftv e)) } @-}
lem_fv_bound_in_fenv :: FEnv -> Expr -> FType -> HasFType -> Vname -> Proof
lem_fv_bound_in_fenv g e t (FTBC _g b) x      = ()
lem_fv_bound_in_fenv g e t (FTIC _g n) x      = ()
lem_fv_bound_in_fenv g e t (FTVar1 _ y _t) x  = ()
lem_fv_bound_in_fenv g e t (FTVar2 _ y _t p_y_t z t') x = ()
lem_fv_bound_in_fenv g e t (FTVar3 _ y _y p_y_t z k)  x = ()
lem_fv_bound_in_fenv g e t (FTPrm _g c) x     = ()
lem_fv_bound_in_fenv g e t (FTAbs _g y t_y _ _ e' t' y' p_e'_t') x 
    = case ( x == y' ) of
        (True)  -> ()
        (False) -> () ? lem_fv_bound_in_fenv (FCons y' t_y g) (unbind y y' e') t' p_e'_t' x
lem_fv_bound_in_fenv g e t (FTApp _g e1 t_y t' p_e1_tyt' e2 p_e2_ty) x 
    = () ? lem_fv_bound_in_fenv g e1 (FTFunc t_y t') p_e1_tyt' x
         ? lem_fv_bound_in_fenv g e2 t_y p_e2_ty x
lem_fv_bound_in_fenv g e t (FTAbsT _g a k e' t' a' p_e'_t') x
    = case ( x == a' ) of
        True  -> ()
        False -> () ? lem_fv_bound_in_fenv (FConsT a' k g) (unbind_tv a a' e') 
                                           (unbindFT a a' t') p_e'_t' x
lem_fv_bound_in_fenv g e t (FTAppT _g e' a k t' p_e'_at' ref_t' _) x
    = () ? lem_fv_bound_in_fenv g e' (FTPoly a k t') p_e'_at' x
lem_fv_bound_in_fenv g e t (FTLet _g e_y t_y p_ey_ty y e' t' y' p_e'_t') x 
    = case ( x == y' ) of
        (True)  -> () ? lem_fv_bound_in_fenv g e_y t_y p_ey_ty x
        (False) -> () ? lem_fv_bound_in_fenv g e_y t_y p_ey_ty x
                      ? lem_fv_bound_in_fenv (FCons y' t_y g) (unbind y y' e') t' p_e'_t' x
lem_fv_bound_in_fenv g e t (FTAnn _g e' _t ann_t p_e'_t) x 
    = () ? lem_fv_bound_in_fenv g e' t p_e'_t x

{-@ lem_fv_subset_bindsF :: g:FEnv -> e:Expr -> t:FType -> ProofOf(HasFType g e t)
                -> { pf:_ | Set_sub (fv e) (bindsF g) } @-}
lem_fv_subset_bindsF :: FEnv -> Expr -> FType -> HasFType -> Proof
lem_fv_subset_bindsF g e t (FTBC _g b)       = ()
lem_fv_subset_bindsF g e t (FTIC _g n)       = ()
lem_fv_subset_bindsF g e t (FTVar1 _ y _t)   = ()
lem_fv_subset_bindsF g e t (FTVar2 _ y _t p_y_t z t') = ()
lem_fv_subset_bindsF g e t (FTVar3 _ y _t p_y_t a k)  = ()
lem_fv_subset_bindsF g e t (FTPrm _g c)      = ()
lem_fv_subset_bindsF g e t (FTAbs _g y t_y _ _ e' t' y' p_e'_t')  
    = () ? lem_fv_subset_bindsF (FCons y' t_y g) (unbind y y' e') t' p_e'_t' 
lem_fv_subset_bindsF g e t (FTApp _g e1 t_y t' p_e1_tyt' e2 p_e2_ty) 
    = () ? lem_fv_subset_bindsF g e1 (FTFunc t_y t') p_e1_tyt' 
         ? lem_fv_subset_bindsF g e2 t_y p_e2_ty 
lem_fv_subset_bindsF g e t (FTAbsT _g a k e' t' a' p_e'_t')  
    = () ? lem_fv_subset_bindsF (FConsT a' k g) (unbind_tv a a' e') (unbindFT a a' t') p_e'_t' 
lem_fv_subset_bindsF g e t (FTAppT _g e' a k t1 p_e1_at1 t2 _) 
    = () ? lem_fv_subset_bindsF g e' (FTPoly a k t1)  p_e1_at1
lem_fv_subset_bindsF g e t (FTLet _g e_y t_y p_ey_ty y e' t' y' p_e'_t')  
    = () ? lem_fv_subset_bindsF g e_y t_y p_ey_ty 
         ? lem_fv_subset_bindsF (FCons y' t_y g) (unbind y y' e') t' p_e'_t' 
lem_fv_subset_bindsF g e t (FTAnn _g e' _t ann_t p_e'_t) 
    = () ? lem_fv_subset_bindsF g e' t p_e'_t 

{-@ lem_ftv_subset_bindsF :: g:FEnv -> e:Expr -> t:FType -> ProofOf(HasFType g e t)
                -> { pf:_ | Set_sub (ftv e) (bindsF g) } @-}
lem_ftv_subset_bindsF :: FEnv -> Expr -> FType -> HasFType -> Proof
lem_ftv_subset_bindsF g e t (FTBC _g b)       = ()
lem_ftv_subset_bindsF g e t (FTIC _g n)       = ()
lem_ftv_subset_bindsF g e t (FTVar1 _ y _t)   = ()
lem_ftv_subset_bindsF g e t (FTVar2 _ y _t p_y_t z t') = ()
lem_ftv_subset_bindsF g e t (FTVar3 _ y _t p_y_t a k)  = ()
lem_ftv_subset_bindsF g e t (FTPrm _g c)      = ()
lem_ftv_subset_bindsF g e t (FTAbs _g y t_y _ _ e' t' y' p_e'_t')  
    = () ? lem_ftv_subset_bindsF (FCons y' t_y g) (unbind y y' e') t' p_e'_t' 
lem_ftv_subset_bindsF g e t (FTApp _g e1 t_y t' p_e1_tyt' e2 p_e2_ty) 
    = () ? lem_ftv_subset_bindsF g e1 (FTFunc t_y t') p_e1_tyt' 
         ? lem_ftv_subset_bindsF g e2 t_y p_e2_ty 
lem_ftv_subset_bindsF g e t (FTAbsT _g a k e' t' a' p_e'_t')  
    = () ? lem_ftv_subset_bindsF (FConsT a' k g) (unbind_tv a a' e') (unbindFT a a' t') p_e'_t' 
lem_ftv_subset_bindsF g e t (FTAppT _g e' a k t1 p_e1_at1 t2 _) 
    = () ? lem_ftv_subset_bindsF g e' (FTPoly a k t1)  p_e1_at1
lem_ftv_subset_bindsF g e t (FTLet _g e_y t_y p_ey_ty y e' t' y' p_e'_t')  
    = () ? lem_ftv_subset_bindsF g e_y t_y p_ey_ty 
         ? lem_ftv_subset_bindsF (FCons y' t_y g) (unbind y y' e') t' p_e'_t' 
lem_ftv_subset_bindsF g e t (FTAnn _g e' _t ann_t p_e'_t) 
    = () ? lem_ftv_subset_bindsF g e' t p_e'_t 

{-
{-@ lem_fv_ftv_subset_bindsF :: g:FEnv -> e:Expr -> t:FType -> ProofOf(HasFType g e t)
                -> { pf:_ | Set_sub (Set_cup (fv e) (ftv e)) (bindsF g) } @-}
lem_fv_ftv_subset_bindsF :: FEnv -> Expr -> FType -> HasFType -> Proof
lem_fv_ftv_subset_bindsF g e t (FTBC _g b)       = ()
lem_fv_ftv_subset_bindsF g e t (FTIC _g n)       = ()
lem_fv_ftv_subset_bindsF g e t (FTVar1 _ y _t)   = ()
lem_fv_ftv_subset_bindsF g e t (FTVar2 _ y _t p_y_t z t') = ()
lem_fv_ftv_subset_bindsF g e t (FTVar3 _ y _t p_y_t a k)  = ()
lem_fv_ftv_subset_bindsF g e t (FTPrm _g c)      = ()
lem_fv_ftv_subset_bindsF g e t (FTAbs _g y t_y e' t' y' p_e'_t')  
    = () ? lem_fv_ftv_subset_bindsF (FCons y' t_y g) (unbind y y' e') t' p_e'_t' 
lem_fv_ftv_subset_bindsF g e t (FTApp _g e1 t_y t' p_e1_tyt' e2 p_e2_ty) 
    = () ? lem_fv_ftv_subset_bindsF g e1 (FTFunc t_y t') p_e1_tyt' 
         ? lem_fv_ftv_subset_bindsF g e2 t_y p_e2_ty 
lem_fv_ftv_subset_bindsF g e t (FTAbsT _g a k e' t' a' p_e'_t')  
    = () ? lem_fv_ftv_subset_bindsF (FConsT a' k g) (unbind_tv a a' e') t' p_e'_t' 
lem_fv_ftv_subset_bindsF g e t (FTAppT _g e' a k t1 p_e1_at1 t2) 
    = () ? lem_fv_ftv_subset_bindsF g e' (FTPoly a k t1)  p_e1_at1
lem_fv_ftv_subset_bindsF g e t (FTLet _g e_y t_y p_ey_ty y e' t' y' p_e'_t')  
    = () ? lem_fv_ftv_subset_bindsF g e_y t_y p_ey_ty 
         ? lem_fv_ftv_subset_bindsF (FCons y' t_y g) (unbind y y' e') t' p_e'_t' 
lem_fv_ftv_subset_bindsF g e t (FTAnn _g e' _t ann_t p_e'_t) 
    = () ? lem_fv_ftv_subset_bindsF g e' t p_e'_t 
-}
{-@ lem_free_bound_in_env :: g:Env -> t:Type -> k:Kind -> ProofOf(WFType g t k)
                -> { x:Vname | not (in_env x g) }
                -> { pf:_ | not (Set_mem x (free t)) } @-}
lem_free_bound_in_env :: Env -> Type -> Kind -> WFType -> Vname -> Proof
lem_free_bound_in_env g t k (WFBase _ _) x = ()
lem_free_bound_in_env g t k (WFRefn _g z b p_g_b p z' p_z'_p_bl) x
    = case ( x == z' ) of
        (True)  -> ()
        (False) -> () ? lem_fv_bound_in_fenv (FCons z' (FTBasic b) (erase_env g)) 
                                             (unbind z z' p) (FTBasic TBool) p_z'_p_bl x
lem_free_bound_in_env g t k (WFVar1 g' a _k) x = ()
lem_free_bound_in_env g t k (WFVar2 g' a _k p_a_k y t') x
    = () ? lem_free_bound_in_env g' t k p_a_k x
lem_free_bound_in_env g t k (WFVar3 g' a _k p_a_k a' k') x
    = () ? lem_free_bound_in_env g' t k p_a_k x
lem_free_bound_in_env g t k (WFFunc _g y t_y k_y p_ty_wf t' k' y' p_y'_t'_wf) x
    = case ( x == y' ) of
        (True)  -> () ? lem_free_bound_in_env g t_y k_y p_ty_wf x
        (False) -> () ? lem_free_bound_in_env g t_y k_y p_ty_wf x
                      ? lem_free_bound_in_env (Cons y' t_y g) (unbindT y y' t') k' p_y'_t'_wf x
lem_free_bound_in_env g t k (WFExis _g y t_y k_y p_ty_wf t' k' y' p_y'_t'_wf) x
    = case ( x == y' ) of 
        (True)  -> () ? lem_free_bound_in_env g t_y k_y p_ty_wf x
        (False) -> () ? lem_free_bound_in_env g t_y k_y p_ty_wf x
                      ? lem_free_bound_in_env (Cons y' t_y g) (unbindT y y' t') k' p_y'_t'_wf x
lem_free_bound_in_env g t k (WFPoly _g a k' t' k_t' a' p_a'_t'_kt') x
    = case ( x == a' ) of
        (True)  -> ()
        (False) -> () ? lem_free_bound_in_env (ConsT a' k' g) (unbind_tvT a a' t') k_t' p_a'_t'_kt' x
lem_free_bound_in_env g t k (WFKind _g _t p_t_B) x = () ? lem_free_bound_in_env g t Base p_t_B x

{-@ lem_free_subset_binds :: g:Env -> t:Type -> k:Kind -> ProofOf(WFType g t k) 
                  -> { pf:_ | Set_sub (free t) (binds g) } @-}
lem_free_subset_binds :: Env -> Type -> Kind -> WFType -> Proof 
lem_free_subset_binds g t k (WFBase _ _ ) = ()
lem_free_subset_binds g t k (WFRefn _g z b p_g_b p z' p_z'_p_bl)
    = () ? lem_fv_subset_bindsF (FCons z' (FTBasic b) (erase_env g)) (unbind z z' p) 
                                (FTBasic TBool) p_z'_p_bl
lem_free_subset_binds g t k (WFVar1 g' a _k) = ()
lem_free_subset_binds g t k (WFVar2 g' a _k p_a_k y t') = ()
lem_free_subset_binds g t k (WFVar3 g' a _k p_a_k a' k') = ()
lem_free_subset_binds g t k (WFFunc _g y t_y k_y p_ty_wf t' k' y' p_y'_t'_wf)
    = () ? lem_free_subset_binds g t_y k_y p_ty_wf
         ? lem_free_subset_binds (Cons y' t_y g) (unbindT y y' t') k' p_y'_t'_wf
lem_free_subset_binds g t k (WFExis _g y t_y k_y p_ty_wf t' k' y' p_y'_t'_wf)
    = () ? lem_free_subset_binds g t_y k_y p_ty_wf
         ? lem_free_subset_binds (Cons y' t_y g) (unbindT y y' t') k' p_y'_t'_wf
lem_free_subset_binds g t k (WFPoly _g a k' t' k_t' a' p_a'_t'_kt')
    = () ? lem_free_subset_binds (ConsT a' k' g) (unbind_tvT a a' t') k_t' p_a'_t'_kt'
lem_free_subset_binds g t k (WFKind _g _t p_t_B) = () ? lem_free_subset_binds g t Base p_t_B

{-@ lem_truncate_wfenv :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> ProofOf(WFEnv g) @-}
lem_truncate_wfenv :: Env -> Env -> WFEnv -> WFEnv
lem_truncate_wfenv g Empty          p_g_wf    = p_g_wf          
lem_truncate_wfenv g (Cons x v g')  p_xg'g_wf = lem_truncate_wfenv g g' p_g'g_wf
  where
    (WFEBind _ p_g'g_wf _ _ _ _) = p_xg'g_wf 
lem_truncate_wfenv g (ConsT a k g') p_ag'g_wf = lem_truncate_wfenv g g' p_g'g_wf
  where
    (WFEBindT _ p_g'g_wf _ _) = p_ag'g_wf


   ----- SYSTEM F VERSIONS
{-@ lem_ffreeTV_bound_in_fenv :: g:FEnv -> t:FType -> k:Kind -> ProofOf(WFFT g t k)
                -> { a:Vname | not (in_envF a g) }
                -> { pf:_ | not (Set_mem a (ffreeTV t)) } @-}
lem_ffreeTV_bound_in_fenv :: FEnv -> FType -> Kind -> WFFT -> Vname -> Proof
lem_ffreeTV_bound_in_fenv g t k (WFFTBasic _g b) x = ()
lem_ffreeTV_bound_in_fenv g t k (WFFTFV1 g' a _k) x = ()
lem_ffreeTV_bound_in_fenv g t k (WFFTFV2 g' a _k p_a_k y t') x
    = () ? lem_ffreeTV_bound_in_fenv g' t k p_a_k x
lem_ffreeTV_bound_in_fenv g t k (WFFTFV3 g' a _k p_a_k a' k') x
    = () ? lem_ffreeTV_bound_in_fenv g' t k p_a_k x
lem_ffreeTV_bound_in_fenv g t k (WFFTFunc _g t1 k1 p_t1_wf t2 k2 p_t2_wf) a
    = () ? lem_ffreeTV_bound_in_fenv g t1 k1 p_t1_wf a
         ? lem_ffreeTV_bound_in_fenv g t2 k2 p_t2_wf a
lem_ffreeTV_bound_in_fenv g t k (WFFTPoly _g a' k' t' k_t' a'' p_a''g_t'_kt') a
    = case ( a == a'' ) of
        (True)  -> ()
        (False) -> () ? lem_ffreeTV_bound_in_fenv (FConsT a'' k' g) (unbindFT a' a'' t') 
                                                  k_t' p_a''g_t'_kt' a
lem_ffreeTV_bound_in_fenv g t k (WFFTKind _g _t p_t_B) a 
    = () ? lem_ffreeTV_bound_in_fenv g t Base p_t_B a

{-@ lem_ffreeTV_subset_bindsF :: g:FEnv -> t:FType -> k:Kind -> ProofOf(WFFT g t k) 
                  -> { pf:_ | Set_sub (ffreeTV t) (bindsF g) } @-}
lem_ffreeTV_subset_bindsF :: FEnv -> FType -> Kind -> WFFT -> Proof 
lem_ffreeTV_subset_bindsF g t k (WFFTBasic _g b)  = ()
lem_ffreeTV_subset_bindsF g t k (WFFTFV1 g' a _k) = ()
lem_ffreeTV_subset_bindsF g t k (WFFTFV2 g' a _k p_a_k y t') 
    = () ? lem_ffreeTV_subset_bindsF g' t k p_a_k 
lem_ffreeTV_subset_bindsF g t k (WFFTFV3 g' a _k p_a_k a' k') 
    = () ? lem_ffreeTV_subset_bindsF g' t k p_a_k 
lem_ffreeTV_subset_bindsF g t k (WFFTFunc _g t1 k1 p_t1_wf t2 k2 p_t2_wf) 
    = () ? lem_ffreeTV_subset_bindsF g t1 k1 p_t1_wf 
         ? lem_ffreeTV_subset_bindsF g t2 k2 p_t2_wf 
lem_ffreeTV_subset_bindsF g t k (WFFTPoly _g a' k' t' k_t' a'' p_a''g_t'_kt') 
    = () ? lem_ffreeTV_subset_bindsF (FConsT a'' k' g) (unbindFT a' a'' t') 
                                     k_t' p_a''g_t'_kt' 
lem_ffreeTV_subset_bindsF g t k (WFFTKind _g _t p_t_B) 
    = () ? lem_ffreeTV_subset_bindsF g t Base p_t_B 

