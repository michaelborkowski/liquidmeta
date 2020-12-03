{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module BasicPropsEnvironments where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import SystemFTyping
import WellFormedness
import BasicPropsSubstitution

{-@ reflect foo20 @-}
foo20 x = Just x 
foo20 :: a -> Maybe a 

----------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of ENVIRONMENTS / BARE-TYPED ENVIRONMENTS
----------------------------------------------------------------------------

{-@ reflect concatE @-}
{-@ concatE :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
                     -> { h:Env | binds h   == (Set_cup (binds g)   (binds g')) } @-}
concatE :: Env -> Env -> Env
concatE g Empty          = g
concatE g (Cons  x t g') = Cons x t  (concatE g g')

{-@ lem_empty_concatE :: g:Env -> { pf:_ | concatE Empty g == g } @-}
lem_empty_concatE :: Env -> Proof
lem_empty_concatE Empty         = ()
lem_empty_concatE (Cons  x t g) = () ? lem_empty_concatE g

--             && (not (in_env x (concatE g g')) <=> (not (in_env x g) && not (in_env x g'))) } @-}
{-@ lem_in_env_concat :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
      ->  x:Vname -> {pf:_ | (in_env x (concatE g g')) <=> ((in_env x g) || (in_env x g'))} @-}
lem_in_env_concat :: Env -> Env -> Vname -> Proof
lem_in_env_concat g Empty          x = ()
lem_in_env_concat g (Cons  y s g') x = () ? lem_in_env_concat g g' x 

{-@ lem_erase_tsubFV :: x:Vname -> e:Expr -> t:Type 
                                -> { pf:_ | erase (tsubFV x e t) == erase t } @-}
lem_erase_tsubFV :: Vname -> Expr -> Type -> Proof
lem_erase_tsubFV x e (TRefn   b   z p) = ()
lem_erase_tsubFV x e (TFunc   z t_z t) = () ? lem_erase_tsubFV x e t_z
                                            ? lem_erase_tsubFV x e t
lem_erase_tsubFV x e (TExists z t_z t) = () ? lem_erase_tsubFV x e t

{-@ lem_erase_tsubBV :: x:Vname -> e:Expr -> t:Type 
                                -> { pf:_ | erase (tsubBV x e t) == erase t } @-}
lem_erase_tsubBV :: Vname -> Expr -> Type -> Proof
lem_erase_tsubBV x e (TRefn   b   z p) = ()
lem_erase_tsubBV x e (TFunc   z t_z t) = () ? lem_erase_tsubBV x e t_z
                                            ? lem_erase_tsubBV x e t
lem_erase_tsubBV x e (TExists z t_z t) = () ? lem_erase_tsubBV x e t


{-@ reflect concatF @-}
{-@ concatF :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) } 
                      -> { h:FEnv  | bindsF h == Set_cup (bindsF g) (bindsF g') } @-}
concatF :: FEnv -> FEnv -> FEnv
concatF g FEmpty          = g
concatF g (FCons  x t g') = FCons  x t (concatF g g')

{-@ lem_in_env_concatF :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) } 
      ->  x:Vname -> {pf:_ | (in_envF x (concatF g g')) <=> ((in_envF x g) || (in_envF x g'))} @-}
lem_in_env_concatF :: FEnv -> FEnv -> Vname -> Proof
lem_in_env_concatF g FEmpty          x = ()
lem_in_env_concatF g (FCons  y s g') x = () ? lem_in_env_concatF g g' x 

{-@ lem_empty_concatF :: g:FEnv -> { pf:_ | concatF FEmpty g == g } @-}
lem_empty_concatF :: FEnv -> Proof
lem_empty_concatF FEmpty         = ()
lem_empty_concatF (FCons  x t g) = () ? lem_empty_concatF g

{-@ lem_binds_cons_concatF :: g:FEnv -> g':FEnv -> x:Vname -> t_x:FType
      -> { pf:_ | Set_sub (bindsF (concatF g g')) (bindsF (concatF (FCons x t_x g) g')) && 
             bindsF (concatF (FCons x t_x g) g') == Set_cup (Set_cup (bindsF g) (Set_sng x)) (bindsF g') } @-}
lem_binds_cons_concatF :: FEnv -> FEnv -> Vname -> FType -> Proof
lem_binds_cons_concatF g FEmpty          x t = ()
lem_binds_cons_concatF g (FCons  y s g') x t = () ? lem_binds_cons_concatF g g' x t

{-@ lem_erase_concat :: g:Env -> g':Env 
           -> { pf:_ |  erase_env (concatE g g') == concatF (erase_env g) (erase_env g') } @-}
lem_erase_concat :: Env -> Env -> Proof
lem_erase_concat g Empty          = ()
lem_erase_concat g (Cons  x t g') = () ? lem_erase_concat g g'


-- -- -- -- -- -- -- -- -- -- -- --
-- Substitutions in Environments --
-- -- -- -- -- -- -- -- -- -- -- --

{-@ reflect esubFV @-}
{-@ esubFV :: x:Vname -> v:Value -> g:Env -> { g':Env | binds g == binds g' } @-}
esubFV :: Vname -> Expr -> Env -> Env
esubFV x e_x Empty           = Empty
esubFV x e_x (Cons  z t_z g) = Cons z (tsubFV x e_x t_z) (esubFV x e_x g)

{-@ lem_in_env_esub :: g:Env -> x:Vname -> v_x:Value -> y:Vname
        -> { pf:_ | in_env y (esubFV x v_x g) <=> in_env y g } @-}
lem_in_env_esub :: Env -> Vname -> Expr -> Vname -> Proof
lem_in_env_esub Empty           x v_x y = ()
lem_in_env_esub (Cons  z t_z g) x v_x y = () ? lem_in_env_esub g x v_x y

{-@ lem_erase_esubFV :: x:Vname -> v:Expr -> g:Env
        -> { pf:_ | erase_env (esubFV x v g) == erase_env g } @-}
lem_erase_esubFV :: Vname -> Expr -> Env -> Proof
lem_erase_esubFV x e (Empty)       = ()
lem_erase_esubFV x e (Cons  y t g) = () ? lem_erase_esubFV x e g
                                        ? lem_erase_tsubFV x e t


{-@ lem_esubFV_inverse :: g0:Env -> { x:Vname | not (in_env x g0) } -> t_x:Type
        -> { g:Env | Set_emp (Set_cap (binds g0) (binds g)) && not (in_env x g) } 
        -> ProofOf(WFEnv (concatE (Cons x t_x g0) g))
        -> { y:Vname | not (in_env y g) && not (in_env y g0) } 
        -> { pf:Proof | esubFV y (FV x) (esubFV x (FV y) g) == g } @-}
lem_esubFV_inverse :: Env -> Vname -> Type -> Env -> WFEnv -> Vname -> Proof
lem_esubFV_inverse g0 x t_x Empty           p_g0g_wf y = ()
lem_esubFV_inverse g0 x t_x (Cons z t_z g') p_g0g_wf y = case p_g0g_wf of
  (WFEBind env' p_env'_wf _z _tz p_env'_tz) -> case ( x == y ) of
    (True)  -> () ? lem_esubFV_inverse g0 x t_x g' p_env'_wf y
                  ? lem_tsubFV_id x t_z
    (False) -> () {- toProof (
          esubFV y (FV x) (esubFV x (FV y) (Cons z t_z g'))
      === esubFV y (FV x) (Cons z (tsubFV x (FV y) t_z) (esubFV x (FV y) g'))
      === Cons z (tsubFV y (FV x) (tsubFV x (FV y) t_z)) (esubFV y (FV x) (esubFV x (FV y) g')) -}
        ? lem_esubFV_inverse g0 x t_x g' p_env'_wf y 
   {- === Cons z (tsubFV y (FV x) (tsubFV x (FV y) t_z)) g' -}
        ? lem_chain_tsubFV x y (FV x) (t_z ? lem_free_bound_in_env env' t_z p_env'_tz (y ? lem_in_env_concat (Cons x t_x g0) (Cons z t_z g') y ? lem_in_env_concat (Cons x t_x g0) g'))
        ? lem_tsubFV_id x t_z
   {- === Cons z t_z g'  ) -}

-----------------------------------------------------------------------------------------
----- | Properties of JUDGEMENTS : the Bare-Typing Relation and Well-Formedness of Types
-----------------------------------------------------------------------------------------

-- Lemma. All free variables in a (bare) typed expression are bound in the (bare) environment
{-@ lem_fv_bound_in_fenv :: g:FEnv -> e:Expr -> t:FType -> ProofOf(HasFType g e t)
                -> { x:Vname | not (in_envF x g) } -> { pf:_ | not (Set_mem x (fv e)) } @-}
lem_fv_bound_in_fenv :: FEnv -> Expr -> FType -> HasFType -> Vname -> Proof
lem_fv_bound_in_fenv g e t (FTBC _g b) x      = ()
lem_fv_bound_in_fenv g e t (FTIC _g n) x      = ()
lem_fv_bound_in_fenv g e t (FTVar1 _ y _t) x  = ()
lem_fv_bound_in_fenv g e t (FTVar2 _ y _t p_y_t z t') x = ()
lem_fv_bound_in_fenv g e t (FTPrm _g c) x     = ()
lem_fv_bound_in_fenv g e t (FTAbs _g y t_y e' t' y' p_e'_t') x = case ( x == y' ) of
        (True)  -> ()
        (False) -> () ? lem_fv_bound_in_fenv (FCons y' t_y g) (unbind y y' e') t' p_e'_t' x
lem_fv_bound_in_fenv g e t (FTApp _g e1 t_y t' p_e1_tyt' e2 p_e2_ty) x  
  = () ? lem_fv_bound_in_fenv g e1 (FTFunc t_y t') p_e1_tyt' x
                  ? lem_fv_bound_in_fenv g e2 t_y p_e2_ty x
lem_fv_bound_in_fenv g e t (FTLet _g e_y t_y p_ey_ty y e' t' y' p_e'_t') x = {-case e of
  (Let _ _ _) ->-} case ( x == y' ) of
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
lem_fv_subset_bindsF g e t (FTPrm _g c)      = ()
lem_fv_subset_bindsF g e t (FTAbs _g y t_y e' t' y' p_e'_t')  
    = () ? lem_fv_subset_bindsF (FCons y' t_y g) (unbind y y' e') t' p_e'_t' 
lem_fv_subset_bindsF g e t (FTApp _g e1 t_y t' p_e1_tyt' e2 p_e2_ty) 
    = () ? lem_fv_subset_bindsF g e1 (FTFunc t_y t') p_e1_tyt' 
         ? lem_fv_subset_bindsF g e2 t_y p_e2_ty 
lem_fv_subset_bindsF g e t (FTLet _g e_y t_y p_ey_ty y e' t' y' p_e'_t')  
    = () ? lem_fv_subset_bindsF g e_y t_y p_ey_ty 
         ? lem_fv_subset_bindsF (FCons y' t_y g) (unbind y y' e') t' p_e'_t' 
lem_fv_subset_bindsF g e t (FTAnn _g e' _t ann_t p_e'_t) 
    = () ? lem_fv_subset_bindsF g e' t p_e'_t 

{-@ lem_free_bound_in_env :: g:Env -> t:Type -> ProofOf(WFType g t)
                -> { x:Vname | not (in_env x g) }
                -> { pf:_ | not (Set_mem x (free t)) } @-}
lem_free_bound_in_env :: Env -> Type -> WFType -> Vname -> Proof
lem_free_bound_in_env g t (WFRefn _g z b p z' p_z'_p_bl) x = case t of
  (TRefn _ _ _) -> case ( x == z' ) of
        (True)  -> () 
        (False) -> () ? lem_fv_bound_in_fenv (FCons z' (FTBasic b) (erase_env g)) 
                                             (unbind z z' p) (FTBasic TBool) p_z'_p_bl x
lem_free_bound_in_env g t (WFFunc _g y t_y p_ty_wf t' y' p_y'_t'_wf) x = case t of
  (TFunc _ _ _) -> case ( x == y' ) of
        (True)  -> () ? lem_free_bound_in_env g t_y p_ty_wf x
        (False) -> () ? lem_free_bound_in_env g t_y p_ty_wf x
                      ? lem_free_bound_in_env (Cons y' t_y g) (unbindT y y' t') p_y'_t'_wf x
lem_free_bound_in_env g t (WFExis _g y t_y p_ty_wf t' y' p_y'_t'_wf) x = case t of
  (TExists _ _ _) -> case ( x == y' ) of 
        (True)  -> () ? lem_free_bound_in_env g t_y p_ty_wf x
        (False) -> () ? lem_free_bound_in_env g t_y p_ty_wf x
                      ? lem_free_bound_in_env (Cons y' t_y g) (unbindT y y' t') p_y'_t'_wf x

{-@ lem_free_subset_binds :: g:Env -> t:Type -> ProofOf(WFType g t) 
                -> { pf:_ | Set_sub (free t) (binds g) } @-}
lem_free_subset_binds :: Env -> Type -> WFType -> Proof 
lem_free_subset_binds g t (WFRefn _g z b p z' p_z'_p_bl) = case t of 
  (TRefn _ _ _) -> () ? lem_fv_subset_bindsF (FCons z' (FTBasic b) (erase_env g)) (unbind z z' p) 
                                (FTBasic TBool) p_z'_p_bl
lem_free_subset_binds g t (WFFunc _g y t_y p_ty_wf t' y' p_y'_t'_wf) = case t of
  (TFunc _ _ _) -> () ? lem_free_subset_binds g t_y p_ty_wf
                      ? lem_free_subset_binds (Cons y' t_y g) (unbindT y y' t') p_y'_t'_wf
lem_free_subset_binds g t (WFExis _g y t_y p_ty_wf t' y' p_y'_t'_wf) = case t of
  (TExists _ _ _) -> () ? lem_free_subset_binds g t_y p_ty_wf
                        ? lem_free_subset_binds (Cons y' t_y g) (unbindT y y' t') p_y'_t'_wf

{-@ lem_truncate_wfenv :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> ProofOf(WFEnv g) @-}
lem_truncate_wfenv :: Env -> Env -> WFEnv -> WFEnv
lem_truncate_wfenv g Empty          p_g_wf    = p_g_wf          
lem_truncate_wfenv g (Cons x v g')  p_xg'g_wf = lem_truncate_wfenv g g' p_g'g_wf
  where
    (WFEBind _ p_g'g_wf _ _ _) = p_xg'g_wf 
