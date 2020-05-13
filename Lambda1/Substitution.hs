{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-} 
{- @ LIQUID "--no-totality" @-} 
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Substitution where

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
import TechLemmas2
import DenotationalSoundness

-- force these into scope
semantics = (Step, EvalsTo)
typing = (HasBType, HasType, Subtype, WFType, WFEnv)
denotations = (Entails, Denotes, DenotesEnv, ValueDenoted)

{-@ reflect foo16 @-}
foo16 x = Just x
foo16 :: a -> Maybe a

{-@ measure envSize @-}
{-@ envSize :: Env -> { n:Int | n >= 0 } @-}
envSize :: Env -> Int
envSize Empty          = 0
envSize (Cons x t_x g) = 1 + envSize g


{-@ lem_subst_wfenv :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> ProofOf(HasType g v_x t_x)
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') )
        -> ProofOf(WFEnv (concatE g (esubFV x v_x g')) ) / [envSize g'] @-}
lem_subst_wfenv :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv -> WFEnv
lem_subst_wfenv g Empty           x v_x t_x p_vx_tx p_xg_wf  = case p_xg_wf of
  (WFEBind _g p_g_wf _x _tx _) -> p_g_wf
lem_subst_wfenv g (Cons z t_z g') x v_x t_x p_vx_tx p_env_wf = case p_env_wf of
  (WFEBind env' p_env'_wf _z _tz p_env'_tz) -> WFEBind env'' p_env''_wf z (tsubFV x v_x t_z) p_env''_tzvx
    where
      env''        = concatE g (esubFV x v_x g')
      p_env''_wf   = lem_subst_wfenv g g' x v_x t_x p_vx_tx p_env'_wf
      p_env''_tzvx = lem_subst_wf g g' x v_x t_x p_vx_tx p_env'_wf t_z p_env'_tz

{-@ lem_subst_typ :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> ProofOf(HasType g v_x t_x) 
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType (concatE (Cons x t_x g) g') e t }
        -> ProofOf(HasType (concatE g (esubFV x v_x g')) (subFV x v_x e) (tsubFV x v_x t)) / [typSize p_e_t] @-}
lem_subst_typ :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Expr -> Type -> HasType -> HasType
lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e t (TBC _env b) 
  = TBC (concatE g (esubFV x v_x g')) b ? lem_tsubFV_tybc x v_x b
lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e t (TIC _env n) 
  = TIC (concatE g (esubFV x v_x g')) n ? lem_tsubFV_tyic x v_x n 
lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e t (TVar1 _env z _t) 
  = case g' of
      (Empty)           -> p_vx_tx ? lem_free_bound_in_env g t_x p_g_tx x
                                   ? toProof ( tsubFV x v_x t === t_x )
        where
          (WFEBind _g p_g_wf _x _tx p_g_tx) = p_env_wf
      (Cons _z _ g'')  -> TVar1 (concatE g (esubFV x v_x g'')) --z 
                                (z ? lem_in_env_esub g'' x v_x z
                                   ? lem_in_env_concat g g'' z
                                   ? lem_in_env_concat (Cons x t_x g) g'' z)          
                                (tsubFV x v_x t) 
lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e t (TVar2 env_ z _t p_z_t w_ t_w)
    = case g' of             -- g''=Emp so x=w and p_z_t :: HasBType(g (FV z) t)
        (Empty)           -> case (x == z) of
                               (True)  -> impossible "it is"
                               (False) -> p_z_t
                                           ? toProof ( tsubFV x v_x t === t )
                                           ? lem_free_bound_in_env g t p_g_t x
                                           ? toProof ( e === (FV z) )
                                   where
                                     (WFEBind g_ p_g_wf _ _ _) = p_env_wf
                                     p_g_t = lem_typing_wf g (FV z) t p_z_t p_g_wf
        (Cons _w _tw g'') -> case (x == z) of
                    (True)  -> lem_weaken_typ (concatE g (esubFV x v_x g'')) Empty p_env'_wf
                                              v_x (tsubFV x v_x t) p_gg''_vx_tx w (tsubFV x v_x t_w)
                                              ? toProof ( e === (FV x) )
                                   where
                                     w = w_ ? lem_in_env_esub g'' x v_x w_
                                            ? lem_in_env_concat g g'' w_
                                            ? lem_in_env_concat (Cons x t_x g) g'' w_
                                            ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx w_
                                     p_env'_wf    = lem_subst_wfenv g g'' x v_x t_x p_vx_tx p_gg''_wf
                                     p_gg''_vx_tx = lem_subst_typ g g'' x v_x t_x p_vx_tx p_gg''_wf
                                                                  e t p_z_t
                                     (WFEBind _gg'' p_gg''_wf _ _ _) = p_env_wf
                                     p_xg_wf = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
                                     (WFEBind _ p_g_wf _ _ _) = p_xg_wf
                                     p_vx_er_tx    = lem_typing_hasbtype g v_x t_x p_vx_tx p_g_wf
                    (False) -> TVar2 (concatE g (esubFV x v_x g'')) --z
                                 (z ? lem_in_env_esub g'' x v_x z
                                    ? lem_in_env_concat g g'' z
                                    ? lem_in_env_concat (Cons x t_x g) g'' z) 
                                 (tsubFV x v_x t) p_z_tvx w 
                                 (tsubFV x v_x t_w)
                                   where
                                     w = w_ ? lem_in_env_esub g'' x v_x w_
                                            ? lem_in_env_concat g g'' w_
                                            ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx w_
                                            ? lem_in_env_concat (Cons x t_x g) g'' w_
                                     (WFEBind _gg'' p_gg''_wf _ _ _) = p_env_wf
                                     p_z_tvx = lem_subst_typ g g'' x v_x t_x p_vx_tx
                                                             p_gg''_wf e t p_z_t
                                     p_xg_wf = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
                                     (WFEBind _ p_g_wf _ _ _) = p_xg_wf
                                     p_vx_er_tx    = lem_typing_hasbtype g v_x t_x p_vx_tx p_g_wf
lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e t (TPrm _en c) 
  = TPrm (concatE g (esubFV x v_x g')) c ? lem_tsubFV_ty x v_x c 
lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e t (TAbs env_ z t_z p_env_tz e' t' y_ p_yenv_e'_t') 
  = TAbs (concatE g (esubFV x v_x g')) z (tsubFV x v_x t_z) p_g'g_tzvx
         (subFV x v_x e') (tsubFV x v_x t') y p_yg'g_e'vx_t'vx
      where
        y                = y_  ? lem_in_env_esub g' x v_x y_ 
                               ? lem_in_env_concat g  g' y_ 
                               ? lem_in_env_concat (Cons x t_x g) g' y_
                               ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx y_
        p_xg_wf     = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _) = p_xg_wf
        p_vx_er_tx       = lem_typing_hasbtype g v_x t_x p_vx_tx p_g_wf
        p_yenv_wf        = WFEBind (concatE (Cons x t_x g) g') p_env_wf y t_z p_env_tz
        p_g'g_tzvx       = lem_subst_wf g g' x v_x t_x p_vx_tx p_env_wf t_z p_env_tz
        p_yg'g_e'vx_t'vx = lem_subst_typ g (Cons y t_z g') x v_x t_x p_vx_tx p_yenv_wf
                                         (unbind z y e') (unbindT z y t') p_yenv_e'_t'
                                         ? lem_commute_subFV_subBV1 z (FV y) x v_x e'
                                         ? lem_commute_tsubFV_tsubBV1 z (FV y) x v_x t'
lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e t (TApp env_ e' z t_z t' p_env_e'_tzt' e_z p_env_ez_tz) 
  = TApp (concatE g (esubFV x v_x g')) (subFV x v_x e') z (tsubFV x v_x t_z) (tsubFV x v_x t') 
         p_g'g_e'vx_tzt'vx (subFV x v_x e_z)  p_g'g_ezvx_tzvx         
      where
        p_g'g_e'vx_tzt'vx = lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e' 
                                          (TFunc z t_z t') p_env_e'_tzt'
        p_g'g_ezvx_tzvx   = lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e_z t_z p_env_ez_tz
lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e t (TLet env_ e_z t_z p_env_ez_tz z e' t_ 
                                                        p_env_t y_ p_yenv_e'_t) 
  = TLet (concatE g (esubFV x v_x g')) (subFV x v_x e_z) (tsubFV x v_x t_z) p_g'g_ezvx_tzvx z
         (subFV x v_x e') (tsubFV x v_x t) p_g'g_t'vx y p_yg'g_e'vx_tvx
      where
        y                = y_  ? lem_in_env_esub g' x v_x y_ 
                               ? lem_in_env_concat g  g' y_ 
                               ? lem_in_env_concat (Cons x t_x g) g' y_
                               ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx y_
        p_xg_wf     = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _) = p_xg_wf
        p_vx_er_tx       = lem_typing_hasbtype g v_x t_x p_vx_tx p_g_wf
        p_env_tz         = lem_typing_wf env_ e_z t_z p_env_ez_tz p_env_wf
        p_yenv_wf        = WFEBind (concatE (Cons x t_x g) g') p_env_wf y t_z p_env_tz
        p_g'g_ezvx_tzvx  = lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e_z t_z p_env_ez_tz
        p_g'g_t'vx       = lem_subst_wf  g g' x v_x t_x p_vx_tx p_env_wf t p_env_t
        p_yg'g_e'vx_tvx  = lem_subst_typ g (Cons y t_z g') x v_x t_x p_vx_tx p_yenv_wf 
                                         (unbind z y e') (unbindT z y t) p_yenv_e'_t
                                         ? lem_commute_subFV_subBV1 z (FV y) x v_x e'
                                         ? lem_commute_tsubFV_tsubBV1 z (FV y) x v_x t
lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e t (TAnn env_ e' t_ p_env_e'_t) 
  = TAnn (concatE g (esubFV x v_x g')) (subFV x v_x e') (tsubFV x v_x t) p_g'g_e'_t
      where
        p_g'g_e'_t = lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e' t p_env_e'_t
lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e t (TSub env_ e_ s p_env_e_s t_ p_env_t p_env_s_t) 
  = TSub (concatE g (esubFV x v_x g')) (subFV x v_x e) (tsubFV x v_x s) p_g'g_e_s
         (tsubFV x v_x t) p_g'g_t p_g'g_s_t
      where
        p_g'g_e_s  = lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e s p_env_e_s
        p_g'g_t    = lem_subst_wf  g g' x v_x t_x p_vx_tx p_env_wf t p_env_t
        p_env_s    = lem_typing_wf (concatE (Cons x t_x g) g') e s p_env_e_s p_env_wf
        p_g'g_s_t  = lem_subst_sub g g' x v_x t_x p_vx_tx p_env_wf s p_env_s t p_env_t p_env_s_t


data AugmentedCSubstP where
    AugmentedCSubst :: Env -> Env -> Vname -> Expr -> Type -> CSubst -> AugmentedCSubstP

data AugmentedCSubst where
    InsertInCS :: Env -> Env -> Vname -> Expr -> Type -> CSubst -> CSubst -> DenotesEnv
                      -> (Expr -> Proof) -> (Type -> Proof) -> AugmentedCSubst

{-@ data AugmentedCSubst where
    InsertInCS :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value -> t_x:Type 
        -> th':CSubst -> th:CSubst -> ProofOf(DenotesEnv (concatE (Cons x t_x g) g') th)
        -> ( p:Pred -> { pf:Proof | csubst th p  ==  csubst th'  (subFV x v_x p) } )
        -> ( t:Type -> { pf:Proof | ctsubst th t == ctsubst th' (tsubFV x v_x t) } )
        -> ProofOf(AugmentedCSubst g g' x v_x t_x th') @-}

{-@ lem_add_var_csubst :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> ProofOf(HasType g v_x t_x)
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') )
        -> th':CSubst -> ProofOf(DenotesEnv (concatE g (esubFV x v_x g')) th')
        -> ProofOf(AugmentedCSubst g g' x v_x t_x th') / [envSize g'] @-}
lem_add_var_csubst :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                          -> CSubst -> DenotesEnv -> AugmentedCSubst
lem_add_var_csubst g Empty           x v_x_ t_x p_vx_tx p_env_wf zth' den_env'_th' = case p_env_wf of 
  (WFEBind _ p_g_wf _ _ _) -> case (lem_denote_sound_typ g v_x_ t_x p_vx_tx p_g_wf zth' den_env'_th') of
      (ValDen _ _ val ev_th'vx_val den_th'tx_val) 
        -> InsertInCS g Empty x v_x t_x zth' {-th-} (CCons x th'vx (zth' ? lem_binds_env_th g zth' den_env'_th'))
                      (DExt g zth' den_env'_th' x t_x th'vx  den_th'tx_th'vx) eq_func1 eq_func2
                     {-(csubst zth' v_x ? lem_csubst_value zth' v_x
                                      ? lem_den_nofv (csubst zth' v_x) (ctsubst zth' t_x)
                                                     (den_th'tx_val ? lem_value_refl th'vx val ev_th'vx_val)))-}
                  {-   (den_th'tx_val ? lem_value_refl th'vx 
                          {-(csubst zth' v_x ? lem_csubst_value zth' v_x
                                           ? lem_den_nofv (csubst zth' v_x) (ctsubst zth' t_x)
                                                   (den_th'tx_val ? lem_value_refl th'vx val ev_th'vx_val)))-}
                          val ev_th'vx_val)) eq_func1 eq_func2 -}
             where
               {-@ v_x :: { v_x:Value | Set_sub (fv v_x) (bindsC zth') && v_x == v_x_ } @-}
               v_x   = v_x_ ? lem_binds_env_th g zth' den_env'_th'
                            ? lem_fv_subset_bindsB (erase_env g) v_x_ (erase t_x) p_vx_er_tx
                            ? lem_csubst_value zth' v_x_
                            ? lem_den_nofv (csubst zth' v_x_) (ctsubst zth' t_x) -- den_th'tx_th'vx
                                               (den_th'tx_val ? lem_value_refl (csubst zth' v_x_) val ev_th'vx_val) 
               p_vx_er_tx   = lem_typing_hasbtype g v_x_ t_x p_vx_tx p_g_wf
               {-@ th'vx :: { v:Value | Set_emp (fv v) && v == csubst zth' v_x } @-}
               th'vx :: Expr
               th'vx = csubst zth' v_x {-? lem_csubst_value zth' v_x
                                ? lem_den_nofv (csubst zth' v_x) (ctsubst zth' t_x) -- den_th'tx_th'vx 
                                               (den_th'tx_val ? lem_value_refl th'vx val ev_th'vx_val) -}
        --(WFEBind _ p_g_wf _ _ _) = p_env_wf 
        --vd_th'vx_th'tx = lem_denote_sound_typ g v_x t_x p_vx_tx p_g_wf zth' den_env'_th' 
        --(ValDen _ _ val ev_th'vx_val den_th'tx_val) = vd_th'vx_th'tx
               {-@ den_th'tx_th'vx :: ProofOf(Denotes (ctsubst zth' t_x) (csubst zth' v_x)) @-}
               den_th'tx_th'vx :: Denotes
               den_th'tx_th'vx = den_th'tx_val ? lem_value_refl th'vx val ev_th'vx_val
        {- @ eq_func1 :: p:Pred -> { pf:Proof | csubst th p == csubst zth' (subFV x v_x_ p) } @-}
               eq_func1 :: Expr -> Proof   -- csubst th p
               eq_func1 p = () ? lem_csubst_subFV   zth' x v_x  p 
        {- @ eq_func2 :: t:Type -> { pf:Proof | ctsubst th t == ctsubst zth' (tsubFV x v_x_ t) } @-}
               eq_func2 :: Type -> Proof
               eq_func2 t = () ? lem_ctsubst_tsubFV zth' x v_x  t
        --th    = (CCons x th'vx (zth' ? lem_binds_env_th g zth' den_env'_th'))
lem_add_var_csubst g (Cons z t_z g') x v_x_ t_x p_vx_tx p_zenv_wf zth' den_zenv'_zth'
  = case den_zenv'_zth' of   
      (DExt env' th' den_env'_th' _z tzvx v_z den_th'tzvx_vz)
        -> InsertInCS g (Cons z t_z g') x v_x_ t_x zth' zth den_zenv_zth eq_funcz1 eq_funcz2
             where
               zth          = CCons z v_z (th ? lem_binds_env_th env th den_env_th) 
               den_zenv_zth = DExt env th den_env_th z t_z v_z den_thtz_vz
               den_thtz_vz  = den_th'tzvx_vz ? eq_func2 t_z

               (WFEBind _ p_env_wf _ _ _) = p_zenv_wf
               env          = concatE (Cons x t_x g) g'
               p_vx_er_tx   = lem_typing_hasbtype g v_x_ t_x p_vx_tx p_g_wf
               p_xg_wf      = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
               (WFEBind _ p_g_wf _ _ _) = p_xg_wf
               {-@ eq_func1 :: p:Pred -> { pf:Proof | csubst th p == csubst th' (subFV x v_x_ p) } @-}
               {-@ eq_func2 :: t:Type -> { pf:Proof | ctsubst th t == ctsubst th' (tsubFV x v_x_ t) } @-}
               eq_func1 :: Pred -> Proof
               eq_func2 :: Type -> Proof 
               (InsertInCS _ _ _ _ _ _ th den_env_th eq_func1 eq_func2)
                            = lem_add_var_csubst g g' x v_x_ t_x p_vx_tx p_env_wf th' den_env'_th'
               -- csubst zth p  ==  csubst zth'  (subFV x v_x p)
               {-@ eq_funcz1 :: p:Pred
                        -> { pf:Proof | csubst (CCons z v_z th) p == csubst zth' (subFV x v_x_ p) } @-}
               eq_funcz1 :: Expr -> Proof
               eq_funcz1 p = ()     ? toProof ( csubst zth' (subFV x v_x_ p)
                                              ? lem_binds_env_th env' th' den_env'_th'
                                              ? toProof ( zth' === CCons z v_z th' )
                                            === csubst th' (subFV z v_z (subFV x v_x_ p))
                                            === csubst th' (subFV z (subFV x v_x_ v_z) (subFV x v_x_ p))
                                              ? lem_commute_subFV  z v_z x -- v_x_ p
                                                       (v_x_ ? lem_fv_bound_in_benv (erase_env g) v_x_ (erase t_x) 
                                                                   p_vx_er_tx z) p
                                            === csubst th' (subFV x v_x_ (subFV z v_z p))
                                              ? eq_func1 (subFV z v_z p)
                                            === csubst th (subFV z v_z p) )
               {-@ eq_funcz2 :: t:Type 
                        -> { pf:Proof | ctsubst (CCons z v_z th) t == ctsubst zth' (tsubFV x v_x_ t) } @-}
               eq_funcz2 :: Type -> Proof
               eq_funcz2 t = ()     ? toProof ( ctsubst zth' (tsubFV x v_x_ t)
                                              ? lem_binds_env_th env' th' den_env'_th'
                                              ? toProof ( zth' === CCons z v_z th' )
                                            === ctsubst th' (tsubFV z v_z (tsubFV x v_x_ t))
                                            === ctsubst th' (tsubFV z (subFV x v_x_ v_z) (tsubFV x v_x_ t))
                                              ? lem_commute_tsubFV  z v_z x -- v_x_ p
                                                       (v_x_ ? lem_fv_bound_in_benv (erase_env g) v_x_ (erase t_x) 
                                                                   p_vx_er_tx z) t
                                            === ctsubst th' (tsubFV x v_x_ (tsubFV z v_z t))
                                              ? eq_func2 (tsubFV z v_z t)
                                            === ctsubst th (tsubFV z v_z t) )


{-@ lem_subst_ent :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
            -> t_x:Type -> ProofOf(HasType g v_x t_x) 
            -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) 
            -> { p:Pred | Set_sub (fv p) (binds (concatE (Cons x t_x g) g')) }
            -> ProofOf(Entails (concatE (Cons x t_x g) g') p) 
            -> ProofOf(Entails (concatE g (esubFV x v_x g')) (subFV x v_x p)) @-}
lem_subst_ent :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv -> Pred -> Entails -> Entails
lem_subst_ent g g' x v_x t_x p_vx_tx p_env_wf p (EntPred env _p evals_func)
  = EntPred (concatE g (esubFV x v_x g')) (subFV x v_x p) evals_func'
      where
        {-@ evals_func' :: th':CSubst -> ProofOf(DenotesEnv (concatE g (esubFV x v_x g')) th')
                                -> ProofOf(EvalsTo (csubst th' (subFV x v_x p)) (Bc True)) @-}
        evals_func' :: CSubst -> DenotesEnv -> EvalsTo  
        evals_func' th' den_env'_th' = evals_func th den_env_th ? eq_func p
          where
            (InsertInCS _ _ _ _ _ _ th den_env_th eq_func _) 
                = lem_add_var_csubst g g' x v_x t_x p_vx_tx p_env_wf th' den_env'_th'

{-@ lem_subst_sub :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> ProofOf(HasType g v_x t_x) 
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) 
        -> s:Type -> ProofOf(WFType (concatE (Cons x t_x g) g') s)
        -> t:Type -> ProofOf(WFType (concatE (Cons x t_x g) g') t)
        -> { p_s_t:Subtype | propOf p_s_t == Subtype (concatE (Cons x t_x g) g') s t }
        -> ProofOf(Subtype (concatE g (esubFV x v_x g')) (tsubFV x v_x s) (tsubFV x v_x t)) / [subtypSize p_s_t] @-}
lem_subst_sub :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Type -> WFType -> Type -> WFType -> Subtype -> Subtype
lem_subst_sub g g' x v_x t_x p_vx_tx p_env_wf s p_env_s t p_env_t 
              (SBase env z1 b p1 z2 p2 y_ ent_yenv_p2) -- p_env_s_t
  = SBase (concatE g (esubFV x v_x g')) z1 b (subFV x v_x p1) z2 (subFV x v_x p2) y
          ent_yenv'_p2vx  -- Entails (Cons y (TRefn b z1 (subFV x v_x p1)) env') (unbind z2 y (subFV x v_x p2))
      where
        y                = y_  ? lem_in_env_esub g' x v_x y_ 
                               ? lem_in_env_concat g  g' y_ 
                               ? lem_in_env_concat (Cons x t_x g) g' y_
                               ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx y_
        p_xg_wf          = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _)       = p_xg_wf
        p_vx_er_tx       = lem_typing_hasbtype g v_x t_x p_vx_tx p_g_wf
        (WFRefn _ _ _ _p2 w_ p_wenv_p2_bl) = p_env_t
        w                = w_  ? lem_in_env_concat g  g' w_ 
                               ? lem_in_env_concat (Cons x t_x g) g' w_
        p_yenv_wf        = WFEBind env p_env_wf y (TRefn b z1 p1) p_env_s
        p_yenv_p2_bl     = lem_change_var_btyp (erase_env env) w (BTBase b) BEmpty (unbind z2 w p2)
                                               (BTBase TBool) p_wenv_p2_bl y
                                               ? lem_subFV_unbind z2 w (FV y) p2
        --EntPred _yenv _p2 func_th_thp_tt = ent_yenv_p2 -- Entails (Cons y (TRefn b z1 p1) env) (unbind z2 y p2)
        ent_yenv'_p2vx   = lem_subst_ent g (Cons y (TRefn b z1 p1) g') x v_x t_x p_vx_tx p_yenv_wf
                                   (unbind z2 y p2 ? lem_fv_subset_bindsB (BCons y (BTBase b) (erase_env env)) 
                                           (unbind z2 y p2) (BTBase TBool) p_yenv_p2_bl)
                                   ent_yenv_p2 
                                   ? lem_commute_subFV_subBV1 z2 (FV y) x v_x p2
lem_subst_sub g g' x v_x t_x p_vx_tx p_env_wf ty1 p_env_ty1 ty2 p_env_ty2
              (SFunc env_ x1 s1 x2 s2 p_s2_s1 t1 t2 y_ p_yenv_t1_t2)
  = SFunc (concatE g (esubFV x v_x g')) x1 (tsubFV x v_x s1) x2 (tsubFV x v_x s2)
          p_s2vx_s1vx (tsubFV x v_x t1) (tsubFV x v_x t2) y p_yg'g_t1vx_t2vx
      where 
        y                = y_  ? lem_in_env_esub g' x v_x y_ 
                               ? lem_in_env_concat g  g' y_ 
                               ? lem_in_env_concat (Cons x t_x g) g' y_
                               ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx y_
        p_xg_wf          = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _)       = p_xg_wf
        p_vx_er_tx       = lem_typing_hasbtype g v_x t_x p_vx_tx p_g_wf
        (WFFunc _ _ _s1 p_env_s1 _ w1 p_w1env_t1) = p_env_ty1
        (WFFunc _ _ _s2 p_env_s2 _ w2 p_w2env_t2) = p_env_ty2
        _p_yenv_t1       = lem_change_var_wf (concatE (Cons x t_x g) g') w1 s1 Empty 
                                             (unbindT x1 w1 t1) p_w1env_t1 y
                                             `withProof` lem_tsubFV_unbindT x1 w1 (FV y) t1
        p_yenv_t1        = lem_subtype_in_env_wf (concatE (Cons x t_x g) g') Empty y s2 s1 
                                             p_s2_s1 (unbindT x1 y t1) _p_yenv_t1
        p_yenv_t2        = lem_change_var_wf (concatE (Cons x t_x g) g') w2 s2 Empty
                                             (unbindT x2 w2 t2) p_w2env_t2 y
                                             `withProof` lem_tsubFV_unbindT x2 w2 (FV y) t2
        p_s2vx_s1vx      = lem_subst_sub g g' x v_x t_x p_vx_tx p_env_wf 
                                         s2 p_env_s2 s1 p_env_s1 p_s2_s1 
        p_yenv_wf        = WFEBind (concatE (Cons x t_x g) g') p_env_wf y s2 p_env_s2
        p_yg'g_t1vx_t2vx = lem_subst_sub g (Cons y s2 g') x v_x t_x p_vx_tx p_yenv_wf
                                         (unbindT x1 y t1) p_yenv_t1 
                                         (unbindT x2 y t2) p_yenv_t2 p_yenv_t1_t2
                                         ? lem_commute_tsubFV_tsubBV1 x1 (FV y) x v_x t1
                                         ? lem_commute_tsubFV_tsubBV1 x2 (FV y) x v_x t2
lem_subst_sub g g' x v_x t_x p_vx_tx p_env_wf t p_env_t t2 p_env_t2
              (SWitn env v_z t_z p_env_vz_tz _t z t' p_env_t_t'vz)
  = SWitn (concatE g (esubFV x v_x g')) (subFV x v_x v_z) (tsubFV x v_x t_z) p_g'g_vzvx_tzvx
          (tsubFV x v_x t) z (tsubFV x v_x t') p_g'g_tvx_t'vzvx
      where
        p_g'g_vzvx_tzvx  = lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf v_z t_z p_env_vz_tz
        (WFExis _ _ _ p_env_tz _ y p_yenv_t') = p_env_t2
        p_yenv_wf        = WFEBind env p_env_wf y t_z p_env_tz
        p_env_t'vz       = lem_subst_wf (concatE (Cons x t_x g) g') Empty y v_z t_z p_env_vz_tz 
                              p_yenv_wf (unbindT z y t') p_yenv_t' ? lem_tsubFV_unbindT z y v_z t'
        p_g'g_tvx_t'vzvx = lem_subst_sub g g' x v_x t_x p_vx_tx p_env_wf t p_env_t 
                                         (tsubBV z v_z t') p_env_t'vz p_env_t_t'vz
                                         ? lem_commute_tsubFV_tsubBV z v_z x v_x t'
lem_subst_sub g g' x v_x t_x p_vx_tx p_env_wf t1 p_env_t1 t' p_env_t'
              (SBind env z t_z t _t' w_ p_wenv_t_t')
  = SBind (concatE g (esubFV x v_x g')) z (tsubFV x v_x t_z) (tsubFV x v_x t) (tsubFV x v_x t')
          w p_wenv'_tvx_t'vx
      where 
        w                = w_ ? lem_in_env_esub g' x v_x w_
                              ? lem_in_env_concat g g' w_
                              ? lem_in_env_concat (Cons x t_x g) g' w_
                              ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx w_
        p_xg_wf          = lem_truncate_wfenv (Cons x t_x g) g' p_env_wf
        (WFEBind _ p_g_wf _ _ _)       = p_xg_wf
        p_vx_er_tx       = lem_typing_hasbtype g v_x t_x p_vx_tx p_g_wf
        (WFExis _ _ _ p_env_tz _ y p_yenv_t) = p_env_t1
        p_wenv_wf        = WFEBind (concatE (Cons x t_x g) g') p_env_wf w t_z p_env_tz
        p_wenv_t         = lem_change_var_wf env y t_z Empty (unbindT z y t) p_yenv_t w
                                         ? lem_tsubFV_unbindT z y (FV w) t
        p_wenv_t'        = lem_weaken_wf env Empty t' p_env_t' w t_z
        p_wenv'_tvx_t'vx = lem_subst_sub g (Cons w t_z g') x v_x t_x p_vx_tx p_wenv_wf
                                         (unbindT z w t) p_wenv_t t' p_wenv_t' p_wenv_t_t'
                                         ? lem_commute_tsubFV_tsubBV z (FV w) x v_x t

