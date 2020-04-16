{-# LANGUAGE GADTs #-}

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Substitution where

--import Control.Exception (assert)
import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Syntax
import Envioronments
import Semantics
import BareTyping
import WellFormedness
import Typing
import STLCLemmas
import STLCSoundness
import Primitives
import BasicLemmas
import BasicLemmas2
import DenotationalSoundness

-- force these into scope
semantics = (Step, EvalsTo)
typing = (HasBType, HasType, Subtype, WFType, WFEnv)
denotations = (Entails, Denotes, DenotesEnv, ValueDenoted)


{-@ lem_subst_typ :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
            -> t_x:Type -> ProofOf(HasType g v_x t_x) 
            -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> e:Expr -> t:Type 
            -> ProofOf(HasType (concatE (Cons x t_x g) g') e t) 
            -> ProofOf(HasType (concatE g (esubFV x v_x g')) (subFV x v_x e) (tsubFV x v_x t)) @-}
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
lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e t (TVar2 env_ z _t p_z_t w t_w)
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
                    (True)  -> lem_weaken_typ (concatE g (esubFV x v_x g'')) Empty v_x 
                                              (tsubFV x v_x t) p_gg''_vx_tx w (tsubFV x v_x t_w)
                                              ? toProof ( e === (FV x) )
                                   where
                                     p_gg''_vx_tx = lem_subst_typ g g'' x v_x t_x p_vx_tx 
                                                                  p_gg''_wf e t p_z_t
                                     (WFEBind _gg'' p_gg''_wf _ _ _) = p_env_wf
                    (False) -> TVar2 (concatE g (esubFV x v_x g'')) --z
                                 (z ? lem_in_env_esub g'' x v_x z
                                    ? lem_in_env_concat g g'' z
                                    ? lem_in_env_concat (Cons x t_x g) g'' z) 
                                 (tsubFV x v_x t) p_z_tvx --w 
                                 (w ? lem_in_env_esub g'' x v_x w
                                    ? lem_in_env_concat g g'' w
                                    ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx w
                                    ? lem_in_env_concat (Cons x t_x g) g'' w)
                                 (tsubFV x v_x t_w)
                                   where
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
        p_g'g_tzvx       = lem_subst_wf g g' x v_x t_x p_vx_tx t_z p_env_tz
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
        p_g'g_t'vx       = lem_subst_wf  g g' x v_x t_x p_vx_tx t p_env_t
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
        p_g'g_t    = lem_subst_wf  g g' x v_x t_x p_vx_tx t p_env_t
        p_env_s    = lem_typing_wf (concatE (Cons x t_x g) g') e s p_env_e_s p_env_wf
        p_g'g_s_t  = lem_subst_sub g g' x v_x t_x p_vx_tx p_env_wf s p_env_s t p_env_t p_env_s_t


{-@ assume lem_subst_in_csubst ::  g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
        -> t_x:Type -> thCon:CSubst -> ProofOf(DenotesEnv (concatE (Cons x t_x g) g') thCon)
        -> th:CSubst -> { th': CSubst | thCon == concatCS (CCons x v_x th) th'} -> e:Expr
        -> { pf:_ | csubst thCon e == csubst (concatCS th (sub_inCS x v_x th')) (subFV x v_x e) } @-}
lem_subst_in_csubst :: Env -> Env -> Vname -> Value -> Type -> CSubst -> DenotesEnv
                           -> CSubst -> CSubst -> Expr -> Proof
lem_subst_in_csubst = undefined
{- lem_subst_in_csubst {-g g'-}   th CEmpty ...
lem_subst_in_csubst {-g g'-}  x v_x t_x thCon den_env_thcon th (CCons y v th') e
lem_subst_in_csubst th x v_x (CCons y v th') e
  =   csubst (concatCS (CCons x v_x th) (CCons y v th')) e  
  === csubst (CCons y v (concatCS (CCons x v_x th) th')) e
  === csubst (concatCS (CCons x v_x th) th') (subFV y v e)
    ? lem_subst_in_csubst th x v_x th' (subFV y v e)
  === csubst (concatCS th (sub_inCS x v_x th')) (subFV x v_x (subFV y v e))
    ? lem_commute_subFV x v_x y v e
  === csubst (concatCS .... -}

{-@ lem_subst_sub :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
            -> t_x:Type -> ProofOf(HasType g v_x t_x) 
            -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) 
            -> s:Type -> ProofOf(WFType (concatE (Cons x t_x g) g') s)
            -> t:Type -> ProofOf(WFType (concatE (Cons x t_x g) g') t)
            -> ProofOf(Subtype (concatE (Cons x t_x g) g') s t) 
            -> ProofOf(Subtype (concatE g (esubFV x v_x g')) (tsubFV x v_x s) (tsubFV x v_x t)) @-}
lem_subst_sub :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Type -> WFType -> Type -> WFType -> Subtype -> Subtype
{-lem_subst_sub g g' x v_x t_x p_vx_tx p_env_wf s p_env_s t p_env_t 
              (SBase _g z1 b p1 z2 p2 y ent_yg_p2) 
  = SBase (concatE g (esubFV x v_x g')) x1 b .....
      where
        EntPred _yg _p2 func_th_thp_tt = ent_yg_p2
-}
lem_subst_sub g g' x v_x t_x p_vx_tx p_env_wf ty1 p_env_ty1 ty2 p_env_ty2
              (SFunc env_ x1 s1 x2 s2 p_s2_s1 t1 t2 y_ p_yenv_t1_t2)
  = SFunc (concatE g (esubFV x v_x g')) x1 (tsubFV x v_x s1) x2 (tsubFV x v_x s2)
          p_s2vx_s1vx (tsubFV x v_x t1) (tsubFV x v_x t2) y p_yg'g_t1vx_t2vx
      where 
        y                = y_  ? lem_in_env_esub g' x v_x y_ 
                               ? lem_in_env_concat g  g' y_ 
                               ? lem_in_env_concat (Cons x t_x g) g' y_
                               ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx y_
        (WFFunc _ _ _s1 p_env_s1 _ w1 p_w1env_t1) = p_env_ty1
        (WFFunc _ _ _s2 p_env_s2 _ w2 p_w2env_t2) = p_env_ty2
        _p_yenv_t1       = lem_change_var_wf (concatE (Cons x t_x g) g') w s1 Empty 
                                             (unbindT x1 w1 t1) p_w1env_t1 y
                                             `withProof` lem_unbindT_and_tsubFV x1 w1 (FV y) t1
        p_yenv_t1        = lem_subtype_in_env_wf (concatE (Cons x t_x g) g') Empty y s2 s1 
                                             p_s2_s1 (unbindT x1 y t1) _p_yenv_t1
        p_yenv_t2        = lem_change_var_wf (concatE (Cons x t_x g) g') w s2 Empty
                                             (unbindT x2 w2 t2) p_w2env_t2 y
                                             `withProof` lem_unbindT_and_tsubFV x2 w2 (FV y) t2
        p_s2vx_s1vx      = lem_subst_sub g g' x v_x t_x p_vx_tx p_env_wf 
                                         s2 p_env_s2 s1 p_env_s1 p_s2_s1 
        p_yenv_wf        = WFEBind (concatE (Cons x t_x g) g') p_env_wf y s2 p_env_s2
        p_yg'g_t1vx_t2vx = lem_subst_sub g (Cons y s2 g') x v_x t_x p_vx_tx p_yenv_wf
                                         (unbindT x1 y t1) p_yenv_t1 
                                         (unbindT x2 y t2) p_yenv_t2 p_yenv_t1_t2
lem_subst_sub g g' x v_x t_x p_vx_tx p_env_wf t p_env_t t2 p_env_t2
              (SWitn env_ v_z t_z p_env_vz_tz _t z t' p_env_t_t'vz)
  = SWitn (concatE g (esubFV x v_x g')) (subFV x v_x v_z) (tsubFV x v_x t_z) p_g'g_vzvx_tzvx
          (tsubFV x v_x t) z (tsubFV x v_x t') p_g'g_tvx_t'vzvx
      where
        p_g'g_vzvx_tzvx  = lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf v_z t_z p_env_vz_tz
        (WFExis _ _ _ _ _ y p_yenv_t') = p_env_t2
        p_env_t'vz       = lem_subst_wf (concatE (Cons x t_x g) g') Empty y v_z t_z p_vz_tz 
                              (unbindT z y t') p_yenv_t' ? lem_tsubFV_unbindT z y v_z t'
        p_g'g_tvx_t'vzvx = lem_subst_sub g g' x v_x t_x p_vx_tx p_env_wf t p_env_t 
                                         (tsubBV z v_z t') p_env_t'vz p_env_t_t'vz
                                         ? lem_commute_tsubFV_tsubBV z v_z x v_x t'

{-@ data Subtype where
    SBase :: g:Env -> v1:Vname -> b:Base -> p1:Pred -> v2:Vname -> p2:Pred 
               -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p2)) }
               -> ProofOf(Entails ( Cons y (TRefn b v1 p1) g) (unbind v2 y p2))
               -> ProofOf(Subtype g (TRefn b v1 p1) (TRefn b v2 p2))
 |  SBind :: g:Env -> x:Vname -> t_x:Type -> t:Type -> {t':Type | not Set_mem x (free t')} 
               -> { y:Vname | not (in_env y g) && not (Set_mem y (free t))
                                               && not (Set_mem y (free t')) }
               -> ProofOf(Subtype (Cons y t_x g) (unbindT x y t) t')
               -> ProofOf(Subtype g (TExists x t_x t) t')
@-} 

