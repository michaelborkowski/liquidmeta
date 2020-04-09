{-# LANGUAGE GADTs #-}

--{-@ LIQUID "--higherorder" @-}
{- @ LIQUID "--diff"        @-}
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
import Semantics
import Typing
import Primitives
import BasicLemmas
import BasicLemmas2
import DenotationalSoundness

-- force these into scope
semantics = (Step, EvalsTo)
typing = (HasBType, HasType, Subtype, WFType, WFEnv)
denotations = (Entails, Denotes, DenotesEnv)

{- @ assume lem_subst_btyp :: g:BEnv -> { g':BEnv | Set_emp (Set_cap (bindsB g) (bindsB g')) }
        -> { x:Vname | (not (in_envB x g)) && not (in_envB x g') } -> v_x:Value
        -> t_x:BType -> ProofOf(HasBType g v_x t_x) -> e:Expr -> t:BType
        -> ProofOf(HasBType (concatB (BCons x t_x g) g') e t)
        -> ProofOf(HasBType (concatB g g') (subFV x v_x e) t) @-}

{- @ assume lem_subtype_in_env_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> { x:Vname | (not (in_env x g)) && not (in_env x g') }
      -> s_x:Type -> t_x:Type -> ProofOf(Subtype g s_x t_x) -> t:Type
      -> ProofOf(WFType (concatE (Cons x t_x g) g') t)
      -> ProofOf(WFType (concatE (Cons x s_x g) g') t) @-} 
{-
{-@ lem_subst_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
            -> t_x:Type -> ProofOf(HasType g v_x t_x) -> t:Type 
            -> ProofOf(WFType (concatE (Cons x t_x g) g') t) 
            -> ProofOf(WFType (concatE g (esubFV x v_x g')) (tsubFV x v_x t)) @-}
lem_subst_wf :: Env -> Env -> Vname -> Expr -> Type -> HasType -> Type -> WFType -> WFType
lem_subst_wf g g' x v_x t_x p_vx_tx t (WFRefn _env z b p y_ p_env'_p_bl) -- _env = g'; x:tx; g
  = WFRefn (concatE g (esubFV x v_x g')) z b (subFV x v_x p) y 
           p_ygg'_pvx_bl 
      where
        y             = y_ ? lem_in_env_esub g' x v_x y_
                           ? lem_in_env_concat g  g' y_
                           ? lem_in_env_concat (Cons x t_x g) g' y_
                           ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx y_
        p_vx_er_tx    = (lem_typing_hasbtype g v_x t_x p_vx_tx)
        p_ygg'_pvx_bl = lem_subst_btyp (erase_env g) (BCons y (BTBase b) (erase_env g')) 
                           (x ? lem_in_env_concatB (erase_env g) (erase_env g') x
                              ? lem_in_env_concatB (erase_env g) (BCons y (BTBase b) (erase_env g')) x)
                           v_x (erase t_x)  p_vx_er_tx (unbind z y p) (BTBase TBool) 
                           (p_env'_p_bl ? lem_erase_concat (Cons x t_x g) g')
                           ? lem_commute_subFV_subBV1 z (FV y) x v_x p
                           ? lem_erase_concat g (esubFV x v_x g')
                           ? lem_erase_esubFV x v_x g'
lem_subst_wf g g' x v_x t_x p_vx_tx t (WFFunc _env z t_z p_env_tz t' y_ p_yenv_t')
  = WFFunc (concatE g (esubFV x v_x g')) z (tsubFV x v_x t_z) p_g'g_tzvx (tsubFV x v_x t') y p_yg'g_t'vx
      where
        {- @ y :: { yy:Vname | t == TFunc z t_z t' } @-}
        y           = y_ ? lem_in_env_esub g' x v_x y_ 
                         ? lem_in_env_concat g  g' y_ 
                         ? lem_in_env_concat (Cons x t_x g) g' y_
                         ? lem_in_env_concat (Cons x t_x g) g' y_
                         ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx y_
                         ---- ? lem_binds_esubFV g' x v_x  ----
        p_vx_er_tx  = lem_typing_hasbtype g v_x t_x p_vx_tx
        p_g'g_tzvx  = lem_subst_wf g g'              x v_x t_x p_vx_tx t_z p_env_tz
        p_yg'g_t'vx = lem_subst_wf g (Cons y t_z g') x v_x t_x p_vx_tx (unbindT z y t')  
                         (p_yenv_t' ? lem_erase_concat (Cons x t_x g) g')
                         ? lem_commute_tsubFV_tsubBV1 z (FV y) x v_x t'
                         -- ? toProof ( t === TFunc z t_z t' ) --
                         -- ? lem_erase_concat g (esubFV x v_x g') --
                         -- ? lem_erase_esubFV x v_x g' --
lem_subst_wf g g' x v_x t_x p_vx_tx t (WFExis _env z t_z p_env_tz t' y_ p_yenv_t')
  = WFExis (concatE g (esubFV x v_x g')) z (tsubFV x v_x t_z) p_g'g_tzvx (tsubFV x v_x t') y p_yg'g_t'vx
      where
        y           = y_ ? lem_in_env_esub g' x v_x y_ 
                         ? lem_in_env_concat g  g' y_ 
                         ? lem_in_env_concat (Cons x t_x g) g' y_
                         ? lem_in_env_concat (Cons x t_x g) g' y_
                         ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx y_
        p_vx_er_tx  = lem_typing_hasbtype g v_x t_x p_vx_tx
        p_g'g_tzvx  = lem_subst_wf g g'              x v_x t_x p_vx_tx t_z p_env_tz
        p_yg'g_t'vx = lem_subst_wf g (Cons y t_z g') x v_x t_x p_vx_tx (unbindT z y t')  
                         (p_yenv_t' ? lem_erase_concat (Cons x t_x g) g')
                         ? lem_commute_tsubFV_tsubBV1 z (FV y) x v_x t'
  -}
{-@ assume lem_subst_sub :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
            -> t_x:Type -> ProofOf(HasType g v_x t_x) 
            -> ProofOf(WFEnv (concatE (Cons x t_x g) g') ) -> s:Type -> t:Type 
            -> ProofOf(Subtype (concatE (Cons x t_x g) g') s t) 
            -> ProofOf(Subtype (concatE g (esubFV x v_x g')) (tsubFV x v_x s) (tsubFV x v_x t)) @-}
lem_subst_sub :: Env -> Env -> Vname -> Expr -> Type -> HasType -> WFEnv
                    -> Type -> Type -> Subtype -> Subtype
lem_subst_sub g g' x v_x t_x p_vx_tx p_env_wf s t p_s_t = undefined

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
  = TIC (concatE g (esubFV x v_x g')) n ? lem_tsubFV_tyic x v_x n {-
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
                                     p_vx_er_tx    = (lem_typing_hasbtype g v_x t_x p_vx_tx)
lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e t (TPrm _en c) 
  = TPrm (concatE g (esubFV x v_x g')) c ? lem_tsubFV_ty x v_x c -}
lem_subst_typ g g' x v_x t_x p_vx_tx p_env_wf e t (TAbs env_ z t_z p_env_tz e' t' y_ p_yenv_e'_t') 
  = TAbs (concatE g (esubFV x v_x g')) z (tsubFV x v_x t_z) p_g'g_tzvx
         (subFV x v_x e') (tsubFV x v_x t') y p_yg'g_e'vx_t'vx
      where
        y                = y_  ? lem_in_env_esub g' x v_x y_ 
                               ? lem_in_env_concat g  g' y_ 
                               ? lem_in_env_concat (Cons x t_x g) g' y_
                               ? lem_fv_bound_in_benv (erase_env g) v_x (erase t_x) p_vx_er_tx y_
        p_vx_er_tx       = lem_typing_hasbtype g v_x t_x p_vx_tx
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
        p_vx_er_tx       = lem_typing_hasbtype g v_x t_x p_vx_tx
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
        p_g'g_s_t  = lem_subst_sub g g' x v_x t_x p_vx_tx p_env_wf s t p_env_s_t
{- 
 |  TSub  :: g:Env -> e:Expr -> s:Type -> ProofOf(HasType g e s) -> t:Type 
                -> ProofOf(WFType g t) -> ProofOf(Subtype g s t) 
                -> ProofOf(HasType g e t) @} -- @}

{-@ data Subtype where
    SBase :: g:Env -> v1:Vname -> b:Base -> p1:Pred -> v2:Vname -> p2:Pred 
               -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p2)) }
               -> ProofOf(Entails ( Cons y (TRefn b v1 p1) g) (unbind v2 y p2))
               -> ProofOf(Subtype g (TRefn b v1 p1) (TRefn b v2 p2))
 |  SFunc :: g:Env -> x1:Vname -> s1:Type -> { x2:Vname | not (in_env x2 g) } -> s2:Type
               -> ProofOf(Subtype g s2 s1) -> t1:Type -> t2:Type
               -> { y:Vname | not (in_env y g) && not (Set_mem y (free t1)) 
                                               && not (Set_mem y (free t2)) }
               -> ProofOf(Subtype (Cons y s2 g) (unbindT x1 y t1) (unbindT x2 y t2))
               -> ProofOf(Subtype g (TFunc x1 s1 t1) (TFunc x2 s2 t2))
 |  SWitn :: g:Env -> e:Value  -> t_x:Type -> ProofOf(HasType g e t_x) 
               -> t:Type -> x:Vname -> t':Type -> ProofOf(Subtype g t (tsubBV x e t'))
               -> ProofOf(Subtype g t (TExists x t_x t'))
 |  SBind :: g:Env -> x:Vname -> t_x:Type -> t:Type -> {t':Type | not Set_mem x (free t')} 
               -> { y:Vname | not (in_env y g) && not (Set_mem y (free t))
                                               && not (Set_mem y (free t')) }
               -> ProofOf(Subtype (Cons y t_x g) (unbindT x y t) t')
               -> ProofOf(Subtype g (TExists x t_x t) t')
@-} -- TODO remove the req that x \not\in free(t')

{-@ lem_denote_sound_sub :: g:Env -> t1:Type -> t2:Type -> ProofOf(Subtype g t1 t2)
                -> ProofOf(WFEnv g) -> ProofOf(WFType g t1) -> ProofOf(WFType g t2) 
                -> th:CSubst -> ProofOf(DenotesEnv g th) -> v:Value 
                -> ProofOf(Denotes (ctsubst th t1) v) 
                -> ProofOf(Denotes (ctsubst th t2) v) @-}
lem_denote_sound_sub :: Env -> Type -> Type -> Subtype -> WFEnv -> WFType -> WFType
                            -> CSubst -> DenotesEnv -> Expr -> Denotes -> Denotes 
lem_denote_sound_sub g t1 t2 (SBase _g x1 b p1 x2 p2 y pf_ent_p2) p_g_wf p_g_t1 p_g_t2
--lem_denote_sound_sub g t1@(TRefn _ _ _) t2@(TRefn _ _ _) (SBase _g x1 b p1 x2 p2 y pf_ent_p2)
                    -- t1 = b{x1:p1}, t2 = b{x2:p2}  -- Pf(Entails g' p2[y/x2])
                       th den_g_th val den_t1_v@(DRefn _b _ _ also_val pf_v_b pf_th_p1v_tt)
    = case (pf_ent_p2) of                                        -- EvalsTo th(p1[v/x1]) tt
        (EntPred y_g _p2 ev_thp2_tt) 
                       -- forall th' in [[x1,g]]. EvalsTo th'(p2[x1/x2]) tt 
            -> DRefn b x2 (csubst th p2) also_val pf_v_b' pf_th'_p2v_tt
                     `withProof` lem_ctsubst_refn th b x2 p2
                where
                  pf_v_b'       = pf_v_b `withProof`  lem_ctsubst_refn th b x1 p1 
                  th'           = CCons y val th -- y is fresh repl. x1
                                 -- th' = (y |-> v, th) \in [[ Cons y t1 g ]]
                  den_g'_th'    = DExt g th den_g_th y t1 val den_t1_v
                  pf_th'_p2v_tt = ev_thp2_tt th' den_g'_th' 
                                    `withProof` lem_csubst_and_unbind x2 y val b pf_v_b' th p2
lem_denote_sound_sub g t1 t2  -----------------------------------
--lem_denote_sound_sub g t1@(TFunc _ _ _) t2@(TFunc _ _ _)  -----------------------------------
             p_t1_t2@(SFunc _g x1 s1 x2 s2 p_g_s2_s1 t1' t2' y p_g'_t1_t2) p_g_wf p_g_t1 p_g_t2
                                                -- Subtype (Cons y s2 g) t1'[y/x1] t2'[y/x2]
             th den_g_th _v den_tht1_v@(DFunc _x1 ths1 tht1' val pf_v_er_t1 _pf_den_tht1'_vv')
   =   DFunc x2 (ctsubst th s2) (ctsubst th t2') val pf_v_er_t2 (pf_den_tht2'_vv')
            `withProof` lem_ctsubst_func th x1 s1 t1'
            `withProof` lem_ctsubst_func th x2 s2 t2'
        where
          (WFFunc _ _ _s1 p_g_s1 _t1' z p_zg_t1') = p_g_t1
          (WFFunc _ _ _s2 p_g_s2 _t2' w p_wg_t2') = p_g_t2 
          _p_yg_t1'    = lem_change_var_wf g z s1 Empty (unbindT x1 z t1') p_zg_t1' y
                                    `withProof` lem_unbindT_and_tsubFV x1 z y t1'
          {-@ p_yg_t1' :: ProofOf(WFType (Cons y s2 g) (unbindT x1 y t1')) @-}
          p_yg_t1'     = lem_subtype_in_env_wf g Empty y s2 s1 p_g_s2_s1 (unbindT x1 y t1') _p_yg_t1'
          {-@ p_yg_t2' :: ProofOf(WFType (Cons y s2 g) (unbindT x2 y t2')) @-}
          p_yg_t2'     = lem_change_var_wf g w s2 Empty (unbindT x2 w t2') p_wg_t2' y
                                    `withProof` lem_unbindT_and_tsubFV x2 w y t2'
          pf_v_er_t2   = pf_v_er_t1 `withProof` lem_erase_th_sub g t1 t2 p_t1_t2 th
                                    `withProof` lem_ctsubst_func th x1 s1 t1'
                                    `withProof` lem_ctsubst_func th x2 s2 t2'
          g'           = Cons y s2 g
          ths2_ths1    = lem_denote_sound_sub g s2 s1 p_g_s2_s1 p_g_wf p_g_s2 p_g_s1 th den_g_th 
          tht1'_tht2'  = lem_denote_sound_sub g' (unbindT x1 y t1') (unbindT x2 y t2')
                                              p_g'_t1_t2 (WFEBind g p_g_wf y s2 p_g_s2)
                                              p_yg_t1' p_yg_t2'
          {-@ pf_den_tht2'_vv' :: v':Value -> ProofOf(Denotes (ctsubst th s2) v') 
                 -> ProofOf(ValueDenoted (App val v') (tsubBV x2 v' (ctsubst th t2'))) @-}
          pf_den_tht2'_vv' v' den_ths2_v' = ValDen (App val v') (tsubBV x2 v' (ctsubst th t2'))
                                                    v''  evalpf   den_t2'v'_v'' 
              where
                pf_v'_er_s2    = get_btyp_from_den (ctsubst th s2)  v' den_ths2_v' 
                                         `withProof` lem_erase_th_sub g s2 s1 p_g_s2_s1 th 
                th'            = CCons y v' th -- (y |-> v', th) in [[y:s2,g]]
                den_g'_th'     = DExt g th den_g_th y s2 v' den_ths2_v' 
                (ValDen _ _ v'' evalpf denpf) = get_obj_from_dfunc x1 (ctsubst th s1) (ctsubst th t1') 
                         val den_tht1_v v' 
                         (ths2_ths1 v' (den_ths2_v' `withProof` lem_ctsubst_func th x2 s2 t2')
                                                    `withProof` lem_ctsubst_func th x1 s1 t1')
                pf_vv'_er_t1'  = BTApp BEmpty val (erase (ctsubst th s1)) 
                                       (erase (ctsubst th t1')) pf_v_er_t1
                                       v' (get_btyp_from_den (ctsubst th s2) v' den_ths2_v')
                pf_v''_er_t1'  = lemma_soundness (App val v') v'' evalpf
                                                 (erase t1') pf_vv'_er_t1'
                {-@ den_t2'v'_v'' :: ProofOf(Denotes (tsubBV x2 v' (ctsubst th t2')) v'') @-}
                den_t2'v'_v''  = tht1'_tht2' th' den_g'_th' v'' 
                                      (denpf `withProof` lem_ctsubst_and_unbindT 
                                                            x1 y v' (erase (ctsubst th s1)) 
                                                            pf_v'_er_s2 th t1')
                                      `withProof` lem_ctsubst_func th x2 s2 t2'
                                      `withProof` lem_ctsubst_func th x1 s1 t1'
                                      `withProof` lem_ctsubst_and_unbindT x2 y v' 
                                          (erase (ctsubst th s2)) 
                                          (get_btyp_from_den (ctsubst th s2) v' den_ths2_v') 
                                          th t2'
lem_denote_sound_sub g t1 t2 -- @(TExists x t_x t')  -----------------------------------
             p_t1_t2@(SWitn _g v_x t_x p_vx_tx _t1 x t2' p_t1_t2'vx) 
             p_g_wf p_g_t1 p_g_t2 th den_g_th v den_tht1_v
    = DExis x (ctsubst th t_x) (ctsubst th t2') v p_v_er_t2' thvx -- v'  
            den_thtx_thvx (den_tht2'vx_v `withProof` lem_value_refl also_thvx thvx pf1)
        where -- By the inductive hypothesis and mutual induction:
          (WFExis _ _ _tx _ _ y _p_yg_t2') = p_g_t2 ? toProof ( t2 === TExists x t_x t2' )
          {-@ p_yg_t2' :: ProofOf(WFType (concatE (Cons y t_x g) Empty) (unbindT x y t2')) @-}
          p_yg_t2' = _p_yg_t2' --`withProof` lem_unbindT_and_tsubFV x w y t2'
          {-@ p_g_t2'vx :: ProofOf(WFType g (tsubBV x v_x t2')) @-}
          p_g_t2'vx = lem_subst_wf g Empty y v_x t_x p_vx_tx (unbindT x y t2') p_yg_t2'
                              `withProof` lem_tsubFV_unbindT x y v_x t2' 
          den_tht2'vx_v = lem_denote_sound_sub g t1 (tsubBV x v_x t2') p_t1_t2'vx p_g_wf 
                              p_g_t1 p_g_t2'vx th den_g_th v den_tht1_v -- v \in [[ t2'[v_x/x] ]]
                              `withProof` lem_ctsubst_exis th x t_x t2'    
                              `withProof` lem_commute_ctsubst_tsubBV th x v_x t2'
          also_thvx     = csubst th v_x `withProof` lem_csubst_value th v_x  -- new
          {- @ (thvx, pfs)_ :: (v'::{ v:Expr | isValue v && Set_emp (freeBV v) }, 
                     ({ pf1:EvalsTo | propOf pf1 == EvalsTo (csubst th v_x) v'}, 
                      { pf2:Denotes | propOf pf2 == Denotes (ctsubst th t_x) v'})) @-}
          {-@ thvx :: { v:Expr | isValue v && Set_emp (freeBV v) } @-} 
          {- @ pfs :: ({ pf1:EvalsTo | propOf pf1 == EvalsTo (csubst th v_x) thvx}, 
                      { pf2:Denotes | propOf pf2 == Denotes (ctsubst th t_x) thvx}) @-}
          (ValDen _ _ thvx pf1 pf2)      = lem_denote_sound_typ g v_x t_x p_vx_tx p_g_wf th den_g_th
          {-@ den_thtx_thvx :: ProofOf(Denotes (ctsubst th t_x) thvx) @-}
          den_thtx_thvx = pf2  -- th(v_x) in [[th(t_x)]]. Let v' = th(v_x)...
                          `withProof` lem_commute_ctsubst_tsubBV th x v_x t2'
          -- these are ingredients to show that v \in [[th(TExists x t_x t2')]]
          p_v_er_t2'    = get_btyp_from_den (ctsubst th (tsubBV x v_x t2')) v den_tht2'vx_v
                              `withProof` lem_erase_ctsubst th t2'
                              `withProof` lem_erase_tsubBV x v_x t2'
                              `withProof` lem_erase_ctsubst th (tsubBV x v_x t2')
--          v'            = csubst th v_x `withProof` lem_csubst_value th v_x
--                              `withProof` lem_value_refl (csubst th v_x) thvx (fst pfs)
lem_denote_sound_sub g t1 t2 -- @(TExists x t_x t') t2 --------------------------------------
             p_t1_t2@(SBind _g x t_x t' _t2 y p_t'yx_t2) p_g_wf p_g_t1 p_g_t2 th den_g_th v 
             den_tht1_v -- @(DExis _ thtx tht' _v pf_v_er_t' v_x den_thtx_vx den_tht'vx_v)
    = case (t1, den_tht1_v) of 
        (TExists _ _ _, DExis _ thtx tht' _v pf_v_er_t' v_x den_thtx_vx den_tht'vx_v) 
          -> den_tht2_v
            where -- by the inductive hypothesis we have
              (WFExis _ _ _tx p_g_tx _ w p_wg_t') = p_g_t1
              g'         = Cons y t_x g
              p_g'_wf    = WFEBind g p_g_wf y t_x p_g_tx
              p_g'_t'    = lem_change_var_wf g w t_x Empty (unbindT x w t') p_wg_t' y
                              `withProof` lem_unbindT_and_tsubFV x w y t' 
              p_g'_t2    = lem_weaken_wf g Empty t2 p_g_t2 y t_x p_g_tx
              th'        = CCons y v_x th
              den_g'_th' = DExt g th den_g_th y t_x v_x den_thtx_vx
              pf_vx_ertx = get_btyp_from_den thtx v_x den_thtx_vx
              den_tht'_v = den_tht'vx_v `withProof` lem_ctsubst_exis th x t_x t'
                               `withProof` lem_ctsubst_and_unbindT x y v_x (erase thtx) 
                                                                   pf_vx_ertx th t'
              den_tht2_v = lem_denote_sound_sub g' (unbindT x y t') t2 p_t'yx_t2 
                               p_g'_wf p_g'_t' p_g'_t2 th' den_g'_th' v den_tht'_v
                               `withProof` lem_ctsubst_head_not_free y v_x th t2
        --(TExists _ _ _, _) -> impossible "certainly"
        (_, _) -> impossible ("clearly" ? lem_ctsubst_exis th x t_x t')

{-@ data WFType where
    WFRefn :: g:Env -> x:Vname -> b:Base -> p:Pred 
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) }
        -> ProofOf(HasBType (BCons y (BTBase b) (erase_env g)) (unbind x y p) (BTBase TBool)) 
        -> ProofOf(WFType g (TRefn b x p))
 |  WFFunc :: g:Env -> x:Vname -> t_x:Type 
        -> ProofOf(WFType g t_x) -> t:Type 
        -> { y:Vname | not (in_env y g) && not (Set_mem y (free t)) }
        -> ProofOf(WFType (Cons y t_x g) (unbindT x y t)) -> ProofOf(WFType g (TFunc x t_x t))
 |  WFExis :: g:Env -> x:Vname -> t_x:Type 
        -> ProofOf(WFType g t_x) -> t:Type 
        -> { y:Vname | not (in_env y g) && not (Set_mem y (free t)) }
        -> ProofOf(WFType (Cons y t_x g) (unbindT x y t)) -> ProofOf(WFType g (TExists x t_x t)) @-} 

{-@ data WFEnv where
    WFEEmpty :: ProofOf(WFEnv Empty)
 |  WFEBind  :: g:Env -> ProofOf(WFEnv g) -> { x:Vname | not (in_env x g) } -> t:Type 
                      -> ProofOf(WFType g t) -> ProofOf(WFEnv (Cons x t g)) @-}

{-@ data Entails where
    EntPred :: g:Env -> p:Pred 
               -> (th:CSubst -> ProofOf(DenotesEnv g th) 
                             -> ProofOf(EvalsTo (csubst th p) (Bc True)) )
               -> ProofOf(Entails g p) @-} 

{-@ data ValueDenoted where 
    ValDen :: e:Expr -> t:Type -> v:Value -> ProofOf(EvalsTo e v)
                                  -> ProofOf(Denotes t v) -> ProofOf(ValueDenoted e t) @-}
{-@ data Denotes where
    DRefn :: b:Base -> x:Vname -> p:Pred -> v:Value  
              -> ProofOf(HasBType BEmpty v (BTBase b))
              -> ProofOf(EvalsTo (subBV x v p) (Bc True)) 
              -> ProofOf(Denotes (TRefn b x p) v)
  | DFunc :: x:Vname -> t_x:Type -> t:Type -> v:Value  
              -> ProofOf(HasBType BEmpty v (erase (TFunc x t_x t)))
              -> ( v_x:Value -> ProofOf(Denotes t_x v_x)
                             -> ProofOf(ValueDenoted (App v v_x) (tsubBV x v_x t)) ) 
              -> ProofOf(Denotes (TFunc x t_x t) v)
  | DExis :: x:Vname -> t_x:Type -> t:Type -> v:Value 
              -> ProofOf(HasBType BEmpty v (erase t)) 
              -> v_x:Value -> ProofOf(Denotes t_x v_x)
              -> ProofOf(Denotes (tsubBV x v_x t) v)
              -> ProofOf(Denotes (TExists x t_x t) v)  @-} -- @-}

{- @ data DenotesEnv where 
    DEmp :: ProofOf(DenotesEnv Empty CEmpty)
 |  DExt :: g:Env -> th:CSubst -> ProofOf(DenotesEnv g th) 
               -> { x:Vname | not (in_env x g) } -> t:Type 
               -> v:Value -> ProofOf(Denotes (ctsubst th t) v)
               -> ProofOf(DenotesEnv (Cons x t g) (CCons x v th)) @-}



{- @ lem_substitution_sub :: @-}

