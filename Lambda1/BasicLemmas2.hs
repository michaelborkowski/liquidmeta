{-# LANGUAGE GADTs #-}

--{-@ LIQUID "--higherorder" @-}
{- @ LIQUID "--diff"        @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module BasicLemmas2 where

--import Control.Exception (assert)
import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Syntax
import Semantics
import Typing
import Primitives
import BasicLemmas

-- force these into scope
semantics = (Step, EvalsTo)
typing = (HasBType, HasType, Subtype, WFType, WFEnv)
denotations = (Entails, Denotes, DenotesEnv)

------------------------------------------------------------------------------
----- | METATHEORY Development
------------------------------------------------------------------------------


{-@ assume lem_sub_refl :: g:Env -> t:Type -> ProofOf(WFType g t) -> ProofOf(Subtype g t t) @-}
lem_sub_refl :: Env -> Type -> WFType -> Subtype
lem_sub_refl g t p_g_t = undefined
{-lem_sub_refl g t (WFRefn _g x b p p_p_bl) -- t = b{x:p}
    = SBase g x b p x p (EntExt (Cons x (TRefn b x p) g) (subst x (V x) p) eval_thp)
        where
    -- need eval_thp :: th:CSubst -> ProofOf(DenotesEnv (Cons x (TRefn b x p) g) th)
    --     --                            -> ProofOf(EvalsTo (csubst th p) (True))
    --                 eval_thp th pf_den_gx_th = Refl (csubst th p)
    --                                 where
    --                                                     (DRefn _ _ _ _ _ pf_pxx_tt) =
    --}                                              

{-@ assume lem_witness_sub :: g:Env -> v_x:Value -> t_x:Type -> ProofOf(HasType g v_x t_x)
        -> x:Vname -> t':Type -> { y:Vname | not (in_env y g) && not (Set_mem y (free t')) }
        -> ProofOf(WFType (Cons y t_x g) (unbindT x y t'))
        -> ProofOf(Subtype g (tsubBV x v_x t') (TExists x t_x t')) @-}
lem_witness_sub :: Env -> Expr -> Type -> HasType -> Vname -> Type 
                       -> Vname -> WFType -> Subtype
lem_witness_sub g v_x t_x p_vx_tx x t' y p_yg_t' = undefined

-- -- -- -- -- -- -- -- -- -- -- ---
-- Part of the Substitution Lemma --
-- -- -- -- -- -- -- -- -- -- -- ---

{-@ assume lem_subst_btyp :: g:BEnv -> { g':BEnv | Set_emp (Set_cap (bindsB g) (bindsB g')) }
        -> { x:Vname | (not (in_envB x g)) && not (in_envB x g') } -> v_x:Value
        -> t_x:BType -> ProofOf(HasBType g v_x t_x) -> e:Expr -> t:BType
        -> ProofOf(HasBType (concatB (BCons x t_x g) g') e t)
        -> ProofOf(HasBType (concatB g g') (subFV x v_x e) t) @-}
lem_subst_btyp :: BEnv -> BEnv -> Vname -> Expr -> BType -> HasBType 
        -> Expr -> BType -> HasBType -> HasBType
lem_subst_btyp g g' x v_x t_x p_vx_tx e t p_e_t = undefined

{-@ assume lem_subtype_in_env_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> { x:Vname | (not (in_env x g)) && not (in_env x g') }
      -> s_x:Type -> t_x:Type -> ProofOf(Subtype g s_x t_x) -> t:Type
      -> ProofOf(WFType (concatE (Cons x t_x g) g') t)
      -> ProofOf(WFType (concatE (Cons x s_x g) g') t) @-} 
lem_subtype_in_env_wf :: Env -> Env -> Vname -> Type -> Type -> Subtype -> Type -> WFType -> WFType
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t p_gtxg'_t = undefined

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
  

{-@ lem_bad :: v:Int -> { w:Int | v > 1 } @-}
lem_bad :: Int -> Int
lem_bad y = _y
  where
    y = _y
      
--lem_subst_wf g g' x v_x t_x p_vx_tx p_gxg'_t = undefined            

{- @ assume lem_binds_esubFV :: g:Env -> x:Vname -> v_x:Value 
                                 -> { pf:_ | binds g == binds (esubFV x v_x g) } @-}
-- lem_binds_esubFV :: Env -> Vname -> Expr -> Proof
-- lem_binds_esubFV g x v_x = undefined
