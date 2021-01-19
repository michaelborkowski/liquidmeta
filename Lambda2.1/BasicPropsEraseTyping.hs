{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module BasicPropsEraseTyping where

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
import SystemFLemmasWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasFTyping2
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst

{-@ reflect foo29 @-}
foo29 x = Just x 
foo29 :: a -> Maybe a 

{-@ lem_unbind_tvT_equals :: a:Vname -> a':Vname -> { t1:FType | not (Set_mem a' (ffreeTV t1)) }
        -> { t2:FType | unbindFT a a' t1 == unbindFT a a' t2 && not (Set_mem a' (ffreeTV t2)) } 
        -> { pf:_ | t1 == t2 } @-}
lem_unbind_tvT_equals :: Vname -> Vname -> FType -> FType -> Proof
lem_unbind_tvT_equals a a' (FTBasic b) (FTBasic _) = case b of
  (BTV a) -> ()
  _       -> ()
lem_unbind_tvT_equals a a' (FTFunc t11 t12) (FTFunc t21 t22) 
  = () ? lem_unbind_tvT_equals a a' t11 t21
       ? lem_unbind_tvT_equals a a' t12 t22
lem_unbind_tvT_equals a a' (FTPoly a1 k t1') (FTPoly _ _ t2')
  = () ? lem_unbind_tvT_equals a a' t1' t2'

-- LEMMA 6. If G |- s <: t, then if we erase the types then (erase s) and (erase t)
--               equiv up to alpha-renaming bound variables
{-@ lem_erase_subtype :: g:Env -> t1:Type -> t2:Type -> ProofOf(Subtype g t1 t2)
               -> { pf:_ | erase t1 == erase t2 } @-}
lem_erase_subtype :: Env -> Type -> Type -> Subtype -> Proof
lem_erase_subtype g t1 t2 (SBase _g x1 b p1 x2 p2 y _) = ()
lem_erase_subtype g t1 t2 (SFunc _g x1 s1 x2 s2 p_s2_s1 t1' t2' y p_t1'_t2')
  = () ? lem_erase_subtype  g s2 s1 p_s2_s1
       ? lem_erase_tsubBV x1 (FV y) t1'
       ? lem_erase_tsubBV x2 (FV y) t2'
       ? lem_erase_subtype (Cons y s2 g) (unbindT x1 y t1') (unbindT x2 y t2') p_t1'_t2'
lem_erase_subtype g t1 t2 (SWitn _g v t_x p_v_tx _t1 x t' p_t1_t'v)
  = () ? lem_erase_subtype g t1 (tsubBV x v t') p_t1_t'v
       ? lem_erase_tsubBV x v t'
{- toProof ( erase t1 ? lem_erase_subtype g t1 (tsubBV x v t') p_t1_t'v
            === erase (tsubBV x v t') ? lem_erase_tsubBV x v t'
            === erase t' === erase (TExists x t_x t') ) -}
lem_erase_subtype g t1 t2 (SBind _g x t_x t _t2 y p_t_t')
  = () ? lem_erase_subtype (Cons y t_x g) (unbindT x y t) t2 p_t_t'
       ? lem_erase_tsubBV x (FV y) t
lem_erase_subtype g t1 t2 (SPoly _g a1 k t1' a2 t2' a p_ag_t1'_t2') 
  = () ? lem_erase_subtype (ConsT a k g) (unbind_tvT a1 a t1') (unbind_tvT a2 a t2')
                           p_ag_t1'_t2' 
       ? lem_erase_unbind_tvT a1 a t1'
       ? lem_erase_unbind_tvT a2 a t2'
       ? lem_unbind_tvT_equals a1 a (erase t1' ? lem_erase_freeTV t1') 
                                    (erase t2' ? lem_erase_freeTV t2')

{-@ lem_erase_ctsubst :: th:CSub -> t1:Type 
        -> { t2:Type | erase t1 == erase t2 }
        -> { pf:_ | erase (ctsubst th t1) == erase (ctsubst th t2) } @-}
lem_erase_ctsubst :: CSub -> Type -> Type -> Proof
lem_erase_ctsubst CEmpty             t1 t2 = () 
lem_erase_ctsubst (CCons  x v_x th') t1 t2 
    = () ? lem_erase_ctsubst  th' (tsubFV x v_x t1 ? lem_erase_tsubFV x v_x t1) 
                                  (tsubFV x v_x t2 ? lem_erase_tsubFV x v_x t2) 
         ? lem_unroll_ctsubst_left th' x v_x t1
         ? lem_erase_tsubFV x v_x (ctsubst th' t1)
         ? lem_unroll_ctsubst_left th' x v_x t2
         ? lem_erase_tsubFV x v_x (ctsubst th' t2)
lem_erase_ctsubst (CConsT a t_a th') t1 t2 
    = () ? lem_erase_ctsubst  th' (tsubFTV a t_a t1 ? lem_erase_tsubFTV a t_a t1)
                                  (tsubFTV a t_a t2 ? lem_erase_tsubFTV a t_a t2)
         ? lem_unroll_ctsubst_tv_left th' a t_a t1
         ? lem_erase_tsubFTV a t_a (ctsubst th' t1)
         ? lem_unroll_ctsubst_tv_left th' a t_a t2
         ? lem_erase_tsubFTV a t_a (ctsubst th' t2)

{-
data TailEnvP where
    TailEnv :: Env -> CSub -> TailEnvP

data TailEnv where
    Tail  :: Vname -> Type -> Expr -> Denotes -> Env -> CSub -> DenotesEnv -> TailEnv
    TailT :: Vname -> Kind -> Type -> WFType  -> Env -> CSub -> DenotesEnv -> TailEnv
{-@ data TailEnv where
        Tail  :: x:Vname -> t:Type -> { v:Value | Set_emp (fv v) && Set_emp (ftv v) &&
                                                  Set_emp (freeBV v) && Set_emp (freeBTV v) }
                   -> ProofOf(Denotes t v) -> { g:Env | not (in_env x g) } 
                   -> { th:CSub | binds g == bindsC th }
                   -> ProofOf(DenotesEnv (concatE (Cons x t Empty) g) (concatCS (CCons x v CEmpty) th))
                   -> ProofOf(TailEnv (concatE (Cons x t Empty) g) (concatCS (CCons x v CEmpty) th)) 
        TailT :: a:Vname -> k:Kind -> { t:UserType | Set_emp (free t) && Set_emp (freeTV t) &&
                                                     Set_emp (tfreeBV t) && Set_emp (tfreeBTV t) } 
                   -> ProofOf(WFType Empty t k) -> { g:Env | not (in_env a g) } 
                   -> { th:CSub | binds g == bindsC th }
                   -> ProofOf(DenotesEnv (concatE (ConsT a k Empty) g) (concatCS (CConsT a t CEmpty) th))
                   -> ProofOf(TailEnv (concatE (ConsT a k Empty) g) (concatCS (CConsT a t CEmpty) th)) @-}
{-
{-@ tailEnv :: { g:Env | not (g == Empty) } 
        -> (Env,Env)<{\g' g'' -> (envsize g' == 1) && (g == concatE g' g'')}> @-}
tailEnv :: Env -> (Env, Env)
tailEnv (Cons x t g') = case g' of
  Empty -> (Cons x t Empty, Empty)
  _     -> (g0, Cons x t (g'' ? toProof( binds g' === S.union (binds g0) (binds g''))))
    where
      (g0, g'') = tailEnv g'
tailEnv (ConsT a k g') = case g' of
  Empty -> (ConsT a k Empty, Empty)
  _     -> (g0, ConsT a k g'' ? toProof(  g' ===  (concatE g0 g'') ))
    where
      (g0, g'') = tailEnv g'
-}

{-@ lem_get_tail_denotesenv :: { g:Env | not (g == Empty) } -> th:CSub -> ProofOf(DenotesEnv g th)
            -> ProofOf(TailEnv g th) @-}
lem_get_tail_denotesenv :: Env -> CSub -> DenotesEnv -> TailEnv
lem_get_tail_denotesenv g th den_g_th@(DExt g' th' den_g'_th' y t_y v_y den_th'ty_vy) = case g' of
    Empty -> Tail y t_y v_y den_th'ty_vy Empty CEmpty den_g_th
                  ? lem_binds_env_th Empty th' den_g'_th'
    _     -> case (lem_get_tail_denotesenv g' th' den_g'_th') of
      (Tail  x t v den_t_v g'' th'' _) 
          -> Tail  x t v den_t_v (Cons y t_y g'') (CCons y v_y th'') den_g_th
--                   ? lem_binds_env_th g' th' den_g'_th'
      (TailT a k t p_emp_t g''_ th''_ _) 
          -> TailT a k t p_emp_t (Cons y t_y g'') (CCons y v_y th'') den_g_th
        where
          g''  = g''_ ? lem_in_env_concat (ConsT a k Empty) g'' y
                      ? lem_binds_env_th g' th' den_g'_th'
          th'' = th''_ ? lem_binds_consT_concatCS CEmpty th''_ a t
                       ? lem_binds_env_th g' th' den_g'_th'
  --                 ? lem_binds_env_th g' th' den_g'_th'
lem_get_tail_denotesenv g th den_g_th@(DExtT g' th' den_g'_th' a' k' t' p_emp_t') = case g' of
    Empty -> TailT a' k' t' p_emp_t' Empty CEmpty den_g_th
                   ? lem_binds_env_th Empty th' den_g'_th'
    _     -> case (lem_get_tail_denotesenv g' th' den_g'_th') of
      (Tail  x t v den_t_v g'' th'' _) 
          -> Tail  x t v den_t_v (ConsT a' k' g'') (CConsT a' t' th'') den_g_th
                   ? lem_binds_env_th g' th' den_g'_th'
      (TailT a k t p_emp_t g'' th'' _) 
          -> TailT a k t p_emp_t (ConsT a' k' g'') (CConsT a' t' th'') den_g_th
                   ? lem_binds_env_th g' th' den_g'_th'
-}        


{-@ lem_csubst_hasftype_basic :: g:Env -> e:Expr -> { b:Basic | b == TBool || b == TInt }
        -> ProofOf(HasFType (erase_env g) e (FTBasic b)) -> th:CSub -> ProofOf(DenotesEnv g th)
        -> ProofOf(HasFType FEmpty (csubst th e) (FTBasic b)) @-}
lem_csubst_hasftype_basic :: Env -> Expr -> Basic -> HasFType -> CSub -> DenotesEnv -> HasFType
lem_csubst_hasftype_basic g e b p_e_b th den_g_th 
    = lem_csubst_hasftype' g e (TRefn b Z (Bc True)) p_e_b th den_g_th
                           ? lem_ctsubst_erase_basic th (TRefn b Z (Bc True)) b

{-@ lem_csubst_fv_in ::  y:Vname -> { v:Value | Set_emp (fv v) && Set_emp (ftv v) &&
                                         Set_emp (freeBV v) && Set_emp (freeBTV v) }
                                 -> { th:CSub | not (in_csubst y th ) }
                                 -> { pf:_ | csubst (CCons y v th) (FV y) == v } @-}
lem_csubst_fv_in :: Vname -> Expr -> CSub -> Proof
lem_csubst_fv_in y v th = () ? lem_csubst_nofv th v


{-@ lem_csubst_hasftype' :: g:Env -> e:Expr -> t:Type -> ProofOf(HasFType (erase_env g) e (erase t))
        -> th:CSub -> ProofOf(DenotesEnv g th)
        -> ProofOf(HasFType FEmpty (csubst th e) (erase (ctsubst th t))) @-}
lem_csubst_hasftype' :: Env -> Expr -> Type -> HasFType {-> WFFE-} -> CSub -> DenotesEnv -> HasFType
lem_csubst_hasftype' g e t p_e_t th den_g_th = undefined

{-
        -- -> ProofOf(WFFE (erase_env g)) -> th:CSub -> ProofOf(DenotesEnv g th)
{-@ lem_csubst_hasftype' :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> e:Expr -> t:Type -> ProofOf(HasFType (erase_env (concatE g g')) e (erase t))
        -> ProofOf(WFFE (erase_env g)) -> th:CSub -> ProofOf(DenotesEnv g th)
        -> ProofOf(HasFType (erase_env g') (csubst th e) (erase (ctsubst th t))) @-}
lem_csubst_hasftype' :: Env -> Env -> Expr -> Type -> HasFType -> WFFE -> CSub -> DenotesEnv -> HasFType
--lem_csubst_hasftype' g g' e t p_e_t th den_g_th = undefined
{- -}
lem_csubst_hasftype' Empty          g' e t p_e_t p_g_wf th den_g_th = case den_g_th of
  (DEmp) -> p_e_t ? lem_binds_env_th Empty th den_g_th
lem_csubst_hasftype' (Cons x t_x g) g' e t p_e_t p_g_wf xth den_xg_xth = case den_xg_xth of
  (DExt g th den_g_th _x _tx v_x den_thtx_vx)
      -> 
       
    where
      p_emp_vx_tx = get_ftyp_from_den (ctsubst th t_x)  v_x den_th'tx_vx
      p_the_tht   = lem_csubst_hasftype' g (concatE (Cons x t_x Empty) g') e t p_e_t 
                                         {-p_g'_wf-} th den_g_th
      p_xthe_xtht = lem_subst_ftyp FEmpty (erase_env g') x v_x t_x p_emp_vx_tx p_??_wf
                                   (csusbt th e) (erase (ctsubst th t)) p_the_tht

--      (WFFBind _ p_g'_wf_ _ _ _ _) = p_g_wf
--      p_g'_wf     = p_g'_wf_ ? lem_empty_concatF (erase_env g')
      p_g'_vx_tx  = lem_weaken_many_ftyp FEmpty (erase_env g') p_g'_wf v_x s_x p_emp_vx_tx
                                         ? lem_empty_concatF (erase_env g')


      p_g'_sx     = lem_ftyping_wfft (erase_env g') v_x s_x p_g'_vx_sx p_g'_wf
      p_xg'_wf    = WFFBind (erase_env g') p_g'_wf x s_x Star p_g'_sx
      (AEWitness _xg' _e _s s' aeqv_s'_s p_e_s')
                  = lem_alpha_in_env_ftyp (erase_env g') FEmpty x s_x (erase t_x) eqv_sx_tx e s p_e_s
      aeqv'_s_t   = lem_strengthen_alpha (erase_env g') x (erase t_x) FEmpty s (erase t) aeqv_s_t
      aeqv''_s_t  = lem_weaken_alpha     (erase_env g')               FEmpty s (erase t) aeqv'_s_t x s_x
      aeqv_s'_t   = lem_alpha_trans (FCons x s_x (erase_env g')) s' s (erase t) aeqv_s'_s aeqv''_s_t
                                    ? lem_erase_tsubFV x v_x t

      p_evx_s'vx  = lem_subst_ftyp (erase_env g') FEmpty x v_x s_x p_g'_vx_sx p_xg'_wf
                                   e s' p_e_s' -- (erase t) p_e_t ? lem_erase_tsubFV x v_x t


      (AEWitness _ _the _tht s'' aeqv_s''_tht p_the_s'')
--- need a lemma for ctsubst of FV x, then do induction on the structure of p_e_s
lem_csubst_hasftype'' (ConsT a k_a g') e t s aeqv_s_t p_e_s {-p_g_wf-} th den_g_th
  = undefined {- 1 -}
-}
