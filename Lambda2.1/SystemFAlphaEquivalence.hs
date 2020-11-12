{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SystemFAlphaEquivalence where

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
import SystemFLemmasSubstitution
import Typing

{-@ reflect foo26a @-}   
foo26a x = Just x 
foo26a :: a -> Maybe a 

-- | Alpha equivalence in System F. Normalization is basically de Bruijn indices

data AlphaEqvP where
    AlphaEqv :: FType -> FType -> AlphaEqvP

data AlphaEqv where
    AEBasic :: Basic -> AlphaEqv
    AEFunc  :: FType -> FType -> AlphaEqv -> FType -> FType -> AlphaEqv -> AlphaEqv
    AEPoly  :: Vname -> Kind -> FType -> Vname -> FType -> Vname -> AlphaEqv -> AlphaEqv

{-@ data AlphaEqv where
        AEBasic :: b:Basic -> ProofOf(AlphaEqv (FTBasic b) (FTBasic b))
     |  AEFunc  :: s1:FType -> s2:FType -> ProofOf(AlphaEqv s1 s2) 
                     -> t1:FType -> t2:FType -> ProofOf(AlphaEqv t1 t2)
                     -> ProofOf(AlphaEqv (FTFunc s1 t1) (FTFunc s2 t2))
     |  AEPoly  :: a1:Vname -> k:Kind -> t1:FType -> a2:Vname -> t2:FType 
                     -> a:Vname -> ProofOf(AlphaEqv (unbindFT a1 a t1) (unbindFT a2 a t2))
                     -> ProofOf(AlphaEqv (FTPoly a1 k t1) (FTPoly a2 k t2)) @-} -- @-}
                       
-- Lemma. Given a System F Typing judgment in the empty environment, FEmpty |- e : t1,
--   we can produce an F-Typing judgment for any alpha-equiv type t2 such that t1 =a= t2,
--   FEmpty |- e : t2. i
--   This is more complciated to prove for non-empty environments because
--   we'd have to argue about the alpha-equivalence of types in the environment.
{-@ lem_alpha_eqv_ftyp :: g:FEnv -> e:Expr -> t1:FType -> ProofOf(HasFType g e t1)
        ->  t2:FType -> ProofOf(AlphaEqv t1 t2) -> ProofOf(HasFType g e t2) @-}
lem_alpha_eqv_ftyp :: FEnv -> Expr -> FType -> HasFType -> FType -> AlphaEqv -> HasFType
lem_alpha_eqv_ftyp g e t1 (FTBC _g b) t2 alpha_t1_t2  = case alpha_t1_t2 of
  (AEBasic _tbool) -> FTBC g b
lem_alpha_eqv_ftyp g e t1 (FTIC _g n) t2 alpha_t1_t2  = case alpha_t1_t2 of
  (AEBasic _tint)  -> FTIC g n
lem_alpha_eqv_ftyp g e t1 (FTVar1 _g x t) t2 alpha_t1_t2
  = undefined
lem_alpha_eqv_ftyp g e t1 (FTVar2 _g x t p_x_t y t') t2 alpha_t1_t2
  = undefined
lem_alpha_eqv_ftyp g e t1 (FTVar3 _g x t p_x_t a k)  t2 alpha_t1_t2
  = undefined
lem_alpha_eqv_ftyp g e t1 (FTPrm _g c) t2 alpha_t1_t2 = undefined {-case c of 
  (Eql a1) -> case alpha_t1_t2 of
    (AEPoly a1 k ty'1 a2 ty'2 a alpha_ty'1_ty'2) -> FTPrm FEmpty (Eql a2)
  _        -> case alpha_t1_t2 of
    (FTFunc {})                                  -> FTPrm FEtmpy c-}
lem_alpha_eqv_ftyp g e t1 (FTAbs _g x s1 k_s p_emp_s1 e' t1' y p_e'_t1') t2 alpha_t1_t2 
  = undefined {-case alpha_t1_t2 of
      (AEFunc _s1 s2 alpha_s1_s2 _t1' t2' alpha_t1'_t2') 
         -> FTAbs FEmpty x s2 k_s ???? e' t2' 
              where
                ????     =
                p_e'_t2' = lem_alpha_eqv_ftyp  -}
lem_alpha_eqv_ftyp g e t1 (FTApp _g e1 s s' p_e1_ss' e2 p_e2_s) t2 alpha_t1_t2 
  = undefined
lem_alpha_eqv_ftyp g e t1 (FTAbsT _g a k e' t1' a' p_e'_t1') t2 alpha_t1_t2 
  = undefined
lem_alpha_eqv_ftyp g e t1 (FTAppT _g e' a k t1' p_e_at1' rt p_g_er_rt) t2 alpha_t1_t2
  = undefined
lem_alpha_eqv_ftyp g e t1 (FTLet _g e_x t_x p_ex_tx x e' t1' y p_e'_t1') t2 alpha_t1_t2
  = undefined
lem_alpha_eqv_ftyp g e t1 (FTAnn _g e' _t1 rt p_e'_t1) t2 alpha_t1_t2
  = undefined
lem_alpha_eqv_ftyp g e t1 (FTEqv _g _e a0 k t0' p_e_a0t0' a1 t1' a) t2 alpha_t1_t2 
  = undefined {-
  = case alpha_t1_t2 of
      (AEPoly _a1 _k _t1' a2 t2' a' alpha_t1'_t2') -}

-- | Substitution Properties

-- with bound type vars, these are only equiv up to alhpa-renaming bound variables
{-@ lem_erase_subtype :: g:Env -> t1:Type -> t2:Type -> ProofOf(Subtype g t1 t2)
               -> ProofOf(AlphaEqv (erase t1) (erase t2)) @-}
lem_erase_subtype :: Env -> Type -> Type -> Subtype -> AlphaEqv
lem_erase_subtype g t1 t2 (SBase _g x1 b p1 x2 p2 y _) = AEBasic b
lem_erase_subtype g t1 t2 (SFunc _g x1 s1 x2 s2 p_s2_s1 t1' t2' y p_t1'_t2')
    = undefined {-
    = () ? lem_erase_subtype g s2 s1 p_s2_s1
         ? lem_erase_tsubBV x1 (FV y) t1' ? lem_erase_tsubBV x2 (FV y) t2'
         ? lem_erase_subtype (Cons y s2 g) (unbindT x1 y t1') (unbindT x2 y t2') p_t1'_t2'  -}
lem_erase_subtype g t1 t2 (SWitn _g v t_x p_v_tx _t1 x t' p_t1_t'v)
    = undefined {-
    = () ? lem_erase_subtype g t1 (tsubBV x v t') p_t1_t'v
         ? lem_erase_tsubBV x v t'  {- toProof ( erase t1 ? lem_erase_subtype g t1 (tsubBV x v t') p_t1_t'v
            === erase (tsubBV x v t') ? lem_erase_tsubBV x v t'
            === erase t' === erase (TExists x t_x t') ) -} -}
lem_erase_subtype g t1 t2 (SBind _g x t_x t _t2 y p_t_t')
    = undefined {-
    = () ? lem_erase_subtype (Cons y t_x g) (unbindT x y t) t2 p_t_t'
         ? lem_erase_tsubBV x (FV y) t -}
lem_erase_subtype g t1 t2 (SPoly _g a1 k t1' a2 t2' a p_ag_t1'_t2') = undefined
{-    = toProof ( normalize (erase (TPoly a1 k t1))
            === normalize (FTPoly a1 k (erase t1))
            === let a' = maxbinder (FTPoly a1 k (normalize t1)) in
                  FTPoly a' k (ftsubBV a1 (FTBasic (BTV a')) (normalize t1))
            === let a' = maxbinder (FTPoly a2 k (normalize t2)) in 
                  FTPoly a' k (ftsubBV a1 (FTBasic (BTV a')) (normalize t1)) -}
{-    = () ? lem_erase_subtype (ConsT a k g) (unbind_tvT a1 a t1') (unbind_tvT a2 a t2') p_ag_t1'_t2'
         ? lem_erase_tsubBTV a1 (TRefn (BTV (maxBinder (FTPoly a1 k (normalize (erase t1))))) 1 (Bc True))
                                (normalize (erase t1))  
         ? lem_erase_tsubBTV a2 (TRefn (BTV (maxBinder (FTPoly a2 k (normalize (erase t2))))) 1 (Bc True))
                                (normalize (erase t2))  -}

{-@ lem_erase_ctsubst :: th:CSub -> t:Type 
               -> { pf:_ | erase (ctsubst th t) == erase t } @-} -- not quite true
lem_erase_ctsubst :: CSub -> Type -> Proof
lem_erase_ctsubst (CEmpty)       t = ()
lem_erase_ctsubst (CCons y v th) t = () {-toProof ( erase (ctsubst (CCons y v th) t)
                                           === erase (ctsubst th (tsubFV y v t))-}
                                             ? lem_erase_ctsubst th (tsubFV y v t)
{-                                           === erase (tsubFV y v t)-}
                                             ? lem_erase_tsubFV y v t
{-                                           === erase t )-}
lem_erase_ctsubst (CConsT a t_a th) t
    = undefined

{-@ lem_erase_th_sub :: g:Env -> t1:Type -> t2:Type -> ProofOf(Subtype g t1 t2) -> th:CSub 
        -> ProofOf(AlphaEqv (erase (ctsubst th t1)) (erase (ctsubst th t2))) @-}
lem_erase_th_sub :: Env -> Type -> Type -> Subtype -> CSub -> AlphaEqv
lem_erase_th_sub g t1 t2 p_t1_t2 th = undefined {-
toProof ( normalize (erase (ctsubst th t1))
                                              ? lem_erase_ctsubst th t1
                                            === normalize (erase t1) ? lem_erase_subtype g t1 t2 p_t1_t2
                                            === normalize (erase t2) ? lem_erase_ctsubst th t2
                                            === normalize (erase (ctsubst th t2)) ) -}
