{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SystemFAlphaEquivalence where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import SameBinders
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

{-@ reflect foo27 @-}   
foo27 x = Just x 
foo27 :: a -> Maybe a 

{-      AEBasic :: b:Basic -> ProofOf(AlphaEqv (FTBasic b) (FTBasic b))
     |  AEFunc  :: s1:FType -> s2:FType -> ProofOf(AlphaEqv s1 s2) 
                     -> t1:FType -> t2:FType -> ProofOf(AlphaEqv t1 t2)
                     -> ProofOf(AlphaEqv (FTFunc s1 t1) (FTFunc s2 t2))
     |  AEPoly  :: a1:Vname -> k:Kind -> t1:FType -> a2:Vname -> t2:FType 
                     -> a:Vname -> ProofOf(AlphaEqv (unbindFT a1 a t1) (unbindFT a2 a t2))
                     -> ProofOf(AlphaEqv (FTPoly a1 k t1) (FTPoly a2 k t2)) -} 

data EqvFTypingP where
    EqvFTyping :: FEnv -> Expr -> FType -> EqvFTypingP

{-@ data EqvFTyping where
        AEWitness :: g:FEnv -> e:Expr -> t:FType -> s:FType -> ProofOf(AlphaEqv g s t)
                            -> ProofOf(HasFType g e s) -> ProofOf(EqvFTyping g e t) @-}
data EqvFTyping where
    AEWitness :: FEnv -> Expr -> FType -> FType -> AlphaEqv -> HasFType -> EqvFTyping

{-@ get_aewitness_from_den :: t:Type -> v:Value -> ProofOf(Denotes t v)
        -> ProofOf(EqvFTyping FEmpty v (erase t)) @-}
get_aewitness_from_den :: Type -> Expr -> Denotes -> EqvFTyping
get_aewitness_from_den t v (DRefn b _ _ _ pf_v_b _)         
  = AEWitness FEmpty v (FTBasic b) (FTBasic b) (AEBasic FEmpty b) pf_v_b
get_aewitness_from_den t v (DFunc _ _ _ _ s_x s eqv_sxs_t pf_v_b _) 
  = AEWitness FEmpty v (erase t) (FTFunc s_x s) eqv_sxs_t pf_v_b
get_aewitness_from_den t v (DExis _ _ _ _ s eqv_s_t pf_v_b _ _ _) 
  = AEWitness FEmpty v (erase t) s eqv_s_t pf_v_b
get_aewitness_from_den t v (DPoly _ k _ _ a0 s eqv_a0s_t pf_v_b _)  
  = AEWitness FEmpty v (erase t) (FTPoly a0 k s) eqv_a0s_t pf_v_b

-- with bound type vars, these are only equiv up to alhpa-renaming bound variables
{-@ lem_erase_subtype :: g:Env -> t1:Type -> t2:Type -> ProofOf(Subtype g t1 t2)
               -> ProofOf(AlphaEqv (erase_env g) (erase t1) (erase t2)) @-}
lem_erase_subtype :: Env -> Type -> Type -> Subtype -> AlphaEqv
lem_erase_subtype g t1 t2 (SBase _g x1 b p1 x2 p2 y _) = AEBasic (erase_env g) b
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
               -> { pf:_ | erase (ctsubst th t) == erase t } @-} -- not quite true undefined undefined
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
        -> ProofOf(AlphaEqv FEmpty (erase (ctsubst th t1)) (erase (ctsubst th t2))) @-}
lem_erase_th_sub :: Env -> Type -> Type -> Subtype -> CSub -> AlphaEqv
lem_erase_th_sub g t1 t2 p_t1_t2 th = undefined {-
toProof ( normalize (erase (ctsubst th t1))
                                              ? lem_erase_ctsubst th t1
                                            === normalize (erase t1) ? lem_erase_subtype g t1 t2 p_t1_t2
                                            === normalize (erase t2) ? lem_erase_ctsubst th t2
                                            === normalize (erase (ctsubst th t2)) ) -}

{-@ lem_alpha_refl :: g:FEnv -> t1:FType -> ProofOf(AlphaEqv g t1 t1) / [ftsize t1] @-}
lem_alpha_refl :: FEnv -> FType -> AlphaEqv
lem_alpha_refl g (FTBasic b)    = AEBasic g b
lem_alpha_refl g (FTFunc t t')  
  = AEFunc g t t (lem_alpha_refl g t) t' t' (lem_alpha_refl g t')
lem_alpha_refl g (FTPoly a k t) = AEPoly g a k t a t a' eqv_t_t
  where
    a'      = fresh_varF g
    eqv_t_t = lem_alpha_refl (FConsT a' k g) (unbindFT a a' t) 

{-@ lem_alpha_trans :: g:FEnv -> t1:FType -> t2:FType -> t3:FType 
        -> ProofOf(AlphaEqv g t1 t2) -> ProofOf(AlphaEqv g t2 t3) -> ProofOf(AlphaEqv g t1 t3) @-}
lem_alpha_trans :: FEnv -> FType -> FType -> FType -> AlphaEqv -> AlphaEqv -> AlphaEqv
lem_alpha_trans g t1 t2 t3 (AEBasic _ b) (AEBasic _ _) = AEBasic g b
lem_alpha_trans g t1 t2 t3 (AEFunc _ s1 s2 eqv_s1_s2 t1' t2' eqv_t1'_t2') eqv_t2_t3
  = case eqv_t2_t3 of
      (AEFunc _ _ s3 eqv_s2_s3 _ t3' eqv_t2'_t3') 
          -> AEFunc g s1 s3 eqv_s1_s3 t1' t3' eqv_t1'_t3'
        where
          eqv_s1_s3   = lem_alpha_trans g s1  s2  s3  eqv_s1_s2   eqv_s2_s3
          eqv_t1'_t3' = lem_alpha_trans g t1' t2' t3' eqv_t1'_t2' eqv_t2'_t3'
lem_alpha_trans g t1 t2 t3 (AEPoly _ a1 k t1' a2 t2' a eqv_t1'_t2') eqv_t2_t3
  = case eqv_t2_t3 of
      (AEPoly _ _ _ _ a3 t3' a' eqv_t2'_t3') 
          -> AEPoly g a1 k t1' a3 t3' a eqv_t1'_t3'
        where
          eqv_t1'_t3' = undefined

{-@ lem_alpha_ftapp :: g:FEnv -> v:Expr -> v_x:Expr -> t_x:FType -> t:FType
        -> ProofOf(EqvFTyping g v (FTFunc t_x t)) -> ProofOf(EqvFTyping g v_x t_x)
        -> ProofOf(EqvFTyping g (App v v_x) t) @-}
lem_alpha_ftapp :: FEnv -> Expr -> Expr -> FType -> FType -> EqvFTyping 
                        -> EqvFTyping -> EqvFTyping
lem_alpha_ftapp = undefined
