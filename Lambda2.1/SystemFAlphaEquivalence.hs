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

{-@ reflect foo27 @-}   
foo27 x = Just x 
foo27 :: a -> Maybe a 

{- data AlphaEqv where
     AEBasic :: b:Basic -> ProofOf(AlphaEqv (FTBasic b) (FTBasic b))
     AEFunc  :: s1:FType -> s2:FType -> ProofOf(AlphaEqv s1 s2)
             -> t1:FType -> t2:FType -> ProofOf(AlphaEqv t1 t2)
             -> ProofOf(AlphaEqv (FTFunc s1 t1) (FTFunc s2 t2))
     AEPoly  :: a1:Vname -> k:Kind -> t1:FType -> a2:Vname -> t2:FType
                  -> { a:Vname | not (Set_mem a (ffreeTV t1)) && not (Set_mem a (ffreeTV t2)) }
                  -> ProofOf(AlphaEqv (unbindFT a1 a t1) (unbindFT a2 a t2))
                  -> ProofOf(AlphaEqv (FTPoly a1 k t1)   (FTPoly a2 k t2)) @-}

-- This relation means that w.r.t. F-Env g, expr e has F-Type in the equivalence class of t

data EqvFTypingP where
    EqvFTyping :: FEnv -> Expr -> FType -> EqvFTypingP

{-@ data EqvFTyping where
        AEWitness :: g:FEnv -> e:Expr -> t:FType -> s:FType -> ProofOf(AlphaEqv s t)
                            -> ProofOf(HasFType g e s) -> ProofOf(EqvFTyping g e t) @-}
data EqvFTyping where
    AEWitness :: FEnv -> Expr -> FType -> FType -> AlphaEqv -> HasFType -> EqvFTyping

{-@ get_aewitness_from_den :: t:Type -> v:Value -> ProofOf(Denotes t v)
        -> ProofOf(EqvFTyping FEmpty v (erase t)) @-}
get_aewitness_from_den :: Type -> Expr -> Denotes -> EqvFTyping
get_aewitness_from_den t v (DRefn b _ _ _ pf_v_b _)         
  = AEWitness FEmpty v (FTBasic b) (FTBasic b) (AEBasic b) pf_v_b
get_aewitness_from_den t v (DFunc _ _ _ _ s_x s eqv_sxs_t pf_v_b _) 
  = AEWitness FEmpty v (erase t) (FTFunc s_x s) eqv_sxs_t pf_v_b
get_aewitness_from_den t v (DExis _ _ _ _ s eqv_s_t pf_v_b _ _ _) 
  = AEWitness FEmpty v (erase t) s eqv_s_t pf_v_b
get_aewitness_from_den t v (DPoly _ k _ _ a0 s eqv_a0s_t pf_v_b _)  
  = AEWitness FEmpty v (erase t) (FTPoly a0 k s) eqv_a0s_t pf_v_b

-- Choosing a fresh variable from FTypes

{-@ reflect fresh_var_ftype @-}
{-@ fresh_var_ftype :: t:FType -> t':FType 
        -> { a:Vname | not (Set_mem a (ffreeTV t)) && not (Set_mem a (ffreeTV t')) } @-}
fresh_var_ftype :: FType -> FType -> Vname
fresh_var_ftype t t' = maxpFType (FTFunc t t') -- i.e., max (maxpFType t) (maxpFType t')

{-@ reflect fresh_var_ftype_excluding @-}
{-@ fresh_var_ftype_excluding :: t:FType -> t':FType -> a:Vname
        -> { a':Vname | not (Set_mem a' (ffreeTV t)) && not (Set_mem a' (ffreeTV t')) && a' != a } @-}
fresh_var_ftype_excluding :: FType -> FType -> Vname -> Vname
fresh_var_ftype_excluding t t' a = maxpFType (FTFunc (FTBasic (FTV a)) (FTFunc t t'))

{-@ reflect maxpFType @-}
{-@ maxpFType :: t:FType -> { a':Vname | Set_mem a' (ffreeTV t) => (a' < maxpFType t) } @-}
maxpFType :: FType -> Int
maxpFType (FTBasic b)    = case b of
  (FTV a) -> a + 1
  _       -> 1
maxpFType (FTFunc t_x t) = let a' = max (maxpFType t_x) (maxpFType t) 
                           in a' `withProof` lem_maxp_ftype a' (FTFunc t_x t)
maxpFType (FTPoly a k t) = maxpFType t

{-@ reflect lem_maxp_ftype @-}
{-@ lem_maxp_ftype :: a':Vname -> t:FType -> { pf:_ | Set_mem a' (ffreeTV t) => (a' < maxpFType t) } @-}
lem_maxp_ftype :: Vname -> FType -> Bool
lem_maxp_ftype a' (FTBasic b) = case b of
  (FTV a) -> True
  _       -> True
lem_maxp_ftype a' (FTFunc t_x t) 
  = True `withProof` lem_maxp_ftype a' t_x
         `withProof` lem_maxp_ftype a' t
lem_maxp_ftype a' (FTPoly a k t) 
  = True `withProof` lem_maxp_ftype a' t

-- Algebraic properties of Alpha Equivalence that make it an equivalence relation:
{-@ lem_alpha_refl :: t1:FType -> ProofOf(AlphaEqv t1 t1) / [ftsize t1] @-}
lem_alpha_refl :: FType -> AlphaEqv
lem_alpha_refl (FTBasic b)    = AEBasic b
lem_alpha_refl (FTFunc t t')  
  = AEFunc t t (lem_alpha_refl t) t' t' (lem_alpha_refl t')
lem_alpha_refl (FTPoly a k t) = AEPoly a k t a t a' eqv_t_t
  where
    a'      = fresh_var_ftype t t
    eqv_t_t = lem_alpha_refl (unbindFT a a' t) 

{-@ lem_alpha_commutes :: t1:FType -> t2:FType -> ProofOf(AlphaEqv t1 t2)
                                               -> ProofOf(AlphaEqv t2 t1) @-}
lem_alpha_commutes :: FType -> FType -> AlphaEqv -> AlphaEqv
lem_alpha_commutes t1 t2 ae_t1_t2@(AEBasic b) = ae_t1_t2
lem_alpha_commutes t1 t2 (AEFunc s1 s2 ae_s1_s2 t1' t2' ae_t1'_t2')
  = AEFunc s2 s1 ae_s2_s1 t2' t1' ae_t2'_t1'
      where
        ae_s2_s1   = lem_alpha_commutes s1  s2  ae_s1_s2
        ae_t2'_t1' = lem_alpha_commutes t1' t2' ae_t1'_t2'
lem_alpha_commutes t1 t2 (AEPoly a1 k t1' a2 t2' a ae_t1'_t2')
  = AEPoly a2 k t2' a1 t1' a ae_t2'_t1'
      where
        ae_t2'_t1' = lem_alpha_commutes (unbindFT a1 a t1') (unbindFT a2 a t2') ae_t1'_t2'

{-@ lem_alpha_trans :: t1:FType -> t2:FType -> t3:FType 
        -> { eqv_t1_t2:AlphaEqv | propOf eqv_t1_t2 == AlphaEqv t1 t2 } 
        -> { eqv_t2_t3:AlphaEqv | propOf eqv_t2_t3 == AlphaEqv t2 t3 } 
        -> ProofOf(AlphaEqv t1 t3) / [alphaSize eqv_t1_t2] @-}
lem_alpha_trans :: FType -> FType -> FType -> AlphaEqv -> AlphaEqv -> AlphaEqv
lem_alpha_trans t1 t2 t3 (AEBasic b) (AEBasic _) = AEBasic b
lem_alpha_trans t1 t2 t3 (AEFunc s1 s2 eqv_s1_s2 t1' t2' eqv_t1'_t2') eqv_t2_t3
  = case eqv_t2_t3 of
      (AEFunc _ s3 eqv_s2_s3 _ t3' eqv_t2'_t3') 
          -> AEFunc s1 s3 eqv_s1_s3 t1' t3' eqv_t1'_t3'
        where
          eqv_s1_s3   = lem_alpha_trans s1  s2  s3  eqv_s1_s2   eqv_s2_s3
          eqv_t1'_t3' = lem_alpha_trans t1' t2' t3' eqv_t1'_t2' eqv_t2'_t3'
lem_alpha_trans t1 t2 t3 (AEPoly a1 k t1' a2 t2' a eqv_t1'_t2') eqv_t2_t3
  = case eqv_t2_t3 of
      (AEPoly _ _ _ a3 t3' a' eqv_t2'_t3') -> AEPoly a1 k t1' a3 t3' a'' eqv_t1'_t3'
        where
          a''_            = max (fresh_var_ftype t1' t2') (fresh_var_ftype t2' t3')
          a''             = a''_ ? lem_maxp_ftype a''_ t1'
                                 ? lem_maxp_ftype a''_ t2'
                                 ? lem_maxp_ftype a''_ t3'
          eqv_a''_t1'_t2' = lem_change_tvar_alpha (unbindFT a1 a t1') (unbindFT a2 a t2')  
                                                  a eqv_t1'_t2' a''
                                 ? lem_ftsubFV_unbindFT a1 a (FTBasic (FTV a'')) t1'
                                 ? lem_ftsubFV_unbindFT a2 a (FTBasic (FTV a'')) t2'
          eqv_a''_t2'_t3' = lem_change_tvar_alpha (unbindFT a2 a' t2') (unbindFT a3 a' t3')  
                                                  a' eqv_t2'_t3' a''
                                 ? lem_ftsubFV_unbindFT a2 a' (FTBasic (FTV a'')) t2'
                                 ? lem_ftsubFV_unbindFT a3 a' (FTBasic (FTV a'')) t3'
          eqv_t1'_t3'     = lem_alpha_trans (unbindFT a1 a'' t1') (unbindFT a2 a'' t2') 
                                            (unbindFT a3 a'' t3') eqv_a''_t1'_t2' eqv_a''_t2'_t3'

{-@ lem_eqvftyping_refl :: g:FEnv -> e:Expr -> t:FType -> ProofOf(HasFType g e t)
                                  -> ProofOf(WFFE g) -> ProofOf(EqvFTyping g e t) @-}
lem_eqvftyping_refl :: FEnv -> Expr -> FType -> HasFType -> WFFE -> EqvFTyping
lem_eqvftyping_refl g e t p_e_t p_g_wf = AEWitness g e t t (lem_alpha_refl t) p_e_t
  where
    p_g_t      = lem_ftyping_wfft g e t p_e_t p_g_wf

{-@ lem_eqvftyping_basic :: g:FEnv -> e:Expr -> b:Basic 
        -> ProofOf(EqvFTyping g e (FTBasic b)) -> ProofOf(HasFType g e (FTBasic b)) @-}
lem_eqvftyping_basic :: FEnv -> Expr -> Basic -> EqvFTyping -> HasFType
lem_eqvftyping_basic g e b (AEWitness _ _ _ s ae_s_b p_e_s) = case ae_s_b of 
  (AEBasic _b) -> p_e_s

{-@ lem_change_tvar_alpha :: t1:FType -> t2:FType -> a:Vname 
        -> { p_t1_t2:AlphaEqv | propOf p_t1_t2 == AlphaEqv t1 t2 } -> a':Vname
        -> { p'_t1_t2:AlphaEqv | propOf p'_t1_t2 == AlphaEqv  
                            (ftsubFV a (FTBasic (FTV a')) t1) (ftsubFV a (FTBasic (FTV a')) t2) &&
                                 alphaSize p_t1_t2 == alphaSize p'_t1_t2 } / [alphaSize p_t1_t2] @-} 
lem_change_tvar_alpha :: FType -> FType -> Vname -> AlphaEqv -> Vname -> AlphaEqv
lem_change_tvar_alpha t1 t2 a (AEBasic b) a' = case b of 
  (FTV a1) | a1 == a   -> AEBasic (FTV a')
           | otherwise -> AEBasic (FTV a1)
  _                    -> AEBasic  b
lem_change_tvar_alpha t1 t2 a (AEFunc s1 s2 ae_s1_s2 t1' t2' ae_t1'_t2') a' 
  = AEFunc (ftsubFV a (FTBasic (FTV a')) s1) (ftsubFV a (FTBasic (FTV a')) s2) ae_env'_s1_s2 
           (ftsubFV a (FTBasic (FTV a')) t1') (ftsubFV a (FTBasic (FTV a')) t2') ae_env'_t1'_t2' 
      where
        ae_env'_s1_s2   = lem_change_tvar_alpha s1  s2  a ae_s1_s2   a'
        ae_env'_t1'_t2' = lem_change_tvar_alpha t1' t2' a ae_t1'_t2' a'
lem_change_tvar_alpha t1 t2 a (AEPoly a1 kk t1' a2 t2' aa ae_t1'_t2') a' 
  = AEPoly a1 kk (ftsubFV a (FTBasic (FTV a')) t1')
           a2    (ftsubFV a (FTBasic (FTV a')) t2') aa' ae_aa'env'_t1'_t2'
      where
        aa'                = fresh_var_ftype_excluding (ftsubFV a (FTBasic (FTV a')) t1')
                                                       (ftsubFV a (FTBasic (FTV a')) t2') a
        ae_aa'env_t1'_t2'  = lem_change_tvar_alpha (unbindFT a1 aa t1') (unbindFT a2 aa t2') 
                                                   aa ae_t1'_t2' aa'
                                 ? lem_ftsubFV_unbindFT a1 aa (FTBasic (FTV aa')) t1'
                                 ? lem_ftsubFV_unbindFT a2 aa (FTBasic (FTV aa')) t2'
        ae_aa'env'_t1'_t2' = lem_change_tvar_alpha (unbindFT a1 aa' t1') (unbindFT a2 aa' t2') 
                                                   a ae_aa'env_t1'_t2' a'
                                 ? lem_commute_ftsubFV_unbindFT a (FTBasic (FTV a')) a1 aa' t1'
                                 ? lem_commute_ftsubFV_unbindFT a (FTBasic (FTV a')) a2 aa' t2'

{-@ lem_subst_alpha :: t1:FType -> t2:FType -> a:Vname -> { t_a:UserType | Set_emp (tfreeBTV t_a) }
        -> { p_t1_t2:AlphaEqv | propOf p_t1_t2 == AlphaEqv t1 t2 }
        -> { p'_t1_t2:AlphaEqv | propOf p'_t1_t2 == AlphaEqv (ftsubFV a (erase t_a) t1) 
                                     (ftsubFV a (erase t_a) t2) } / [alphaSize p_t1_t2] @-}
lem_subst_alpha :: FType -> FType -> Vname -> Type -> AlphaEqv -> AlphaEqv
lem_subst_alpha t1 t2 a t_a (AEBasic b) = case b of 
  (FTV a1) | a1 == a   -> lem_alpha_refl (erase t_a)
           | otherwise -> AEBasic (FTV a1)
  _                    -> AEBasic b
lem_subst_alpha t1 t2 a t_a (AEFunc s1 s2 ae_s1_s2 t1' t2' ae_t1'_t2')
  = AEFunc (ftsubFV a (erase t_a) s1) (ftsubFV a (erase t_a) s2) ae_s1ta_s2ta 
           (ftsubFV a (erase t_a) t1') (ftsubFV a (erase t_a) t2') ae_t1'ta_t2'ta
      where
        ae_s1ta_s2ta   = lem_subst_alpha s1  s2  a t_a ae_s1_s2
        ae_t1'ta_t2'ta = lem_subst_alpha t1' t2' a t_a ae_t1'_t2' 
lem_subst_alpha t1 t2 a t_a (AEPoly a1 kk t1' a2 t2' aa ae_t1'_t2')
  = AEPoly a1 kk (ftsubFV a (erase t_a) t1') a2 (ftsubFV a (erase t_a) t2') aa' ae_t1'ta_t2'ta
      where
        aa'            = fresh_var_ftype_excluding (ftsubFV a (erase t_a) t1') 
                                                   (ftsubFV a (erase t_a) t2') a
        ae'_t1'_t2'    = lem_change_tvar_alpha (unbindFT a1 aa t1') (unbindFT a2 aa t2')
                                               aa ae_t1'_t2' aa'
                                               ? lem_ftsubFV_unbindFT a1 aa (FTBasic (FTV aa')) t1'
                                               ? lem_ftsubFV_unbindFT a2 aa (FTBasic (FTV aa')) t2'
        ae_t1'ta_t2'ta = lem_subst_alpha (unbindFT a1 aa' t1') (unbindFT a2 aa' t2') a t_a ae'_t1'_t2'
                                         ? lem_commute_ftsubFV_unbindFT a (erase t_a) 
                                               a1 (aa' ? lem_erase_freeBV t_a)  t1'
                                         ? lem_commute_ftsubFV_unbindFT a (erase t_a) 
                                               a2 (aa' ? lem_erase_freeBV t_a)  t2'

{-@ lem_alpha_ctsubst :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th) -> t1:Type -> t2:Type
        -> ProofOf(AlphaEqv (erase t1) (erase t2)) 
        -> ProofOf(AlphaEqv (erase (ctsubst th t1)) (erase (ctsubst th t2))) @-}
lem_alpha_ctsubst :: Env -> CSub -> DenotesEnv -> Type -> Type -> AlphaEqv -> AlphaEqv
lem_alpha_ctsubst Empty            th den_g_th t1 t2 ae_t1_t2 = case den_g_th of
  DEmp -> ae_t1_t2
lem_alpha_ctsubst (Cons  x t_x g') th den_g_th t1 t2 ae_t1_t2 = case den_g_th of
  (DExt  _g' th' den_g'_th' _x _tx v_x den_th'tx_vx)
    -> lem_alpha_ctsubst g' th' den_g'_th' (tsubFV x v_x t1) (tsubFV x v_x t2) ae_t1vx_t2vx
         where
           ae_t1vx_t2vx = ae_t1_t2 ? lem_erase_tsubFV x v_x t1
                                   ? lem_erase_tsubFV x v_x t2
lem_alpha_ctsubst (ConsT a k_a g') th den_g_th t1 t2 ae_t1_t2 = case den_g_th of
  (DExtT _g' th' den_g'_th' _a _ka t_a p_emp_ta)
    -> lem_alpha_ctsubst g' th' den_g'_th' (tsubFTV a t_a t1) (tsubFTV a t_a t2) ae_t1ta_t2ta
         where
           ae_t1ta_t2ta = lem_subst_alpha (erase t1) (erase t2) a t_a ae_t1_t2
                                          ? lem_erase_tsubFTV a t_a t1
                                          ? lem_erase_tsubFTV a t_a t2

-- the rest of this will be uncommented and worked out (possibly with changes to AlphaEqv) as needed

-- LEMMA 6. If G |- s <: t, then if we erase the types then (erase s) and (erase t)
--               equiv up to alpha-renaming bound variables
{-@ lem_erase_subtype :: g:Env -> t1:Type -> t2:Type -> ProofOf(Subtype g t1 t2)
               -> ProofOf(AlphaEqv (erase t1) (erase t2)) @-}
lem_erase_subtype :: Env -> Type -> Type -> Subtype -> AlphaEqv
lem_erase_subtype g t1 t2 (SBase _g x1 b p1 x2 p2 y _) = AEBasic b
lem_erase_subtype g t1 t2 (SFunc _g x1 s1 x2 s2 p_s2_s1 t1' t2' y p_t1'_t2')
  = AEFunc (erase s1) (erase s2) ae_s1_s2 (erase t1') (erase t2') ae_t1'_t2'
      where
        ae_s2_s1     = lem_erase_subtype  g s2 s1 p_s2_s1
        ae_s1_s2     = lem_alpha_commutes (erase s2) (erase s1) ae_s2_s1
        ae_t1'_t2'   = lem_erase_subtype (Cons y s2 g) (unbindT x1 y t1') (unbindT x2 y t2') 
                                         p_t1'_t2' ? lem_erase_tsubBV x1 (FV y) t1' 
                                                   ? lem_erase_tsubBV x2 (FV y) t2'
lem_erase_subtype g t1 t2 (SWitn _g v t_x p_v_tx _t1 x t' p_t1_t'v)
  = lem_erase_subtype g t1 (tsubBV x v t') p_t1_t'v
                      ? lem_erase_tsubBV x v t'
{- toProof ( erase t1 ? lem_erase_subtype g t1 (tsubBV x v t') p_t1_t'v
            === erase (tsubBV x v t') ? lem_erase_tsubBV x v t'
            === erase t' === erase (TExists x t_x t') ) -}
lem_erase_subtype g t1 t2 (SBind _g x t_x t _t2 y p_t_t')
  = lem_erase_subtype (Cons y t_x g) (unbindT x y t) t2 p_t_t'
                                        ? lem_erase_tsubBV x (FV y) t
lem_erase_subtype g t1 t2 (SPoly _g a1 k t1' a2 t2' a_ p_ag_t1'_t2') 
  = AEPoly a1 k (erase t1') a2 (erase t2') a ae_ag_t1'_t2'
      where
        a             = a_ ? lem_erase_freeTV t1' ? lem_erase_freeTV t2'
        ae_ag_t1'_t2' = lem_erase_subtype (ConsT a k g) (unbind_tvT a1 a t1') (unbind_tvT a2 a t2')
                                          p_ag_t1'_t2' ? lem_erase_unbind_tvT a1 a t1'
                                                       ? lem_erase_unbind_tvT a2 a t2' 

{-@ lem_alpha_wfft :: g:FEnv -> t:FType -> k:Kind -> ProofOf(WFFT g t k) 
        -> s:FType -> ProofOf(AlphaEqv s t) -> ProofOf(WFFT g s k) @-}
lem_alpha_wfft :: FEnv -> FType -> Kind -> WFFT -> FType -> AlphaEqv -> WFFT
lem_alpha_wfft g t k (WFFTBasic _ b) s ae_s_t = case ae_s_t of
  (AEBasic {}) -> WFFTBasic g b
lem_alpha_wfft g t k (WFFTFV1 _ a k_a) s ae_s_t = case ae_s_t of
  (AEBasic {}) -> WFFTFV1 g a k_a
lem_alpha_wfft g t k (WFFTFV2 _ a k_a p_g_a x t_x) s ae_s_t = case ae_s_t of
  (AEBasic {}) -> WFFTFV2 g a k_a p_g_a x t_x 
lem_alpha_wfft g t k (WFFTFV3 _ a k_a p_g_a a' k') s ae_s_t = case ae_s_t of
  (AEBasic {}) -> WFFTFV3 g a k_a p_g_a a' k' 
lem_alpha_wfft g t k (WFFTFunc _ t1 k1 p_g_t1 t2 k2 p_g_t2) s ae_s_t = case ae_s_t of
  (AEFunc s1 _ ae_s1_t1 s2 _ ae_s2_t2) -> WFFTFunc g s1 k1 p_g_s1 s2 k2 p_g_s2
    where
      p_g_s1 = lem_alpha_wfft g t1 k1 p_g_t1 s1 ae_s1_t1
      p_g_s2 = lem_alpha_wfft g t2 k2 p_g_t2 s2 ae_s2_t2
lem_alpha_wfft g t k (WFFTPoly _ a k' t' k_t' a' p_a'g_t') s ae_s_t = case ae_s_t of
  (AEPoly aa _ s' a t' a'' ae_a''_s'_t') -> WFFTPoly g aa k' s' k_t' a' p_a'g_s'
    where
      ae_a'_s'_t' = lem_change_tvar_alpha (unbindFT aa a'' s') (unbindFT a a'' t') 
                                          a'' ae_a''_s'_t' a'
                            ? lem_ftsubFV_unbindFT aa a'' (FTBasic (FTV a')) s'
                            ? lem_ftsubFV_unbindFT a  a'' (FTBasic (FTV a')) t'
      p_a'g_s'    = lem_alpha_wfft (FConsT a' k' g) (unbindFT a a' t') k_t' p_a'g_t' 
                                   (unbindFT aa a' s') ae_a'_s'_t'
lem_alpha_wfft g t k (WFFTKind _ _t p_g_t_base) s ae_s_t = WFFTKind g s p_g_s_base
  where
    p_g_s_base = lem_alpha_wfft g t Base p_g_t_base s ae_s_t 

{-@ lem_alpha_ftabs :: g:FEnv -> x:Vname -> e:Expr -> t:FType -> t':FType
        -> ProofOf(HasFType g (Lambda x e) (FTFunc t t')) -> s:FType -> ProofOf(AlphaEqv s t)
        -> ProofOf(HasFType g (Lambda x e) (FTFunc s t')) @-}
lem_alpha_ftabs :: FEnv -> Vname -> Expr -> FType -> FType -> HasFType 
                        -> FType -> AlphaEqv -> HasFType
lem_alpha_ftabs g x e t t' (FTAbs _ _ _ k p_g_t _ _ y p_ytg_e_t') s ae_s_t
  = FTAbs g x s k p_g_s e s' y p_ysg_e_s'
      where
        p_g_s      = lem_alpha_wfft g t k p_g_t s ae_s_t
        (AEWitness _ _ _ s' ae_s'_t' p_ysg_e_s')
                   = lem_alpha_in_env_ftyp g FEmpty y s t ae_s_t (unbind x y e ) t' p_ytg_e_t'

-- will probably only work w/r/t empty??
{-@ lem_alpha_ftapp :: g:FEnv -> v:Expr -> v_x:Expr -> t_x:FType -> t:FType
        -> ProofOf(EqvFTyping g v (FTFunc t_x t)) -> ProofOf(EqvFTyping g v_x t_x)
        -> ProofOf(EqvFTyping g (App v v_x) t) @-}
lem_alpha_ftapp :: FEnv -> Expr -> Expr -> FType -> FType -> EqvFTyping 
                        -> EqvFTyping -> EqvFTyping
lem_alpha_ftapp g v v_x t_x t eqv_v_txt eqv_vx_tx  
  = AEWitness g (App v v_x) t r ae_r_t p_vvx_r 
      where
        (AEWitness _ _ _ s_x ae_sx_tx  p_vx_sx) = eqv_vx_tx
        (AEWitness _ _ _ r'  ae_r'_txt p_v_r')  = eqv_v_txt
        (AEFunc    r_x _tx ae_rx_tx r t ae_r_t) = ae_r'_txt

        (FTAbs _ x _ _ _ v' _ _ _)              = p_v_r' 
        ae_tx_rx = lem_alpha_commutes r_x t_x ae_rx_tx
        ae_sx_rx = lem_alpha_trans s_x t_x r_x ae_sx_tx ae_tx_rx
        p_v_sxr  = lem_alpha_ftabs g x v' r_x r p_v_r' s_x ae_sx_rx
        p_vvx_r  = FTApp g v s_x r p_v_sxr v_x p_vx_sx 

--        -> e:Expr -> { t:FType | Set_sub (ffreeTV t) (tvbindsF (concatF (FCons x t_x g) g')) }
{-@ lem_alpha_in_env_ftyp :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> { x:Vname | (not (in_envF x g)) && not (in_envF x g') } 
        -> s_x:FType -> t_x:FType -> ProofOf(AlphaEqv s_x t_x) -> e:Expr -> t:FType 
        -> { p_e_t:HasFType | propOf p_e_t == HasFType (concatF (FCons x t_x g) g') e t }
        -> ProofOf(EqvFTyping (concatF (FCons x s_x g) g') e t) / [ftypSize p_e_t] @-}
lem_alpha_in_env_ftyp :: FEnv -> FEnv -> Vname -> FType -> FType -> AlphaEqv 
                              -> Expr -> FType -> HasFType -> EqvFTyping 
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t (FTBC _ b) 
 -- = undefined {- CHECKED
  = AEWitness (concatF (FCons x s_x g) g') (Bc b) (FTBasic TBool) (FTBasic TBool)
              (lem_alpha_refl (FTBasic TBool)) p_e_t
      where
        p_e_t = FTBC (concatF (FCons x s_x g) g') b
{- -}
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t (FTIC _ n) 
 -- = undefined {- CHECKED
  = AEWitness (concatF (FCons x s_x g) g') (Ic n) (FTBasic TInt) (FTBasic TInt)
              (lem_alpha_refl (FTBasic TInt)) p_e_t
      where
        p_e_t = FTIC (concatF (FCons x s_x g) g') n
{- -}
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t p_e_t@(FTVar1 _ z _t) = case g' of
  FEmpty           -> AEWitness (FCons x s_x g) (FV x) t_x s_x eqv_sx_tx (FTVar1 g x s_x)
  (FCons _z _ g'') -> AEWitness (concatF (FCons x s_x g) g') (FV z) t t eqv_t_t p'_e_t
    where
      eqv_t_t = lem_alpha_refl t
      p'_e_t  = FTVar1 (concatF (FCons x s_x g) g'') (z 
                                           ? lem_in_env_concatF (FCons x t_x g) g'' z
                                           ? lem_in_env_concatF (FCons x s_x g) g'' z
                                           ? lem_in_env_concatF g g'' z) t
{- -}
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t (FTVar2 _ z _t p_z_t w t_w) = case g' of
  FEmpty           -> AEWitness (FCons x s_x g) (FV z) t t (lem_alpha_refl t) 
                                (FTVar2 g z t p_z_t w s_x)
  (FCons _w _ g'') -> AEWitness (concatF (FCons x s_x g) g') (FV z) t s eqv_s_t p'_e_s
    where
      (AEWitness _env'' _ _ s eqv_s_t p_g''_e_s)
              = lem_alpha_in_env_ftyp g g'' x s_x t_x eqv_sx_tx e t p_z_t
      p'_e_s  = FTVar2 (concatF (FCons x s_x g) g'') (z
                                           ? lem_in_env_concatF (FCons x t_x g) g'' z
                                           ? lem_in_env_concatF (FCons x s_x g) g'' z
                                           ? lem_in_env_concatF g g'' z) s p_g''_e_s w t_w
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t (FTVar3 _ z _t p_z_t a k) = case g' of
  FEmpty            -> impossible ""
  (FConsT _a _ g'') -> AEWitness (concatF (FCons x s_x g) g') (FV z) t s eqv_s_t p'_e_s
    where
      (AEWitness _env'' _ _ s eqv_s_t p_g''_e_s)
              = lem_alpha_in_env_ftyp g g'' x s_x t_x eqv_sx_tx e t p_z_t
      p'_e_s  = FTVar3 (concatF (FCons x s_x g) g'') (z                                                                                                 ? lem_in_env_concatF (FCons x t_x g) g'' z
                                           ? lem_in_env_concatF (FCons x s_x g) g'' z
                                           ? lem_in_env_concatF g g'' z) s p_g''_e_s a k
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t (FTPrm _ c) 
 -- = undefined {- CHECKED
  = AEWitness (concatF (FCons x s_x g) g') (Prim c) (erase_ty c) (erase_ty c)
              (lem_alpha_refl (erase_ty c)) p_e_t
      where
        p_e_t = FTPrm (concatF (FCons x s_x g) g') c
{- -}
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t (FTAbs _ z t1 k1 p_env_t1 e' t2 z'_ p_e'_t2)
  = AEWitness (concatF (FCons x s_x g) g') (Lambda z e') (FTFunc t1 t2) (FTFunc t1 s2) 
              ae_t1s2_t1t2 p_e_s
      where
        z'           = z'_ ? lem_in_env_concatF (FCons x t_x g) g' z'_
                           ? lem_in_env_concatF (FCons x s_x g) g' z'_
                           ? lem_in_env_concatF g g' z'_
        p_g'g_t1     = lem_strengthen_wfft g x t_x g' t1 k1 p_env_t1
        p_env'_t1    = lem_weaken_wfft g g' t1 k1 p_g'g_t1 x s_x
        (AEWitness _ _ _ s2 eqv_s2_t2 p_e'_s2) 
                     = lem_alpha_in_env_ftyp g (FCons z' t1 g') x s_x t_x eqv_sx_tx 
                                             (unbind z z' e') t2 p_e'_t2
        ae_t1s2_t1t2 = AEFunc t1 t1 (lem_alpha_refl t1) s2 t2 eqv_s2_t2
        p_e_s     = FTAbs (concatF (FCons x s_x g) g') z t1 k1 p_env'_t1 e' s2 z' p_e'_s2
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t (FTApp _ e1 t1 _t p_e1_t1t e2 p_e2_t1)
  = AEWitness (concatF (FCons x s_x g) g') (App e1 e2) t s ae_s_t p_e1e2_s
      where
        env'        = concatF (FCons x s_x g) g'
        (AEWitness _ _ _ r' ae_r'_t1t p_e1_r')
                    = lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e1 (FTFunc t1 t) p_e1_t1t
        (AEWitness _ _ _ s1 ae_s1_t1  p_e2_s1)
                    = lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e2 t1 p_e2_t1
        (AEFunc r1 _t1 ae_r1_t1 r _t ae_r_t)  = ae_r'_t1t


        (FTAbs _g z _r1 k p_g_r1 e' _r y p_yr1g_e'_r) = p_e1_r'
        ae_t1_r1    = lem_alpha_commutes r1 t1 ae_r1_t1
        ae_s1_r1    = lem_alpha_trans s1 t1 r1 ae_s1_t1 ae_t1_r1
        p_g_s1      = lem_alpha_wfft env' r1 k p_g_r1 s1 ae_s1_r1
        (AEWitness _ _ _ s ae_s_r p_ys1g_e'_s)
                    = lem_alpha_in_env_ftyp env' FEmpty y s1 r1 ae_s1_r1 (unbind z y e') r p_yr1g_e'_r
        ae_s_t      = lem_alpha_trans s r t ae_s_r ae_r_t 
        p_e1_s1s    = FTAbs env' z s1 k p_g_s1 e' s y p_ys1g_e'_s
        p_e1e2_s    = FTApp env' e1 s1 s p_e1_s1s e2 p_e2_s1
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t (FTAbsT {}) 
  = undefined
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t (FTAppT {}) 
  = undefined
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t (FTLet {}) 
  = undefined
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t (FTAnn {}) 
  = undefined


{- lem_erase_ctsubst -- deleted because it's not true: erase (ctsubst th t) != erase t -}


