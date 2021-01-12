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
       AEBasic :: g:FEnv -> b:Basic -> ProofOf(AlphaEqv g (FTBasic b) (FTBasic b))
    |  AEFunc  :: g:FEnv -> s1:FType -> s2:FType -> ProofOf(AlphaEqv g s1 s2)
                         -> t1:FType -> t2:FType -> ProofOf(AlphaEqv g t1 t2)
                         -> ProofOf(AlphaEqv g (FTFunc s1 t1) (FTFunc s2 t2))
    |  AEPoly  :: g:FEnv -> a1:Vname -> k:Kind -> t1:FType -> a2:Vname -> t2:FType
                         -> { a:Vname | not (Set_mem a (bindsF g)) }
                         -> ProofOf(AlphaEqv (FConsT a k g) (unbindFT a1 a t1) (unbindFT a2 a t2))
                         -> ProofOf(AlphaEqv g (FTPoly a1 k t1) (FTPoly a2 k t2)) @-}

-- This relation means that w.r.t. F-Env g, expr e has F-Type in the equivalence class of t

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
  = AEWitness FEmpty v (FTBasic b) (FTBasic b) (AEBasic FEmpty (b
              ? lem_ffreeTV_subset_bindsF FEmpty (FTBasic b) Star pf_emp_b)) pf_v_b
      where
        pf_emp_b = lem_ftyping_wfft FEmpty v (FTBasic b) pf_v_b WFFEmpty
get_aewitness_from_den t v (DFunc _ _ _ _ s_x s eqv_sxs_t pf_v_b _) 
  = AEWitness FEmpty v (erase t) (FTFunc s_x s) eqv_sxs_t pf_v_b
get_aewitness_from_den t v (DExis _ _ _ _ s eqv_s_t pf_v_b _ _ _) 
  = AEWitness FEmpty v (erase t) s eqv_s_t pf_v_b
get_aewitness_from_den t v (DPoly _ k _ _ a0 s eqv_a0s_t pf_v_b _)  
  = AEWitness FEmpty v (erase t) (FTPoly a0 k s) eqv_a0s_t pf_v_b

-- Algebraic properties of Alpha Equivalence that make it an equivalence relation:

{-@ lem_alpha_refl :: g:FEnv -> { t1:FType | Set_sub (ffreeTV t1) (tvbindsF g) } 
                             -> ProofOf(AlphaEqv g t1 t1) / [ftsize t1] @-}
lem_alpha_refl :: FEnv -> FType -> AlphaEqv
lem_alpha_refl g (FTBasic b)    = AEBasic g b
lem_alpha_refl g (FTFunc t t')  
  = AEFunc g t t (lem_alpha_refl g t) t' t' (lem_alpha_refl g t')
lem_alpha_refl g (FTPoly a k t) = AEPoly g a k t a t a' eqv_t_t
  where
    a'      = fresh_varF g
    eqv_t_t = lem_alpha_refl (FConsT a' k g) (unbindFT a a' t) 

{-@ lem_alpha_commutes :: g:FEnv -> t1:FType -> t2:FType -> ProofOf(AlphaEqv g t1 t2)
                                                         -> ProofOf(AlphaEqv g t2 t1) @-}
lem_alpha_commutes :: FEnv -> FType -> FType -> AlphaEqv -> AlphaEqv
lem_alpha_commutes g t1 t2 ae_t1_t2@(AEBasic _ b) = ae_t1_t2
lem_alpha_commutes g t1 t2 (AEFunc _ s1 s2 ae_s1_s2 t1' t2' ae_t1'_t2')
  = AEFunc g s2 s1 ae_s2_s1 t2' t1' ae_t2'_t1'
      where
        ae_s2_s1   = lem_alpha_commutes g s1  s2  ae_s1_s2
        ae_t2'_t1' = lem_alpha_commutes g t1' t2' ae_t1'_t2'
lem_alpha_commutes g t1 t2 (AEPoly _ a1 k t1' a2 t2' a ae_t1'_t2')
  = AEPoly g a2 k t2' a1 t1' a ae_t2'_t1'
      where
        ae_t2'_t1' = lem_alpha_commutes (FConsT a k g) (unbindFT a1 a t1') (unbindFT a2 a t2')
                                        ae_t1'_t2'

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
      (AEPoly _ _ _ _ a3 t3' a' eqv_t2'_t3') -> AEPoly g a1 k t1' a3 t3' a' eqv_t1'_t3'
        where
          eqv_a'_t1'_t2' = lem_change_tvar_alpha g a k FEmpty (unbindFT a1 a t1') 
                                                 (unbindFT a2 a t2')  eqv_t1'_t2' a'
                                 ? toProof ( S.isSubsetOf (tvbindsF g) (bindsF g) )
                                 ? lem_ftsubFV_unbindFT a1 a (FTBasic (FTV a')) t1'
                                 ? lem_ftsubFV_unbindFT a2 a (FTBasic (FTV a')) t2'
          eqv_t1'_t3'    = lem_alpha_trans (FConsT a' k g) (unbindFT a1 a' t1')
                                           (unbindFT a2 a' t2') (unbindFT a3 a' t3')
                                           eqv_a'_t1'_t2' eqv_t2'_t3'

{-@ lem_eqvftyping_refl :: g:FEnv -> e:Expr -> t:FType -> ProofOf(HasFType g e t)
                                  -> ProofOf(WFFE g) -> ProofOf(EqvFTyping g e t) @-}
lem_eqvftyping_refl :: FEnv -> Expr -> FType -> HasFType -> WFFE -> EqvFTyping
lem_eqvftyping_refl g e t p_e_t p_g_wf = AEWitness g e t t refl_proof p_e_t
  where
    p_g_t      = lem_ftyping_wfft g e t p_e_t p_g_wf
    refl_proof = lem_alpha_refl g (t ? lem_ffreeTV_subset_bindsF g t Star p_g_t)

{-@ lem_eqvftyping_basic :: g:FEnv -> e:Expr -> b:Basic 
        -> ProofOf(EqvFTyping g e (FTBasic b)) -> ProofOf(HasFType g e (FTBasic b)) @-}
lem_eqvftyping_basic :: FEnv -> Expr -> Basic -> EqvFTyping -> HasFType
lem_eqvftyping_basic g e b (AEWitness _ _ _ s ae_s_b p_e_s) = case ae_s_b of 
  (AEBasic _ _b) -> p_e_s

-- Only type-variables are relevant in the environment for FTypes
{-@ lem_strengthen_alpha :: g:FEnv -> { x:Vname | not (in_envF x g) } -> t_x:FType
        -> { g':FEnv | not (in_envF x g') && Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> t1:FType -> t2:FType -> ProofOf(AlphaEqv (concatF (FCons x t_x g) g') t1 t2)
        -> ProofOf(AlphaEqv (concatF g g') t1 t2) @-}
lem_strengthen_alpha :: FEnv -> Vname -> FType -> FEnv -> FType -> FType -> AlphaEqv -> AlphaEqv
lem_strengthen_alpha g x t_x g' t1 t2 (AEBasic _ b) = AEBasic (concatF g g') (b
                             ? lem_binds_cons_concatF g g' x t_x)
lem_strengthen_alpha g x t_x g' t1 t2 (AEFunc _ s1 s2 ae_s1_s2 t1' t2' ae_t1'_t2')
  = AEFunc (concatF g g') s1 s2 ae_g'g_s1_s2 t1' t2' ae_g'g_t1'_t2'
      where
        ae_g'g_s1_s2   = lem_strengthen_alpha g x t_x g' s1 s2 ae_s1_s2
        ae_g'g_t1'_t2' = lem_strengthen_alpha g x t_x g' t1' t2' ae_t1'_t2'
lem_strengthen_alpha g x t_x g' t1 t2 (AEPoly _ a1 k t1' a2 t2' a_ ae_t1'_t2')
  = AEPoly (concatF g g') a1 k t1' a2 t2' a ae_ag'g_t1'_t2'
      where
        a               = a_ ? lem_binds_cons_concatF g g' x t_x
        ae_ag'g_t1'_t2' = lem_strengthen_alpha g x t_x (FConsT a k g') (unbindFT a1 a t1') 
                                               (unbindFT a2 a t2') ae_t1'_t2'

{-@ lem_weaken_alpha :: g:FEnv  -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> t1:FType -> t2:FType -> ProofOf(AlphaEqv (concatF g g') t1 t2)
        -> { x:Vname | not (in_envF x g) && not (in_envF x g') } -> t_x:FType
        -> ProofOf(AlphaEqv (concatF (FCons x t_x g) g') t1 t2) @-}
lem_weaken_alpha :: FEnv -> FEnv -> FType -> FType -> AlphaEqv -> Vname -> FType -> AlphaEqv
lem_weaken_alpha = undefined

{-@ lem_change_tvar_alpha :: g:FEnv -> { a:Vname | not (in_envF a g) } -> k:Kind 
        -> { g':FEnv | not (in_envF a g') && Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> t1:FType -> t2:FType 
        -> { p_t1_t2:AlphaEqv | propOf p_t1_t2 == AlphaEqv (concatF (FConsT a k g) g') t1 t2 }
        -> { a':Vname | not (in_envF a' g) && not (in_envF a' g') }
        -> { p'_t1_t2:AlphaEqv | propOf p'_t1_t2 == AlphaEqv (concatF (FConsT a' k g) g') 
                            (ftsubFV a (FTBasic (FTV a')) t1) (ftsubFV a (FTBasic (FTV a')) t2) &&
                                 alphaSize p_t1_t2 == alphaSize p'_t1_t2 } / [alphaSize p_t1_t2] @-} 
lem_change_tvar_alpha :: FEnv -> Vname -> Kind -> FEnv -> FType -> FType -> AlphaEqv
                              -> Vname -> AlphaEqv
lem_change_tvar_alpha g a k g' t1 t2 (AEBasic _ b) a' = case b of 
  (FTV a1) | a1 == a   -> AEBasic (concatF (FConsT a' k g) g') (FTV a')
           | otherwise -> AEBasic (concatF (FConsT a' k g) g') (FTV a1
                             ? lem_binds_consT_concatF g g' a k)
  _                    -> AEBasic (concatF (FConsT a' k g) g') b
lem_change_tvar_alpha g a k g' t1 t2 (AEFunc _ s1 s2 ae_s1_s2 t1' t2' ae_t1'_t2') a' 
  = AEFunc (concatF (FConsT a' k g) g') 
           (ftsubFV a (FTBasic (FTV a')) s1) (ftsubFV a (FTBasic (FTV a')) s2) ae_env'_s1_s2 
           (ftsubFV a (FTBasic (FTV a')) t1') (ftsubFV a (FTBasic (FTV a')) t2') ae_env'_t1'_t2' 
      where
        ae_env'_s1_s2   = lem_change_tvar_alpha g a k g' s1 s2 ae_s1_s2 a'
        ae_env'_t1'_t2' = lem_change_tvar_alpha g a k g' t1' t2' ae_t1'_t2' a'
lem_change_tvar_alpha g a k g' t1 t2 (AEPoly _ a1 kk t1' a2 t2' aa ae_t1'_t2') a' 
  = AEPoly (concatF (FConsT a' k g) g') a1 kk (ftsubFV a (FTBasic (FTV a')) t1')
           a2 (ftsubFV a (FTBasic (FTV a')) t2') aa' ae_aa'env'_t1'_t2'
      where
        aa'_               = fresh_var_excludingF (concatF (FConsT a k g) g') a'
        aa'                = aa'_ ? lem_in_env_concatF (FConsT a  k g) g' aa'_
                                  ? lem_in_env_concatF (FConsT a' k g) g' aa'_
                                  ? lem_binds_consT_concatF g g' a k
        ae_aa'env_t1'_t2'  = lem_change_tvar_alpha (concatF (FConsT a k g) g') aa kk FEmpty
                                 (unbindFT a1 aa t1') (unbindFT a2 aa t2') ae_t1'_t2' aa'
                                 ? toProof ( S.isSubsetOf (tvbindsF (concatF (FConsT a k g) g')) 
                                                          (bindsF (concatF (FConsT a k g) g')) )
                                 ? lem_ftsubFV_unbindFT a1 aa (FTBasic (FTV aa')) t1'
                                 ? lem_ftsubFV_unbindFT a2 aa (FTBasic (FTV aa')) t2'
        ae_aa'env'_t1'_t2' = lem_change_tvar_alpha g a k (FConsT aa' kk g') 
                                 (unbindFT a1 aa' t1') (unbindFT a2 aa' t2') ae_aa'env_t1'_t2' a'
                                 ? lem_commute_ftsubFV_unbindFT a (FTBasic (FTV a')) a1 aa' t1'
                                 ? lem_commute_ftsubFV_unbindFT a (FTBasic (FTV a')) a2 aa' t2'

{-@ lem_subst_alpha :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> { a:Vname | not (in_envF a g) && not (in_envF a g') } 
        -> { t_a:UserType | Set_sub (free t_a) (vbindsF  g) && Set_sub (freeTV t_a) (tvbindsF g) &&
                            Set_emp (tfreeBV t_a) && Set_emp (tfreeBTV t_a) }   -> k_a:Kind
        -> ProofOf(WFFT g (erase t_a) k_a) -> t1:FType -> t2:FType 
        -> { p_t1_t2:AlphaEqv | propOf p_t1_t2 == AlphaEqv (concatF (FConsT a k_a g) g') t1 t2 }
        -> { p'_t1_t2:AlphaEqv | propOf p'_t1_t2 == AlphaEqv (concatF g (fesubFV a (erase t_a) g'))
                            (ftsubFV a (erase t_a) t1) (ftsubFV a (erase t_a) t2) } / [alphaSize p_t1_t2] @-}
lem_subst_alpha :: FEnv -> FEnv -> Vname -> Type -> Kind -> WFFT -> FType -> FType 
                        -> AlphaEqv -> AlphaEqv
lem_subst_alpha g g' a t_a k_a p_g_ta t1 t2 (AEBasic _ b) = case b of 
  (FTV a1) | a1 == a  -> lem_alpha_refl (concatF g (fesubFV a (erase t_a) g')) (erase t_a
                             ? lem_ffreeTV_subset_bindsF g (erase t_a) k_a p_g_ta)
           | otherwise -> AEBasic (concatF g (fesubFV a (erase t_a) g')) (FTV a1
                             ? lem_binds_consT_concatF g g' a k_a)                  
  _                    -> AEBasic (concatF g (fesubFV a (erase t_a) g')) b
lem_subst_alpha g g' a t_a k_a p_g_ta t1 t2 (AEFunc _ s1 s2 ae_s1_s2 t1' t2' ae_t1'_t2')
  = AEFunc (concatF g (fesubFV a (erase t_a) g')) 
           (ftsubFV a (erase t_a) s1) (ftsubFV a (erase t_a) s2) ae_s1ta_s2ta 
           (ftsubFV a (erase t_a) t1') (ftsubFV a (erase t_a) t2') ae_t1'ta_t2'ta
      where
        ae_s1ta_s2ta   = lem_subst_alpha g g' a t_a k_a p_g_ta s1 s2 ae_s1_s2
        ae_t1'ta_t2'ta = lem_subst_alpha g g' a t_a k_a p_g_ta t1' t2' ae_t1'_t2' 
lem_subst_alpha g g' a t_a k_a p_g_ta t1 t2 (AEPoly _ a1 kk t1' a2 t2' aa_ ae_t1'_t2')
  = AEPoly (concatF g (fesubFV a (erase_ta) g')) 
           a1 kk (ftsubFV a (erase t_a) t1' ? lem_binds_consT_concatF g g' a k_a) 
           a2 (ftsubFV a (erase_ta) t2' ? lem_binds_consT_concatF g g' a k_a) aa ae_t1'ta_t2'ta
      where
        aa             = aa_ ? lem_in_env_concatF (FConsT a k_a g) g' aa_
                             ? lem_in_env_concatF g g' aa_
        erase_ta       = erase t_a ? lem_ffreeTV_subset_bindsF g (erase t_a) k_a p_g_ta
        ae_t1'ta_t2'ta = lem_subst_alpha g (FConsT aa kk g') a t_a k_a p_g_ta 
                                         (unbindFT a1 aa t1') (unbindFT a2 aa t2') ae_t1'_t2'
                                         ? lem_commute_ftsubFV_unbindFT a erase_ta
                                               (a1 ? lem_erase_freeBV t_a) aa t1'
                                         ? lem_commute_ftsubFV_unbindFT a erase_ta
                                               (a2 ? lem_erase_freeBV t_a) aa t2'

{-@ lem_alpha_ctsubst :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th) -> t1:Type -> t2:Type
        -> ProofOf(AlphaEqv (erase_env g) (erase t1) (erase t2)) 
        -> ProofOf(AlphaEqv FEmpty (erase (ctsubst th t1)) (erase (ctsubst th t2))) @-}
lem_alpha_ctsubst :: Env -> CSub -> DenotesEnv -> Type -> Type -> AlphaEqv -> AlphaEqv
lem_alpha_ctsubst Empty            th den_g_th t1 t2 ae_t1_t2 = case den_g_th of
  DEmp -> ae_t1_t2
lem_alpha_ctsubst (Cons  x t_x g') th den_g_th t1 t2 ae_t1_t2 = case den_g_th of
  (DExt  _g' th' den_g'_th' _x _tx v_x den_th'tx_vx)
    -> lem_alpha_ctsubst g' th' den_g'_th' (tsubFV x v_x t1) (tsubFV x v_x t2) ae_t1vx_t2vx
         where
           ae_t1vx_t2vx = lem_strengthen_alpha (erase_env g') x (erase t_x) FEmpty 
                                               (erase t1) (erase t2) ae_t1_t2
                                               ? lem_erase_tsubFV x v_x t1
                                               ? lem_erase_tsubFV x v_x t2
lem_alpha_ctsubst (ConsT a k_a g') th den_g_th t1 t2 ae_t1_t2 = case den_g_th of
  (DExtT _g' th' den_g'_th' _a _ka t_a p_emp_ta)
    -> lem_alpha_ctsubst g' th' den_g'_th' (tsubFTV a t_a t1) (tsubFTV a t_a t2) ae_t1ta_t2ta
         where
           p_emp_er_ta  = lem_erase_wftype Empty t_a k_a p_emp_ta
           p_g'_er_ta   = lem_weaken_many_wfft FEmpty (erase_env g') (erase t_a) k_a p_emp_er_ta 
                                               ? lem_empty_concatF (erase_env g')
           ae_t1ta_t2ta = lem_subst_alpha (erase_env g') FEmpty a t_a k_a p_g'_er_ta
                                          (erase t1) (erase t2) ae_t1_t2
                                          ? lem_erase_tsubFTV a t_a t1
                                          ? lem_erase_tsubFTV a t_a t2

-- the rest of this will be uncommented and worked out (possibly with changes to AlphaEqv) as needed


-- with bound type vars, these are only equiv up to alpha-renaming bound variables
{-@ lem_erase_subtype :: g:Env -> t1:Type -> t2:Type -> ProofOf(Subtype g t1 t2)
               -> ProofOf(AlphaEqv (erase_env g) (erase t1) (erase t2)) @-}
lem_erase_subtype :: Env -> Type -> Type -> Subtype -> AlphaEqv
lem_erase_subtype g t1 t2 (SBase _g x1 b p1 x2 p2 y _) = undefined -- AEBasic (erase_env g) b
lem_erase_subtype g t1 t2 (SFunc _g x1 s1 x2 s2 p_s2_s1 t1' t2' y p_t1'_t2')
  = AEFunc (erase_env g) (erase s1) (erase s2) ae_s1_s2 (erase t1') (erase t2') ae_g_t1'_t2'
      where
        ae_s2_s1     = lem_erase_subtype  g s2 s1 p_s2_s1
        ae_s1_s2     = lem_alpha_commutes (erase_env g) (erase s2) (erase s1) ae_s2_s1
        ae_t1'_t2'   = lem_erase_subtype (Cons y s2 g) (unbindT x1 y t1') (unbindT x2 y t2') 
                                         p_t1'_t2' ? lem_erase_tsubBV x1 (FV y) t1' 
                                                   ? lem_erase_tsubBV x2 (FV y) t2'
        ae_g_t1'_t2' = lem_strengthen_alpha (erase_env g) y (erase s2) FEmpty 
                                            (erase t1') (erase t2') ae_t1'_t2'
lem_erase_subtype g t1 t2 (SWitn _g v t_x p_v_tx _t1 x t' p_t1_t'v)
  = lem_erase_subtype g t1 (tsubBV x v t') p_t1_t'v
                      ? lem_erase_tsubBV x v t'
{- toProof ( erase t1 ? lem_erase_subtype g t1 (tsubBV x v t') p_t1_t'v
            === erase (tsubBV x v t') ? lem_erase_tsubBV x v t'
            === erase t' === erase (TExists x t_x t') ) -}
lem_erase_subtype g t1 t2 (SBind _g x t_x t _t2 y p_t_t')
  = lem_strengthen_alpha (erase_env g) y (erase t_x) FEmpty (erase t1) (erase t2) ae_yg_t1_t2
      where
        ae_yg_t1_t2 = lem_erase_subtype (Cons y t_x g) (unbindT x y t) t2 p_t_t'
                                        ? lem_erase_tsubBV x (FV y) t
{-
    = () ? lem_erase_subtype (Cons y t_x g) (unbindT x y t) t2 p_t_t'
         ? lem_erase_tsubBV x (FV y) t -}
lem_erase_subtype g t1 t2 (SPoly _g a1 k t1' a2 t2' a p_ag_t1'_t2')  = undefined {- REDO DEFN
  = AEPoly (erase_env g) a1 k (erase t1') a2 (erase t2') a ae_ag_t1'_t2'
--                            ? lem_binds_consT_concatF (erase_env g) FEmpty a k 
           --    ? toProof ( S.isSubsetOf (tvbindsF (erase_env g)) (bindsF (erase_env g)) )
      where
        ae_ag_t1'_t2' = lem_erase_subtype (ConsT a k g) (unbind_tvT a1 a t1') (unbind_tvT a2 a t2')
                                          p_ag_t1'_t2' ? toProof ( S.isSubsetOf (tvbinds g) (binds g) )
                                                       ? lem_erase_unbind_tvT a1 a t1'
                                                       ? lem_erase_unbind_tvT a2 a t2' 
-}
{-    = toProof ( normalize (erase (TPoly a1 k t1))
            === normalize (FTPoly a1 k (erase t1))
            === let a' = maxbinder (FTPoly a1 k (normalize t1)) in
                  FTPoly a' k (ftsubBV a1 (FTBasic (BTV a')) (normalize t1))
            === let a' = maxbinder (FTPoly a2 k (normalize t2)) in 
                  FTPoly a' k (ftsubBV a1 (FTBasic (BTV a')) (normalize t1)) -}

{-@ lem_alpha_in_env_ftyp :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> { x:Vname | (not (in_envF x g)) && not (in_envF x g') } 
        -> s_x:FType -> t_x:FType -> ProofOf(AlphaEqv g s_x t_x) 
        -> e:Expr -> { t:FType | Set_sub (ffreeTV t) (tvbindsF (concatF (FCons x t_x g) g')) }
        -> ProofOf(HasFType (concatF (FCons x t_x g) g') e t)
        -> ProofOf(EqvFTyping (concatF (FCons x s_x g) g') e t) @-}
lem_alpha_in_env_ftyp :: FEnv -> FEnv -> Vname -> FType -> FType -> AlphaEqv 
                              -> Expr -> FType -> HasFType -> EqvFTyping 
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t (FTBC _ b) -- = undefined {- CHECKED
  = AEWitness (concatF (FCons x s_x g) g') (Bc b) (FTBasic TBool) (FTBasic TBool)
              (lem_alpha_refl (concatF (FCons x s_x g) g') (FTBasic TBool)) p_e_t
      where
        p_e_t = FTBC (concatF (FCons x s_x g) g') b
{--}
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t (FTIC _ n) -- = undefined {- CHECKED
  = AEWitness (concatF (FCons x s_x g) g') (Ic n) (FTBasic TInt) (FTBasic TInt)
              (lem_alpha_refl (concatF (FCons x s_x g) g') (FTBasic TInt)) p_e_t
      where
        p_e_t = FTIC (concatF (FCons x s_x g) g') n
{- -}
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t p_e_t@(FTVar1 _ z _t) = case g' of
  FEmpty           -> AEWitness (FCons x s_x g) (FV x) t_x s_x eqv_xg_sx_tx (FTVar1 g x s_x)
    where
      eqv_xg_sx_tx = lem_weaken_alpha g FEmpty s_x t_x eqv_sx_tx x s_x
  (FCons _z _ g'') -> AEWitness (concatF (FCons x s_x g) g') (FV z) t t eqv_t_t p'_e_t
    where
      eqv_t_t = lem_alpha_refl (concatF (FCons x s_x g) g') (t
                      ? lem_binds_cons_concatF g g' x t_x)
      p'_e_t  = FTVar1 (concatF (FCons x s_x g) g'') (z 
                                           ? lem_in_env_concatF (FCons x t_x g) g'' z
                                           ? lem_in_env_concatF (FCons x s_x g) g'' z
                                           ? lem_in_env_concatF g g'' z) t
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t (FTVar2 _ z _t p_z_t w t_w)
  = undefined
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t (FTVar3 _ z _t p_z_t a k)
  = undefined
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t (FTPrm _ c) -- = undefined {- CHECKED
  = AEWitness (concatF (FCons x s_x g) g') (Prim c) (erase_ty c) (erase_ty c)
              (lem_alpha_refl (concatF (FCons x s_x g) g') (erase_ty c)) p_e_t
      where
        p_e_t = FTPrm (concatF (FCons x s_x g) g') c
{- -}
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t (FTAbs {}) = undefined
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t (FTApp {}) = undefined
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t (FTAbsT {}) = undefined
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t (FTAppT {}) = undefined
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t (FTLet {}) = undefined
lem_alpha_in_env_ftyp g g' x s_x t_x eqv_sx_tx e t (FTAnn {}) = undefined

{- lem_erase_ctsubst -- deleted because it's not true: erase (ctsubst th t) != erase t -}
{-
{-@ lem_erase_th_sub :: g:Env -> t1:Type -> t2:Type -> ProofOf(Subtype g t1 t2) -> th:CSub 
        -> ProofOf(AlphaEqv FEmpty (erase (ctsubst th t1)) (erase (ctsubst th t2))) @-}
lem_erase_th_sub :: Env -> Type -> Type -> Subtype -> CSub -> AlphaEqv
lem_erase_th_sub g t1 t2 p_t1_t2 th = undefined {-
toProof ( normalize (erase (ctsubst th t1))
                                              ? lem_erase_ctsubst th t1
                                            === normalize (erase t1) ? lem_erase_subtype g t1 t2 p_t1_t2
                                            === normalize (erase t2) ? lem_erase_ctsubst th t2
                                            === normalize (erase (ctsubst th t2)) ) -}
-}

{-
{-@ lem_alpha_ftapp :: g:FEnv -> v:Expr -> v_x:Expr -> t_x:FType -> t:FType
        -> ProofOf(EqvFTyping g v (FTFunc t_x t)) -> ProofOf(EqvFTyping g v_x t_x)
        -> ProofOf(EqvFTyping g (App v v_x) t) @-}
lem_alpha_ftapp :: FEnv -> Expr -> Expr -> FType -> FType -> EqvFTyping 
                        -> EqvFTyping -> EqvFTyping
lem_alpha_ftapp = undefined
-}
